#!/usr/bin/perl
package Ed2k_link;
our $VERSION = '20090427';

use strict;
use warnings;
use base qw(Exporter);
our @EXPORT = ();
our @EXPORT_OK = ();

use Carp qw(croak);
use File::Basename qw();
use URI::Escape;
use Digest::MD4 qw(md4_hex);
use Digest::SHA1 qw(sha1);

use constant {
  CHANK_SIZE => 9_728_000,
  BLOCK_SIZE => 184_320,
};

sub encode_base32 {
  my %bits_to_char = qw# 00000 A 00001 B 00010 C 00011 D 00100 E 00101 F 00110 G 00111 H
			 01000 I 01001 J 01010 K 01011 L 01100 M 01101 N 01110 O 01111 P
			 10000 Q 10001 R 10010 S 10011 T 10100 U 10101 V 10110 W 10111 X
			 11000 Y 11001 Z 11010 2 11011 3 11100 4 11101 5 11110 6 11111 7
		       #;
  my ($source, $bits, $res) = shift;
  $bits .= unpack('B*', substr($source, $_, 1)) for 0 .. length($source) - 1;
  # generally $bits could be not 40 * k length and have to be padding. but not in our case
  $res .= $bits_to_char{$&} while $bits =~ m/.{5}/g;
  $res;
}

sub define_base_trees_orientation { # l/r, array_ref, start_idx, end_idx
  if ($_[2] - $_[3] >= 0) {
    $_[1][$_[2]] = $_[0];
  } elsif ($_[2] + 1 == $_[3]) {
    $_[1][$_[2]] = 'l';
    $_[1][$_[3]] = 'r';
  } else {
    my $med = sprintf("%d", ($_[2] + $_[3]) / 2);
    $med-- if $_[0] eq 'r' && $_[2] + $_[3] == $med * 2;
    &define_base_trees_orientation('l', $_[1], $_[2], $med++);
    &define_base_trees_orientation('r', $_[1], $med, $_[3]);
  }
}

sub get_root_hash {		# l/r, array_ref, start_idx, end_idx
  my $med = $_[3];
  if ($_[2] - $_[3] >= 0) {
    return;
  } elsif ($_[3] - $_[2] > 1) {
    $med = sprintf("%d", ($_[2] + $_[3]) / 2);
    $med-- if $_[0] eq 'r' && $_[2] + $_[3] == $med * 2;
    &get_root_hash('l', $_[1], $_[2], $med++);
    &get_root_hash('r', $_[1], $med, $_[3]);
  }
  $_[1] -> [$_[2]] = sha1($_[1] -> [$_[2]], $_[1] -> [$med]);
}

sub from_file {
  my $either = shift;
  %$either = () if ref $either;
  my $file = shift;
  return undef unless defined $file;

  # file must exist and be not empty!
  return undef unless -f $file && -s $file;

  my $self = { path_to_file => $file };
  $self -> {filename} = File::Basename::fileparse($file);
  $self -> {escaped_filename} = uri_escape_utf8($self -> {filename}, '^A-Za-z0-9\-_.!~*\'()\@#[]\$&+,;=');
  $self -> {size} = -s $file;
  # hashes. step 1
  my @aich_tree;
  {
    my $base_blocks = sprintf("%d", $self -> {size} / CHANK_SIZE);
    $base_blocks-- if $self -> {size} == $base_blocks * CHANK_SIZE;
    &define_base_trees_orientation('l', \@aich_tree, 0, $base_blocks);
  }

  {
    open my $f, '<', $file or return undef;
    binmode $f;
    my ($t, $readed_bytes);
    my $md4 = Digest::MD4 -> new;
    while (defined($readed_bytes = read $f, $t, CHANK_SIZE)) {
      $md4 -> add($t);
      $self -> {hash} .= $md4 -> clone -> digest;
      push @{$self -> {p}}, uc $md4 -> hexdigest;
      if ($readed_bytes) {
	my $pos = 0;
	my @t_sha1;
	while ($pos < $readed_bytes) {
	  push @t_sha1, sha1(substr($t, $pos, BLOCK_SIZE));
	  $pos += BLOCK_SIZE;
	}
	# sha1 for chank
	&get_root_hash($aich_tree[$#{$self -> {p}}], \@t_sha1, 0, $#t_sha1);
	$aich_tree[$#{$self -> {p}}] = $t_sha1[0];
      }
      last if $readed_bytes != CHANK_SIZE;
    }
    close $f;
    return undef unless defined $readed_bytes
      && $self -> {size} == $#{$self -> {p}} * CHANK_SIZE + $readed_bytes;
  }

  # hashes. step 2
  if (@{$self -> {p}} == 1) {
    $self -> {hash} = $self -> {p}[0];
  } else {
    $self -> {hash} = uc md4_hex($self -> {hash});
  }
  # aich hashset
  &get_root_hash('l', \@aich_tree, 0, $#aich_tree);
  $self -> {aich} = encode_base32($aich_tree[0]);
  $self -> {reliable} = 1;

  if (ref $either) {
    %$either = %$self;
    1;
  } else {
    bless $self, $either;
  }
}

sub from_link {
  my $either = shift;
  %$either = () if ref $either;
  my $link = shift;
  return undef unless defined $link;
  return undef unless $link =~ m#^ed2k://\|file\|([\d\D]+?)\|(\d+)\|([\da-f]{32})\|#i;
  my $self;
  $self -> {escaped_filename} = $1;
  $self -> {filename} = uri_unescape($1);
  $self -> {size} = $2;
  $self -> {hash} = uc $3;
  $self -> {reliable} = 1;
  $link = "|$'";
  return undef unless $self -> {size};

  # complete hashset
  if ($link =~ m/\|p=([\d\D]*?)\|/) {
    my $t = uc $1;
    $link = "|$`$'";
    return undef unless $t =~ m/^([\dA-F]{32}(:[\dA-F]{32})*)$/;

    my @t = split ':', $1;
    $t = sprintf("%d", $self -> {size} / CHANK_SIZE);
    $t++ if $self -> {size} >= $t * CHANK_SIZE;
    return undef unless $t == @t;

    if (@t == 1) {
      return undef unless $self -> {hash} eq $t[0];
    } else {
      my $t = '';
      foreach my $bh (@t) {
	$t .= chr(hex($&)) while $bh =~ m/../g;
      }
      return undef unless $self -> {hash} eq uc md4_hex($t);
      $self -> {reliable} = 0;
    }
    $self -> {p} = \@t;
  }
  $self -> {p}[0] = $self -> {hash} if $self -> {size} < CHANK_SIZE && not exists $self -> {p};

  # aich
  if ($link =~ m/\|h=([\d\D]*?)\|/) {
    $self -> {aich} = uc $1;
    $link = "|$`$'";
    return undef unless $self -> {aich} =~ m/^[A-Z2-7]{32}$/;
    $self -> {reliable} = 0;
  }

  if (ref $either) {
    %$either = %$self;
    1;
  } else {
    bless $self, $either;
  }
}

sub ok {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  return exists $instance -> {escaped_filename} && exists $instance -> {size} && exists $instance -> {hash};
}

sub filename {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {filename};
}

sub escaped_filename {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {escaped_filename};
}

sub filesize {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {size};
}

sub hash {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {hash};
}

sub has_complete_hashset {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  exists $instance -> {p} && @{$instance -> {p}};
}

sub complete_hashset {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> has_complete_hashset ?
    join ':', @{$instance -> {p}}
      : undef;
}

sub has_aich {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  exists $instance -> {aich};
}

sub aich {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {aich};
}

sub link {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  my $optional = shift;
  return undef unless $instance -> ok;
  my $res = 'ed2k://|file|'.$instance -> escaped_filename.'|'.$instance -> filesize.'|'.$instance -> hash.'|';
  if (defined $optional) {
    # complete hashset
    $res .= "p=" . $instance -> complete_hashset . '|'
      if $optional =~ /p/ && $instance -> filesize >= CHANK_SIZE && $instance -> has_complete_hashset;
    # aich hashset
    $res .= 'h=' . $instance -> aich . '|' if $optional =~ /h/ && $instance -> has_aich;
  }
  $res .= '/';
}

sub is_reliable {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {reliable};
}

sub set_reliable {
  ref(my $instance = shift) or croak "class usage! need to be instance usage";
  $instance -> {reliable} = 1;
}

sub equal {
  my $class = shift;
  return undef unless @_ == 2;
  my $one = shift;
  my $two = shift;
  my $res = $one -> ok && $two -> ok && $one -> filesize == $two -> filesize && $one -> hash eq $two -> hash;
  return undef unless $res;
  $res = $one -> complete_hashset eq $two -> complete_hashset
    if $one -> has_complete_hashset && $two -> has_complete_hashset;
  return undef unless $res;
  $res = $one -> aich eq $two -> aich
    if $one -> has_aich && $two -> has_aich;
  return undef unless $res;

  # cases with copying complete hash or aich and setting reliable flag
  if ($one -> is_reliable && $two -> is_reliable) {
    if ($one -> has_complete_hashset && !$two -> has_complete_hashset) {
      $two -> {p} = $one -> {p};
    } elsif (!$one -> has_complete_hashset && $two -> has_complete_hashset) {
      $one -> {p} = $two -> {p};
    }
    if ($one -> has_aich && !$two -> has_aich) {
      $two -> {aich} = $one -> {aich};
    } elsif (!$one -> has_aich && $two -> has_aich) {
      $one -> {aich} = $two -> {aich};
    }
  } elsif ($one -> is_reliable) {
    my $t = 0;
    if ($one -> has_complete_hashset) {
      $t++;
      $two -> {p} = $one -> {p};
    }
    if ($one -> has_aich) {
      $t++;
      $two -> {aich} = $one -> {aich};
    }
    $t-- if $two -> has_complete_hashset;
    $t-- if $two -> has_aich;
    $two -> set_reliable if $t >= 0;
  } elsif ($two -> is_reliable) {
    my $t = 0;
    if ($two -> has_complete_hashset) {
      $t++;
      $one -> {p} = $two -> {p};
    }
    if ($two -> has_aich) {
      $t++;
      $one -> {aich} = $two -> {aich};
    }
    $t-- if $one -> has_complete_hashset;
    $t-- if $one -> has_aich;
    $one -> set_reliable if $t >= 0;
  }

  $res;
}

1;
__END__

=head1 NAME

Ed2k_link - module for creation and work with eD2K links

=head1 VERSION

Version 20090427

=head1 SYNOPSIS

  use Ed2k_link;

  print Ed2k_link -> from_file('c:\\temp\\new_movie.mkv') -> link('h') . "\n";

  my $emule = Ed2k_link -> from_file('eMule0.49c.zip') or die 'something wrong with file!');

  my $sources = Ed2k_link -> from_link('ed2k://|file|eMule0.49c.zip|2868871|0F88EEFA9D8AD3F43DABAC9982D2450C|/') or die 'incorrect link!';

  $sources -> from_link('ed2k://|file|eMule0.49c-Sources.zip|5770302|195B6D8286BF184C3CC0665148D746CF|/') or die 'incorrect link!';

  print $emule -> link('h') if $emule -> filesize <= 10 * 1024 * 1024, "\n";

  if (Ed2k_link -> equal($emule, $sources) {
    print "files " . $emule -> filename . " and " . $sources -> filename . " are the same\n";
  }

  print Ed2k_link -> from_file('/somethere/cool_file.txt') -> link('hp');

=head1 DESCRIPTION

Ed2k_link module for generation eD2K links from files with correct hash, AICH hash and complete hashset fields.
Also it can work with already created links (e. g. from textfile).

=head1 CLASS METHODS

=head2 from_file

Can be called as class or instance method:

  my $t = Ed2k_link -> from_file('file_1.txt') or die 'something wrong!';

  $t -> from_file('file_2.txt') or die 'something wrong!';

Creates all fields of eD2K link including hash, AICH hashset, complete hashset.

In case of any error returns undef and object doesn't hold any link information.

Sets Reliable flag to true.

=head2 from_link

Can be called as class or instance method:

  my $tl = Ed2k_link -> from_link('ed2k://|file|eMule0.49c.zip|2868871|0F88EEFA9D8AD3F43DABAC9982D2450C|/')
    or die 'incorrect link!';

  $t1 = from_link('ed2k://|file|eMule0.49c-Sources.zip|5770302|195B6D8286BF184C3CC0665148D746CF|/')
    or die 'incorrect link!';

Takes mandatory (filename/size/hash) and optional (AICH hash, complete hashset) fields from link.
Checks some correctness of fields (acceptable symbols, length, ...).
If link in parameter has complete hashset, checks compliance between hash and complete hashset.

In case of any incorrectness returns undef and object doesn't hold any link information.

If link in parameter has AICH and/or complete hashset, sets Reliable flag to false. Otherwise it's true.

=head2 ok

Instance only method. Returns true if object was successfully created and holds all required fields;

  &do_something if $t1 -> ok;

=head2 link

Instance only method. Returns string representation of link. Can have parameter with options:

    h - include (if present) AICH hash (recommended)
    p - include (if present) complete hashset

  my $link1 = $t -> link;
  my $link_with_aich = $t -> link('h');
  my $link_with_hashset = $t -> link('p');
  my $iron_link = $t -> link('hp');

=head2 filename

Instance method. Returns filename;

  print $t -> filename;

=head2 escaped_filename

Instance method. Returns escaped filename (as in link);

  print $t -> escaped_filename;

=head2 filesize

Instance method. Returns filesize;

=head2 hash

Instance method. Returns hash field from link;

=head2 has_complete_hashset

Instance method. Returns true if object has complete hashset, false otherwise;

=head2 complete_hashset

Instance method. Returns complete hashset if object has it. undef otherwise;

=head2 has_aich

Instance method. Returns true if object has aich hash, false otherwise;

=head2 aich

Instance method. Returns AICH hash if object has it. undef otherwise;

=head2 is_reliable

Instance method. Returns true if object is reliable, false otherwise;

=head2 set_reliable

Instance method. Sets Reliable flag for object. Use it very carefully, or you could end up with fake links,
that lead nowhere and you couldn't download anything with them.

Carefully means: you got string link from someone, who you trust. Or you previously created it from file
by yourself and saved somethere. And now you're reading those links from file of database.
Such using of this method is appropriated;

=head2 equal

Class only method.
Compares two Ed2k_link objects by complex rules. Returns true if they point to the same file.
Could fill some fields of one object with other's objects fields. Also can set Reliable flag.

  print "hey! they are the same!" if Ed2k_link -> equal($t1, $t2);

=head1 AUTHOR

Valery Kalesnik, C<< <valkoles at gmail.com> >>

=head1 BUGS

Please report any bugs or feature requests to C<bug-ed2k_link at rt.cpan.org>, or through
the web interface at L<http://rt.cpan.org/NoAuth/ReportBug.html?Queue=Ed2k_link>.  I will be notified, and then you'll
automatically be notified of progress on your bug as I make changes.




=head1 SUPPORT

You can find documentation for this module with the perldoc command.

    perldoc Ed2k_link


You can also look for information at:

=over 4

=item * RT: CPAN's request tracker

L<http://rt.cpan.org/NoAuth/Bugs.html?Dist=Ed2k_link>

=item * AnnoCPAN: Annotated CPAN documentation

L<http://annocpan.org/dist/Ed2k_link>

=item * CPAN Ratings

L<http://cpanratings.perl.org/d/Ed2k_link>

=item * Search CPAN

L<http://search.cpan.org/dist/Ed2k_link/>

=back

=head1 COPYRIGHT & LICENSE

Copyright 2009 Valery Kalesnik, all rights reserved.

This program is free software; you can redistribute it and/or modify it
under the same terms as Perl itself.


=cut
