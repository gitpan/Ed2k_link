use strict;
use warnings;
use Module::Build;

my $builder = Module::Build->new(
    module_name         => 'Ed2k_link',
    license             => 'perl',
    dist_author         => 'Valery Kalesnik <valkoles@gmail.com>',
    dist_version_from   => 'lib/Ed2k_link.pm',
    build_requires => {
        'Test::More' => 0,
    },
    requires => {
        'Carp' => 0,
        'File::Basename' => 0,
        'URI::Escape' => 0,
        'Digest::MD4' => 0,
        'Digest::SHA1' => 0
    },
    add_to_cleanup      => [ 'Ed2k_link-*' ],
);

$builder->create_build_script();
