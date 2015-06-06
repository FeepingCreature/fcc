#!/bin/bash
set -e

vagrant_install=`which vagrant`
if [ "$vagrant_install" == "" ]; then
    echo "Vagrant is not installed. Install vagrant from https://www.vagrantup.com/"
    exit 1
fi

rm fcc-latest.tar.bz2 || true

hashsum=`sha256sum -b fcc-ubuntu-12.04.box | head -c 64`
sha256="31687095f28e0cc8a4008cb6990dca269d142a4a292877d056be51de9caa5967"
box_url="http://fcc.afforess.com/fcc-ubuntu-12.04.box"

if [ "$hashsum" != "$sha256" ]; then
    echo "Fetching fcc-ubuntu-12.04 virtualbox image..."
    wget $box_url
    vagrant box add fcc-ubuntu-12.04 ./fcc-ubuntu-12.04.box
fi

vagrant up
vagrant ssh -- << EOF
    cp /fcc/vagrant/incremental/data/vagrant_build.sh ~/
    bash ./vagrant_build.sh
EOF

vagrant destroy -f
