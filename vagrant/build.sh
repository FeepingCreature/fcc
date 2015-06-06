#!/bin/bash

vagrant_install=`which vagrant`
if [ "$vagrant_install" == "" ]; then
    echo "Vagrant is not installed. Install vagrant from https://www.vagrantup.com/"
    exit 1
fi

rm fcc-latest.tar.bz2

vagrant up
vagrant ssh -- << EOF
    cp /fcc/vagrant/data/vagrant_build.sh ~/
    bash ./vagrant_build.sh
EOF

#vagrant destroy -f
