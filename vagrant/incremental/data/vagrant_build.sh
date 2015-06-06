#!/bin/bash
 
tools="http://svn.dsource.org/projects/scrapple/trunk/tools/tools/"

#copy over ffc
cp -r /fcc ~/fcc
cd ~/fcc
svn checkout $tools

export LIBRARY_PATH=/usr/lib/i386-linux-gnu/
export C_INCLUDE_PATH=/usr/include/i386-linux-gnu/

#build fcc
make all

#compress fcc binary
strip fcc
upx fcc

#archive final fcc build
mkdir ~/fcc-latest
cp *.nt ~/fcc-latest/
cp *.h ~/fcc-latest/
cp -r std/ tests/ ~/fcc-latest/
cp ./fcc ~/fcc-latest/
cd ~
tar -cvjSf fcc-latest.tar.bz2 fcc-latest/

#copy to host machine
cp fcc-latest.tar.bz2 /vagrant
