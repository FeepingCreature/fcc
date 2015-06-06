#!/bin/bash
 
tools="http://svn.dsource.org/projects/scrapple/trunk/tools/tools/"
 
#install git, svn, libc
sudo apt-get install git subversion libc6-dev libgmp-dev -y

#install llvm 3.2
sudo add-apt-repository ppa:kxstudio-team/builds -y
sudo apt-get update
sudo apt-get install llvm -y
 
#sudo ln -s /usr/lib/i386-linux-gnu/libgmp.so /usr/lib/libgmp.so
#sudo ln -s /usr/include/i386-linux-gnu/sys/ /usr/include/sys

#copy over ffc
cp -r /fcc ~/fcc
cd ~/fcc
svn checkout $tools
 
#export for gcc build
export LIBRARY_PATH=/usr/lib/$(gcc -print-multiarch)
export C_INCLUDE_PATH=/usr/include/$(gcc -print-multiarch)
export CPLUS_INCLUDE_PATH=/usr/include/$(gcc -print-multiarch)

#setup gcc
cd ~
wget "ftp://ftp.gnu.org/gnu/gcc/gcc-4.5.3/gcc-core-4.5.3.tar.bz2" 
tar xvf "gcc-core-4.5.3.tar.bz2"
 
#setup gdc
git clone https://github.com/D-Programming-GDC/GDC.git
cd GDC/
git checkout 50a7fea0718055dc124069d6d6f49251d9ab9c92
mv d/ ./../gcc-4.5.3/gcc/
 
cd ./../gcc-4.5.3
 
#gcc deps
wget ftp://ftp.gnu.org/gnu/mpc/mpc-1.0.3.tar.gz
tar xvf mpc-1.0.3.tar.gz 
rm mpc-1.0.3.tar.gz 
mv mpc-1.0.3/ mpc
 
wget http://www.mpfr.org/mpfr-2.4.2/mpfr-2.4.2.tar.bz2
tar xvf mpfr-2.4.2.tar.bz2 
rm mpfr-2.4.2.tar.bz2 
mv mpfr-2.4.2/ mpfr
 
wget ftp://gcc.gnu.org/pub/gcc/infrastructure/gmp-4.3.2.tar.bz2
tar xvf gmp-4.3.2.tar.bz2 
rm gmp-4.3.2.tar.bz2
mv gmp-4.3.2/ gmp
 
#patch gcc for gdc support
./gcc/d/setup-gcc.sh
 
#build gcc
./configure --disable-multilib
make
sudo make install
 
 #build fcc
cd ./../fcc
make all

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
