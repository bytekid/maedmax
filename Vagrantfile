# -*- mode: ruby -*-
# vi: set ft=ruby :

# All Vagrant configuration is done below. The "2" in Vagrant.configure
# configures the configuration version (we support older styles for
# backwards compatibility). Please don't change it unless you know what
# you're doing.
Vagrant.configure("2") do |config|
  # Every Vagrant development environment requires a box. You can search for
  # boxes at https://vagrantcloud.com/search.
  config.vm.box = "hashicorp/bionic64"

  # Provision the VM with maedmax.
  config.vm.provision "shell", privileged: false, inline: <<-SHELL
    yes | {
      sudo apt-get update
      sudo apt-get install opam
      sudo apt-get install m4
      sudo apt-get install python3-distutils
      sudo opam init
      eval `opam config env`
      sudo opam update
      sudo opam install ocamlfind
      sudo opam install ocamlbuild
      sudo opam install yojson
      sudo opam depext conf-gmp.1
      wget -q -O- http://git.io/sWxMmg | sudo sh -s /vagrant/yices.tar.gz
      sudo opam install ocamlyices
      sudo opam install xml-light
      sudo opam install zarith
      LIB_PATH="/home/vagrant/.opam/system/lib"
      Z3_PATH="$LIB_PATH/z3"
      Z3_PATH_ALT="$LIB_PATH/Z3"
      CMD="export LD_LIBRARY_PATH=\"$Z3_PATH/lib:$LD_LIBRARY_PATH\""
      echo "$CMD" >> .bashrc
      eval "$CMD"
      git clone https://github.com/Z3Prover/z3
      cd z3
      git checkout 79734f26aee55309077de1f26e9b6f50ecd99ceb # version 4.8.9 official release
      python3 scripts/mk_make.py --ml --prefix="$Z3_PATH"
      cd build; sudo make
      sudo make install
      sudo cp "$Z3_PATH/lib/libz3.so" "$Z3_PATH" # I have no idea why this is necessary, but it is, and mv instead of cp doesn't work
      sudo mv $Z3_PATH_ALT/* "$Z3_PATH" # merge z3 directories (I'm not sure why they're separate to begin with)
      sudo rm -r "$Z3_PATH_ALT"
      cd ~
      CMD="cp -r /vagrant maedmax-build; cd maedmax-build"
      echo "$CMD" >> buildlocal.sh
      eval "$CMD"
      make
      mv maedmax ..
      cd ..
      rm -rf maedmax-build
    }
    exit
  SHELL
end
