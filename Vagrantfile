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
      sudo opam init
      eval `opam config env`
      sudo opam update
      sudo opam install ocamlfind
      sudo opam install ocamlbuild
      sudo opam install yojson
      sudo opam depext conf-gmp.1
      sudo opam install z3
      wget -q -O- http://git.io/sWxMmg | sudo sh -s /vagrant/yices.tar.gz
      sudo opam install ocamlyices
      sudo opam install xml-light
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
