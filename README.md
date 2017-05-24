# CertiuCOS2
A refinement-based verification framework for preemptive OS kenerls. 

# Coq8.5
Download : https://coq.inria.fr/distrib/V8.5/files/coq-8.5.tar.gz

# Compilation
1. Dowload coq8.5
2. ./configure -prefix path_to_install_coq 
3. make && make install. 
4. vim ~/.bashrc 
5. add command "export coq85bin=path_to_install_coq" to .bashrc  
6.  make -j4 ucos_correct.vo  (32G Memory at least)

