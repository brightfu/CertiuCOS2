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
6. cd CertiuCOS2/coqimp
7. make -j4 certiucos/proofs/ucos_correct.vo  (32G Memory at least)

# New features of the verification framework 
1. Extending our separation logic assertion to support half permission, which is able to specify more complicated protocols used in OS kernels.
2. Do NOT require arbitrary client code for system APIs, we can specify our expectation for the client code with the specification language.
3. Extend the framework to support reasoning about task creation and deletion, and the corresponding APIs in uC/OS-II have been verified in our new framework.
