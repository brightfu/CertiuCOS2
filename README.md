# CertiuCOS2
A refinement-based verification framework for preemptive OS kenerls. 

# Coq8.5
Download [Coq8.5](https://coq.inria.fr/distrib/V8.5/files/coq-8.5.tar.gz)
Install [Emacs](https://www.gnu.org/software/emacs/)
Install [Company-coq](https://github.com/cpitclaudel/company-coq)
Install [Visual Studio Code](https://www.gnu.org/software/emacs/) and Coq extenstions

# Compilation
1. Dowload coq8.5
2. ./configure -prefix path_to_install_coq (choose your own path)
3. make && make install. 
4. vim ~/.bashrc 
5. add command "export coq85bin=path_to_install_coq" to .bashrc
6. cd CertiuCOS2/coqimp
7. make -j4 certiucos/proofs/ucos_correct.vo  (32G Memory at least)

(You can have many versions of Coq simultaneously using different coq install path )

# New features of the verification framework 
1. Extending our separation logic assertion to support half permission, which is able to specify more complicated protocols used in OS kernels.
2. Do NOT require arbitrary client code for system APIs, we can specify our expectation for the client code with the specification language.
3. Extend the framework to support reasoning about task creation and deletion, and the corresponding APIs in uC/OS-II have been verified in our new framework.

# Following features are NOT allowed in our C language 

1. union type :
   ```C
    union Id{
       //... member 
    };
   ```
2. float and double types 
    
3. cast integers to pointers : 
   ```C
   int a = 1;
   int * p = &a;
    ```
4. pointer arithmetic :
   ```C
   int *q ;
   //假设当前地址为 ： q = 2231H 
   q += 4 ; // q = q + 4*4 = 2239H
   ```

4. FOR loop : (Now we only have while loop, we can encode FOR loop with our while loop)
   ```C
   for( int a = 10; a < 20; a = a + 1 )
   {
      printf("value of a: %d\n", a);
   }
   ```
5. Kernel API could not access the application's resource (verification reason). Our framework physically partitions the states between applications and kernels, and we do not allow the resource to be passed from the application to the kernel. For example, we cannot write a kenel API "f" as below, which might be used by a user application "g":
   ```C
   void f (int * p){
      * p = 1;
      return;
   }
   
   void g (){
      int a = 0;
      f(&a);
      return;
   }
   ```
