# semi-c interpreter
## Usage
### Rust
To build and run you need to have rust installed. You can use the rustup toolchain installer to install rust:

https://www.rust-lang.org/tools/install
### Build
At first compile the program
```bash
cargo build --release
```
the binary is ``./target/release/semi-C-interpreter``
### Run
> ``semi-C-interpreter`` refers to the binary previously build, but you may prefer to use ``cargo run -- <arguments>`` instead of using the built binary
#### Help
```bash
./semi-C-interpreter -h
```
#### Interpret c source code file
```bash
./semi-C-interpreter -p <PATH>
```
the example of the course with the function call printed
```bash
cargo run -- -p c_programs/slides_examples/course_example.c --print-function-call
```
#### Debug
There is two kinds of debug. The one from the logging and if you want to see the flow in live.
##### Logging
Set the environment variable ``RUST_LOG`` to ``debug``
```bash
# for linux
export RUST_LOG=debug 
```
But this feature only enable the debug logs which are not interesting
##### Display flow
> Be sure not to have activated the logs

If you want to use see the flow in live add ``-d`` to the command line

```bash
./semi-C-interpreter -p <PATH> -d
```
By default, it will sleep during 50 milliseconds between each step, but you can change it with ``-s <milliseconds>``

```bash
./semi-C-interpreter -p <PATH> -d -s 100
```
You also can run it manually, but you will have to press ``enter`` between each step

```bash
./semi-C-interpreter -p <PATH> -d -m
```

## Features
## Type
- Int
- Float
- Pointer
- 
### All unary operators
- ``` +x ```
- ``` -x ```
- ``` !x ```
- ``` ++x ```
- ``` x++ ```
- ``` --x ```
- ``` x-- ```
- ``` &x ```
- ``` *x ```

Operators works a least with ```int``` and ```float```, pointer arithmetic is not implemented, addresses have some minor flow for example ```&(*x[1])``` will just do ```x[1]``` which shouldn't happen.
### All binary operators
- ``` x[y] ```
- ``` x*y ```
- ``` x/y ```
- ``` x%y ```
- ``` x+y ```
- ``` x-y ```
- ``` x>>y ```
- ``` x<<y ```
- ``` x<y ```
- ``` x>y ```
- ``` x<y ```
- ``` x<=y ```
- ``` x>=y ```
- ``` x==y ```
- ``` x&y ```
- ``` x^y ```
- ``` x|y ```
- ``` x&&y ```
- ``` x||y ```
- ``` x=y ```
- ``` x*=y ```
- ``` x/=y ```
- ``` x%=y ```
- ``` x+=y ```
- ``` x-=y ```
- ``` x<<=y ```
- ``` x>>=y ```
- ``` x&=y ```
- ``` x^=y ```
- ``` x|=y ```

Not all feature have been well tested but everything seems to work.
### Flow
#### If else
```c
if (...){
    ...
}else{
    ...
}
```
#### For loop
```c
int count = 20;
int x;
for (int i = 0; i < count; i++) {
x++;
}
```
#### While loop
```c
while (...) {
 ...
}
```
### printf
you can use printf like in c
```
printf("Number1: %d, Number 2: %f", x, y);
```
The variable will take the place for on of the following tag:
```
["%c","%d","%e","%f", "%lf", "%lf", "%lu", "%i", "%p", "%s"]
```
But in fact there is no differences between them, they will just be replaced by the string of the value.
(a ``float`` with ``%d`` will still be evaluated as a float)

> they may be some issue with the \n
### Differences from c
- Variable like ``float`` and ``int`` are set to ``0`` by default
- You may not be able to play with the stack because the memory is to not a 1-1 representation. 
- Arguments for the main function are not used
- Even if main should return a int, the interpreter will not check the type and just return the value asked to be return. So you can return whatever you want at the end of the program.