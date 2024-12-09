int foo(){
    int count = 100;
    for (int i = 0; i < count; i++) {
        while (1){
            {
                return foo2();
            }

        }
    }
}
int foo2(){
    int count = 100;
    for (int i = 0; i < count; i++) {
        while (1){
            {
                return 5;
            }

        }
    }
}
int main(){
    int a = 10;
    a = foo();
    return a;
}
