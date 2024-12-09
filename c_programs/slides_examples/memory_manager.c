int foo(int a, int b) {
    if (a == 0){
        int b = 4;
        {
            int b = 5;
            b = 4;
            a = 0;
        }
    }
    return 0;
}



int main(){
    int c = 0;
    {
        foo(0, 3);
    }
    return 0;
}
