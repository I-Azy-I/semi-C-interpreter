int foo(int n_a, float **n_b, float n_c){
    return n_c;
}

int main(){
    int a = 111;
    float c = 7.0;
    float b[4] = {c+10, 2*c + 10, 39.0, 42.0};
    c = foo(a, &b, c);
}