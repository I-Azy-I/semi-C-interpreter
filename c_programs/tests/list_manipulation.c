int main(void) {
    int x[10], y;
    x[6] = 10;
    y += 5;
    int z[3];
    z[1] = 10;
    z[1] *= 3;
    z[0] = 2;
    z[0] *= z[1] - y / 20;
    return z[0];
}