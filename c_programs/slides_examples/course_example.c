float avg(int count, int *value) {
  int total;
  int sum;
  sum = 0;
  for (int i = 0; i < count; i++) {  // Starting from 0 to include all elements
    total += value[i];
  }
  return (float) total /  count;  // Return a float for average
}

int main(void) {
  int studentNumber, count, i, sum;
  int mark[4];
  float average;
  count = 4;
  sum = 0;
  for (int i = 0; i < count; i++) {  // Loop from 0 to count-1 for array indexing
    mark[i] = (i * 30);  // Adding a missing semicolon
    sum = sum + mark[i];
    average = avg(i + 1, mark);
    if (average > 40) {
        printf("%f\n", average);
    }
  }


}