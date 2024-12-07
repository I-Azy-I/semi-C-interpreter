void swap(int* arr, int i, int j) {
    int temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
}

void bubbleSort(int arr[], int n) {
    for (int i = 0; i < n - 1; i++) {

        // Last i elements are already in place, so the loop
        // will only num n - i - 1 times
        for (int j = 0; j < n - i - 1; j++) {
            if (arr[j] > arr[j + 1])
                swap(arr, j, j + 1);
        }
    }
}

int main() {
    int arr[7] = {2,4,5,6,1,4,7};
    int n = 7;

    // Calling bubble sort on array arr
    bubbleSort(arr, n);

    for (int i = 0; i < n; i++)
        printf("%d ", arr[i]);

    return arr[5];
}