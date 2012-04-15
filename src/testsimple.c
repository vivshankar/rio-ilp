#include <stdio.h>
#include <stdlib.h>

int main()
{
    int *a = (int *) malloc(2 * sizeof(int));
    a[0] = 0;
    a[1] = 0;
    memset(a, 0, sizeof(int) * 2);
    free(a);

    return 0;
}
