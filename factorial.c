
#include <stdio.h>

/*@ requires x >= 0;
  @ ensures \result >= 1;
  @ ensures x == 0 ==> \result == 1;
  @*/
int factorial(int x) {
    if (x <= 1) return 1;
    return x * factorial(x - 1);
}

/*@ requires n > 0;
  @ ensures \result > 0;
  @*/
int fibonacci(int n) {
    if (n <= 1) return n;
    return fibonacci(n-1) + fibonacci(n-2);
}
/*@ requires a >= 0 && b >= 0;
  @ ensures \result == a + b;
  @*/
int add(int a, int b) {
    return a + b;
}

/*@ requires n >= 0;
  @ ensures \result >= 0;
  @ ensures \result * \result <= n;
  @ ensures ( \result+1 ) * ( \result+1 ) > n;
  @*/
int integer_sqrt(int n) {
    int res = 0;
    while ((res+1)*(res+1) <= n) {
        res++;
    }
    return res;
}

/*
int main() {
    int fact_result = factorial(5);
    int fib_result = fibonacci(8);
    
    printf("Factorial of 5: %d\n", fact_result);
    printf("Fibonacci of 8: %d\n", fib_result);
    
    return 0;
}
*/





























