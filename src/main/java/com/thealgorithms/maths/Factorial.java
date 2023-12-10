package com.thealgorithms.maths;

public final class Factorial {
    private Factorial() {
    }

    //@ requires n >= 0;
    //@ requires n < Integer.MAX_VALUE;
    //@ ensures \result <= Long.MAX_VALUE;
    //@ exceptional_behavior requires (n < 0);
    //@ signals_only IllegalArgumentException;
    //@ code_java_math
    public static /*@ pure*/  long factorial(int n) {
        if (n < 0) {
            throw new IllegalArgumentException("Input number cannot be negative");
        }
        long factorial = 1;
        for (int i = 1; i <= n; ++i) {
            factorial *= i;
        }
        //@ assert \forall int i; 1 <= i <= n; i >=1;
        return factorial;
    }
}
