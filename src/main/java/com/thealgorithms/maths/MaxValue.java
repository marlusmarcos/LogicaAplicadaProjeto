package com.thealgorithms.maths;

public final class MaxValue {
    private MaxValue() {
    }
    /**
     * Returns the greater of two {@code int} values. That is, the result is the
     * argument closer to the value of {@link Integer#MAX_VALUE}. If the
     * arguments have the same value, the result is that same value.
     *
     * @param a an argument.
     * @param b another argument.
     * @return the larger of {@code a} and {@code b}.
     */
    //@ requires true; 
    //@ requires Integer.MIN_VALUE < a < Integer.MAX_VALUE;
    //@ requires Integer.MIN_VALUE < b < Integer.MAX_VALUE;
    //@ ensures \result == a || \result == b; 
    //@ ensures (\result == a && a >= b) || (\result == b && b > a);
    public static int max(int a, int b) {
        return a >= b ? a : b;
    }
}
