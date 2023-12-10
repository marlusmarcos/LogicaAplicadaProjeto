package com.thealgorithms.maths;

// POWER (exponentials) Examples (a^b)
public class Pow {

    public static void main(String[] args) {
        assert pow(2, 0) == Math.pow(2, 0); // == 1
        assert pow(0, 2) == Math.pow(0, 2); // == 0
        assert pow(2, 10) == Math.pow(2, 10); // == 1024
        assert pow(10, 2) == Math.pow(10, 2); // == 100
    }

    //@ requires Double.isNaN(b);
    //@ ensures !Double.isNaN(\result);
    public static /*@ pure*/ long pow(int a, int b) {
        long result = 1;
        //@ maintaining 1 <= i <= b;
        // @ maintaining \forall int i; 1 <= i < b;
        for (int i = 1; i <= b; i++) {
            result *= a;
        }
        return result;
    }
}
