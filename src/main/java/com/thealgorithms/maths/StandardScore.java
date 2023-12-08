package com.thealgorithms.maths;

public class StandardScore {
	
	//@ requires stdDev != 0;
    //@ ensures \result == (num - mean) / stdDev;
	//@ signals (ArithmeticException) stdDev == 0; 
    public static /*@ pure @*/ double zScore(double num, double mean, double stdDev) {
        return (num - mean) / stdDev;
    }
}
