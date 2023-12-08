package com.thealgorithms.maths;

public class StandardScore {
	
	//@ requires num > 0;
	//@ requires mean > 0;
	//@ requires stdDev > 0;
    //@ ensures \result == (num - mean) / stdDev;
	//@ signals (ArithmeticException) stdDev == 0; 
    public static double zScore(double num, double mean, double stdDev) {
        return (num - mean) / stdDev;
    }
}
