package com.thealgorithms.maths;

public class AbsoluteValue {

    /**
     * Returns the absolute value of a number.
     *
     * @param number The number to be transformed
     * @return The absolute value of the {@code number}
     */
	//@ requires true; 
	//@ requires number > Integer.MIN_VALUE;
	//@ ensures \result >= 0; 
	//@ ensures \result == (number < 0 ? -number : number); 
    public static /*@ pure*/ int getAbsValue(int number) {
        return number < 0 ? -number : number;
    }
}
