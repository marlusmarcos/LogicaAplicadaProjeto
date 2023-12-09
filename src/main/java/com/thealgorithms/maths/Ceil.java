package com.thealgorithms.maths;

public class Ceil {

    /**
     * Returns the smallest (closest to negative infinity)
     *
     * @param number the number
     * @return the smallest (closest to negative infinity) of given
     * {@code number}
     */
	//@ requires !Double.isNaN(number);
	//@ ensures \result >= (double) number || \result == (int) number || \result == (int) number + 1;
    public static double ceil(double number) {
        if (number - (int) number == 0) {
            return number;
        } else if (number - (int) number > 0) {
            return (int) (number + 1);
        } else {
            return (int) number;
        }
    }
}
