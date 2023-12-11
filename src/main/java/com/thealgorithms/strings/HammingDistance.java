package com.thealgorithms.strings;

/* In information theory, the Hamming distance between two strings of equal length
is the number of positions at which the corresponding symbols are different.
https://en.wikipedia.org/wiki/Hamming_distance
*/
//@ code_java_math spec_java_math
public class HammingDistance {


    //@ requires s1 != null && s2 != null;
    //@ requires s1.length() == s2.length();
    //@ requires s1.length() < Integer.MAX_VALUE;
    //@ requires s2.length() < Integer.MAX_VALUE;
    // @ ensures \result >= 0;
    //@ also
    //@ exceptional_behavior requires (s1.length() != s2.length());
    //@ signals_only Exception;
    //@ pure helper
    public static int calculateHammingDistance(String s1, String s2) throws Exception {
        if (s1.length() != s2.length()) {
            throw new Exception("String lengths must be equal");
        }

        int stringLength = s1.length();
        int counter = 0;

        for (int i = 0; i < s1.length(); i++) {
            if (s1.charAt(i) != s2.charAt(i)) {
                counter++;
            }
        }
        return counter;
    }
}
