package com.thealgorithms.maths;

/* Calculate the volume of various shapes.*/
public class Volume {
	
	//@ requires sideLength > 0;
	//@ ensures \result == sideLength * sideLength * sideLength;
	//@ signals (IllegalArgumentException) sideLength <= 0; 
    public static /*@ pure @*/ double volumeCube(double sideLength) {
        return sideLength * sideLength * sideLength;
    }

	//@ requires width > 0;
	//@ requires height > 0;
	//@ requires length > 0;
	//@ ensures \result == width * height * length;
	//@ signals (IllegalArgumentException) width <= 0;
	//@ signals (IllegalArgumentException) height <= 0;
	//@ signals (IllegalArgumentException) length <= 0;
    public static /*@ pure @*/ double volumeCuboid(double width, double height, double length) {
        return width * height * length;
    }

    //@ requires radius > 0;
    //@ ensures \result == (4 * Math.PI * radius * radius * radius) / 3;
    //@ signals (IllegalArgumentException) radius <= 0;
    public static /*@ pure @*/ double volumeSphere(double radius) {
        return (4 * Math.PI * radius * radius * radius) / 3;
    }
    
    //@ requires radius > 0;
    //@ requires height > 0;
    //@ ensures \result == Math.PI * radius * radius * height;
    //@ signals (IllegalArgumentException) radius <= 0; 
    //@ signals (IllegalArgumentException) height <= 0; 
    public static /*@ pure @*/ double volumeCylinder(double radius, double height) {
        return Math.PI * radius * radius * height;
    }
    
    //@ requires radius > 0;
    //@ ensures \result == (2 * Math.PI * radius * radius * radius) / 3;
    //@ signals (IllegalArgumentException) radius <= 0; 
    public static /*@ pure @*/ double volumeHemisphere(double radius) {
        return (2 * Math.PI * radius * radius * radius) / 3;
    }
    
    //@ requires radius > 0;
    //@ requires height > 0;
    //@ ensures \result == (Math.PI * radius * radius * height) / 3;
    //@ signals (IllegalArgumentException) radius <= 0;  
    //@ signals (IllegalArgumentException) height <= 0; 
    public static /*@ pure @*/ double volumeCone(double radius, double height) {
        return (Math.PI * radius * radius * height) / 3;
    }

    //@ requires baseArea > 0;
    //@ requires height > 0;
    //@ ensures \result == baseArea * height;
    //@ signals (IllegalArgumentException) baseArea <= 0;  
    //@ signals (IllegalArgumentException) height <= 0; 
    public static /*@ pure @*/ double volumePrism(double baseArea, double height) {
        return baseArea * height;
    }

    //@ requires baseArea > 0;
    //@ requires height > 0;
    //@ ensures \result == (baseArea * height) / 3;
    //@ signals (IllegalArgumentException) baseArea <= 0;  
    //@ signals (IllegalArgumentException) height <= 0; 
    public static /*@ pure @*/ double volumePyramid(double baseArea, double height) {
        return (baseArea * height) / 3;
    }
}
