package com.thealgorithms.maths;

/**
 * Find the area of various geometric shapes
 */
public class Area {

    //@ invariant POSITIVE_RADIUS != null && POSITIVE_HEIGHT != null && POSITIVE_BASE != null;

    /**
     * String of IllegalArgumentException for radius
     */
    //@ spec_public
    private static final /*@ non_null @*/ String POSITIVE_RADIUS = "Must be a positive radius";

    /**
     * String of IllegalArgumentException for height
     */
    //@ spec_public
    private static final /*@ non_null @*/ String POSITIVE_HEIGHT = "Must be a positive height";

    /**
     * String of IllegalArgumentException for base
     */
    //@ spec_public
    private static final /*@ non_null @*/ String POSITIVE_BASE = "Must be a positive base";

   
    //@ requires sideLength > 0;
    //@ ensures \result == 6 * sideLength * sideLength;
    //@ exceptional_behavior requires (sideLength <= 0);
    //@ signals (IllegalArgumentException) sideLength <= 0;
    public static /*@ pure*/  double surfaceAreaCube(final double sideLength) {
        if (sideLength <= 0) {
            throw new IllegalArgumentException("Must be a positive sideLength");
        }
        return 6 * sideLength * sideLength;
    }

    
    //@ requires radius > 0;
    //@ ensures \result == 4 * Math.PI * radius * radius;
    //@ exceptional_behavior requires (radius <= 0);
    //@ signals (IllegalArgumentException) radius <= 0;
    public static /*@ pure @*/ double surfaceAreaSphere(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 4 * Math.PI * radius * radius;
    }


    //@ requires length > 0 && width > 0;
    //@ ensures \result == length * width;
    //@ exceptional_behavior requires (length <= 0);
    //@ signals (IllegalArgumentException) length <= 0;
    //@ exceptional_behavior requires (width <= 0);
    //@ signals (IllegalArgumentException) width <= 0;
    public static /*@ pure @*/ double surfaceAreaRectangle(final double length, final double width) {
        if (length <= 0) {
            throw new IllegalArgumentException("Must be a positive length");
        }
        if (width <= 0) {
            throw new IllegalArgumentException("Must be a positive width");
        }
        return length * width;
    }

   
    //@ requires radius > 0 && height > 0;
    //@ ensures \result == 2 * (Math.PI * radius * radius + Math.PI * radius * height);
    //@ exceptional_behavior requires (radius <= 0);
    //@ signals (IllegalArgumentException) radius <= 0;
    //@ exceptional_behavior requires (height <= 0);
    //@ signals (IllegalArgumentException) height <= 0;
    public static /*@ pure @*/ double surfaceAreaCylinder(final double radius, final double height) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 2 * (Math.PI * radius * radius + Math.PI * radius * height);
    }

 
    
    //@ requires sideLength > 0;
    //@ ensures \result == sideLength * sideLength;
    //@ exceptional_behavior requires (sideLength <= 0);
    //@ signals (IllegalArgumentException) sideLength <= 0;
    public static /*@ pure @*/ double surfaceAreaSquare(final double sideLength) {
        if (sideLength <= 0) {
            throw new IllegalArgumentException("Must be a positive sideLength");
        }
        return sideLength * sideLength;
    }



    //@ requires base > 0 && height > 0;
    //@ ensures \result == base * height / 2;
    //@ exceptional_behavior requires (base <= 0);
    //@ signals (IllegalArgumentException) base <= 0;
    //@ exceptional_behavior requires (height <= 0);
    //@ signals (IllegalArgumentException) height <= 0;
    public static /*@ pure @*/ double surfaceAreaTriangle(final double base, final double height) {
        if (base <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }
        return base * height / 2;
    }

   
    
    //@ requires base > 0 && height > 0;
    //@ ensures \result == base * height;
    //@ exceptional_behavior requires (base <= 0);
    //@ signals (IllegalArgumentException) base <= 0;
    //@ exceptional_behavior requires (height <= 0);
    //@ signals (IllegalArgumentException) height <= 0;
    public static /*@ pure @*/ double surfaceAreaParallelogram(final double base, final double height) {
        if (base <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }
        return base * height;
    }

 
    
    //@ requires base1 > 0 && base2 > 0 && height > 0;
    //@ ensures \result == (base1 + base2) * height / 2;
    // @ exceptional_behavior requires (base1 <= 0);
    // @ signals (IllegalArgumentException) base1 <= 0;
    // @ exceptional_behavior requires (base2 <= 0);
    // @ signals (IllegalArgumentException) base2 <= 0;
    // @ exceptional_behavior requires (height <= 0);
    // @ signals (IllegalArgumentException) height <= 0;
    public static /*@ pure @*/ double surfaceAreaTrapezium(final double base1, final double base2, final double height) {
        if (base1 <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE + 1);
        }
        if (base2 <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE + 2);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }
        return (base1 + base2) * height / 2;
    }

    //@ requires radius > 0;
    //@ ensures \result == Math.PI * radius * radius;
    //@ exceptional_behavior requires (radius <= 0);
    //@ signals (IllegalArgumentException) radius <= 0;
    public static /*@ pure @*/ double surfaceAreaCircle(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return Math.PI * radius * radius;
    }
    //@ requires radius > 0;
    //@ ensures \result == 3.0 * Math.PI * radius * radius;
    //@ exceptional_behavior requires (radius <= 0);
    //@ signals (IllegalArgumentException) radius <= 0;
    public static double surfaceAreaHemisphere(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 3.0 * Math.PI * radius * radius;
    }

    //@ requires !Double.isNaN(radius);
    //@ requires !Double.isNaN(height);
    //@ ensures !Double.isNaN(\result);
    //@ requires height * height + radius == 0.0;
    //@ ensures \result == 1.0;
    //@ requires radius > 0.0 && height > 0.0 && Math.PI > 0.0;
    //@ ensures \result > 0;
    //@ ensures \result == Math.PI * radius * (radius + Math.pow(height * height + radius * radius, 0.5));
    //@ exceptional_behavior requires (radius <= 0);
    //@ signals (IllegalArgumentException) radius <= 0;
    //@ exceptional_behavior requires (height <= 0);
    //@ signals (IllegalArgumentException) height <= 0;
    public static double surfaceAreaCone(final double radius, final double height) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }

        return Math.PI * radius * (radius + Math.pow(height * height + radius * radius, 0.5));
    }
}