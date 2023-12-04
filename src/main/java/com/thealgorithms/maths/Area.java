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

    /* @ ensures \result > 0; */
    // @ ensures \result == 6 * sideLength * sideLength;
    //@ requires sideLength > 0;
    public static /*@ pure @*/ double surfaceAreaCube(final double sideLength) {
        if (sideLength <= 0) {
            throw new IllegalArgumentException("Must be a positive sideLength");
        }
        return 6 * sideLength * sideLength;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == 4 * Math.PI * radius * radius;
    //@ requires radius > 0;
    public static /*@ pure @*/ double surfaceAreaSphere(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 4 * Math.PI * radius * radius;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == length * width;
    //@ requires length > 0 && width > 0;
    public static /*@ pure @*/ double surfaceAreaRectangle(final double length, final double width) {
        if (length <= 0) {
            throw new IllegalArgumentException("Must be a positive length");
        }
        if (width <= 0) {
            throw new IllegalArgumentException("Must be a positive width");
        }
        return length * width;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == 2 * (Math.PI * radius * radius + Math.PI * radius * height);
    //@ requires radius > 0 && height > 0;
    public static /*@ pure @*/ double surfaceAreaCylinder(final double radius, final double height) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 2 * (Math.PI * radius * radius + Math.PI * radius * height);
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == sideLength * sideLength;
    //@ requires sideLength > 0;
    public static /*@ pure @*/ double surfaceAreaSquare(final double sideLength) {
        if (sideLength <= 0) {
            throw new IllegalArgumentException("Must be a positive sideLength");
        }
        return sideLength * sideLength;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == base * height / 2;
    //@ requires base > 0 && height > 0;
    public static /*@ pure @*/ double surfaceAreaTriangle(final double base, final double height) {
        if (base <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }
        return base * height / 2;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == base * height;
    //@ requires base > 0 && height > 0;
    public static /*@ pure @*/ double surfaceAreaParallelogram(final double base, final double height) {
        if (base <= 0) {
            throw new IllegalArgumentException(POSITIVE_BASE);
        }
        if (height <= 0) {
            throw new IllegalArgumentException(POSITIVE_HEIGHT);
        }
        return base * height;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == (base1 + base2) * height / 2;
    //@ requires base1 > 0 && base2 > 0 && height > 0;
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
    // @ ensures \result > 0;
    // @ ensures \result == Math.PI * radius * radius;
    public static /*@ pure @*/ double surfaceAreaCircle(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return Math.PI * radius * radius;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == 3 * Math.PI * radius * radius;
    //@ requires radius > 0;
    public static /*@ pure @*/ double surfaceAreaHemisphere(final double radius) {
        if (radius <= 0) {
            throw new IllegalArgumentException(POSITIVE_RADIUS);
        }
        return 3 * Math.PI * radius * radius;
    }

    /* @ ensures \result > 0; */
    // @ ensures \result == Math.PI * radius * (radius + Math.pow(height * height + radius * radius, 0.5));
    //@ requires radius > 0 && height > 0;
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