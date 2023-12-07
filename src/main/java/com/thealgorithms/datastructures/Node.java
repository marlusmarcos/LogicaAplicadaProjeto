package com.thealgorithms.datastructures;

import java.util.ArrayList;
import java.util.List;


public class Node<T> {
    
    //@ spec_public
    private final /*@ nullable @*/ T value;
    //@ spec_public
    private final /*@ nullable @*/ List<Node<T>> children;

    //@ ensures \result == value;
    public /*@ pure @*/ T getValue() {
        return value;
    }

       

    //@  requires child != null;
    //@  ensures children.size() == \old(children.size())+1;
    //@  requires child == null;
    //@ signals (NullPointerException);
    public void addChild( /*@ non_null */ Node<T>  child) {
        if (child != null)  children.add(child);
    }

    //@ ensures \result == children;
    public /*@ pure @*/ List<Node<T>> getChildren() {
        return children;
    }

    //@ ensures this.value == value;
    public Node(final /*@ nullable @*/ T value) {
        this.value = value;
        this.children = new ArrayList<>();
    }

    //@ requires value != null && children != null;
    //@ ensures this.value == value && this.children == children ;
    //@ requires value == null || children == null;
    //@ signals (NullPointerException);
    public Node(final /*@ non_null @*/ T value, final /*@ non_null @*/ List<Node<T>> children) {
        this.value = value;
        this.children = children;
 
    }
}
