package com.thealgorithms.datastructures;

import java.util.ArrayList;
import java.util.List;


public class Node<T> {
    
    //@ spec_public
    private final /*@ nullable @*/ T value;

    private final /*@ nullable @*/ List<Node<T>> children;

    //@ ensures \result == value;
    public /*@ pure @*/ T getValue() {
        return value;
    }

    //@ requires child != null;
    // @ invariant child != null
    public void addChild(Node<T> child) {
        if (child != null) 
        {
            children.add(child);
        } else {
            
        }
    }

    public /*@ pure @*/ List<Node<T>> getChildren() {
        return children;
    }

    //@ ensures this.value == value;
    public Node(final /*@ nullable @*/ T value) {
        this.value = value;
        this.children = new ArrayList<>();
    }

    //@ ensures this.value == value && getChildren().equals(children);
    public Node(final /*@ nullable @*/ T value, final /*@ nullable @*/ List<Node<T>> children) {
        this.value = value;
        this.children = children;
 
    }
}
