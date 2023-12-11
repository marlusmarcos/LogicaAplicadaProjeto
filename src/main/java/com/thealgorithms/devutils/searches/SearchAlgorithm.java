package com.thealgorithms.devutils.searches;


 * The common interface of most searching algorithms
 *
 * @author Podshivalov Nikita (https://github.com/nikitap492)
 */


//@non-null-by-default
public interface SearchAlgorithm {

    //@requires key != null && array != null;
    //@ pure helper
    <T extends Comparable<T>> int find(T[] array, T key);
}
