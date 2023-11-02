// frama-c-gui -wp -wp-rte -warn-unsigned-overflow -warn-unsigned-downcast Section2.c
#include <stddef.h>
/* 2. Non-mutating: Equality of Arrays */
/*@ 
    requires \valid_read(a_1 + (0 .. n-1));
    requires \valid_read(a_2 + (0 .. n-1));
    
    assigns \nothing;
    
    ensures \result == 0 || \result == 1;
*/
int equal(const int* a_1, const int* a_2, size_t n) 
{
    //returns true if and only if two arrays are equal 
    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall size_t j; 0 <= j < i ==> a_1[j] == a_2[j];
        loop assigns i; 
        loop variant n - i;
    */
    for(size_t i = 0; i < n; ++i){
        if(a_1[i] != a_2[i]) 
            return 0;
    }
    return 1;
}

/*@ 
    requires \valid_read(a_1 + (0 .. n-1));
    requires \valid_read(a_2 + (0 .. n-1));

    assigns \nothing;
    
    ensures \result == 0 || \result == 1;
*/
int different(const int* a_1, const int* a_2, size_t n) 
{
    // use equal function
    // returns true if two arrays are different
    // postcondition should contain an existential quantifier 
    return !equal(a_1, a_2, n);
}