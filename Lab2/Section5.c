// frama-c-gui -wp -wp-rte -warn-unsigned-overflow -warn-unsigned-downcast Section5.c
#include <stddef.h>
#include <limits.h>
/* 5. Mutating: Copy */
// copies a range of values into another array, starting from the first cell of the array
// Consider and Specify that the two ranges are entirely separated
/*@
    requires \valid(dst + (0 .. len-1));
    requires \valid_read(src + (0 .. len-1));
    requires \separated(&src[0 .. len-1], dst);

    requires \forall size_t i ; 0 <= i < len ==> INT_MIN <= src[i] <= INT_MAX;
    requires \forall size_t i ; 0 <= i < len ==> INT_MIN <= dst[i] <= INT_MAX;

    assigns dst[0 .. len-1];

    ensures \forall size_t i; 0 <= i < len ==> \old(src[i]) == dst[i];
*/
void copy(int const *src, int *dst, size_t len)
{
    /*@
        loop invariant 0 <= i <= len;
        // \at(variable, label) - gives us the value of the variable v at the program point Label
        loop invariant \forall size_t j; 0 <= j < i ==> \at(src[j], Pre) == dst[j];
        loop invariant \forall size_t j; i <= j < len ==> \at(src[j], Pre) == src[j];
        loop assigns i, dst[0 .. len-1];
        loop variant len - i;
    */
    for (size_t i = 0; i < len; ++i)
    {
        dst[i] = src[i];
    }
}
/*@
  requires \valid(dst + (0 .. len-1));
  requires \valid_read(src + (0 .. len-1));
  requires \separated(&src[0 .. len-1], &dst[0 .. len-1]) ;

  assigns dst[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> \old(src[j]) == dst[j] ;
*/
void true_copy(int const *src, int *dst, size_t len)
{
    /*@
        loop invariant 0 <= i <= len ;
        loop invariant \forall size_t j ; 0 <= j < i ==> \at(src[j], Pre) == dst[j];
        loop invariant \forall size_t j ; i <= j < len ==> \at(src[j], Pre) == src[j];
        loop assigns i, dst[0 .. len-1] ;
        loop variant len - i ;
    */
    for (size_t i = 0; i < len; ++i)
    {
        dst[i] = src[i];
    }
}

/*@
    requires \valid(dst + (0 .. len-1));
    requires \valid_read(src + (0 .. len-1));
    requires \separated(&src[0 .. len-1], &dst[0 .. len-1]) ;

    requires \forall size_t i ; 0 <= i < len ==> INT_MIN <= src[i] <= INT_MAX;
    requires \forall size_t i ; 0 <= i < len ==> INT_MIN <= dst[i] <= INT_MAX;

    assigns dst[0 .. len-1];

    ensures \forall size_t j ; 0 <= j < len ==> \old(src[j]) == dst[j] ;
*/
void copy_backward(int const *src, int *dst, size_t len)
{
    /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall size_t j; i <= j < len ==> \at(src[j], Pre) == dst[j];
        loop invariant \forall size_t j; 0 <= j < i ==> \at(src[j], Pre) == src[j];
        loop assigns i, dst[0 .. len-1];
        loop variant i;
    */
    for (size_t i = len; i > 0; --i)
    {
        dst[i - 1] = src[i - 1];
    }
}