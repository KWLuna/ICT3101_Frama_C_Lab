// frama-c-gui -wp -wp-rte -warn-unsigned-overflow -warn-unsigned-downcast Section4.c
#include <stddef.h>
#include <limits.h>
/* 4. Mutating: Reverse */
/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int *a, int *b)
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
/*@
    requires \valid(array + (0 .. len-1));
    requires \forall size_t i ; 0 <= i < len ==> INT_MIN <= array[i] <= INT_MAX;

    assigns array[0 .. len-1];

    ensures \forall size_t j; 0 <= j < len ==> array[j] == \old(array[len-j-1]);
    ensures \forall size_t i ; 0 <= i < len ==> INT_MIN <= array[i] <= INT_MAX;
*/
void reverse(int *array, size_t len)
{
  /*@
      loop invariant 0 <= i <= len/2;
      loop invariant \forall size_t j ; (0 <= j < i || len-i <= j < len) ==> array[j] == \at(array[len-j-1], Pre);
      loop invariant \forall size_t j ; i <= j < len-i ==> array[j] == \at(array[j], Pre);
      loop assigns i, array[0 .. len-1] ;
      loop variant len - i;
  */
  for (size_t i = 0; i < len / 2; ++i)
  {
    swap(array + i, array + len - i - 1);
  }
}