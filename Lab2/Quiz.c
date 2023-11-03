#include <stddef.h>
#include <limits.h>

/*@
  requires \valid(v1 + (0 .. len-1));
  requires \valid_read(v2 + (0 .. len-1));
  requires \separated(v1 + (0 .. len-1), v2 + (0 .. len-1));

  requires \forall size_t i; 0 <= i < len ==> INT_MIN <= v1[i] <= INT_MAX;
  requires \forall size_t i; 0 <= i < len ==> INT_MIN <= v2[i] <= INT_MAX;
  requires \forall size_t i; 0 <= i < len ==> INT_MIN <= v1[i] + v2[i] <= INT_MAX;

  assigns v1[0 .. len-1];

  ensures \forall size_t i; 0 <= i < len ==> v1[i] == \old(v1[i]) + v2[i];
  ensures \forall size_t i; 0 <= i < len ==> v2[i] == \old(v2[i]);
*/
void add_vectors(int* v1, int* v2, size_t len)
{
  /*@
    loop invariant 0 <= i <= len;
    loop invariant \forall size_t j; i <= j < len ==> v1[j] == \at(v1[j], Pre);
    loop invariant \forall size_t j; 0 <= j < i ==> v1[j] == \at(v1[j], Pre) + v2[j];
    loop assigns i, v1[0 .. len-1];
    loop variant len - i;
  */
  for(size_t i = 0; i < len; ++i)
  {
    v1[i] = v1[i] + v2[i];
  }
}

