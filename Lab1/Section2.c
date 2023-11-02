#include <limits.h>
// frama-c-gui -wp -rte Section2.c
/* 2.1 Division and Remaining */
/*@
    requires 0 < x < UINT_MAX;
    requires 0 < y < UINT_MAX;
    requires \valid(q) && \valid(r);
    requires \separated(q, r);

    assigns *q, *r;

    ensures *q == x / y;
    ensures *r == x % y;
*/
void div_rem(unsigned x, unsigned y, unsigned *q, unsigned *r)
{
    *q = x / y;
    *r = x % y;
}

/* 2.2 Reset on condition */
/*@
    requires \valid(a);
    requires \valid_read(b);
    requires \separated(a, b);

    assigns *a;

    ensures *b == \old(*b);
    ensures \old(*b) ==> *a == 0;
    ensures ! \old(*b) ==> *a == \old(*a);
*/
void reset_1st_if_2nd_is_true(int *a, int const *b)
{
    if (*b)
        *a = 0;
}

/* 2.3 Addition of pointed values */
/*@
    requires \valid(r);
    requires \valid_read(a) && \valid_read(b);
    requires INT_MIN <= *a <= INT_MAX;
    requires INT_MIN <= *b <= INT_MAX;
    requires INT_MIN <= *a + *b <= INT_MAX;
    requires \separated(a, r);
    requires \separated(b, r);

    assigns *r;

    ensures *r == *a + *b;
    // ensures *r == \old(*r);
*/
void add(int *a, int *b, int *r)
{
    *r = *a + *b;
}

/* 2.4 Maximum of pointed values */
/*@
    requires \valid(a) && \valid(b);
    requires \valid_read(a) && \valid_read(b);
    requires INT_MIN <= *a <= INT_MAX;
    requires INT_MIN <= *b <= INT_MAX;

    assigns  *a, *b;

    ensures  \old(*a) < \old(*b) ==> *a == \old(*b) && *b == \old(*a);
    ensures  \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b);
*/
void max_ptr(int *a, int *b)
{
    if (*a < *b)
    {
        int tmp = *b;
        *b = *a;
        *a = tmp;
    }
}

extern int h;
int main()
{
    /* 2.2 Reset on condition */
    int a = 5;
    int x = 0;

    reset_1st_if_2nd_is_true(&a, &x);
    //@ assert a == 5;
    //@ assert x == 0;

    int const b = 1;

    reset_1st_if_2nd_is_true(&a, &b);
    //@ assert a == 0;
    //@ assert b == 1;

    /* 2.3 Addition of pointed values */
    // using another variable name for a, b, x
    int c = 24;
    int d = 42;
    int y;
    add(&c, &d, &y);
    //@ assert y == c + d;
    //@ assert y == 66;

    add(&c, &c, &y);
    //@ assert y == c + c;
    //@ assert y == 48;

    /* 2.4 Maximum of pointed values */
    h = 42;
    int e = 24;
    int f = 42;
    max_ptr(&e, &f);
    //@ assert e == 42 && f == 24;
    //@ assert h == 42;
}

/* 2.5 Order 3 values */
/*@
    requires \valid(a) && \valid(b) && \valid(c);
    requires \separated(a, b, c);

    assigns *a, *b, *c;

    ensures *a <= *b <= *c;
    ensures { *a, *b, *c } == \old({ *a, *b, *c }) ;
    ensures \old(*a == *b == *c) ==> *a == *b == *c;
    ensures \old(*a == *b < *c || *a == *c < *b || *b == *c < *a) ==> *a == *b;
    ensures \old(*a == *b > *c || *a == *c > *b || *b == *c > *a) ==> *b == *c;
*/
void order_3(int *a, int *b, int *c)
{
    // Order inputs in increasing order
    // Compare values
    // If a is bigger than b, swap a to b.
    if (*a > *b)
    {
        int tmp = *b;
        *b = *a;
        *a = tmp;
    }
    // if a is bigger than c, swap a to c.
    if (*a > *c)
    {
        int tmp = *c;
        *c = *a;
        *a = tmp;
    }
    // if b is bigger than c, swap b to c.
    if (*b > *c)
    {
        int tmp = *c;
        *c = *b;
        *b = tmp;
    }
}

void test()
{
    int a1 = 5, b1 = 3, c1 = 4;
    order_3(&a1, &b1, &c1);
    //@ assert a1 == 3 && b1 == 4 && c1 == 5;

    int a2 = 2, b2 = 2, c2 = 2;
    order_3(&a2, &b2, &c2);
    //@ assert a2 == 2 && b2 == 2 && c2 == 2;

    int a3 = 4, b3 = 3, c3 = 4;
    order_3(&a3, &b3, &c3);
    //@ assert a3 == 3 && b3 == 4 && c3 == 4;

    int a4 = 4, b4 = 5, c4 = 4;
    order_3(&a4, &b4, &c4);
    //@ assert a4 == 4 && b4 == 4 && c4 == 5;
}