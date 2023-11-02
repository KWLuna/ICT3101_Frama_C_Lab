#include <limits.h>

/* Behaviors */
/* 3.1 Previous Exercises */

// Distance between integers
/*@
	requires b > a ==> b - a <= INT_MAX;
    requires b <= a ==> a - b <= INT_MAX;

    assigns \nothing;
    
    behavior more:
        assumes a < b;
        ensures \result == b - a;
    
    behavior left:
        assumes a >= b;
        ensures \result == a - b;

    complete behaviors;
    disjoint behaviors;
*/
int distance(int a, int b)
{
	if (a < b) return b - a;
	else return a - b;
}
// Reset on condition
/*@
    requires \valid(a);
    requires \valid_read(b);
    requires \separated(a, b);

    assigns *a;

    behavior reset:
        assumes *b;
        ensures *a == 0;
    
    behavior no_change:
        assumes ! *b;
        ensures *a == \old(*a);

    complete behaviors;
    disjoint behaviors;
*/
void reset_1st_if_2nd_is_true(int* a, int const* b)
{
    if(*b) *a = 0;
}

// Days of month
/*@
	requires 1 <= month <= 12;

    assigns \nothing;

    behavior day_twenty_eight:
        assumes month == 2;
        ensures \result == 28;
    behavior day_thirty:
        assumes month \in { 4, 6, 9, 11 };
        ensures \result == 30;
    behavior day_thirty_one:
        assumes month \in { 1, 3, 5, 7, 8, 10, 12 };
        ensures \result == 31;

    complete behaviors;
    disjoint behaviors;
*/
int day_of(int month)
{
	int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
	return days[month - 1];
}

// Max of pointed values
/*@
    requires \valid(a) && \valid(b);
    requires \valid_read(a) && \valid_read(b);
    requires INT_MIN <= *a <= INT_MAX;
    requires INT_MIN <= *b <= INT_MAX;

    assigns  *a, *b;
    
    behavior change_order:
        assumes *a < *b;
        ensures *a == \old(*b) && *b == \old(*a);
    
    behavior no_change:
        assumes *a >= *b;
        ensures *a ==  *a == \old(*a) && *b == \old(*b);

    complete behaviors;
    disjoint behaviors;
*/
void max_ptr (int* a, int* b)
{
    if(*a < *b)
    {
        int tmp = *b;
        *b = *a;
        *a = tmp;
    }
}