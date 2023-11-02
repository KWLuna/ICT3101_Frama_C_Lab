#include <limits.h>
// frama-c-gui -wp -rte Section1.c
/* 1.1 Addition */
/*@
	requires INT_MIN <= a <= INT_MAX;
	requires INT_MIN <= b <= INT_MAX;
	requires INT_MIN <= a + b <= INT_MAX;

	assigns \nothing;

	ensures \result == a + b;
*/
int add(int a, int b)
{
	return a + b;
}

/* 1.2 Distance */
/*@
	requires b > a ==> b - a <= INT_MAX;
	requires b <= a ==> a - b <= INT_MAX;

	assigns \nothing;

	ensures \result == b - a || \result == a - b;
*/
int distance(int a, int b)
{
	if (a < b)
		return b - a;
	else
		return a - b;
}

/* 1.3 Alpabet Letter */
/*@
	assigns \nothing;

	ensures \result <==> ('a' <= c <= 'z') || ('A' <= c <= 'Z');
*/
int alpabet_letter(char c)
{
	if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))
		return 1;
	else
		return 0;
}

int main()
{
	int r;

	r = alpabet_letter('x');
	//@ assert r;
	r = alpabet_letter('H');
	//@ assert r;
	r = alpabet_letter(' ');
	//@ assert !r;
}

/* 1.4 Days of the month */
/*@
	requires 1 <= month <= 12;

	assigns \nothing;

	ensures \result \in  {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
*/
int day_of(int month)
{
	int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
	return days[month - 1];
}

/* 1.5 Last angle of a triangle */
/*@
	requires 0 <= first <= 180;
	requires 0 <= second <= 180;
	requires first + second <= 180;

	ensures \result == 180 - first - second;
	ensures \result + first + second == 180;
	ensures 0 <= \result <= 180;
*/
int last_angle(int first, int second)
{
	return 180 - first - second;
}