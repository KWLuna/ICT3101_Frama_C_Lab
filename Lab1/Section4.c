#include <limits.h>
/* Section 4: WP Modularity */

/* 4.1 Days of the month */
/*@ 
  assigns \nothing ;

  ensures \result == ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0);
*/
int leap(int y)
{
    return ((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0);
}

/*@
	requires 1 <= m <= 12;
	requires INT_MIN <= y <= INT_MAX;

    assigns \nothing;
    
    ensures \result \in { 28, 29, 30, 31 };
*/
int day_of(int m, int y)
{
	int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
	int n = days[m-1];
    // if year input is leap year
    if(leap(y) && m == 2)
        n = 29;
    return n;
}

/* 4.2 Alpa-numeric character */
/*@
  assigns \nothing ;
  ensures \result <==> 'a' <= c <= 'z' ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> 'A' <= c <= 'Z' ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> '0' <= c <= '9' ;
*/
int is_digit(char c){
  return '0' <= c && c <= '9' ;
}

/*@
  assigns \nothing ;
  ensures 
  \result <==> (
    ('a' <= c <= 'z') ||
    ('A' <= c <= 'Z') ||
    ('0' <= c <= '9')
  ) ;
*/
int is_alpha_num(char c){
  return
    is_lower_alpha(c) || 
    is_upper_alpha(c) ||
    is_digit(c) ;
}

/* 4.3 Give the change */
enum note {N500, N200, N100, N50, N20, N10, N5, N2, N1};
int const values[] = {500, 200, 100, 50, 20, 10, 5, 2, 1};

/*@
    requires n \in {N500, N200, N100, N50, N20, N10, N5, N2, N1};
    requires \valid(rest);
    requires \valid_read(rest);

    assigns *rest;

    ensures \result == \old(*rest)/values[n];
    ensures \old(*rest) == *rest + \result * values[n] ;
*/
int remove_max_notes(enum note n, int* rest)
{
    int num = (*rest)/values[n];
    (*rest) -= num * values[n];
    return num;
}
/*@ 
    requires \valid(change+(0..8));
    requires 0 <= amount <= INT_MAX;
    requires 0 <= received <= INT_MAX;
    // requires received >= amount;
    requires received - amount >= 0;

    assigns change[0..8];

  behavior not_enough:
    assumes amount > received ;
    ensures \result == -1;

  behavior change:
    assumes amount <= received ;
    ensures \result == 0;
    ensures
      received - amount ==
          change[N500] * values[N500]
        + change[N200] * values[N200]
        + change[N100] * values[N100]
        + change[N50]  * values[N50]
        + change[N20]  * values[N20]
        + change[N10]  * values[N10]
        + change[N5]   * values[N5]
        + change[N2]   * values[N2]
        + change[N1]   * values[N1];
    ensures
         values[N2]   > change[N1]   * values[N1] 
      && values[N5]   > change[N2]   * values[N2]   
      && values[N10]  > change[N5]   * values[N5]
      && values[N20]  > change[N10]  * values[N10]
      && values[N50]  > change[N20]  * values[N20] 
      && values[N100] > change[N50]  * values[N50]
      && values[N200] > change[N100] * values[N100] 
      && values[N500] > change[N200] * values[N200];

    complete behaviors;
    disjoint behaviors;
*/
int make_change(int amount, int received, int change[9])
{
    // if amount recieved is less than price, return -1
    // if amount recieved is more or equal to price, return 0
    if (received < amount)
        return -1;
    
    int rest = received - amount;

    // for(int i=0; i < sizeof(values); ++i)
        // change[i] = remove_max_notes(i, &rest);

    change[N500] = remove_max_notes(N500, &rest);
    change[N200] = remove_max_notes(N200, &rest);
    change[N100] = remove_max_notes(N100, &rest);
    change[N50]  = remove_max_notes(N50,  &rest);
    change[N20]  = remove_max_notes(N20,  &rest);
    change[N10]  = remove_max_notes(N10,  &rest);
    change[N5]   = remove_max_notes(N5,   &rest);
    change[N2]   = remove_max_notes(N2,   &rest);
    change[N1]   = remove_max_notes(N1,   &rest);

    return 0;
}