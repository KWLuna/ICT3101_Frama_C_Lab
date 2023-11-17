/*@ ensures \result >= \old(a) && \result >= \old(b);
    ensures \result == \old(a) || \result == \old(b);
    assigns \nothing;
*/
extern int max(int a, int b);