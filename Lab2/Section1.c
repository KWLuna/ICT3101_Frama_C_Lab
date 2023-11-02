// frama-c-gui -wp -wp-rte -warn-unsigned-overflow -warn-unsigned-downcast Section1.c
int main()
{
    int x = 0;
    int y = 10;

    /* 1.1 Invariant where variable x does not appear on it */
    /*@
        loop invariant 0 <= y <= 10;
        loop invariant x == 10 - y;
    */
    while (y > 0)
    {
        x++;
        y--;
    }

    /* 1.2 Invariant where both x and y appear on it */
    /*@
        loop invariant 0 <= x <= 10;
        loop invariant 0 <= y <= 10;
        loop invariant x + y == 10;
    */
    while (y > 0)
    {
        x++;
        y--;
    }

    /* 1.3 Invariant where y does not appear on it */
    /*@
        loop invariant 0 <= x < 11;
        loop invariant y == 10 - x;
    */
    while (y > 0)
    {
        x++;
        y--;
    }

    return 0;
}