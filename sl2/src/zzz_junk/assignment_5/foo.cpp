/*
Make unit mismatches work.
*/
int foo () {
    int x := 5;     // in seconds           def x_phys := 5 (in time in seconds)
    int y := 6;     // in minutes           def y_phys := 6 (in time in minutes)
    int z := x + y; // oops!                def z_phys := plus x_phys y_phys  
}

/*
Annotate i: interpretated as a value in seconds
*/
int server (int i) {
    return i;
}

/*
Annotate 7: in milliseconds
*/
void client () {
    server(7);
}

/*
I want to get a units mismatch.
*/

