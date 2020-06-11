#include <iostream>
#include "vec.h"

using namespace std;

int main(int argc, char **argv){

  Vec v1(1.0,1.0,1.0); // as in frame 1;
  Vec v2(2.0,2.0,2.0); // as in frame 2;

  Vec v3 = v1.vec_add(v1); // as in the same frame as v1 -- frame 1
  Vec v4 = v1.vec_add(v2); // should be rejected;

  return 0;
}
