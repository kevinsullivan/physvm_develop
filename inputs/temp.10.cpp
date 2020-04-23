#include "vec_lib.h"


float tmp2(float hey){
  return hey;
}
int main(int argc, char **argv){
  //3.0 + (3.0 + 3.0);
  Vec v1(0,0,0);
  float flt = 2.0;
  flt + flt;
  Vec v2 = v1;
  Vec vvv = v1.vec_add(v2);
  //flt = 3.0;
  v2 = v1;
  (v2.vec_add(v1));
  float flt2 = 3.0;
  float flt3 = flt2;
 // (3.0 + 3.0);
  flt2 + (flt + flt);
 // flt2 + 3.0;
  float flt4 = flt3 * flt3; //(flt3*flt3);
  flt3 = (flt2);
  Vec v3 = v2.vec_mul(flt2);
  Vec v4 = (v3.vec_add(v2.vec_mul(flt)));
  v4 = (v4.vec_add(v4).vec_mul(flt3));

  if(true)
  {
    flt3 = 2;
  }
  if(true)
    flt3 = 4.0;

  //v4 = Vec(0.0, 0.0, 0.0);
  return 0;
}
