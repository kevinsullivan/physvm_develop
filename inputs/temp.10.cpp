#include "vec_lib.h"
#include "transform.h"
//#include <cmath>


float tmp2(float hey){
  return hey;
}
int main(int argc, char **argv){
  //3.0 + (3.0 + 3.0);
  Vec v1(0,0,0);
  //float flt = 2.0;
  //flt + flt;
  Vec v2 = v1;
  //Vec vvv = v1.vec_add(v2);
  //flt = 3.0;
  //v2 = v1;
  //(v2.vec_add(v1));
  //float flt2 = 3.0;
  //float flt3 = flt2;
 // (3.0 + 3.0);
 // flt2 + (flt + flt);
 // flt2 + 3.0;
 // float flt4 = flt3 * flt3; //(flt3*flt3);
  //flt3 = (flt2);
  //Vec v3 = v2.vec_mul(flt2);
  //Vec v4 = (v3.vec_add(v2.vec_add(v2)));
  //v4 = (v4.vec_add(v4).vec_mul(flt3));

  Vec r11(1, 0, 0);
  Vec r12(0, 0, 1);
  Vec r13(0, 1, 0);

  Transform rotation1(
    r11, r12, r13
  );
  Vec res1 = rotation1.apply(v1);

  Vec r21(1, 0, 0);
  Vec r22(0, 0, 1);
  Vec r23(0, 1, 0);

  Transform rotation2(
    r21, r22, r23
  );

  Vec s11(2, 0, 0);
  Vec s12(0, 2, 0);
  Vec s13(0, 0, 2);

  Transform scale1(
    s11, s12, s13
  );

  Vec sh1(1, 1, 1);
  Vec sh2(0, 1, 1);
  Vec sh3(0, 0, 1);

  Transform sheer1(
    sh1, sh2, sh3
  );

  Vec p1(1, 0, 0);
  Vec p2(0, 1, 0);
  Vec p3(0, 0, 0);

  Transform projection(
    p1, p2, p3
  );

  Transform double_rotate = rotation1.compose(rotation2);
  Transform rotate_and_scale = double_rotate.compose(scale1);

  float r2o2 = .71;//std::sqrt(2)/2;//changes from identity basis to coordinates identical to the transformation

  Vec c1(r2o2, r2o2, 0);
  Vec c2(r2o2, -r2o2, 0);
  Vec c3(0, 0, 1);

  Transform cob1(//change of basis
    c1, c2, c3
  );

  Vec res2 = scale1.apply(v2);
  Vec res3 = projection.apply(v1);
  Vec res4 = rotate_and_scale.apply(v1);
  res4 = rotation2.apply(rotation1.apply(v1));
  res4 = scale1.apply(res4);
  res3 = scale1.compose(rotation2.compose(rotation1)).apply(v1);

  res2 = (scale1.apply(v2));
  res2 = (scale1.compose(projection).apply(v2));
  res2 = (scale1.apply((scale1.apply(v1))));

  rotate_and_scale = double_rotate.compose(scale1);
  rotate_and_scale = (double_rotate.compose(scale1));

  //Vec r1 = projection.get_row(0), r2 = projection.get_row(1), r3 = projection.get_row(3);

  //rotate_and_scale = Transform(r1, r2, r3);
  rotate_and_scale = cob1;
  /*
  if(true)
  {
    flt3 = 2;
  }
  if(true)
    flt3 = 4.0;
*/
  //v4 = Vec(0.0, 0.0, 0.0);
  return 0;
}
