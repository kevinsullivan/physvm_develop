#include "vec_lib.h"
#include "transform.h"
#include <vector>
#include <cmath>


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
  Vec v3 = v2.vec_add(flt2);
  Vec v4 = (v3.vec_add(v2.vec_add(v2)));
  //v4 = (v4.vec_add(v4).vec_mul(flt3));

  std::vector<double[3]> rotation_matrix1;

  rotation_matrix1.push_back({1, 0, 0});
  rotation_matrix1.push_back({0, 0, 1});
  rotation_matrix1.push_back({0, 1, 0});

  std::vector<double[3]> rotation_matrix2;

  rotation_matrix2.push_back({0, -1, 0});
  rotation_matrix2.push_back({1, 0, 0});
  rotation_matrix2.push_back({0, 0, 1});

  std::vector<double[3]> scale_matrix1;

  scale_matrix1.push_back({2, 0, 0});
  scale_matrix1.push_back({0, 2, 0});
  scale_matrix1.push_back({0, 0, 2});

  std::vector<double[3]> sheer_matrix;

  sheer_matrix.push_back({1, 1, 1});
  sheer_matrix.push_back({0, 1, 1});
  sheer_matrix.push_back({0, 0, 1});

  std::vector<double[3]> projection_matrix;

  projection_matrix.push_back({1, 0, 0});
  projection_matrix.push_back({0, 1, 0});
  projection_matrix.push_back({0, 0, 0});

  Transform rotation1{rotation_matrix1};
  Transform rotation2{rotation_matrix2};
  Transform scale1{scale_matrix1};
  Transform sheer1{sheer_matrix};
  Transform projection{projection_matrix};
  Transform double_rotate = rotation1.compose(rotation2);
  Transform rotate_and_scale = double_rotate.compose(scale1);

  std::vector<double[3]> cob_matrix;//change of basis

  float r2o2 = std::sqrt(2)/2;//changes from identity basis to coordinates identical to the transformation

  cob_matrix.push_back({r2o2, r2o2, 0});
  cob_matrix.push_back({r2o2, -r2o2, 0});
  cob_matrix.push_back({0, 0, 1});

  Transform cob1{cob_matrix};

  Vec res1 = rotation1.apply(v1);
  Vec res2 = scale1.apply(v2);
  Vec res3 = projection.apply(v3);
  Vec res4 = rotate_and_scale.apply(v4);
  res4 = rotation2.apply(rotation1.apply(v4));
  res4 = scale1.apply(res4);
  res3 = scale1.compose(rotation2.compose(rotation1)).apply(v4);

  res2 = (scale1.apply(v2));
  res2 = (scale1.compose(projection).apply(v2));
  res2 = (scale1.apply((scale1.apply(v1))));

  rotate_and_scale = double_rotate.compose(scale1);
  rotate_and_scale = (double_rotate.compose(scale1));
  rotate_and_scale = Transform(projection_matrix);
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
