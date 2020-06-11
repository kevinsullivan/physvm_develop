
#include <g3log/g3log.hpp>
#include <g3log/logworker.hpp>
#include <string>
#include "vec_lib.h"
#include "transform.h"
//#include <cmath>


float tmp2(float hey){
  return hey;
}
int main(int argc, char **argv){
  //3.0 + (3.0 + 3.0);
using namespace g3;auto worker = g3::LogWorker::createLogWorker();std::string logFile = "Peirce.log";std::string logDir = ".";auto defaultHandler = worker->addDefaultLogger(logFile, logDir);g3::initializeLogging(worker.get());

  Vec v1(0,0,0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);
//float flt = 2.0;
  //flt + flt;
  Vec v2 = v1;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);
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
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r11) with value : " +  std::to_string(r11);
Vec r12(0, 0, 1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r12) with value : " +  std::to_string(r12);
Vec r13(0, 1, 0);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r13) with value : " +  std::to_string(r13);

  Transform rotation1(
    r11, r12, r13
  );
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r11) with value : " +  std::to_string(r11);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r12) with value : " +  std::to_string(r12);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r13) with value : " +  std::to_string(r13);
Vec res1 = rotation1.apply(v1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res1) with value : " +  std::to_string(res1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);

  Vec r21(1, 0, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r21) with value : " +  std::to_string(r21);
Vec r22(0, 0, 1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r22) with value : " +  std::to_string(r22);
Vec r23(0, 1, 0);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r23) with value : " +  std::to_string(r23);

  Transform rotation2(
    r21, r22, r23
  );

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r21) with value : " +  std::to_string(r21);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r22) with value : " +  std::to_string(r22);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r23) with value : " +  std::to_string(r23);

  Vec s11(2, 0, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s11) with value : " +  std::to_string(s11);
Vec s12(0, 2, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s12) with value : " +  std::to_string(s12);
Vec s13(0, 0, 2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s13) with value : " +  std::to_string(s13);

  Transform scale1(
    s11, s12, s13
  );

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s11) with value : " +  std::to_string(s11);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s12) with value : " +  std::to_string(s12);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: s13) with value : " +  std::to_string(s13);

  Vec sh1(1, 1, 1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh1) with value : " +  std::to_string(sh1);
Vec sh2(0, 1, 1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh2) with value : " +  std::to_string(sh2);
Vec sh3(0, 0, 1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh3) with value : " +  std::to_string(sh3);

  Transform sheer1(
    sh1, sh2, sh3
  );

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh1) with value : " +  std::to_string(sh1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh2) with value : " +  std::to_string(sh2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: sh3) with value : " +  std::to_string(sh3);

  Vec p1(1, 0, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p1) with value : " +  std::to_string(p1);
Vec p2(0, 1, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p2) with value : " +  std::to_string(p2);
Vec p3(0, 0, 0);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p3) with value : " +  std::to_string(p3);

  Transform projection(
    p1, p2, p3
  );

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p1) with value : " +  std::to_string(p1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p2) with value : " +  std::to_string(p2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: p3) with value : " +  std::to_string(p3);

  Transform double_rotate = rotation1.compose(rotation2);
  Transform rotate_and_scale = double_rotate.compose(scale1);

  float r2o2 = .71;//std::sqrt(2)/2;//changes from identity basis to coordinates identical to the transformation

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r2o2) with value : " +  std::to_string(r2o2);

  Vec c1(r2o2, r2o2, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c1) with value : " +  std::to_string(c1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r2o2) with value : " +  std::to_string(r2o2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r2o2) with value : " +  std::to_string(r2o2);
Vec c2(r2o2, -r2o2, 0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c2) with value : " +  std::to_string(c2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r2o2) with value : " +  std::to_string(r2o2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: r2o2) with value : " +  std::to_string(r2o2);
Vec c3(0, 0, 1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c3) with value : " +  std::to_string(c3);

  Transform cob1(//change of basis
    c1, c2, c3
  );

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c1) with value : " +  std::to_string(c1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c2) with value : " +  std::to_string(c2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: c3) with value : " +  std::to_string(c3);

  Vec res2 = scale1.apply(v2);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res2) with value : " +  std::to_string(res2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2);
Vec res3 = projection.apply(v1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res3) with value : " +  std::to_string(res3);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);
Vec res4 = rotate_and_scale.apply(v1);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res4) with value : " +  std::to_string(res4);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);
res4 = rotation2.apply(rotation1.apply(v1));
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res4) with value : " +  std::to_string(res4);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);
res4 = scale1.apply(res4);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res4) with value : " +  std::to_string(res4);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res4) with value : " +  std::to_string(res4);
res3 = scale1.compose(rotation2.compose(rotation1)).apply(v1);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res3) with value : " +  std::to_string(res3);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);

  res2 = (scale1.apply(v2));
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res2) with value : " +  std::to_string(res2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2);
res2 = (scale1.compose(projection).apply(v2));
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res2) with value : " +  std::to_string(res2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2);
res2 = (scale1.apply((scale1.apply(v1))));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: res2) with value : " +  std::to_string(res2);

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1);

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
