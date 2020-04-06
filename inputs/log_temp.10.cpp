
include <g3log/g3log.hpp>
include <g3log/logworker.hpp>

class Vec {
public:
  Vec(float i= 0.0, float j= 0.0, float k = 0.0):_x (i),_y (j),_z (k){}; 
	void set(float x, float y, float z)
	{
		_x = x;
		_y = y; 
		_z = z;
	}
  float get_x() const{return _x;}
  float get_y() const{return _y;}
  float get_z() const{return _z;}
  Vec& vec_add(Vec& v)
    {
      set(v._x + _x, v._y + _y, v._z + _z);
      return *this;
    }
  Vec& operator*(const float& scalar){
      set(this->_x * scalar, this->_y *scalar, this->_z * scalar);
      return *this;
  }
  Vec& vec_mul(float& scalar){
      set(this->_x * scalar, this->_y *scalar, this->_z * scalar);
      return *this;
  }
  ~Vec(){};
 private:
	float _x;
	float _y;
	float _z;
};
Vec tmp(Vec hey){
  Vec v5 = Vec(0, 0, 0);
  Vec v6 = v5.vec_add(hey);
  return v6;
}



float tmp2(float hey){
  return hey;
}
int main(int argc, char **argv){
  //3.0 + (3.0 + 3.0);
using namespace g3;auto worker = g3::LogWorker::createLogWorker();std::string logFile = "Peirce.log";std::string logDir = ".";auto defaultHandler = worker->addDefaultLogger(logFile, logDir);g3::initializeLogging(worker.get());

  Vec v1(0,0,0);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1));
float flt = 2.0;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));
flt + flt;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));
Vec v2 = v1;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1));
//flt = 3.0;
  v2 = v1;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1));
(v2.vec_add(v1));
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v1) with value : " +  std::to_string(v1));
float flt2 = 3.0;
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt2) with value : " +  std::to_string(flt2));
float flt3 = flt2;
 /
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt2) with value : " +  std::to_string(flt2));
/ (3.0 + 3.0);
  flt2 + (flt + flt);
 /
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt2) with value : " +  std::to_string(flt2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));
/ flt2 + 3.0;
  float flt4 = flt3 * (flt3*flt3);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt4) with value : " +  std::to_string(flt4));
flt3 = (flt2);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt2) with value : " +  std::to_string(flt2));
Vec v3 = v2.vec_mul(flt2);
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v3) with value : " +  std::to_string(v3));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt2) with value : " +  std::to_string(flt2));
Vec v4 = (v3.vec_add(v2.vec_mul(flt)));
  
LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v4) with value : " +  std::to_string(v4));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v3) with value : " +  std::to_string(v3));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v2) with value : " +  std::to_string(v2));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: flt) with value : " +  std::to_string(flt));
v4 = (v4.vec_add(v4).vec_mul(flt3));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v4) with value : " +  std::to_string(v4));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v4) with value : " +  std::to_string(v4));

LOG(INFO) << "Detected reference or declaraction of physical variable without type provided ( IDENTIFIER: v4) with value : " +  std::to_string(v4));

  if(true)
  {
    flt3 = 2;
  }
  if(true)
    flt3 = 4.0;

  //v4 = Vec(0.0, 0.0, 0.0);
  return 0;
}
