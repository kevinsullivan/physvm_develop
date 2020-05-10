#ifndef vec_lib
#define vec_lib

class Vec {
public:
  Vec(float i= 0.0, float j= 0.0, float k = 0.0);
  void set(float x, float y, float z);
  float get_x() const{return _x;}
  float get_y() const{return _y;}
  float get_z() const{return _z;}
  Vec vec_add(Vec v);
  Vec operator*(const float& scalar);
  Vec vec_mul(float scalar);
  ~Vec(){};
 private:
	float _x;
	float _y;
	float _z;
};

#endif