//#include "memory"
#include "utility"
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
   // return *std::unique_ptr<Vec>(new Vec{this->_x*scalar,this->_y*scalar,this->_z*scalar});
      set(this->_x * scalar, this->_y *scalar, this->_z * scalar);
      
      return *this;
  }

  Vec& vec_mul(float& scalar){
    //return *std::unique_ptr<Vec>(new Vec{this->_x*scalar,this->_y*scalar,this->_z*scalar});
      set(this->_x * scalar, this->_y *scalar, this->_z * scalar);
      
      return *this;
  }
  
  ~Vec(){};

 private:
	float _x;
	float _y;
	float _z;

};

// #include <iostream>

// using namespace std;

Vec tmp(Vec hey){
  Vec v5 = Vec(0, 0, 0);
  Vec v6 = v5.vec_add(hey);

  return v6;
}

float tmp2(float hey){
  return hey;
}


int main(int argc, char **argv){
 // Vec v1 = Vec(1.0,1.0,1.0);
  Vec v1(0,0,0);
  Vec v2 = v1;

  (v2.vec_add(v1));

  float flt = 2.0;
  float flt2 = 3.0;
  float flt3 = flt2;
  flt3 = (flt2);

  //flt2 = flt * flt2;
  //flt2 = (flt2) + (flt + flt2);

  Vec v3 = v2.vec_mul(flt2);

  Vec v4 = (v3.vec_add(v2.vec_mul(flt)));

  //float float3 = ((flt2 + flt) + flt2);

  //float3 = float3 + flt2;

  v4 = (v4);
  //v4 = tmp(v4);
  //Vec v8 = tmp(v4);

  //(2.0f + 2.0f);

  //(((flt2) + flt));

  //(v4.vec_add(v3));

  (Vec(0,0,0));

 // v4;

 // (v4);

 // Vec v9 = Vec(0,0,0);

 // Vec v10 = (v9.vec_add(v4).vec_add(v3)).vec_add(v2);

  //float five = flt2 * flt * (flt + flt * (flt));

  //float t = 3.0f;
 // 3.0f;
  //3.1f + 3.2f;
  //t = t + 3.2f;
  
 // v4 = (v4);
 // v4 = tmp(v4);
  //v2 = v2.vec_add(v3);

  Vec(0,0,0);
  (Vec(0,0,0).vec_add(v2));

 // Vec f = Vec(0,0,0);

 // Vec y = (Vec(0,0,0).vec_add(f));

 // Vec p = f;

  //t = (tmp2(t));

  return 0;
}
