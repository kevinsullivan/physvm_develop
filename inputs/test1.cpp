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

  
  ~Vec(){};

 private:
	float _x;
	float _y;
	float _z;

};

// #include <iostream>

// using namespace std;

int main(int argc, char **argv){

  Vec v1(1.0,1.0,1.0); 
  Vec v3 = v1.vec_add(v1);
  return 0;
}
