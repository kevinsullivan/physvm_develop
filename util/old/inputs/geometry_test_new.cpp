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


/*
When you get to parsing base code, start by asking 
about any global domain elements.
*/
int main(int argc, char **argv){
  @@EuclideanGeometry geom3d<3,"worldGeometry">;  // a space (affine space)
  @@ClassicalTime time<"worldTime">;              // a space (affine space)
  @@ClassicalVelocity vel<"worldVelocities">      // a space (a vector space)

  @@AffineFrame base_link_frame_(geom3d, <computed>, geom3.stdFrame);


  // geom3d.pointTorsor
  // geom3d.vectorSpace
  // geom3d.stdFrame (!)
  // geom3d.vectorSpace.stdBasis
  // vel.stdBasis

  // 1. Add a domain point objects
  // 2. Interpret geom_start as mapping to this new domain point object
  // underscores after name identify domain objects vs machine objects
  @@GeometricPoint geom_start_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
  Point3 geom_start(0.0,0.0,0.0);
  @@Interpret geom_start -> geom_start_

  @@GeometricPoint geom_end_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
  Point3 geom_end(1.0,1.0,1.0);
  @@Interpret geom_end -> geom_end_

 
  @@TimePoint time_then_(time, [-10.0], time.stdFrame);
  Point1 time_then_(time, [-10.0])
  @@Intepret time_then_ -> time_then_
  
  @@TimePoint time_now_(time, [0.0], time.stdFrame);
  Point1 time_now(0.0);
  @@Intepret time_now_ -> time_now_

  @@GeometricVector geom_displacement_(geom3, [1.0,1.0,1.0], geom3.stdFrame);
  Vector3 geom_displacement = geom_end - geom_start;
  @@Interpret geom_displacement -> geom_displacement_

  @@TimeVector....
  Vector1 time_displacement = time_now - time_then;

  @@Scalar+Units ... what's going on here exactly with respect to frames?
  Scalar(?) duration = time_displacement.magnitude();

  @@VelocityVector(vel, [<computed>], <coordinate-free>)
  Vector3 displacement_per_time = geom_displacement / duration;

  Vector3 foobar = displacement_per_time + geom_displacement; // 

  return 0;
}

/*

*/