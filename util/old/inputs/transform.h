
#include "vec_lib.h"

#ifndef transform
#define transform

//using matrix = std::shared_ptr<std::vector<double[3]>>;
class Transform{
public:
    Transform();
    Transform(Vec row1, Vec row2, Vec row3);

    //~Transform(){ delete transform_; }

    Transform compose(Transform inner);
    Vec apply(Vec arg);
    void set_row(int row, Vec row_vec);
    Vec get_row(int row);
    double* get_transform() const{ return this->transform_; };
protected:
    Transform(double *transform) : transform_(transform) {}
    double* apply(double input[3]); //used internally for public apply and public compose
   // double* get_transform() const { return transform_; }
private:
    double* transform_;
};

#endif