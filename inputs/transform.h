#include <vector>
#include "vec.h"

class Transform{
public:
    Transform(std::vector<double[3]> matrix_3x3);

    ~Transform(){ delete transform_; }

    Transform compose(Transform inner);
    Vec apply(Vec arg);


protected:
    Transform(double *transform) : transform_(transform) {}
    double* apply(double input[3]); //used internally for public apply and public compose
    double* get_transform() const { return transform_; }
private:
    double *transform_;
};