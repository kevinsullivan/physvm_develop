#include "ltlib.h"

LinearMap<double, Vec, Vec> *Euclidean3dMap::apply_scalar_action(double scalar){
    return new Euclidean3dMap([scalar, this](Vec in){
        return (this->map_(in)).vec_mul(scalar);
    });
};