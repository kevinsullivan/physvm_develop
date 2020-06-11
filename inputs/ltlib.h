#include "vec_lib.h"

#include <functional>

template <class ScalarField, class InModule, class OutModule>
class LinearMap{
public:
    //~LinearMap() = default;
    LinearMap() = default;
    std::function<OutModule(InModule)> get_map() const{
        return this->map_;
    };

    OutModule apply(InModule input){
        return this->map_(input);
    };
    
    template<class ArgScalarField, class ArgInModule>
    LinearMap<ArgScalarField, ArgInModule, OutModule> compose(LinearMap<ArgScalarField, ArgInModule, InModule> inner){
        return LinearMap<ArgScalarField, ArgInModule, OutModule>(
            [this,inner](ArgInModule input){
                return this->map_(inner.apply(input));
            }
        );
    };

    virtual LinearMap<ScalarField, InModule, OutModule> *apply_scalar_action(ScalarField c) = 0;

protected:
    LinearMap(std::function<OutModule(InModule)> map) : map_{map}{};
    std::function<OutModule(InModule)> map_;
};

class Euclidean3dMap : LinearMap<double, Vec, Vec>{
public:
    Euclidean3dMap(double flattened_matrix[9]) : LinearMap([flattened_matrix](Vec in){
        return Vec(
            in.get_x() * flattened_matrix[0] + in.get_y() * flattened_matrix[1] + in.get_z() * flattened_matrix[2],
            in.get_x() * flattened_matrix[3] + in.get_y() * flattened_matrix[4] + in.get_z() * flattened_matrix[5],
            in.get_x() * flattened_matrix[6] + in.get_y() * flattened_matrix[7] + in.get_z() * flattened_matrix[8]
        );
    }){};

    LinearMap<double, Vec, Vec> *apply_scalar_action(double c) override;
protected:
    Euclidean3dMap(std::function<Vec(Vec)> map) : LinearMap(map){}; 
};