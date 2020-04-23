#include <vector>
#include "transform.h"
#include "vec.h"

Transform::Transform(std::vector<double[3]> matrix_3x3){
        if(matrix_3x3.size() != 3){
            throw "This class only accepts a 3x3 matrix";
        }
        
        double *transform = new double[9];
        transform[0] = matrix_3x3[0][0];
        transform[1] = matrix_3x3[0][1];
        transform[2] = matrix_3x3[0][2];
        transform[3] = matrix_3x3[1][0];
        transform[4] = matrix_3x3[1][1];
        transform[5] = matrix_3x3[1][2];
        transform[6] = matrix_3x3[2][0];
        transform[7] = matrix_3x3[2][1];
        transform[8] = matrix_3x3[2][2];

        this->transform_ = transform;
}

Transform Transform::compose(Transform inner){
    double* new_transform_ = new double[9];
    double* vector_temp_ = new double[3];
    double* inner_transform_ = inner.get_transform();

    for(auto i = 0; i<3; i++){
        vector_temp_[0] = inner_transform_[0 + i];
        vector_temp_[1] = inner_transform_[3 + i];
        vector_temp_[2] = inner_transform_[6 + i];
        vector_temp_ = this->apply(vector_temp_);
        new_transform_[0 + i] = vector_temp_[0];
        new_transform_[3 + i] = vector_temp_[1];
        new_transform_[6 + i] = vector_temp_[2];
    }

    return Transform(new_transform_);
}

Vec Transform::apply(Vec arg){
    double input[3] = {arg.get_x(), arg.get_y(), arg.get_z()};

    double* output = this->apply(input);
    
    return Vec(output[0], output[1], output[2]);
};

double* Transform::apply(double input[3]){
    double* output = new double[3];
    output[0] = input[0] * this->transform_[0] + input[1] * this->transform_[1] + input[2] * this->transform_[2];
    output[1] = input[0] * this->transform_[3] + input[1] * this->transform_[4] + input[2] * this->transform_[5];
    output[2] = input[0] * this->transform_[6] + input[1] * this->transform_[7] + input[2] * this->transform_[8];
    return output;
};