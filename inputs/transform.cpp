#include "transform.h"
#include "vec.h"

Transform::Transform(){
    transform_ = new double[9];
}

Transform::Transform(Vec row1, Vec row2, Vec row3) : Transform() {
    this->set_row(0, row1);
    this->set_row(1, row2);
    this->set_row(2, row3);
}

Transform Transform::compose(Transform inner){
    double* new_transform_ = new double[9];
    double* vector_temp_ = new double[3];
    auto inner_transform_ = inner.get_transform();

    for(auto i = 0; i<3; i++){
        vector_temp_[0] = inner_transform_[0 + i];
        vector_temp_[1] = inner_transform_[3 + i];
        vector_temp_[2] = inner_transform_[6 + i];
        vector_temp_ = this->apply(vector_temp_);
        new_transform_[0 + i] = vector_temp_[0];
        new_transform_[3 + i] = vector_temp_[1];
        new_transform_[6 + i] = vector_temp_[2];
    }

    delete[] vector_temp_;
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

void Transform::set_row(int row, Vec row_vec){
    this->transform_[row*3] = row_vec.get_x();
    this->transform_[row*3 + 1] = row_vec.get_y();
    this->transform_[row*3 + 2] = row_vec.get_z();
}

Vec Transform::get_row(int row){
    return Vec(this->transform_[row*3], this->transform_[row*3 + 1], this->transform_[row*3 + 2]);
}