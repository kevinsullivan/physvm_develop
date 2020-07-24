/*#include "Space.h"

using namespace domain;

// TODO: MOVE THIS STUFF
std::string Space::getName() const { return name_; }
int Space::getDimension() const { return dimension_; }

std::string MapSpace::getName() const { 
    return this->domain_.toString() + " " + this->codomain_.toString(); 
}


const std::unordered_map<std::string, std::function<Space(std::string,int)>> SpaceRegistry = {
    {"EuclideanGeometry",[](std::string name, int dimension){ return (Space)EuclideanSpace(name, dimension); }},
    {"ClassicalTime",[](std::string name, int dimension){ return (Space)AffineSpace(name, dimension); }},
    {"ClassicalVelocity",[](std::string name, int dimension){ return (Space)VectorSpace(name, dimension); }}
};

std::unordered_map<std::string, std::function<Space(std::string,int)>> Space::getRegistry(){
    return SpaceRegistry;
}
*/