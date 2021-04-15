#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only
#include <vector>

#include "Coords.h"
//#include "AST.h"
#include "Domain.h"

/*
namespace interp2domain
{
    class InterpToDomain;
}
#ifndef INTERP2DOMAIN_H
#include "InterpToDomain.h"
#endif
*/
namespace interp{

class Interp {
public:
    Interp(coords::Coords* coords_, domain::DomainContainer* domain_, std::vector<Interp*> operands_) 
        : coords(coords_),domain(domain_),operands(operands_) {};
    std::string toString();
    std::string toStringLinked(std::vector<domain::CoordinateSpace*> spaces);
    Interp* getOperand(int i) const {
        return this->operands[i];
    }
    domain::DomainContainer* getDomain() const {
        return this->domain;
    }
    coords::Coords* getCoords() const {
        return this->coords;
    }
    bool hasValue();
    std::string getType();
private:
    coords::Coords* coords;
    domain::DomainContainer* domain;
    std::vector<Interp*> operands;
};

}

#endif