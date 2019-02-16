#include "CoordsToDomain.h"

#include <iostream>

//using namespace std;
using namespace coords2domain;



void CoordsToDomain::PutVecExpr(const coords::VecExpr* n, domain::VecExpr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

domain::VecExpr* CoordsToDomain::getVecExpr
        (const coords::VecExpr* n)  {
   return interpExpression[*n]; 
}



void CoordsToDomain::PutVector(const coords::Vector* n, domain::Vector* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

domain::Vector* CoordsToDomain::getVector
        (const coords::Vector* n)  {
   return interpExpression[*n]; 
}


void CoordsToDomain::PutVecVecAddExpr(const coords::VecVecAddExpr* n, domain::VecVecAddExpr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

domain::VecVecAddExpr* CoordsToDomain::getVecVecAddExpr
        (const coords::VecVecAddExpr* n)  {
   return interpExpression[*n]; 
}

void CoordsToDomain::putVecIdent(const coords::VecIdent *key, domain::VecIdent *v) {
    interpIdent.insert(std::make_pair(*key, v));
}

const domain::VecIdent* CoordsToDomain::getVecIdent(const coords::VecIdent* n) 
{
    return interpIdent[*n];
}

void CoordsToDomain::putVecDef(coords::VecDef *key, domain::VecDef& b)
{
    interpVecDef.insert(std::make_pair(*key,&b));
}

const domain::VecDef* CoordsToDomain::getVecDef(const coords::VecDef* key)  {
   return interpVecDef[*key];     
}

/*
Constructed vector (from expr, lit, var) -- add vectors table?
*/
void CoordsToDomain::PutVector(const coords::Vector* n, domain::Vector* e) {
    interpVector.insert(std::make_pair(*n, e));
}

domain::Vector* CoordsToDomain::Vector(const coords::Vector* n)  {
   return interpVector[*n]; 
}


void CoordsToDomain::dump() const {
    for (auto it = interpExpression.begin(); it != interpExpression.end(); ++it) {
        //std::std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
        std::cerr << "CoordsToDomain::dump(). STUB.\n";
    }
    std::cerr << std::endl;
}
