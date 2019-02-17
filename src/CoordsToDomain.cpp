#include "CoordsToDomain.h"

#include <iostream>

//using namespace std;
using namespace coords2domain;

// Ident

void CoordsToDomain::putVecIdent(coords::VecIdent *c, domain::VecIdent *d) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::VecIdent *CoordsToDomain::getVecIdent(coords::VecIdent *c) const {
   return interpExpression[*c];
}

coords::VecIdent *CoordsToDomain::getVecIdent(domain::VecIdent *d) const {
    return d->getCoords();
}

// Expr

// base

domain::VecExpr *CoordsToDomain::getVecExpr(coords::VecExpr* c) {
   return interpExpression[*c];
}

coords::VecExpr *CoordsToDomain::getVecExpr(domain::VecExpr* d) const {
    return d->getCoords();
}

void CoordsToDomain::putVecLitExpr(coords::VecLitExpr d, domain::VecLitExpr d) {
    interpExpression.insert(std::make_pair(*c, d));
}

// lit

domain::VecLitExpr *CoordsToDomain::getLitInterp(coords::VecLitExpr c) const {
   return interpExpression[*c];
}

coords::VecLitExpr *CoordsToDomain::getLitInterp(domain::VecLitExpr d) const {
    return d->getCoords();
}

// var

void CoordsToDomain::PutVecVarExpr(coords::VecVarExpr *c, domain::VecVarExpr *d) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::VecVarExpr *CoordsToDomain::getVecVarExpr(coords::VecVarExpr* c) const {
   return interpExpression[*c];
}

coords::VecVarExpr *CoordsToDomain::getVecVarExpr(domain::VecVarExpr* d) const {
    return d->getCoords();
}

// vecvecadd

void CoordsToDomain::PutVecVecAddExpr(coords::VecVecAddExpr *c, domain::VecVecAddExpr *d) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(coords::VecVarExpr* c) const {
   return interpExpression[*c];
}

coords::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(domain::VecVarExpr* d) const {
    return d->getCoords();
}

// Vector

void CoordsToDomain::putVector_Lit(coords::Vector *ast, domain::Vector_Lit *v) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::Vector_Lit *CoordsToDomain::getVector(coords::Vector_Lit* c) const {
   return interpExpression[*c];
}

coords::Vector_Lit *CoordsToDomain::getVector(domain::Vector_Lit* d) const {
    return d->getCoords();
}

void CoordsToDomain::putVector_Expr(coords::Vector *c, domain::Vector_Expr *d) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::Vector *CoordsToDomain::getVector(coords::Vector_Expr* c) const {
     return interpExpression[*c];  
}

coords::Vector_Expr *CoordsToDomain::getVector(domain::Vector_Expr* d const) {
    return d->getCoords();
}

// Def

void CoordsToDomain::putVector_Def(coords::Vector_Def *c, domain::Vector_Def *d) {
    interpExpression.insert(std::make_pair(*c, d));
}

domain::Vector_Def *getVector_Def(coords::Vector_Def* c) const {
   return interpExpression[*c];
}

coords::Vector_Def *getVector_Def(domain::Vector_Def* d) const {
    return d->getCoords();
}


void CoordsToDomain::dump() const {
    for (auto it = interpExpression.begin(); it != interpExpression.end(); ++it) {
        //std::std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
        std::cerr << "CoordsToDomain::dump(). STUB.\n";
    }
    std::cerr << std::endl;
}


//-------------------------

/*
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

void CoordsToDomain::putVector_Def(coords::Vector_Def *key, domain::Vector_Def& b)
{
    interpVector_Def.insert(std::make_pair(*key,&b));
}

const domain::Vector_Def* CoordsToDomain::getVector_Def(const coords::Vector_Def* key)  {
   return interpVector_Def[*key];     
}

void CoordsToDomain::PutVector(const coords::Vector* n, domain::Vector* e) {
    interpVector.insert(std::make_pair(*n, e));
}

domain::Vector* CoordsToDomain::Vector(const coords::Vector* n)  {
   return interpVector[*n]; 
}

*/

