#include "CoordsToDomain.h"

#include <iostream>

//using namespace std;
using namespace coords2domain;

// Ident

void CoordsToDomain::putVecIdent(coords::VecIdent *c, domain::VecIdent *d)
{
    coords2dom_VecIdent[c] = d;
    dom2coords_VecIdent[d] = c;
    //    coords2dom_VecIdent.insert(std::make_pair(c, d));
    //    dom2coords_VecIdent.insert(std::make_pair(d, c));
}

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::VecIdent *CoordsToDomain::getVecIdentDom(coords::VecIdent *c) const
{
    std::unordered_map<coords::VecIdent*, domain::VecIdent*>::iterator it;
    domain::VecIdent *dom = NULL;
    try {
        domain::VecIdent* dom = coords2dom_VecIdent.at(c);
    }
    catch (const std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::VecIdent *CoordsToDomain::getVecIdentCoords(domain::VecIdent *d) const
{
    return dom2coords_VecIdent[d];
    ;
    //    return d->getCoords();
}

// Expr

// base

domain::VecExpr *CoordsToDomain::getVecExpr(coords::VecExpr *c)
{
    return coords2dom_VecExpr[*c];
}

coords::VecExpr *CoordsToDomain::getVecExpr(domain::VecExpr *d) const
{
    return d->getCoords();
}

// lit
/*
void CoordsToDomain::putVecLitExpr(coords::VecLitExpr d, domain::VecLitExpr d) {
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}


domain::VecLitExpr *CoordsToDomain::getLitInterp(coords::VecLitExpr c) const {
   return coord2dom_VecExpr[*c];
}

coords::VecLitExpr *CoordsToDomain::getLitInterp(domain::VecLitExpr d) const {
    return d->getCoords();
}
*/

// var

void CoordsToDomain::PutVecVarExpr(coords::VecVarExpr *c, domain::VecVarExpr *d)
{
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::VecVarExpr *CoordsToDomain::getVecVarExpr(coords::VecVarExpr *c) const
{
    std::cerr << "CoordsToDomain::getVecVarExpr: Warn. Check these static casts.\n";
    return static_cast<domain::VecVarExpr *>(coord2dom_VecExpr[*c]);
}

coords::VecVarExpr *CoordsToDomain::getVecVarExpr(domain::VecVarExpr *d) const
{
    return d->getCoords();
}

// vecvecadd

void CoordsToDomain::PutVecVecAddExpr(coords::VecVecAddExpr *c, domain::VecVecAddExpr *d)
{
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(coords::VecVarExpr *c) const
{
    return static_cast<domain::VecVecAddExpr *>(coord2dom_VecExpr[*c]);
}

coords::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(domain::VecVarExpr *d) const
{
    return d->getCoords();
}

// Vector

void CoordsToDomain::putVector_Lit(coords::Vector *ast, domain::Vector_Lit *v)
{
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::Vector_Lit *CoordsToDomain::getVector(coords::Vector_Lit *c) const
{
    return coord2dom_VecExpr[*c];
}

coords::Vector_Lit *CoordsToDomain::getVector(domain::Vector_Lit *d) const
{
    return d->getCoords();
}

void CoordsToDomain::putVector_Expr(coords::Vector *c, domain::Vector_Expr *d)
{
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::Vector *CoordsToDomain::getVector(coords::Vector_Expr *c) const
{
    return static_cast<domain::Vector *>(coord2dom_VecExpr[*c]);
}

coords::Vector_Expr *CoordsToDomain::getVector(domain::Vector_Expr *d) const
{
    return d->getCoords();
}

// Def

void CoordsToDomain::putVector_Def(coords::Vector_Def *c, domain::Vector_Def *d)
{
    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::Vector_Def *getVector_Def(coords::Vector_Def *c) const
{
    return static_cast<domain::Vector_Def *>(coord2dom_VecExpr[*c]);
}

coords::Vector_Def *getVector_Def(domain::Vector_Def *d) const
{
    return d->getCoords();
}

void CoordsToDomain::dump() const
{
    for (auto it = coord2dom_VecExpr.begin(); it != coord2dom_VecExpr.end(); ++it)
    {
        //std::std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
        std::cerr << "CoordsToDomain::dump(). STUB.\n";
    }
    std::cerr << std::endl;
}

//-------------------------

/*
void CoordsToDomain::PutVecExpr(const coords::VecExpr* n, domain::VecExpr* e) {
    coord2dom_VecExpr.insert(std::make_pair(*n, e));
}

domain::VecExpr* CoordsToDomain::getVecExpr
        (const coords::VecExpr* n)  {
   return coord2dom_VecExpr[*n]; 
}



void CoordsToDomain::PutVector(const coords::Vector* n, domain::Vector* e) {
    coord2dom_VecExpr.insert(std::make_pair(*n, e));
}

domain::Vector* CoordsToDomain::getVector
        (const coords::Vector* n)  {
   return coord2dom_VecExpr[*n]; 
}


void CoordsToDomain::PutVecVecAddExpr(const coords::VecVecAddExpr* n, domain::VecVecAddExpr* e) {
    coord2dom_VecExpr.insert(std::make_pair(*n, e));
}

domain::VecVecAddExpr* CoordsToDomain::getVecVecAddExpr
        (const coords::VecVecAddExpr* n)  {
   return coord2dom_VecExpr[*n]; 
}

void CoordsToDomain::putVecIdent(const coords::VecIdent *key, domain::VecIdent *v) {
    coord2dom_VecIdent.insert(std::make_pair(*key, v));
}

const domain::VecIdent* CoordsToDomain::getVecIdent(const coords::VecIdent* n) 
{
    return coord2dom_VecIdent[*n];
}

void CoordsToDomain::putVector_Def(coords::Vector_Def *key, domain::Vector_Def& b)
{
    coord2dom_Vector_Def.insert(std::make_pair(*key,&b));
}

const domain::Vector_Def* CoordsToDomain::getVector_Def(const coords::Vector_Def* key)  {
   return coord2dom_Vector_Def[*key];     
}

void CoordsToDomain::PutVector(const coords::Vector* n, domain::Vector* e) {
    coord2dom_Vector.insert(std::make_pair(*n, e));
}

domain::Vector* CoordsToDomain::Vector(const coords::Vector* n)  {
   return coord2dom_Vector[*n]; 
}

*/
