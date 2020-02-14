#include "CoordsToDomain.h"

#include <iostream>

#include <g3log/g3log.hpp>



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
domain::VecIdent *CoordsToDomain::getVecIdent(coords::VecIdent *c) const
{
    std::unordered_map<coords::VecIdent*, domain::VecIdent*>::iterator it;
    domain::VecIdent *dom = NULL;
    try {
        dom = coords2dom_VecIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::VecIdent *CoordsToDomain::getVecIdent(domain::VecIdent *d) const
{
    std::unordered_map<domain::VecIdent*, coords::VecIdent*>::iterator it;
    coords::VecIdent *coords = NULL;
    try {
        coords = dom2coords_VecIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// Expr

// base

domain::VecExpr *CoordsToDomain::getVecExpr(coords::VecExpr *c)
{
    std::unordered_map<coords::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = coords2dom_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::VecExpr *CoordsToDomain::getVecExpr(domain::VecExpr *d) const
{
    std::unordered_map<domain::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
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
    coords2dom_VecExpr[c] = d;
    dom2coords_VecExpr[d] = c;
//    coord2dom_VecExpr.insert(std::make_pair(*c, d));
}

domain::VecVarExpr *CoordsToDomain::getVecVarExpr(coords::VecVarExpr *c) const
{
    std::unordered_map<coords::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = coords2dom_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecVarExpr*>(dom);
}

coords::VecVarExpr *CoordsToDomain::getVecVarExpr(domain::VecVarExpr *d) const
{
    std::unordered_map<domain::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecVarExpr *>(coords);
}

// vecvecadd

void CoordsToDomain::PutVecVecAddExpr(coords::VecVecAddExpr *c, domain::VecVecAddExpr *d)
{
    coords2dom_VecExpr[c] = d;
    dom2coords_VecExpr[d] = c;
}

domain::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(coords::VecVecAddExpr *c) const
{
    std::unordered_map<coords::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = coords2dom_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecVecAddExpr*>(dom);
}

coords::VecVecAddExpr *CoordsToDomain::getVecVecAddExpr(domain::VecVecAddExpr *d) const
{
    std::unordered_map<domain::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecVecAddExpr *>(coords);
}


void CoordsToDomain::PutVecParenExpr(coords::VecParenExpr *c, domain::VecParenExpr *d) {
    coords2dom_VecExpr[c] = d;
    dom2coords_VecExpr[d] = c;
}

domain::VecParenExpr *CoordsToDomain::getParenExpr(coords::VecParenExpr* c) const {
    std::unordered_map<coords::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = coords2dom_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecParenExpr*>(dom);
}

coords::VecParenExpr *CoordsToDomain::getParenExpr(domain::VecParenExpr* d) const {
    std::unordered_map<domain::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecParenExpr *>(coords);
}



// Vector

coords::Vector *CoordsToDomain::getVector(domain::Vector* v) {
    std::unordered_map<domain::Vector*, coords::Vector*>::iterator it;
    coords::Vector *coords = NULL;
    try {
        coords = dom2coords_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector *>(coords);
}

domain::Vector *CoordsToDomain::getVector(coords::Vector* v) {
    std::unordered_map<coords::Vector*, domain::Vector*>::iterator it;
    domain::Vector *domvec = NULL;
    try {
        domvec = coords2dom_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<domain::Vector *>(domvec);
}


void CoordsToDomain::putVector_Lit(coords::Vector *c, domain::Vector_Lit *d)
{
    coords2dom_Vector[c] = d;
    dom2coords_Vector[d] = c;
}

domain::Vector_Lit *CoordsToDomain::getVector_Lit(coords::Vector_Lit *c) const
{
    std::unordered_map<coords::Vector_Lit*, domain::Vector_Lit*>::iterator it;
    domain::Vector *dom = NULL;
    try {
        dom = coords2dom_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Lit*>(dom);
}

coords::Vector_Lit *CoordsToDomain::getVector_Lit(domain::Vector_Lit *d) const
{
    std::unordered_map<domain::Vector*, coords::Vector*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector_Lit *>(coords);
}

void CoordsToDomain::putVector_Expr(coords::Vector *c, domain::Vector_Expr *d)
{
    coords2dom_Vector[c] = d;
    dom2coords_Vector[d] = c;
}

domain::Vector_Expr *CoordsToDomain::getVector_Expr(coords::Vector_Expr *c) const
{
    std::unordered_map<coords::Vector_Expr*, domain::Vector_Expr*>::iterator it;
    domain::Vector *dom = NULL;
    try {
        dom = coords2dom_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Expr*>(dom);
}

coords::Vector_Expr *CoordsToDomain::getVector_Expr(domain::Vector_Expr *d) const
{
    std::unordered_map<domain::Vector*, coords::Vector*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector_Expr *>(coords);
}

// Def

void CoordsToDomain::putVector_Def(coords::Vector_Def *c, domain::Vector_Def *d)
{
    coords2dom_Vector_Def[c] = d;
    dom2coords_Vector_Def[d] = c;
}

domain::Vector_Def *CoordsToDomain::getVector_Def(coords::Vector_Def *c) const
{
    std::unordered_map<coords::Vector_Def*, domain::Vector_Def*>::iterator it;
    domain::Vector_Def *dom = NULL;
    try {
        dom = coords2dom_Vector_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Def*>(dom);
}

coords::Vector_Def *CoordsToDomain::getVector_Def(domain::Vector_Def *d) const
{
    std::unordered_map<domain::Vector*, coords::Vector*>::iterator it;
    coords::Vector_Def *coords = NULL;
    try {
        coords = dom2coords_Vector_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Vector_Def *>(coords);
}

/*void CoordsToDomain::dump() const
{
    LOG(DEBUG) <<"CoordsToDomain::dump(). STUB.\n";

    for (auto it = coord2dom_VecExpr.begin(); it != coord2dom_VecExpr.end(); ++it)
    {
        //std::LOG(DEBUG) <<std::hex << &it->first << " : " << std::hex << it.second << "\n";
        LOG(DEBUG) <<"CoordsToDomain::dump(). STUB.\n";
    }
    LOG(DEBUG) <<std::endl;

}
*/

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
