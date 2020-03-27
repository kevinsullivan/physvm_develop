#include "CoordsToDomain.h"

#include <iostream>

//#include <g3log/g3log.hpp>



//using namespace std;
using namespace coords2domain;

// Ident

void CoordsToDomain::putVecIdent(coords::VecIdent *c, domain::VecIdent *d)
{
    coords2dom_VecIdent[c] = d;
    dom2coords_VecIdent[d] = c;
}

void CoordsToDomain::putFloatIdent(coords::FloatIdent *c, domain::FloatIdent *d)
{
    coords2dom_FloatIdent[c] = d;
    dom2coords_FloatIdent[d] = c;
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

domain::FloatIdent *CoordsToDomain::getFloatIdent(coords::FloatIdent *c) const
{
    std::unordered_map<coords::FloatIdent*, domain::FloatIdent*>::iterator it;
    domain::FloatIdent *dom = NULL;
    try {
        dom = coords2dom_FloatIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::FloatIdent *CoordsToDomain::getFloatIdent(domain::FloatIdent *d) const
{
    std::unordered_map<domain::FloatIdent*, coords::FloatIdent*>::iterator it;
    coords::FloatIdent *coords = NULL;
    try {
        coords = dom2coords_FloatIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}
/*
void CoordsToDomain::PutFloatExpr(coords::FloatExpr *c, domain::FloatExpr *d)
{
    coords2dom_FloatExpr[c] = d;
    dom2coords_FloatExpr[d] = c;
    //    coords2dom_VecIdent.insert(std::make_pair(c, d));
    //    dom2coords_VecIdent.insert(std::make_pair(d, c));
}
*/

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::FloatExpr *CoordsToDomain::getFloatExpr(coords::FloatExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = coords2dom_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::FloatExpr *CoordsToDomain::getFloatExpr(domain::FloatExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// Expr

// base

domain::VecExpr *CoordsToDomain::getVecExpr(coords::VecExpr *c) const
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

void CoordsToDomain::PutFloatVarExpr(coords::FloatVarExpr *c, domain::FloatVarExpr *d)
{
    coords2dom_FloatExpr[c] = d;
    dom2coords_FloatExpr[d] = c;
//    coord2dom_FloatExpr.insert(std::make_pair(*c, d));
}

domain::FloatVarExpr *CoordsToDomain::getFloatVarExpr(coords::FloatVarExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = coords2dom_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatVarExpr*>(dom);
}

coords::FloatVarExpr *CoordsToDomain::getFloatVarExpr(domain::FloatVarExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatVarExpr *>(coords);
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

void CoordsToDomain::PutVecScalarMulExpr(coords::VecScalarMulExpr *c, domain::VecScalarMulExpr *d)
{
    coords2dom_VecExpr[c] = d;
    dom2coords_VecExpr[d] = c;
}

void CoordsToDomain::PutFloatFloatAddExpr(coords::FloatFloatAddExpr *c, domain::FloatFloatAddExpr *d)
{
    coords2dom_FloatExpr[c] = d;
    dom2coords_FloatExpr[d] = c;
}

domain::FloatFloatAddExpr *CoordsToDomain::getFloatFloatAddExpr(coords::FloatFloatAddExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = coords2dom_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatFloatAddExpr*>(dom);
}

coords::FloatFloatAddExpr *CoordsToDomain::getFloatFloatAddExpr(domain::FloatFloatAddExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatFloatAddExpr *>(coords);
}


void CoordsToDomain::PutFloatFloatMulExpr(coords::FloatFloatMulExpr *c, domain::FloatFloatMulExpr *d)
{
    coords2dom_FloatExpr[c] = d;
    dom2coords_FloatExpr[d] = c;
}

domain::FloatFloatMulExpr *CoordsToDomain::getFloatFloatMulExpr(coords::FloatFloatMulExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = coords2dom_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatFloatMulExpr*>(dom);
}

coords::FloatFloatMulExpr *CoordsToDomain::getFloatFloatMulExpr(domain::FloatFloatMulExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatFloatMulExpr *>(coords);
}


//coords::VecScalarMulExpr *getVecSCalarMulExpr(domain::VecScalarMulExpr* d) const;
coords::VecScalarMulExpr *CoordsToDomain::getVecScalarMulExpr(domain::VecScalarMulExpr *d) const
{
    std::unordered_map<domain::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = dom2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecScalarMulExpr *>(coords);
}


//domain::VecScalarMulExpr *getVecScalarMulExpr(coords::VecScalarMulExpr* c) const;
domain::VecScalarMulExpr *CoordsToDomain::getVecScalarMulExpr(coords::VecScalarMulExpr *c) const
{
    std::unordered_map<coords::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = coords2dom_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecScalarMulExpr*>(dom);
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


void CoordsToDomain::PutFloatParenExpr(coords::FloatParenExpr *c, domain::FloatParenExpr *d) {
    coords2dom_FloatExpr[c] = d;
    dom2coords_FloatExpr[d] = c;
}

domain::FloatParenExpr *CoordsToDomain::getParenExpr(coords::FloatParenExpr* c) const {
    std::unordered_map<coords::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = coords2dom_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatParenExpr*>(dom);
}

coords::FloatParenExpr *CoordsToDomain::getParenExpr(domain::FloatParenExpr* d) const {
    std::unordered_map<domain::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatParenExpr *>(coords);
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

coords::Float *CoordsToDomain::getFloat(domain::Float* v) {
    std::unordered_map<domain::Float*, coords::Float*>::iterator it;
    coords::Float *coords = NULL;
    try {
        coords = dom2coords_Float.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float *>(coords);
}

domain::Float *CoordsToDomain::getFloat(coords::Float* v) {
    std::unordered_map<coords::Float*, domain::Float*>::iterator it;
    domain::Float *domvec = NULL;
    try {
        domvec = coords2dom_Float.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<domain::Float *>(domvec);
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

void CoordsToDomain::putFloat_Lit(coords::Float *c, domain::Float_Lit *d)
{
    coords2dom_Float[c] = d;
    dom2coords_Float[d] = c;
}

domain::Float_Lit *CoordsToDomain::getFloat_Lit(coords::Float_Lit *c) const
{
    std::unordered_map<coords::Float_Lit*, domain::Float_Lit*>::iterator it;
    domain::Float *dom = NULL;
    try {
        dom = coords2dom_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Lit*>(dom);
}

coords::Float_Lit *CoordsToDomain::getFloat_Lit(domain::Float_Lit *d) const
{
    std::unordered_map<domain::Float*, coords::Float*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_Float.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float_Lit *>(coords);
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


void CoordsToDomain::putFloat_Expr(coords::Float *c, domain::Float_Expr *d)
{
    coords2dom_Float[c] = d;
    dom2coords_Float[d] = c;
}

domain::Float_Expr *CoordsToDomain::getFloat_Expr(coords::Float_Expr *c) const
{
    std::unordered_map<coords::Float_Expr*, domain::Float_Expr*>::iterator it;
    domain::Float *dom = NULL;
    try {
        dom = coords2dom_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Expr*>(dom);
}

coords::Float_Expr *CoordsToDomain::getFloat_Expr(domain::Float_Expr *d) const
{
    std::unordered_map<domain::Float*, coords::Float*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = dom2coords_Float.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float_Expr *>(coords);
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

void CoordsToDomain::putFloat_Def(coords::Float_Def *c, domain::Float_Def *d)
{
    coords2dom_Float_Def[c] = d;
    dom2coords_Float_Def[d] = c;
}

domain::Float_Def *CoordsToDomain::getFloat_Def(coords::Float_Def *c) const
{
    std::unordered_map<coords::Float_Def*, domain::Float_Def*>::iterator it;
    domain::Float_Def *dom = NULL;
    try {
        dom = coords2dom_Float_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Def*>(dom);
}

coords::Float_Def *CoordsToDomain::getFloat_Def(domain::Float_Def *d) const
{
    std::unordered_map<domain::Float*, coords::Float*>::iterator it;
    coords::Float_Def *coords = NULL;
    try {
        coords = dom2coords_Float_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Float_Def *>(coords);
}

void CoordsToDomain::putVector_Assign(coords::Vector_Assign *c, domain::Vector_Assign *d)
{
    coords2dom_Vector_Assign[c] = d;
    dom2coords_Vector_Assign[d] = c;
}

domain::Vector_Assign *CoordsToDomain::getVector_Assign(coords::Vector_Assign *c) const
{
    std::unordered_map<coords::Vector_Assign*, domain::Vector_Assign*>::iterator it;
    domain::Vector_Assign *dom = NULL;
    try {
        dom = coords2dom_Vector_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Assign*>(dom);
}

coords::Vector_Assign *CoordsToDomain::getVector_Assign(domain::Vector_Assign *d) const
{
    std::unordered_map<domain::Vector*, coords::Vector*>::iterator it;
    coords::Vector_Assign *coords = NULL;
    try {
        coords = dom2coords_Vector_Assign.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Vector_Assign *>(coords);
}

void CoordsToDomain::putFloat_Assign(coords::Float_Assign *c, domain::Float_Assign *d)
{
    coords2dom_Float_Assign[c] = d;
    dom2coords_Float_Assign[d] = c;
}

domain::Float_Assign *CoordsToDomain::getFloat_Assign(coords::Float_Assign *c) const
{
    std::unordered_map<coords::Float_Assign*, domain::Float_Assign*>::iterator it;
    domain::Float_Assign *dom = NULL;
    try {
        dom = coords2dom_Float_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Assign*>(dom);
}

coords::Float_Assign *CoordsToDomain::getFloat_Assign(domain::Float_Assign *d) const
{
    std::unordered_map<domain::Float*, coords::Float*>::iterator it;
    coords::Float_Assign *coords = NULL;
    try {
        coords = dom2coords_Float_Assign.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Float_Assign *>(coords);
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
