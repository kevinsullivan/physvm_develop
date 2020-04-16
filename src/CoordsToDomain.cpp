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
}

void CoordsToDomain::putScalarIdent(coords::ScalarIdent *c, domain::ScalarIdent *d)
{
    coords2dom_ScalarIdent[c] = d;
    dom2coords_ScalarIdent[d] = c;
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

domain::ScalarIdent *CoordsToDomain::getScalarIdent(coords::ScalarIdent *c) const
{
    std::unordered_map<coords::ScalarIdent*, domain::ScalarIdent*>::iterator it;
    domain::ScalarIdent *dom = NULL;
    try {
        dom = coords2dom_ScalarIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::ScalarIdent *CoordsToDomain::getScalarIdent(domain::ScalarIdent *d) const
{
    std::unordered_map<domain::ScalarIdent*, coords::ScalarIdent*>::iterator it;
    coords::ScalarIdent *coords = NULL;
    try {
        coords = dom2coords_ScalarIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}
/*
void CoordsToDomain::PutScalarExpr(coords::ScalarExpr *c, domain::ScalarExpr *d)
{
    coords2dom_ScalarExpr[c] = d;
    dom2coords_ScalarExpr[d] = c;
    //    coords2dom_VecIdent.insert(std::make_pair(c, d));
    //    dom2coords_VecIdent.insert(std::make_pair(d, c));
}
*/

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::ScalarExpr *CoordsToDomain::getScalarExpr(coords::ScalarExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = coords2dom_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::ScalarExpr *CoordsToDomain::getScalarExpr(domain::ScalarExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_ScalarExpr.at(d);
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

void CoordsToDomain::PutScalarVarExpr(coords::ScalarVarExpr *c, domain::ScalarVarExpr *d)
{
    coords2dom_ScalarExpr[c] = d;
    dom2coords_ScalarExpr[d] = c;
}

domain::ScalarVarExpr *CoordsToDomain::getScalarVarExpr(coords::ScalarVarExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = coords2dom_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarVarExpr*>(dom);
}

coords::ScalarVarExpr *CoordsToDomain::getScalarVarExpr(domain::ScalarVarExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarVarExpr *>(coords);
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

void CoordsToDomain::PutScalarScalarAddExpr(coords::ScalarScalarAddExpr *c, domain::ScalarScalarAddExpr *d)
{
    coords2dom_ScalarExpr[c] = d;
    dom2coords_ScalarExpr[d] = c;
}

domain::ScalarScalarAddExpr *CoordsToDomain::getScalarScalarAddExpr(coords::ScalarScalarAddExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = coords2dom_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarScalarAddExpr*>(dom);
}

coords::ScalarScalarAddExpr *CoordsToDomain::getScalarScalarAddExpr(domain::ScalarScalarAddExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarScalarAddExpr *>(coords);
}


void CoordsToDomain::PutScalarScalarMulExpr(coords::ScalarScalarMulExpr *c, domain::ScalarScalarMulExpr *d)
{
    coords2dom_ScalarExpr[c] = d;
    dom2coords_ScalarExpr[d] = c;
}

domain::ScalarScalarMulExpr *CoordsToDomain::getScalarScalarMulExpr(coords::ScalarScalarMulExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = coords2dom_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarScalarMulExpr*>(dom);
}

coords::ScalarScalarMulExpr *CoordsToDomain::getScalarScalarMulExpr(domain::ScalarScalarMulExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarScalarMulExpr *>(coords);
}


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


void CoordsToDomain::PutScalarParenExpr(coords::ScalarParenExpr *c, domain::ScalarParenExpr *d) {
    coords2dom_ScalarExpr[c] = d;
    dom2coords_ScalarExpr[d] = c;
}

domain::ScalarParenExpr *CoordsToDomain::getParenExpr(coords::ScalarParenExpr* c) const {
    std::unordered_map<coords::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = coords2dom_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarParenExpr*>(dom);
}

coords::ScalarParenExpr *CoordsToDomain::getParenExpr(domain::ScalarParenExpr* d) const {
    std::unordered_map<domain::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarParenExpr *>(coords);
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

coords::Scalar *CoordsToDomain::getScalar(domain::Scalar* v) {
    std::unordered_map<domain::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar *coords = NULL;
    try {
        coords = dom2coords_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar *>(coords);
}

domain::Scalar *CoordsToDomain::getScalar(coords::Scalar* v) {
    std::unordered_map<coords::Scalar*, domain::Scalar*>::iterator it;
    domain::Scalar *domvec = NULL;
    try {
        domvec = coords2dom_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<domain::Scalar *>(domvec);
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

void CoordsToDomain::putScalar_Lit(coords::Scalar *c, domain::Scalar_Lit *d)
{
    coords2dom_Scalar[c] = d;
    dom2coords_Scalar[d] = c;
}

domain::Scalar_Lit *CoordsToDomain::getScalar_Lit(coords::Scalar_Lit *c) const
{
    std::unordered_map<coords::Scalar_Lit*, domain::Scalar_Lit*>::iterator it;
    domain::Scalar *dom = NULL;
    try {
        dom = coords2dom_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Lit*>(dom);
}

coords::Scalar_Lit *CoordsToDomain::getScalar_Lit(domain::Scalar_Lit *d) const
{
    std::unordered_map<domain::Scalar*, coords::Scalar*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar_Lit *>(coords);
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


void CoordsToDomain::putScalar_Expr(coords::Scalar *c, domain::Scalar_Expr *d)
{
    coords2dom_Scalar[c] = d;
    dom2coords_Scalar[d] = c;
}

domain::Scalar_Expr *CoordsToDomain::getScalar_Expr(coords::Scalar_Expr *c) const
{
    std::unordered_map<coords::Scalar_Expr*, domain::Scalar_Expr*>::iterator it;
    domain::Scalar *dom = NULL;
    try {
        dom = coords2dom_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Expr*>(dom);
}

coords::Scalar_Expr *CoordsToDomain::getScalar_Expr(domain::Scalar_Expr *d) const
{
    std::unordered_map<domain::Scalar*, coords::Scalar*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = dom2coords_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar_Expr *>(coords);
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

void CoordsToDomain::putScalar_Def(coords::Scalar_Def *c, domain::Scalar_Def *d)
{
    coords2dom_Scalar_Def[c] = d;
    dom2coords_Scalar_Def[d] = c;
}

domain::Scalar_Def *CoordsToDomain::getScalar_Def(coords::Scalar_Def *c) const
{
    std::unordered_map<coords::Scalar_Def*, domain::Scalar_Def*>::iterator it;
    domain::Scalar_Def *dom = NULL;
    try {
        dom = coords2dom_Scalar_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Def*>(dom);
}

coords::Scalar_Def *CoordsToDomain::getScalar_Def(domain::Scalar_Def *d) const
{
    std::unordered_map<domain::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar_Def *coords = NULL;
    try {
        coords = dom2coords_Scalar_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Scalar_Def *>(coords);
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

void CoordsToDomain::putScalar_Assign(coords::Scalar_Assign *c, domain::Scalar_Assign *d)
{
    coords2dom_Scalar_Assign[c] = d;
    dom2coords_Scalar_Assign[d] = c;
}

domain::Scalar_Assign *CoordsToDomain::getScalar_Assign(coords::Scalar_Assign *c) const
{
    std::unordered_map<coords::Scalar_Assign*, domain::Scalar_Assign*>::iterator it;
    domain::Scalar_Assign *dom = NULL;
    try {
        dom = coords2dom_Scalar_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Assign*>(dom);
}

coords::Scalar_Assign *CoordsToDomain::getScalar_Assign(domain::Scalar_Assign *d) const
{
    std::unordered_map<domain::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar_Assign *coords = NULL;
    try {
        coords = dom2coords_Scalar_Assign.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Scalar_Assign *>(coords);
}

/*void CoordsToDomain::dump() const
{
    LOG(DBUG) <<"CoordsToDomain::dump(). STUB.\n";

    for (auto it = coord2dom_VecExpr.begin(); it != coord2dom_VecExpr.end(); ++it)
    {
        //std::LOG(DBUG) <<std::hex << &it->first << " : " << std::hex << it.second << "\n";
        LOG(DBUG) <<"CoordsToDomain::dump(). STUB.\n";
    }
    LOG(DBUG) <<std::endl;

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
