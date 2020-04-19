#include "CoordsToInterp.h"

#include <iostream>

#include <g3log/g3log.hpp>


using namespace coords2interp;

// Ident

void CoordsToInterp::putVecIdent(coords::VecIdent *c, interp::VecIdent *d)
{
    coords2interp_VecIdent[c] = d;
    interp2coords_VecIdent[d] = c;
}

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
interp::VecIdent *CoordsToInterp::getVecIdent(coords::VecIdent *c) const
{
    std::unordered_map<coords::VecIdent*, interp::VecIdent*>::iterator it;
    interp::VecIdent *dom = NULL;
    try {
        dom = coords2interp_VecIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::VecIdent *CoordsToInterp::getVecIdent(interp::VecIdent *d) const
{
    std::unordered_map<interp::VecIdent*, coords::VecIdent*>::iterator it;
    coords::VecIdent *coords = NULL;
    try {
        coords = interp2coords_VecIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// Expr

// base

interp::VecExpr *CoordsToInterp::getVecExpr(coords::VecExpr *c)
{
    std::unordered_map<coords::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *dom = NULL;
    try {
        dom = coords2interp_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::VecExpr *CoordsToInterp::getVecExpr(interp::VecExpr *d) const
{
    std::unordered_map<interp::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}


void CoordsToInterp::putVecVarExpr(coords::VecVarExpr *c, interp::VecVarExpr *d)
{
    std::string cstr = c->toString();
    std::string dstr = d->toString();
    LOG(DBUG) << "CoordsToInterp::putVecVarExpr c " << cstr << "\n";
    LOG(DBUG) << "CoordsToInterp::putVecVarExpr d " << dstr << "\n";
    coords2interp_VecExpr[c] = d;
    interp2coords_VecExpr[d] = c;

    interp::VecVarExpr *foo = getVecVarExpr(c);
    std::string s = foo->toString();
    LOG(DBUG) << "Debug " << s << "\n";
}

interp::VecVarExpr *CoordsToInterp::getVecVarExpr(coords::VecVarExpr *c) const
{
    std::unordered_map<coords::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *dom = NULL;
    try {
        dom = coords2interp_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::VecVarExpr*>(dom);
}

coords::VecVarExpr *CoordsToInterp::getVecVarExpr(interp::VecVarExpr *d) const
{
    std::unordered_map<interp::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecVarExpr *>(coords);
}

// vecparenexpr

void CoordsToInterp::putVecParenExpr(coords::VecParenExpr *c, interp::VecParenExpr *i) {
    coords2interp_VecExpr[c] = i;
    interp2coords_VecExpr[i] = c;
}

interp::VecParenExpr *CoordsToInterp::getVecParenExpr(coords::VecParenExpr* c) const {
    std::unordered_map<coords::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *dom = NULL;
    try {
        dom = coords2interp_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::VecParenExpr*>(dom);
}
// TODO: A few template functions should take care of most of this file
coords::VecParenExpr *CoordsToInterp::getVecParenExpr(interp::VecParenExpr* d) const {
    std::unordered_map<interp::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecParenExpr *>(coords);
}

// vecvecadd

void CoordsToInterp::putVecVecAddExpr(coords::VecVecAddExpr *c, interp::VecVecAddExpr *d)
{
    coords2interp_VecExpr[c] = d;
    interp2coords_VecExpr[d] = c;
}

interp::VecVecAddExpr *CoordsToInterp::getVecVecAddExpr(coords::VecVecAddExpr *c) const
{
    std::unordered_map<coords::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *dom = NULL;
    try {
        dom = coords2interp_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::VecVecAddExpr*>(dom);
}

coords::VecVecAddExpr *CoordsToInterp::getVecVecAddExpr(interp::VecVecAddExpr *d) const
{
    std::unordered_map<interp::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecVecAddExpr *>(coords);
}

void CoordsToInterp::putVecScalarMulExpr(coords::VecScalarMulExpr *c, interp::VecScalarMulExpr *d)
{
    coords2interp_VecExpr[c] = d;
    interp2coords_VecExpr[d] = c;
}

interp::VecScalarMulExpr *CoordsToInterp::getVecScalarMulExpr(coords::VecScalarMulExpr *c) const
{
    std::unordered_map<coords::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *dom = NULL;
    try {
        dom = coords2interp_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::VecScalarMulExpr*>(dom);
}

coords::VecScalarMulExpr *CoordsToInterp::getVecScalarMulExpr(interp::VecScalarMulExpr *d) const
{
    std::unordered_map<interp::VecExpr*, coords::VecExpr*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VecScalarMulExpr *>(coords);
}


void CoordsToInterp::putScalarIdent(coords::ScalarIdent *c, interp::ScalarIdent *d)
{
    coords2interp_ScalarIdent[c] = d;
    interp2coords_ScalarIdent[d] = c;
}

interp::ScalarIdent *CoordsToInterp::getScalarIdent(coords::ScalarIdent *c) const
{
    std::unordered_map<coords::ScalarIdent*, interp::ScalarIdent*>::iterator it;
    interp::ScalarIdent *dom = NULL;
    try {
        dom = coords2interp_ScalarIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::ScalarIdent *CoordsToInterp::getScalarIdent(interp::ScalarIdent *d) const
{
    std::unordered_map<interp::ScalarIdent*, coords::ScalarIdent*>::iterator it;
    coords::ScalarIdent *coords = NULL;
    try {
        coords = interp2coords_ScalarIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// Expr

// base

interp::ScalarExpr *CoordsToInterp::getScalarExpr(coords::ScalarExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *dom = NULL;
    try {
        dom = coords2interp_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::ScalarExpr *CoordsToInterp::getScalarExpr(interp::ScalarExpr *d) const
{
    std::unordered_map<interp::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// var

void CoordsToInterp::putScalarVarExpr(coords::ScalarVarExpr *c, interp::ScalarVarExpr *d)
{
    std::string cstr = c->toString();
    std::string dstr = d->toString();
    LOG(DBUG) << "CoordsToInterp::putScalarVarExpr c " << cstr << "\n";
    LOG(DBUG) << "CoordsToInterp::putScalarVarExpr d " << dstr << "\n";
    coords2interp_ScalarExpr[c] = d;
    interp2coords_ScalarExpr[d] = c;

    interp::ScalarVarExpr *foo = getScalarVarExpr(c);
    std::string s = foo->toString();
    LOG(DBUG) << "Debug " << s << "\n";
}

interp::ScalarVarExpr *CoordsToInterp::getScalarVarExpr(coords::ScalarVarExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *dom = NULL;
    try {
        dom = coords2interp_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::ScalarVarExpr*>(dom);
}

coords::ScalarVarExpr *CoordsToInterp::getScalarVarExpr(interp::ScalarVarExpr *d) const
{
    std::unordered_map<interp::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarVarExpr *>(coords);
}


void CoordsToInterp::putScalarScalarAddExpr(coords::ScalarScalarAddExpr *c, interp::ScalarScalarAddExpr *d)
{
    coords2interp_ScalarExpr[c] = d;
    interp2coords_ScalarExpr[d] = c;
}

interp::ScalarScalarAddExpr *CoordsToInterp::getScalarScalarAddExpr(coords::ScalarScalarAddExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *dom = NULL;
    try {
        dom = coords2interp_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::ScalarScalarAddExpr*>(dom);
}

coords::ScalarScalarAddExpr *CoordsToInterp::getScalarScalarAddExpr(interp::ScalarScalarAddExpr *d) const
{
    std::unordered_map<interp::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarScalarAddExpr *>(coords);
}

void CoordsToInterp::putScalarScalarMulExpr(coords::ScalarScalarMulExpr *c, interp::ScalarScalarMulExpr *d)
{
    coords2interp_ScalarExpr[c] = d;
    interp2coords_ScalarExpr[d] = c;
}

interp::ScalarScalarMulExpr *CoordsToInterp::getScalarScalarMulExpr(coords::ScalarScalarMulExpr *c) const
{
    std::unordered_map<coords::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *dom = NULL;
    try {
        dom = coords2interp_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::ScalarScalarMulExpr*>(dom);
}

coords::ScalarScalarMulExpr *CoordsToInterp::getScalarScalarMulExpr(interp::ScalarScalarMulExpr *d) const
{
    std::unordered_map<interp::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarScalarMulExpr *>(coords);
}


// Scalarparenexpr

void CoordsToInterp::putScalarParenExpr(coords::ScalarParenExpr *c, interp::ScalarParenExpr *i) {
    coords2interp_ScalarExpr[c] = i;
    interp2coords_ScalarExpr[i] = c;
}

interp::ScalarParenExpr *CoordsToInterp::getScalarParenExpr(coords::ScalarParenExpr* c) const {
    std::unordered_map<coords::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *dom = NULL;
    try {
        dom = coords2interp_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::ScalarParenExpr*>(dom);
}
// TODO: A few template functions should take care of most of this file
coords::ScalarParenExpr *CoordsToInterp::getScalarParenExpr(interp::ScalarParenExpr* d) const {
    std::unordered_map<interp::ScalarExpr*, coords::ScalarExpr*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ScalarParenExpr *>(coords);
}


// Vector

coords::Vector *CoordsToInterp::getVector(interp::Vector* v) {
    std::unordered_map<interp::Vector*, coords::Vector*>::iterator it;
    coords::Vector *coords = NULL;
    try {
        coords = interp2coords_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector *>(coords);
}

interp::Vector *CoordsToInterp::getVector(coords::Vector* v) {
    std::unordered_map<coords::Vector*, interp::Vector*>::iterator it;
    interp::Vector *domvec = NULL;
    try {
        domvec = coords2interp_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<interp::Vector *>(domvec);
}


void CoordsToInterp::putVector_Lit(coords::Vector *c, interp::Vector_Lit *d)
{
    coords2interp_Vector[c] = d;
    interp2coords_Vector[d] = c;
}

interp::Vector_Lit *CoordsToInterp::getVector_Lit(coords::Vector_Lit *c) const
{
    std::unordered_map<coords::Vector_Lit*, interp::Vector_Lit*>::iterator it;
    interp::Vector *dom = NULL;
    try {
        dom = coords2interp_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Vector_Lit*>(dom);
}

coords::Vector_Lit *CoordsToInterp::getVector_Lit(interp::Vector_Lit *d) const
{
    std::unordered_map<interp::Vector*, coords::Vector*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector_Lit *>(coords);
}

void CoordsToInterp::putVector_Expr(coords::Vector *c, interp::Vector_Expr *d)
{
    coords2interp_Vector[c] = d;
    interp2coords_Vector[d] = c;
}

interp::Vector_Expr *CoordsToInterp::getVector_Expr(coords::Vector_Expr *c) const
{
    std::unordered_map<coords::Vector_Expr*, interp::Vector_Expr*>::iterator it;
    interp::Vector *dom = NULL;
    try {
        dom = coords2interp_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Vector_Expr*>(dom);
}

coords::Vector_Expr *CoordsToInterp::getVector_Expr(interp::Vector_Expr *d) const
{
    std::unordered_map<interp::Vector*, coords::Vector*>::iterator it;
    coords::VecExpr *coords = NULL;
    try {
        coords = interp2coords_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Vector_Expr *>(coords);
}

// Def

void CoordsToInterp::putVector_Def(coords::Vector_Def *c, interp::Vector_Def *d)
{
    coords2interp_Vector_Def[c] = d;
    interp2coords_Vector_Def[d] = c;
}

interp::Vector_Def *CoordsToInterp::getVector_Def(coords::Vector_Def *c) const
{
    std::unordered_map<coords::Vector_Def*, interp::Vector_Def*>::iterator it;
    interp::Vector_Def *dom = NULL;
    try {
        dom = coords2interp_Vector_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Vector_Def*>(dom);
}

coords::Vector_Def *CoordsToInterp::getVector_Def(interp::Vector_Def *d) const
{
    std::unordered_map<interp::Vector*, coords::Vector*>::iterator it;
    coords::Vector_Def *coords = NULL;
    try {
        coords = interp2coords_Vector_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Vector_Def *>(coords);
}

void CoordsToInterp::putVector_Assign(coords::Vector_Assign *c, interp::Vector_Assign *d)
{
    coords2interp_Vector_Assign[c] = d;
    interp2coords_Vector_Assign[d] = c;
}

interp::Vector_Assign *CoordsToInterp::getVector_Assign(coords::Vector_Assign *c) const
{
    std::unordered_map<coords::Vector_Assign*, interp::Vector_Assign*>::iterator it;
    interp::Vector_Assign *dom = NULL;
    try {
        dom = coords2interp_Vector_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Vector_Assign*>(dom);
}

coords::Vector_Assign *CoordsToInterp::getVector_Assign(interp::Vector_Assign *d) const
{
    std::unordered_map<interp::Vector*, coords::Vector*>::iterator it;
    coords::Vector_Assign *coords = NULL;
    try {
        coords = interp2coords_Vector_Assign.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Vector_Assign *>(coords);
}

coords::Scalar *CoordsToInterp::getScalar(interp::Scalar* v) {
    std::unordered_map<interp::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar *coords = NULL;
    try {
        coords = interp2coords_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar *>(coords);
}

interp::Scalar *CoordsToInterp::getScalar(coords::Scalar* v) {
    std::unordered_map<coords::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar *domvec = NULL;
    try {
        domvec = coords2interp_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }

    //for(auto it = coords2interp_Scalar.begin(); it != coords2interp_Scalar.end();it++){
   //     std::cout<<it->first->toString()<<" "<<it->second->toString()<<std::endl;
   // }
    //std::cout<<domvec->toString()<<std::endl;

    return static_cast<interp::Scalar *>(domvec);
}


void CoordsToInterp::putScalar_Lit(coords::Scalar *c, interp::Scalar_Lit *d)
{
    coords2interp_Scalar[c] = d;
    interp2coords_Scalar[d] = c;
}

interp::Scalar_Lit *CoordsToInterp::getScalar_Lit(coords::Scalar_Lit *c) const
{
    std::unordered_map<coords::Scalar_Lit*, interp::Scalar_Lit*>::iterator it;
    interp::Scalar *dom = NULL;
    try {
        dom = coords2interp_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Scalar_Lit*>(dom);
}

coords::Scalar_Lit *CoordsToInterp::getScalar_Lit(interp::Scalar_Lit *d) const
{
    std::unordered_map<interp::Scalar*, coords::Scalar*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar_Lit *>(coords);
}

void CoordsToInterp::putScalar_Expr(coords::Scalar *c, interp::Scalar_Expr *d)
{
    coords2interp_Scalar[c] = d;
    interp2coords_Scalar[d] = c;
}

interp::Scalar_Expr *CoordsToInterp::getScalar_Expr(coords::Scalar_Expr *c) const
{
    std::unordered_map<coords::Scalar_Expr*, interp::Scalar_Expr*>::iterator it;
    interp::Scalar *dom = NULL;
    try {
        dom = coords2interp_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Scalar_Expr*>(dom);
}

coords::Scalar_Expr *CoordsToInterp::getScalar_Expr(interp::Scalar_Expr *d) const
{
    std::unordered_map<interp::Scalar*, coords::Scalar*>::iterator it;
    coords::ScalarExpr *coords = NULL;
    try {
        coords = interp2coords_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Scalar_Expr *>(coords);
}

// Def

void CoordsToInterp::putScalar_Def(coords::Scalar_Def *c, interp::Scalar_Def *d)
{
    coords2interp_Scalar_Def[c] = d;
    interp2coords_Scalar_Def[d] = c;
}

interp::Scalar_Def *CoordsToInterp::getScalar_Def(coords::Scalar_Def *c) const
{
    std::unordered_map<coords::Scalar_Def*, interp::Scalar_Def*>::iterator it;
    interp::Scalar_Def *dom = NULL;
    try {
        dom = coords2interp_Scalar_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Scalar_Def*>(dom);
}

coords::Scalar_Def *CoordsToInterp::getScalar_Def(interp::Scalar_Def *d) const
{
    std::unordered_map<interp::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar_Def *coords = NULL;
    try {
        coords = interp2coords_Scalar_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Scalar_Def *>(coords);
}

void CoordsToInterp::putScalar_Assign(coords::Scalar_Assign *c, interp::Scalar_Assign *d)
{
    coords2interp_Scalar_Assign[c] = d;
    interp2coords_Scalar_Assign[d] = c;
}

interp::Scalar_Assign *CoordsToInterp::getScalar_Assign(coords::Scalar_Assign *c) const
{
    std::unordered_map<coords::Scalar_Assign*, interp::Scalar_Assign*>::iterator it;
    interp::Scalar_Assign *dom = NULL;
    try {
        dom = coords2interp_Scalar_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Scalar_Assign*>(dom);
}

coords::Scalar_Assign *CoordsToInterp::getScalar_Assign(interp::Scalar_Assign *d) const
{
    std::unordered_map<interp::Scalar*, coords::Scalar*>::iterator it;
    coords::Scalar_Assign *coords = NULL;
    try {
        coords = interp2coords_Scalar_Assign.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Scalar_Assign *>(coords);
}
