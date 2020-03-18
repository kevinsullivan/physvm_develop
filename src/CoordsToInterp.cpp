#include "CoordsToInterp.h"

#include <iostream>

//#include <g3log/g3log.hpp>


using namespace coords2interp;

// Ident

void CoordsToInterp::putVecIdent(coords::VecIdent *c, interp::VecIdent *d)
{
    coords2interp_VecIdent[c] = d;
    interp2coords_VecIdent[d] = c;
    //    coords2interp_VecIdent.insert(std::make_pair(c, d));
    //    interp2coords_VecIdent.insert(std::make_pair(d, c));
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

// var

void CoordsToInterp::putVecVarExpr(coords::VecVarExpr *c, interp::VecVarExpr *d)
{
    std::string cstr = c->toString();
    std::string dstr = d->toString();
    //LOG(DEBUG) << "CoordsToInterp::putVecVarExpr c " << cstr << "\n";
    //LOG(DEBUG) << "CoordsToInterp::putVecVarExpr d " << dstr << "\n";
    coords2interp_VecExpr[c] = d;
    interp2coords_VecExpr[d] = c;

    interp::VecVarExpr *foo = getVecVarExpr(c);
    std::string s = foo->toString();
    //LOG(DEBUG) << "Debug " << s << "\n";
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


void CoordsToInterp::putFloatIdent(coords::FloatIdent *c, interp::FloatIdent *d)
{
    coords2interp_FloatIdent[c] = d;
    interp2coords_FloatIdent[d] = c;
    //    coords2interp_VecIdent.insert(std::make_pair(c, d));
    //    interp2coords_VecIdent.insert(std::make_pair(d, c));
}

interp::FloatIdent *CoordsToInterp::getFloatIdent(coords::FloatIdent *c) const
{
    std::unordered_map<coords::FloatIdent*, interp::FloatIdent*>::iterator it;
    interp::FloatIdent *dom = NULL;
    try {
        dom = coords2interp_FloatIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::FloatIdent *CoordsToInterp::getFloatIdent(interp::FloatIdent *d) const
{
    std::unordered_map<interp::FloatIdent*, coords::FloatIdent*>::iterator it;
    coords::FloatIdent *coords = NULL;
    try {
        coords = interp2coords_FloatIdent.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// Expr

// base

interp::FloatExpr *CoordsToInterp::getFloatExpr(coords::FloatExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *dom = NULL;
    try {
        dom = coords2interp_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

coords::FloatExpr *CoordsToInterp::getFloatExpr(interp::FloatExpr *d) const
{
    std::unordered_map<interp::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = interp2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return coords;
}

// var

void CoordsToInterp::putFloatVarExpr(coords::FloatVarExpr *c, interp::FloatVarExpr *d)
{
    std::string cstr = c->toString();
    std::string dstr = d->toString();
    //LOG(DEBUG) << "CoordsToInterp::putFloatVarExpr c " << cstr << "\n";
    //LOG(DEBUG) << "CoordsToInterp::putFloatVarExpr d " << dstr << "\n";
    coords2interp_FloatExpr[c] = d;
    interp2coords_FloatExpr[d] = c;

    interp::FloatVarExpr *foo = getFloatVarExpr(c);
    std::string s = foo->toString();
    //LOG(DEBUG) << "Debug " << s << "\n";
}

interp::FloatVarExpr *CoordsToInterp::getFloatVarExpr(coords::FloatVarExpr *c) const
{
    std::unordered_map<coords::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *dom = NULL;
    try {
        dom = coords2interp_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::FloatVarExpr*>(dom);
}

coords::FloatVarExpr *CoordsToInterp::getFloatVarExpr(interp::FloatVarExpr *d) const
{
    std::unordered_map<interp::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = interp2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatVarExpr *>(coords);
}

// Floatparenexpr

void CoordsToInterp::putFloatParenExpr(coords::FloatParenExpr *c, interp::FloatParenExpr *i) {
    coords2interp_FloatExpr[c] = i;
    interp2coords_FloatExpr[i] = c;
}

interp::FloatParenExpr *CoordsToInterp::getFloatParenExpr(coords::FloatParenExpr* c) const {
    std::unordered_map<coords::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *dom = NULL;
    try {
        dom = coords2interp_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::FloatParenExpr*>(dom);
}
// TODO: A few template functions should take care of most of this file
coords::FloatParenExpr *CoordsToInterp::getFloatParenExpr(interp::FloatParenExpr* d) const {
    std::unordered_map<interp::FloatExpr*, coords::FloatExpr*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = interp2coords_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FloatParenExpr *>(coords);
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


coords::Float *CoordsToInterp::getFloat(interp::Float* v) {
    std::unordered_map<interp::Float*, coords::Float*>::iterator it;
    coords::Float *coords = NULL;
    try {
        coords = interp2coords_Float.at(v);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float *>(coords);
}

interp::Float *CoordsToInterp::getFloat(coords::Float* v) {
    std::unordered_map<coords::Float*, interp::Float*>::iterator it;
    interp::Float *domvec = NULL;
    try {
        domvec = coords2interp_Float.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<interp::Float *>(domvec);
}


void CoordsToInterp::putFloat_Lit(coords::Float *c, interp::Float_Lit *d)
{
    coords2interp_Float[c] = d;
    interp2coords_Float[d] = c;
}

interp::Float_Lit *CoordsToInterp::getFloat_Lit(coords::Float_Lit *c) const
{
    std::unordered_map<coords::Float_Lit*, interp::Float_Lit*>::iterator it;
    interp::Float *dom = NULL;
    try {
        dom = coords2interp_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Float_Lit*>(dom);
}

coords::Float_Lit *CoordsToInterp::getFloat_Lit(interp::Float_Lit *d) const
{
    std::unordered_map<interp::Float*, coords::Float*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = interp2coords_Float.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float_Lit *>(coords);
}

void CoordsToInterp::putFloat_Expr(coords::Float *c, interp::Float_Expr *d)
{
    coords2interp_Float[c] = d;
    interp2coords_Float[d] = c;
}

interp::Float_Expr *CoordsToInterp::getFloat_Expr(coords::Float_Expr *c) const
{
    std::unordered_map<coords::Float_Expr*, interp::Float_Expr*>::iterator it;
    interp::Float *dom = NULL;
    try {
        dom = coords2interp_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Float_Expr*>(dom);
}

coords::Float_Expr *CoordsToInterp::getFloat_Expr(interp::Float_Expr *d) const
{
    std::unordered_map<interp::Float*, coords::Float*>::iterator it;
    coords::FloatExpr *coords = NULL;
    try {
        coords = interp2coords_Float.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::Float_Expr *>(coords);
}

// Def

void CoordsToInterp::putFloat_Def(coords::Float_Def *c, interp::Float_Def *d)
{
    coords2interp_Float_Def[c] = d;
    interp2coords_Float_Def[d] = c;
}

interp::Float_Def *CoordsToInterp::getFloat_Def(coords::Float_Def *c) const
{
    std::unordered_map<coords::Float_Def*, interp::Float_Def*>::iterator it;
    interp::Float_Def *dom = NULL;
    try {
        dom = coords2interp_Float_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<interp::Float_Def*>(dom);
}

coords::Float_Def *CoordsToInterp::getFloat_Def(interp::Float_Def *d) const
{
    std::unordered_map<interp::Float*, coords::Float*>::iterator it;
    coords::Float_Def *coords = NULL;
    try {
        coords = interp2coords_Float_Def.at(d);
    } catch (std::out_of_range &e) {
      coords = NULL;
    }
    return static_cast<coords::Float_Def *>(coords);
}
