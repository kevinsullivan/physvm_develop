#include "CoordsToInterp.h"

#include <iostream>

#include <g3log/g3log.hpp>


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

void CoordsToInterp::pVecVarExpr(coords::VecVarExpr *c, interp::VecVarExpr *d)
{
    coords2interp_VecExpr[c] = d;
    interp2coords_VecExpr[d] = c;
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

