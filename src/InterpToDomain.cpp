#include "InterpToDomain.h"

#include <iostream>

#include <g3log/g3log.hpp>

using namespace interp2domain;

// Ident

void InterpToDomain::putVecIdent(interp::VecIdent *c, domain::VecIdent *d)
{
    interp2domain_VecIdent[c] = d;
    domain2interp_VecIdent[d] = c;
    //    interp2domain_VecIdent.insert(std::make_pair(c, d));
    //    domain2interp_VecIdent.insert(std::make_pair(d, c));
}

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::VecIdent *InterpToDomain::getVecIdent(interp::VecIdent *c) const
{
    std::unordered_map<interp::VecIdent*, domain::VecIdent*>::iterator it;
    domain::VecIdent *dom = NULL;
    try {
        dom = interp2domain_VecIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::VecIdent *InterpToDomain::getVecIdent(domain::VecIdent *d) const
{
    std::unordered_map<domain::VecIdent*, interp::VecIdent*>::iterator it;
    interp::VecIdent *interp = NULL;
    try {
        interp = domain2interp_VecIdent.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

// Expr

// base

domain::VecExpr *InterpToDomain::getVecExpr(interp::VecExpr *c)
{
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::VecExpr *InterpToDomain::getVecExpr(domain::VecExpr *d) const
{
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

// var

void InterpToDomain::putVecVarExpr(interp::VecVarExpr *c, domain::VecVarExpr *d)
{
    interp2domain_VecExpr[c] = d;
    domain2interp_VecExpr[d] = c;
//    coord2domain_VecExpr.insert(std::make_pair(*c, d));
}

domain::VecVarExpr *InterpToDomain::getVecVarExpr(interp::VecVarExpr *c) const
{
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecVarExpr*>(dom);
}

interp::VecVarExpr *InterpToDomain::getVecVarExpr(domain::VecVarExpr *d) const
{
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VecVarExpr *>(interp);
}

// vecvecadd

void InterpToDomain::putVecVecAddExpr(interp::VecVecAddExpr *c, domain::VecVecAddExpr *d)
{
    interp2domain_VecExpr[c] = d;
    domain2interp_VecExpr[d] = c;
}

domain::VecVecAddExpr *InterpToDomain::getVecVecAddExpr(interp::VecVecAddExpr *c) const
{
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecVecAddExpr*>(dom);
}

interp::VecVecAddExpr *InterpToDomain::getVecVecAddExpr(domain::VecVecAddExpr *d) const
{
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VecVecAddExpr *>(interp);
}

// Vector

interp::Vector *InterpToDomain::getVector(domain::Vector* v) {
    std::unordered_map<domain::Vector*, interp::Vector*>::iterator it;
    interp::Vector *interp = NULL;
    try {
        interp = domain2interp_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Vector *>(interp);
}

domain::Vector *InterpToDomain::getVector(interp::Vector* v) {
    std::unordered_map<interp::Vector*, domain::Vector*>::iterator it;
    domain::Vector *domvec = NULL;
    try {
        domvec = interp2domain_Vector.at(v);
    }
    catch (std::out_of_range &e) {
        domvec = NULL;
    }
    return static_cast<domain::Vector *>(domvec);
}


void InterpToDomain::putVector_Lit(interp::Vector *c, domain::Vector_Lit *d)
{
    interp2domain_Vector[c] = d;
    domain2interp_Vector[d] = c;
}

domain::Vector_Lit *InterpToDomain::getVector_Lit(interp::Vector_Lit *c) const
{
    std::unordered_map<interp::Vector_Lit*, domain::Vector_Lit*>::iterator it;
    domain::Vector *dom = NULL;
    try {
        dom = interp2domain_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Lit*>(dom);
}

interp::Vector_Lit *InterpToDomain::getVector_Lit(domain::Vector_Lit *d) const
{
    std::unordered_map<domain::Vector*, interp::Vector*>::iterator it;
    interp::Vector *interp = NULL;
    try {
        interp = domain2interp_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Vector_Lit *>(interp);
}

void InterpToDomain::putVector_Expr(interp::Vector *c, domain::Vector_Expr *d)
{
    interp2domain_Vector[c] = d;
    domain2interp_Vector[d] = c;
}

domain::Vector_Expr *InterpToDomain::getVector_Expr(interp::Vector_Expr *c) const
{
    std::unordered_map<interp::Vector_Expr*, domain::Vector_Expr*>::iterator it;
    domain::Vector *dom = NULL;
    try {
        dom = interp2domain_Vector.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Expr*>(dom);
}

interp::Vector_Expr *InterpToDomain::getVector_Expr(domain::Vector_Expr *d) const
{
    std::unordered_map<domain::Vector*, interp::Vector*>::iterator it;
    interp::Vector *interp = NULL;
    try {
        interp = domain2interp_Vector.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Vector_Expr *>(interp);
}

// Def

void InterpToDomain::putVector_Def(interp::Vector_Def *c, domain::Vector_Def *d)
{
    interp2domain_Vector_Def[c] = d;
    domain2interp_Vector_Def[d] = c;
}

domain::Vector_Def *InterpToDomain::getVector_Def(interp::Vector_Def *c) const
{
    std::unordered_map<interp::Vector_Def*, domain::Vector_Def*>::iterator it;
    domain::Vector_Def *dom = NULL;
    try {
        dom = interp2domain_Vector_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Def*>(dom);
}

interp::Vector_Def *InterpToDomain::getVector_Def(domain::Vector_Def *d) const
{
    std::unordered_map<domain::Vector*, interp::Vector*>::iterator it;
    interp::Vector_Def *interp = NULL;
    try {
        interp = domain2interp_Vector_Def.at(d);
    } catch (std::out_of_range &e) {
      interp = NULL;
    }
    return static_cast<interp::Vector_Def *>(interp);
}