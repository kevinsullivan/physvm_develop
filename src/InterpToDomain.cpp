#include "InterpToDomain.h"

#include <iostream>

//#include <g3log/g3log.hpp>

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

void InterpToDomain::putFloatIdent(interp::FloatIdent *c, domain::FloatIdent *d)
{
    interp2domain_FloatIdent[c] = d;
    domain2interp_FloatIdent[d] = c;
    //    interp2domain_VecIdent.insert(std::make_pair(c, d));
    //    domain2interp_VecIdent.insert(std::make_pair(d, c));
}

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::FloatIdent *InterpToDomain::getFloatIdent(interp::FloatIdent *c) const
{
    std::unordered_map<interp::FloatIdent*, domain::FloatIdent*>::iterator it;
    domain::FloatIdent *dom = NULL;
    try {
        dom = interp2domain_FloatIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::FloatIdent *InterpToDomain::getFloatIdent(domain::FloatIdent *d) const
{
    std::unordered_map<domain::FloatIdent*, interp::FloatIdent*>::iterator it;
    interp::FloatIdent *interp = NULL;
    try {
        interp = domain2interp_FloatIdent.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

// Expr

// base

domain::VecExpr *InterpToDomain::getVecExpr(interp::VecExpr *c) const
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

domain::FloatExpr *InterpToDomain::getFloatExpr(interp::FloatExpr *c) const
{
    std::unordered_map<interp::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = interp2domain_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::FloatExpr *InterpToDomain::getFloatExpr(domain::FloatExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *interp = NULL;
    try {
        interp = domain2interp_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

void InterpToDomain::putVecWrapper(interp::VecWrapper *c, domain::VecWrapper *d)
{
    interp2domain_VecExpr[c] = d;
    domain2interp_VecExpr[d] = c;
//    coord2domain_VecExpr.insert(std::make_pair(*c, d));
}

domain::VecWrapper *InterpToDomain::getVecWrapper(interp::VecWrapper *c) const
{
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecWrapper*>(dom);
}

interp::VecWrapper *InterpToDomain::getVecWrapper(domain::VecWrapper *d) const
{
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VecWrapper *>(interp);
}

void InterpToDomain::putFloatWrapper(interp::FloatWrapper *c, domain::FloatWrapper *d)
{
    interp2domain_FloatExpr[c] = d;
    domain2interp_FloatExpr[d] = c;
//    coord2domain_VecExpr.insert(std::make_pair(*c, d));
}

domain::FloatWrapper *InterpToDomain::getFloatWrapper(interp::FloatWrapper *c) const
{
    std::unordered_map<interp::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = interp2domain_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatWrapper*>(dom);
}

interp::FloatWrapper *InterpToDomain::getFloatWrapper(domain::FloatWrapper *d) const
{
    std::unordered_map<domain::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *interp = NULL;
    try {
        interp = domain2interp_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::FloatWrapper *>(interp);
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

void InterpToDomain::putFloatVarExpr(interp::FloatVarExpr *c, domain::FloatVarExpr *d)
{
    interp2domain_FloatExpr[c] = d;
    domain2interp_FloatExpr[d] = c;
//    coord2domain_VecExpr.insert(std::make_pair(*c, d));
}

domain::FloatVarExpr *InterpToDomain::getFloatVarExpr(interp::FloatVarExpr *c) const
{
    std::unordered_map<interp::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = interp2domain_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatVarExpr*>(dom);
}

interp::FloatVarExpr *InterpToDomain::getFloatVarExpr(domain::FloatVarExpr *d) const
{
    std::unordered_map<domain::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *interp = NULL;
    try {
        interp = domain2interp_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::FloatVarExpr *>(interp);
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

void InterpToDomain::putVecScalarMulExpr(interp::VecScalarMulExpr *c, domain::VecScalarMulExpr *d)
{
    interp2domain_VecExpr[c] = d;
    domain2interp_VecExpr[d] = c;
}

domain::VecScalarMulExpr *InterpToDomain::getVecScalarMulExpr(interp::VecScalarMulExpr *c) const
{
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecScalarMulExpr*>(dom);
}

interp::VecScalarMulExpr *InterpToDomain::getVecScalarMulExpr(domain::VecScalarMulExpr *d) const
{
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VecScalarMulExpr *>(interp);
}



void InterpToDomain::putVecParenExpr(interp::VecParenExpr *c, domain::VecParenExpr *d) {
    interp2domain_VecExpr[c] = d;
    domain2interp_VecExpr[d] = c;

}

domain::VecParenExpr *InterpToDomain::getVecParenExpr(interp::VecParenExpr* c) const {
    std::unordered_map<interp::VecExpr*, domain::VecExpr*>::iterator it;
    domain::VecExpr *dom = NULL;
    try {
        dom = interp2domain_VecExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::VecParenExpr*>(dom);
}

interp::VecParenExpr *InterpToDomain::getVecParenExpr(domain::VecParenExpr* d) const {
    std::unordered_map<domain::VecExpr*, interp::VecExpr*>::iterator it;
    interp::VecExpr *interp = NULL;
    try {
        interp = domain2interp_VecExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VecParenExpr *>(interp);
}


void InterpToDomain::putFloatParenExpr(interp::FloatParenExpr *c, domain::FloatParenExpr *d) {
    interp2domain_FloatExpr[c] = d;
    domain2interp_FloatExpr[d] = c;

}

domain::FloatParenExpr *InterpToDomain::getFloatParenExpr(interp::FloatParenExpr* c) const {
    std::unordered_map<interp::FloatExpr*, domain::FloatExpr*>::iterator it;
    domain::FloatExpr *dom = NULL;
    try {
        dom = interp2domain_FloatExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::FloatParenExpr*>(dom);
}

interp::FloatParenExpr *InterpToDomain::getFloatParenExpr(domain::FloatParenExpr* d) const {
    std::unordered_map<domain::FloatExpr*, interp::FloatExpr*>::iterator it;
    interp::FloatExpr *interp = NULL;
    try {
        interp = domain2interp_FloatExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::FloatParenExpr *>(interp);
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

interp::Float *InterpToDomain::getFloat(domain::Float* v) {
    std::unordered_map<domain::Float*, interp::Float*>::iterator it;
    interp::Float *interp = NULL;
    try {
        interp = domain2interp_Float.at(v);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Float *>(interp);
}

domain::Float *InterpToDomain::getFloat(interp::Float* v) {
    std::unordered_map<interp::Float*, domain::Float*>::iterator it;
    domain::Float *domflt = NULL;
    try {
        domflt = interp2domain_Float.at(v);
    }
    catch (std::out_of_range &e) {
        domflt = NULL;
    }
    return static_cast<domain::Float *>(domflt);
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

void InterpToDomain::putFloat_Lit(interp::Float *c, domain::Float_Lit *d)
{
    interp2domain_Float[c] = d;
    domain2interp_Float[d] = c;
}

domain::Float_Lit *InterpToDomain::getFloat_Lit(interp::Float_Lit *c) const
{
    std::unordered_map<interp::Float_Lit*, domain::Float_Lit*>::iterator it;
    domain::Float *dom = NULL;
    try {
        dom = interp2domain_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Lit*>(dom);
}

interp::Float_Lit *InterpToDomain::getFloat_Lit(domain::Float_Lit *d) const
{
    std::unordered_map<domain::Float*, interp::Float*>::iterator it;
    interp::Float *interp = NULL;
    try {
        interp = domain2interp_Float.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Float_Lit *>(interp);
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

void InterpToDomain::putFloat_Expr(interp::Float *c, domain::Float_Expr *d)
{
    interp2domain_Float[c] = d;
    domain2interp_Float[d] = c;
}

domain::Float_Expr *InterpToDomain::getFloat_Expr(interp::Float_Expr *c) const
{
    std::unordered_map<interp::Float_Expr*, domain::Float_Expr*>::iterator it;
    domain::Float *dom = NULL;
    try {
        dom = interp2domain_Float.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Expr*>(dom);
}

interp::Float_Expr *InterpToDomain::getFloat_Expr(domain::Float_Expr *d) const
{
    std::unordered_map<domain::Float*, interp::Float*>::iterator it;
    interp::Float *interp = NULL;
    try {
        interp = domain2interp_Float.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Float_Expr *>(interp);
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


void InterpToDomain::putFloat_Def(interp::Float_Def *c, domain::Float_Def *d)
{
    interp2domain_Float_Def[c] = d;
    domain2interp_Float_Def[d] = c;
}

domain::Float_Def *InterpToDomain::getFloat_Def(interp::Float_Def *c) const
{
    std::unordered_map<interp::Float_Def*, domain::Float_Def*>::iterator it;
    domain::Float_Def *dom = NULL;
    try {
        dom = interp2domain_Float_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Float_Def*>(dom);
}

interp::Float_Def *InterpToDomain::getFloat_Def(domain::Float_Def *d) const
{
    std::unordered_map<domain::Float*, interp::Float*>::iterator it;
    interp::Float_Def *interp = NULL;
    try {
        interp = domain2interp_Float_Def.at(d);
    } catch (std::out_of_range &e) {
      interp = NULL;
    }
    return static_cast<interp::Float_Def *>(interp);
}