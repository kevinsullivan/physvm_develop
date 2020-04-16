#include "InterpToDomain.h"

#include <iostream>

#include <g3log/g3log.hpp>

using namespace interp2domain;

// Ident

void InterpToDomain::putVecIdent(interp::VecIdent *c, domain::VecIdent *d)
{
    interp2domain_VecIdent[c] = d;
    domain2interp_VecIdent[d] = c;
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

void InterpToDomain::putScalarIdent(interp::ScalarIdent *c, domain::ScalarIdent *d)
{
    interp2domain_ScalarIdent[c] = d;
    domain2interp_ScalarIdent[d] = c;
}

// TODO: Decide whether or not these maps can be partial on queried keys
// As defined here, yes, and asking for a missing key returns NULL
//
domain::ScalarIdent *InterpToDomain::getScalarIdent(interp::ScalarIdent *c) const
{
    std::unordered_map<interp::ScalarIdent*, domain::ScalarIdent*>::iterator it;
    domain::ScalarIdent *dom = NULL;
    try {
        dom = interp2domain_ScalarIdent.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::ScalarIdent *InterpToDomain::getScalarIdent(domain::ScalarIdent *d) const
{
    std::unordered_map<domain::ScalarIdent*, interp::ScalarIdent*>::iterator it;
    interp::ScalarIdent *interp = NULL;
    try {
        interp = domain2interp_ScalarIdent.at(d);
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

domain::ScalarExpr *InterpToDomain::getScalarExpr(interp::ScalarExpr *c) const
{
    std::unordered_map<interp::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = interp2domain_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}

interp::ScalarExpr *InterpToDomain::getScalarExpr(domain::ScalarExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *interp = NULL;
    try {
        interp = domain2interp_ScalarExpr.at(d);
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

void InterpToDomain::putScalarVarExpr(interp::ScalarVarExpr *c, domain::ScalarVarExpr *d)
{
    interp2domain_ScalarExpr[c] = d;
    domain2interp_ScalarExpr[d] = c;
}

domain::ScalarVarExpr *InterpToDomain::getScalarVarExpr(interp::ScalarVarExpr *c) const
{
    std::unordered_map<interp::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = interp2domain_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarVarExpr*>(dom);
}

interp::ScalarVarExpr *InterpToDomain::getScalarVarExpr(domain::ScalarVarExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *interp = NULL;
    try {
        interp = domain2interp_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ScalarVarExpr *>(interp);
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


void InterpToDomain::putScalarScalarAddExpr(interp::ScalarScalarAddExpr *c, domain::ScalarScalarAddExpr *d)
{
    interp2domain_ScalarExpr[c] = d;
    domain2interp_ScalarExpr[d] = c;
}

domain::ScalarScalarAddExpr *InterpToDomain::getScalarScalarAddExpr(interp::ScalarScalarAddExpr *c) const
{
    std::unordered_map<interp::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = interp2domain_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarScalarAddExpr*>(dom);
}

interp::ScalarScalarAddExpr *InterpToDomain::getScalarScalarAddExpr(domain::ScalarScalarAddExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *interp = NULL;
    try {
        interp = domain2interp_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ScalarScalarAddExpr *>(interp);
}


void InterpToDomain::putScalarScalarMulExpr(interp::ScalarScalarMulExpr *c, domain::ScalarScalarMulExpr *d)
{
    interp2domain_ScalarExpr[c] = d;
    domain2interp_ScalarExpr[d] = c;
}

domain::ScalarScalarMulExpr *InterpToDomain::getScalarScalarMulExpr(interp::ScalarScalarMulExpr *c) const
{
    std::unordered_map<interp::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = interp2domain_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarScalarMulExpr*>(dom);
}

interp::ScalarScalarMulExpr *InterpToDomain::getScalarScalarMulExpr(domain::ScalarScalarMulExpr *d) const
{
    std::unordered_map<domain::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *interp = NULL;
    try {
        interp = domain2interp_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ScalarScalarMulExpr *>(interp);
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


void InterpToDomain::putScalarParenExpr(interp::ScalarParenExpr *c, domain::ScalarParenExpr *d) {
    interp2domain_ScalarExpr[c] = d;
    domain2interp_ScalarExpr[d] = c;

}

domain::ScalarParenExpr *InterpToDomain::getScalarParenExpr(interp::ScalarParenExpr* c) const {
    std::unordered_map<interp::ScalarExpr*, domain::ScalarExpr*>::iterator it;
    domain::ScalarExpr *dom = NULL;
    try {
        dom = interp2domain_ScalarExpr.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::ScalarParenExpr*>(dom);
}

interp::ScalarParenExpr *InterpToDomain::getScalarParenExpr(domain::ScalarParenExpr* d) const {
    std::unordered_map<domain::ScalarExpr*, interp::ScalarExpr*>::iterator it;
    interp::ScalarExpr *interp = NULL;
    try {
        interp = domain2interp_ScalarExpr.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ScalarParenExpr *>(interp);
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

interp::Scalar *InterpToDomain::getScalar(domain::Scalar* v) {
    std::unordered_map<domain::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar *interp = NULL;
    try {
        interp = domain2interp_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Scalar *>(interp);
}

domain::Scalar *InterpToDomain::getScalar(interp::Scalar* v) {
    std::unordered_map<interp::Scalar*, domain::Scalar*>::iterator it;
    domain::Scalar *domflt = NULL;
    try {
        domflt = interp2domain_Scalar.at(v);
    }
    catch (std::out_of_range &e) {
        domflt = NULL;
    }
    return static_cast<domain::Scalar *>(domflt);
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

void InterpToDomain::putScalar_Lit(interp::Scalar *c, domain::Scalar_Lit *d)
{
    interp2domain_Scalar[c] = d;
    domain2interp_Scalar[d] = c;
}

domain::Scalar_Lit *InterpToDomain::getScalar_Lit(interp::Scalar_Lit *c) const
{
    std::unordered_map<interp::Scalar_Lit*, domain::Scalar_Lit*>::iterator it;
    domain::Scalar *dom = NULL;
    try {
        dom = interp2domain_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Lit*>(dom);
}

interp::Scalar_Lit *InterpToDomain::getScalar_Lit(domain::Scalar_Lit *d) const
{
    std::unordered_map<domain::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar *interp = NULL;
    try {
        interp = domain2interp_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Scalar_Lit *>(interp);
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

void InterpToDomain::putScalar_Expr(interp::Scalar *c, domain::Scalar_Expr *d)
{
    interp2domain_Scalar[c] = d;
    domain2interp_Scalar[d] = c;
}

domain::Scalar_Expr *InterpToDomain::getScalar_Expr(interp::Scalar_Expr *c) const
{
    std::unordered_map<interp::Scalar_Expr*, domain::Scalar_Expr*>::iterator it;
    domain::Scalar *dom = NULL;
    try {
        dom = interp2domain_Scalar.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Expr*>(dom);
}

interp::Scalar_Expr *InterpToDomain::getScalar_Expr(domain::Scalar_Expr *d) const
{
    std::unordered_map<domain::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar *interp = NULL;
    try {
        interp = domain2interp_Scalar.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::Scalar_Expr *>(interp);
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


void InterpToDomain::putScalar_Def(interp::Scalar_Def *c, domain::Scalar_Def *d)
{
    interp2domain_Scalar_Def[c] = d;
    domain2interp_Scalar_Def[d] = c;
}

domain::Scalar_Def *InterpToDomain::getScalar_Def(interp::Scalar_Def *c) const
{
    std::unordered_map<interp::Scalar_Def*, domain::Scalar_Def*>::iterator it;
    domain::Scalar_Def *dom = NULL;
    try {
        dom = interp2domain_Scalar_Def.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Def*>(dom);
}

interp::Scalar_Def *InterpToDomain::getScalar_Def(domain::Scalar_Def *d) const
{
    std::unordered_map<domain::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar_Def *interp = NULL;
    try {
        interp = domain2interp_Scalar_Def.at(d);
    } catch (std::out_of_range &e) {
      interp = NULL;
    }
    return static_cast<interp::Scalar_Def *>(interp);
}


void InterpToDomain::putVector_Assign(interp::Vector_Assign *c, domain::Vector_Assign *d)
{
    interp2domain_Vector_Assign[c] = d;
    domain2interp_Vector_Assign[d] = c;
}

domain::Vector_Assign *InterpToDomain::getVector_Assign(interp::Vector_Assign *c) const
{
    std::unordered_map<interp::Vector_Assign*, domain::Vector_Assign*>::iterator it;
    domain::Vector_Assign *dom = NULL;
    try {
        dom = interp2domain_Vector_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Vector_Assign*>(dom);
}

interp::Vector_Assign *InterpToDomain::getVector_Assign(domain::Vector_Assign *d) const
{
    std::unordered_map<domain::Vector*, interp::Vector*>::iterator it;
    interp::Vector_Assign *interp = NULL;
    try {
        interp = domain2interp_Vector_Assign.at(d);
    } catch (std::out_of_range &e) {
      interp = NULL;
    }
    return static_cast<interp::Vector_Assign *>(interp);
}


void InterpToDomain::putScalar_Assign(interp::Scalar_Assign *c, domain::Scalar_Assign *d)
{
    interp2domain_Scalar_Assign[c] = d;
    domain2interp_Scalar_Assign[d] = c;
}

domain::Scalar_Assign *InterpToDomain::getScalar_Assign(interp::Scalar_Assign *c) const
{
    std::unordered_map<interp::Scalar_Assign*, domain::Scalar_Assign*>::iterator it;
    domain::Scalar_Assign *dom = NULL;
    try {
        dom = interp2domain_Scalar_Assign.at(c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::Scalar_Assign*>(dom);
}

interp::Scalar_Assign *InterpToDomain::getScalar_Assign(domain::Scalar_Assign *d) const
{
    std::unordered_map<domain::Scalar*, interp::Scalar*>::iterator it;
    interp::Scalar_Assign *interp = NULL;
    try {
        interp = domain2interp_Scalar_Assign.at(d);
    } catch (std::out_of_range &e) {
      interp = NULL;
    }
    return static_cast<interp::Scalar_Assign *>(interp);
}