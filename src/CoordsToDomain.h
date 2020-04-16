#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

/*
	When putting, we know precise subclass, so we don't include
	putters for Expr and Vector super-classes. When getting, we 
	generally don't know, so we can return superclass pointers.
*/

/*
We currently require client to create domain nodes, which we 
then map to and from the given coordinates. From coordinates 
is currently implement as unordered map. From domain object is
currently implemented as domain object method. This enables us
to return precisely typed objects without having to maintain a
lot of separate mapping tables.
*/

namespace coords2domain {

class CoordsToDomain
{
  public:

// Ident

	void putVecIdent(coords::VecIdent *key, domain::VecIdent *i);
	domain::VecIdent *getVecIdent(coords::VecIdent *c) const;
	coords::VecIdent *getVecIdent(domain::VecIdent *d) const;

	void putScalarIdent(coords::ScalarIdent *key, domain::ScalarIdent *i);
	domain::ScalarIdent *getScalarIdent(coords::ScalarIdent *c) const;
	coords::ScalarIdent *getScalarIdent(domain::ScalarIdent *d) const;
// Expr

	domain::ScalarExpr *getScalarExpr(coords::ScalarExpr* c) const;
	coords::ScalarExpr *getScalarExpr(domain::ScalarExpr* d) const;

	domain::VecExpr *getVecExpr(coords::VecExpr* c) const;
	coords::VecExpr *getVecExpr(domain::VecExpr* d) const;

/*	void putVecLitExpr(coords::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(coords::VecLitExpr c) const;
	coords::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/

	void PutVecVarExpr(coords::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(coords::VecVarExpr* c) const;
	coords::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void PutScalarVarExpr(coords::ScalarVarExpr *n, domain::ScalarVarExpr *e);
	domain::ScalarVarExpr *getScalarVarExpr(coords::ScalarVarExpr* c) const;
	coords::ScalarVarExpr *getScalarVarExpr(domain::ScalarVarExpr* d) const;

	void PutVecVecAddExpr(coords::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(coords::VecVecAddExpr* c) const;
	coords::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

	void PutVecScalarMulExpr(coords::VecScalarMulExpr *n, domain::VecScalarMulExpr *e);
	domain::VecScalarMulExpr *getVecScalarMulExpr(coords::VecScalarMulExpr* c) const;
	coords::VecScalarMulExpr *getVecScalarMulExpr(domain::VecScalarMulExpr* d) const;

	void PutScalarScalarAddExpr(coords::ScalarScalarAddExpr *n, domain::ScalarScalarAddExpr *e);
	domain::ScalarScalarAddExpr *getScalarScalarAddExpr(coords::ScalarScalarAddExpr* c) const;
	coords::ScalarScalarAddExpr *getScalarScalarAddExpr(domain::ScalarScalarAddExpr* d) const;

	void PutScalarScalarMulExpr(coords::ScalarScalarMulExpr *n, domain::ScalarScalarMulExpr *e);
	domain::ScalarScalarMulExpr *getScalarScalarMulExpr(coords::ScalarScalarMulExpr* c) const;
	coords::ScalarScalarMulExpr *getScalarScalarMulExpr(domain::ScalarScalarMulExpr* d) const;

	// KEVIN: Added for horizontal VecParenExpr module.
	//
	void PutVecParenExpr(coords::VecParenExpr *n, domain::VecParenExpr *e);
	domain::VecParenExpr *getParenExpr(coords::VecParenExpr* c) const;
	coords::VecParenExpr *getParenExpr(domain::VecParenExpr* d) const;

	void PutScalarParenExpr(coords::ScalarParenExpr *n, domain::ScalarParenExpr *e);
	domain::ScalarParenExpr *getParenExpr(coords::ScalarParenExpr* c) const;
	coords::ScalarParenExpr *getParenExpr(domain::ScalarParenExpr* d) const;

// Vector

	void putVector_Lit(coords::Vector *ast, domain::Vector_Lit *v);
	domain::Vector_Lit *getVector_Lit(coords::Vector_Lit* c) const;
	coords::Vector_Lit *getVector_Lit(domain::Vector_Lit* d) const;

	void putScalar_Lit(coords::Scalar *ast, domain::Scalar_Lit *v);
	domain::Scalar_Lit *getScalar_Lit(coords::Scalar_Lit* c) const;
	coords::Scalar_Lit *getScalar_Lit(domain::Scalar_Lit* d) const;

	void putVector_Expr(coords::Vector *ast, domain::Vector_Expr *v);
	domain::Vector_Expr *getVector_Expr(coords::Vector_Expr* c) const;
	coords::Vector_Expr *getVector_Expr(domain::Vector_Expr* d) const;

	void putScalar_Expr(coords::Scalar *ast, domain::Scalar_Expr *v);
	domain::Scalar_Expr *getScalar_Expr(coords::Scalar_Expr* c) const;
	coords::Scalar_Expr *getScalar_Expr(domain::Scalar_Expr* d) const;

	coords::Vector *getVector(domain::Vector* v);
	domain::Vector *getVector(coords::Vector* v);

	coords::Scalar *getScalar(domain::Scalar* v);
	domain::Scalar *getScalar(coords::Scalar* v);

// Def

	void putVector_Def(coords::Vector_Def *vardecl_wrapper, domain::Vector_Def *b);
	domain::Vector_Def *getVector_Def(coords::Vector_Def* c) const;
	coords::Vector_Def *getVector_Def(domain::Vector_Def* d) const;

	void putScalar_Def(coords::Scalar_Def *vardecl_wrapper, domain::Scalar_Def *b);
	domain::Scalar_Def *getScalar_Def(coords::Scalar_Def* c) const;
	coords::Scalar_Def *getScalar_Def(domain::Scalar_Def* d) const;

	void putVector_Assign(coords::Vector_Assign *vardecl_wrapper, domain::Vector_Assign *b);
	domain::Vector_Assign *getVector_Assign(coords::Vector_Assign* c) const;
	coords::Vector_Assign *getVector_Assign(domain::Vector_Assign* d) const;

	void putScalar_Assign(coords::Scalar_Assign *vardecl_wrapper, domain::Scalar_Assign *b);
	domain::Scalar_Assign *getScalar_Assign(coords::Scalar_Assign* c) const;
	coords::Scalar_Assign *getScalar_Assign(domain::Scalar_Assign* d) const;

	
	void dump() const;

  private:
	/* 
	We implement an interpretation as a collection of typed maps. 
	The keys are "Code Coordinate" objects, which, in turn, are 
	currently just containers for pointers to AST nodes, basically
	just adding operator==() and hash functions.

	TODO: Compare with ast2coords. There it's clear that every
	AST node maps to a coords::Coords. But here we distinguish
	between different kinds of coords. Re-evaluate.
	*/
 
	// TODO: delete "interp" prefixes here -- minor
	
	std::unordered_map <coords::VecIdent*,	domain::VecIdent*	> 	coords2dom_VecIdent;
	std::unordered_map <coords::VecExpr*, 	domain::VecExpr*	> 	coords2dom_VecExpr;
	std::unordered_map <coords::Vector*, 	domain::Vector*		> 	coords2dom_Vector;
	std::unordered_map <coords::Vector_Def*,domain::Vector_Def*	> 	coords2dom_Vector_Def;
	std::unordered_map <coords::Vector_Assign*,domain::Vector_Assign*> 	coords2dom_Vector_Assign;

	std::unordered_map <coords::ScalarIdent*,domain::ScalarIdent* > 	coords2dom_ScalarIdent;
	std::unordered_map <coords::ScalarExpr*, domain::ScalarExpr*	> 	coords2dom_ScalarExpr;
	std::unordered_map <coords::Scalar*, 	domain::Scalar*		> 	coords2dom_Scalar;
	std::unordered_map <coords::Scalar_Def*, domain::Scalar_Def*	> 	coords2dom_Scalar_Def;
	std::unordered_map <coords::Scalar_Assign*, domain::Scalar_Assign*> 	coords2dom_Scalar_Assign;

	std::unordered_map<domain::VecIdent*, 	coords::VecIdent*	> 	dom2coords_VecIdent;
	std::unordered_map<domain::VecExpr*, 	coords::VecExpr*	> 	dom2coords_VecExpr;
	std::unordered_map<domain::Vector*, 	coords::Vector*		> 	dom2coords_Vector;
	std::unordered_map<domain::Vector_Def*, coords::Vector_Def*	> 	dom2coords_Vector_Def;
	std::unordered_map<domain::Vector_Assign*, coords::Vector_Assign*> 	dom2coords_Vector_Assign;

	std::unordered_map<domain::ScalarIdent*, coords::ScalarIdent*	> 	dom2coords_ScalarIdent;
	std::unordered_map<domain::ScalarExpr*, 	coords::ScalarExpr*	> 	dom2coords_ScalarExpr;
	std::unordered_map<domain::Scalar*, 		coords::Scalar*		> 		dom2coords_Scalar;
	std::unordered_map<domain::Scalar_Def*, 	coords::Scalar_Def*	> 	dom2coords_Scalar_Def;
	std::unordered_map<domain::Scalar_Assign*, 	coords::Scalar_Assign*> 	dom2coords_Scalar_Assign;
};

} // namespace

#endif