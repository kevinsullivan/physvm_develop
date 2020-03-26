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

	void putFloatIdent(coords::FloatIdent *key, domain::FloatIdent *i);
	domain::FloatIdent *getFloatIdent(coords::FloatIdent *c) const;
	coords::FloatIdent *getFloatIdent(domain::FloatIdent *d) const;
// Expr

	domain::FloatExpr *getFloatExpr(coords::FloatExpr* c) const;
	coords::FloatExpr *getFloatExpr(domain::FloatExpr* d) const;

	domain::VecExpr *getVecExpr(coords::VecExpr* c) const;
	coords::VecExpr *getVecExpr(domain::VecExpr* d) const;

/*	void putVecLitExpr(coords::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(coords::VecLitExpr c) const;
	coords::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/
/*
	void putVecWrapper(coords::VecWrapper *n, domain::VecWrapper *e);
	domain::VecWrapper *getVecWrapper(coords::VecWrapper *c) const;
	coords::VecWrapper *getVecWrapper(domain::VecWrapper *d) const;

	void putFloatWrapper(coords::FloatWrapper *n, domain::FloatWrapper *e);
	domain::FloatWrapper *getFloatWrapper(coords::FloatWrapper *c) const;
	coords::FloatWrapper *getFloatWrapper(domain::FloatWrapper *d) const;
*/
	void PutVecVarExpr(coords::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(coords::VecVarExpr* c) const;
	coords::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void PutFloatVarExpr(coords::FloatVarExpr *n, domain::FloatVarExpr *e);
	domain::FloatVarExpr *getFloatVarExpr(coords::FloatVarExpr* c) const;
	coords::FloatVarExpr *getFloatVarExpr(domain::FloatVarExpr* d) const;

	void PutVecVecAddExpr(coords::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(coords::VecVecAddExpr* c) const;
	coords::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

	void PutVecScalarMulExpr(coords::VecScalarMulExpr *n, domain::VecScalarMulExpr *e);
	domain::VecScalarMulExpr *getVecScalarMulExpr(coords::VecScalarMulExpr* c) const;
	coords::VecScalarMulExpr *getVecScalarMulExpr(domain::VecScalarMulExpr* d) const;

	void PutFloatFloatAddExpr(coords::FloatFloatAddExpr *n, domain::FloatFloatAddExpr *e);
	domain::FloatFloatAddExpr *getFloatFloatAddExpr(coords::FloatFloatAddExpr* c) const;
	coords::FloatFloatAddExpr *getFloatFloatAddExpr(domain::FloatFloatAddExpr* d) const;

	void PutFloatFloatMulExpr(coords::FloatFloatMulExpr *n, domain::FloatFloatMulExpr *e);
	domain::FloatFloatMulExpr *getFloatFloatMulExpr(coords::FloatFloatMulExpr* c) const;
	coords::FloatFloatMulExpr *getFloatFloatMulExpr(domain::FloatFloatMulExpr* d) const;

	// KEVIN: Added for horizontal VecParenExpr module.
	//
	void PutVecParenExpr(coords::VecParenExpr *n, domain::VecParenExpr *e);
	domain::VecParenExpr *getParenExpr(coords::VecParenExpr* c) const;
	coords::VecParenExpr *getParenExpr(domain::VecParenExpr* d) const;

	void PutFloatParenExpr(coords::FloatParenExpr *n, domain::FloatParenExpr *e);
	domain::FloatParenExpr *getParenExpr(coords::FloatParenExpr* c) const;
	coords::FloatParenExpr *getParenExpr(domain::FloatParenExpr* d) const;

// Vector

	void putVector_Lit(coords::Vector *ast, domain::Vector_Lit *v);
	domain::Vector_Lit *getVector_Lit(coords::Vector_Lit* c) const;
	coords::Vector_Lit *getVector_Lit(domain::Vector_Lit* d) const;

	void putFloat_Lit(coords::Float *ast, domain::Float_Lit *v);
	domain::Float_Lit *getFloat_Lit(coords::Float_Lit* c) const;
	coords::Float_Lit *getFloat_Lit(domain::Float_Lit* d) const;

	void putVector_Expr(coords::Vector *ast, domain::Vector_Expr *v);
	domain::Vector_Expr *getVector_Expr(coords::Vector_Expr* c) const;
	coords::Vector_Expr *getVector_Expr(domain::Vector_Expr* d) const;

	void putFloat_Expr(coords::Float *ast, domain::Float_Expr *v);
	domain::Float_Expr *getFloat_Expr(coords::Float_Expr* c) const;
	coords::Float_Expr *getFloat_Expr(domain::Float_Expr* d) const;

	coords::Vector *getVector(domain::Vector* v);
	domain::Vector *getVector(coords::Vector* v);

	coords::Float *getFloat(domain::Float* v);
	domain::Float *getFloat(coords::Float* v);

// Def

	void putVector_Def(coords::Vector_Def *vardecl_wrapper, domain::Vector_Def *b);
	domain::Vector_Def *getVector_Def(coords::Vector_Def* c) const;
	coords::Vector_Def *getVector_Def(domain::Vector_Def* d) const;

	void putFloat_Def(coords::Float_Def *vardecl_wrapper, domain::Float_Def *b);
	domain::Float_Def *getFloat_Def(coords::Float_Def* c) const;
	coords::Float_Def *getFloat_Def(domain::Float_Def* d) const;

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

	std::unordered_map <coords::FloatIdent*,domain::FloatIdent* > 	coords2dom_FloatIdent;
	std::unordered_map <coords::FloatExpr*, domain::FloatExpr*	> 	coords2dom_FloatExpr;
	std::unordered_map <coords::Float*, 	domain::Float*		> 	coords2dom_Float;
	std::unordered_map <coords::Float_Def*, domain::Float_Def*	> 	coords2dom_Float_Def;

	std::unordered_map<domain::VecIdent*, 	coords::VecIdent*	> 	dom2coords_VecIdent;
	std::unordered_map<domain::VecExpr*, 	coords::VecExpr*	> 	dom2coords_VecExpr;
	std::unordered_map<domain::Vector*, 	coords::Vector*		> 	dom2coords_Vector;
	std::unordered_map<domain::Vector_Def*, coords::Vector_Def*	> 	dom2coords_Vector_Def;

	std::unordered_map<domain::FloatIdent*, coords::FloatIdent*	> 	dom2coords_FloatIdent;
	std::unordered_map<domain::FloatExpr*, 	coords::FloatExpr*	> 	dom2coords_FloatExpr;
	std::unordered_map<domain::Float*, 		coords::Float*		> 		dom2coords_Float;
	std::unordered_map<domain::Float_Def*, 	coords::Float_Def*	> 	dom2coords_Float_Def;
};

} // namespace

#endif