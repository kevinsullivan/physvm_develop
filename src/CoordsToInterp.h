#ifndef COORDSTOINTERP_H
#define COORDSTOINTERP_H

#include <iostream>
#include "Coords.h"
#include "Interp.h"

#include <unordered_map>

namespace coords2interp {

class CoordsToInterp
{
  public:

// Ident

	void putVecIdent(coords::VecIdent *key, interp::VecIdent *i);
	interp::VecIdent *getVecIdent(coords::VecIdent *c) const;
	coords::VecIdent *getVecIdent(interp::VecIdent *d) const;

// Expr

	interp::VecExpr *getVecExpr(coords::VecExpr* c);
	coords::VecExpr *getVecExpr(interp::VecExpr* d) const;

	void putVecVarExpr(coords::VecVarExpr *n, interp::VecVarExpr *e);
	interp::VecVarExpr *getVecVarExpr(coords::VecVarExpr* c) const;
	coords::VecVarExpr *getVecVarExpr(interp::VecVarExpr* d) const;

	void putVecVecAddExpr(coords::VecVecAddExpr *n, interp::VecVecAddExpr *e);
	interp::VecVecAddExpr *getVecVecAddExpr(coords::VecVecAddExpr* c) const;
	coords::VecVecAddExpr *getVecVecAddExpr(interp::VecVecAddExpr* d) const;

	// KEVIN: This stuff here for VecParenExpr module
	void putVecParenExpr(coords::VecParenExpr *ast, interp::VecParenExpr *expr);
	interp::VecParenExpr *getVecParenExpr(coords::VecParenExpr* c) const;
	coords::VecParenExpr *getVecParenExpr(interp::VecParenExpr* d) const;

// Vector

	void putVector_Lit(coords::Vector *ast, interp::Vector_Lit *v);
	interp::Vector_Lit *getVector_Lit(coords::Vector_Lit* c) const;
	coords::Vector_Lit *getVector_Lit(interp::Vector_Lit* d) const;

	void putVector_Expr(coords::Vector *ast, interp::Vector_Expr *v);
	interp::Vector_Expr *getVector_Expr(coords::Vector_Expr* c) const;
	coords::Vector_Expr *getVector_Expr(interp::Vector_Expr* d) const;

	coords::Vector *getVector(interp::Vector* v);
	interp::Vector *getVector(coords::Vector* v);

// Def

	void putVector_Def(coords::Vector_Def *vardecl_wrapper, interp::Vector_Def *b);
	interp::Vector_Def *getVector_Def(coords::Vector_Def* c) const;
	coords::Vector_Def *getVector_Def(interp::Vector_Def* d) const;

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
 
	std::unordered_map <coords::VecIdent*,	interp::VecIdent*	> 	coords2interp_VecIdent;
	std::unordered_map <coords::VecExpr*, 	interp::VecExpr*	> 	coords2interp_VecExpr;
	std::unordered_map <coords::Vector*, 	interp::Vector*		> 	coords2interp_Vector;
	std::unordered_map <coords::Vector_Def*,interp::Vector_Def*	> 	coords2interp_Vector_Def;

	std::unordered_map<interp::VecIdent*, 	coords::VecIdent*	> 	interp2coords_VecIdent;
	std::unordered_map<interp::VecExpr*, 	coords::VecExpr*	> 	interp2coords_VecExpr;
	std::unordered_map<interp::Vector*, 	coords::Vector*		> 	interp2coords_Vector;
	std::unordered_map<interp::Vector_Def*, coords::Vector_Def*	> 	interp2coords_Vector_Def;
};

} // namespace

#endif