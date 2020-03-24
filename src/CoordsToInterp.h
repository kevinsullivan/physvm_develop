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

	void putVecWrapper(coords::VecWrapper *n, interp::VecWrapper *e);
	interp::VecWrapper *getVecWrapper(coords::VecWrapper* c) const;
	coords::VecWrapper *getVecWrapper(interp::VecWrapper* d) const;

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

	void putVecScalarMulExpr(coords::VecScalarMulExpr *n, interp::VecScalarMulExpr *e);
	interp::VecScalarMulExpr *getVecScalarMulExpr(coords::VecScalarMulExpr* c) const;
	coords::VecScalarMulExpr *getVecScalarMulExpr(interp::VecScalarMulExpr* d) const;

// Ident

	void putFloatIdent(coords::FloatIdent *key, interp::FloatIdent *i);
	interp::FloatIdent *getFloatIdent(coords::FloatIdent *c) const;
	coords::FloatIdent *getFloatIdent(interp::FloatIdent *d) const;

// Expr

	interp::FloatExpr *getFloatExpr(coords::FloatExpr* c) const;
	coords::FloatExpr *getFloatExpr(interp::FloatExpr* d) const;

	void putFloatWrapper(coords::FloatWrapper *n, interp::FloatWrapper *e);
	interp::FloatWrapper *getFloatWrapper(coords::FloatWrapper* c) const;
	coords::FloatWrapper *getFloatWrapper(interp::FloatWrapper* d) const;
	

	void putFloatVarExpr(coords::FloatVarExpr *n, interp::FloatVarExpr *e);
	interp::FloatVarExpr *getFloatVarExpr(coords::FloatVarExpr* c) const;
	coords::FloatVarExpr *getFloatVarExpr(interp::FloatVarExpr* d) const;
	
	// KEVIN: This stuff here for FloatParenExpr module
	void putFloatParenExpr(coords::FloatParenExpr *ast, interp::FloatParenExpr *expr);
	interp::FloatParenExpr *getFloatParenExpr(coords::FloatParenExpr* c) const;
	coords::FloatParenExpr *getFloatParenExpr(interp::FloatParenExpr* d) const;

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

// Float

	void putFloat_Lit(coords::Float *ast, interp::Float_Lit *v);
	interp::Float_Lit *getFloat_Lit(coords::Float_Lit* c) const;
	coords::Float_Lit *getFloat_Lit(interp::Float_Lit* d) const;

	void putFloat_Expr(coords::Float *ast, interp::Float_Expr *v);
	interp::Float_Expr *getFloat_Expr(coords::Float_Expr* c) const;
	coords::Float_Expr *getFloat_Expr(interp::Float_Expr* d) const;

	coords::Float *getFloat(interp::Float* v);
	interp::Float *getFloat(coords::Float* v);

// Def

	void putFloat_Def(coords::Float_Def *vardecl_wrapper, interp::Float_Def *b);
	interp::Float_Def *getFloat_Def(coords::Float_Def* c) const;
	coords::Float_Def *getFloat_Def(interp::Float_Def* d) const;

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

	std::unordered_map <coords::FloatIdent*,interp::FloatIdent* > 	coords2interp_FloatIdent;
	std::unordered_map <coords::FloatExpr*, interp::FloatExpr*	> 	coords2interp_FloatExpr;
	std::unordered_map <coords::Float*, 	interp::Float*		> 	coords2interp_Float;
	std::unordered_map <coords::Float_Def*, interp::Float_Def*	> 	coords2interp_Float_Def;


	std::unordered_map<interp::FloatIdent*, coords::FloatIdent*	> 	interp2coords_FloatIdent;
	std::unordered_map<interp::FloatExpr*, 	coords::FloatExpr*	> 	interp2coords_FloatExpr;
	std::unordered_map<interp::Float*, 		coords::Float*		> 	interp2coords_Float;
	std::unordered_map<interp::Float_Def*, 	coords::Float_Def*	> 	interp2coords_Float_Def;
};

} // namespace

#endif