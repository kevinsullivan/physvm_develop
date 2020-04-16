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
/*
	void putVecWrapper(coords::VecWrapper *n, interp::VecWrapper *e);
	interp::VecWrapper *getVecWrapper(coords::VecWrapper* c) const;
	coords::VecWrapper *getVecWrapper(interp::VecWrapper* d) const;
*/
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

	void putScalarScalarAddExpr(coords::ScalarScalarAddExpr *n, interp::ScalarScalarAddExpr *e);
	interp::ScalarScalarAddExpr *getScalarScalarAddExpr(coords::ScalarScalarAddExpr* c) const;
	coords::ScalarScalarAddExpr *getScalarScalarAddExpr(interp::ScalarScalarAddExpr* d) const;
	
	void putScalarScalarMulExpr(coords::ScalarScalarMulExpr *n, interp::ScalarScalarMulExpr *e);
	interp::ScalarScalarMulExpr *getScalarScalarMulExpr(coords::ScalarScalarMulExpr* c) const;
	coords::ScalarScalarMulExpr *getScalarScalarMulExpr(interp::ScalarScalarMulExpr* d) const;
	

// Ident

	void putScalarIdent(coords::ScalarIdent *key, interp::ScalarIdent *i);
	interp::ScalarIdent *getScalarIdent(coords::ScalarIdent *c) const;
	coords::ScalarIdent *getScalarIdent(interp::ScalarIdent *d) const;

// Expr

	interp::ScalarExpr *getScalarExpr(coords::ScalarExpr* c) const;
	coords::ScalarExpr *getScalarExpr(interp::ScalarExpr* d) const;
/*
	void putScalarWrapper(coords::ScalarWrapper *n, interp::ScalarWrapper *e);
	interp::ScalarWrapper *getScalarWrapper(coords::ScalarWrapper* c) const;
	coords::ScalarWrapper *getScalarWrapper(interp::ScalarWrapper* d) const;
*/	

	void putScalarVarExpr(coords::ScalarVarExpr *n, interp::ScalarVarExpr *e);
	interp::ScalarVarExpr *getScalarVarExpr(coords::ScalarVarExpr* c) const;
	coords::ScalarVarExpr *getScalarVarExpr(interp::ScalarVarExpr* d) const;
	
	// KEVIN: This stuff here for ScalarParenExpr module
	void putScalarParenExpr(coords::ScalarParenExpr *ast, interp::ScalarParenExpr *expr);
	interp::ScalarParenExpr *getScalarParenExpr(coords::ScalarParenExpr* c) const;
	coords::ScalarParenExpr *getScalarParenExpr(interp::ScalarParenExpr* d) const;

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

// Assign

	void putVector_Assign(coords::Vector_Assign *varassn_wrapper, interp::Vector_Assign *b);
	interp::Vector_Assign *getVector_Assign(coords::Vector_Assign* c) const;
	coords::Vector_Assign *getVector_Assign(interp::Vector_Assign* d) const;

// Scalar

	void putScalar_Lit(coords::Scalar *ast, interp::Scalar_Lit *v);
	interp::Scalar_Lit *getScalar_Lit(coords::Scalar_Lit* c) const;
	coords::Scalar_Lit *getScalar_Lit(interp::Scalar_Lit* d) const;

	void putScalar_Expr(coords::Scalar *ast, interp::Scalar_Expr *v);
	interp::Scalar_Expr *getScalar_Expr(coords::Scalar_Expr* c) const;
	coords::Scalar_Expr *getScalar_Expr(interp::Scalar_Expr* d) const;

	coords::Scalar *getScalar(interp::Scalar* v);
	interp::Scalar *getScalar(coords::Scalar* v);

// Def

	void putScalar_Def(coords::Scalar_Def *vardecl_wrapper, interp::Scalar_Def *b);
	interp::Scalar_Def *getScalar_Def(coords::Scalar_Def* c) const;
	coords::Scalar_Def *getScalar_Def(interp::Scalar_Def* d) const;

// Assign

	void putScalar_Assign(coords::Scalar_Assign *varassn_wrapper, interp::Scalar_Assign *b);
	interp::Scalar_Assign *getScalar_Assign(coords::Scalar_Assign* c) const;
	coords::Scalar_Assign *getScalar_Assign(interp::Scalar_Assign* d) const;

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
	std::unordered_map <coords::Vector_Assign*,interp::Vector_Assign*> 	coords2interp_Vector_Assign;


	std::unordered_map<interp::VecIdent*, 	coords::VecIdent*	> 	interp2coords_VecIdent;
	std::unordered_map<interp::VecExpr*, 	coords::VecExpr*	> 	interp2coords_VecExpr;
	std::unordered_map<interp::Vector*, 	coords::Vector*		> 	interp2coords_Vector;
	std::unordered_map<interp::Vector_Def*, coords::Vector_Def*	> 	interp2coords_Vector_Def;
	std::unordered_map<interp::Vector_Assign*, coords::Vector_Assign*> 	interp2coords_Vector_Assign;

	std::unordered_map <coords::ScalarIdent*,interp::ScalarIdent* > 	coords2interp_ScalarIdent;
	std::unordered_map <coords::ScalarExpr*, interp::ScalarExpr*	> 	coords2interp_ScalarExpr;
	std::unordered_map <coords::Scalar*, 	interp::Scalar*		> 	coords2interp_Scalar;
	std::unordered_map <coords::Scalar_Def*, interp::Scalar_Def*	> 	coords2interp_Scalar_Def;
	std::unordered_map <coords::Scalar_Assign*, interp::Scalar_Assign*> 	coords2interp_Scalar_Assign;


	std::unordered_map<interp::ScalarIdent*, coords::ScalarIdent*	> 	interp2coords_ScalarIdent;
	std::unordered_map<interp::ScalarExpr*, 	coords::ScalarExpr*	> 	interp2coords_ScalarExpr;
	std::unordered_map<interp::Scalar*, 		coords::Scalar*		> 	interp2coords_Scalar;
	std::unordered_map<interp::Scalar_Def*, 	coords::Scalar_Def*	> 	interp2coords_Scalar_Def;
	std::unordered_map<interp::Scalar_Assign*, 	coords::Scalar_Assign*> 	interp2coords_Scalar_Assign;
};

} // namespace

#endif