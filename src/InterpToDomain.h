#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "Domain.h"
#include "Interp.h"

#include "VecParenExpr.h"

#include <unordered_map>

namespace interp2domain {

class InterpToDomain
{
  public:

// Ident

	void putVecIdent(interp::VecIdent *key, domain::VecIdent *i);
	domain::VecIdent *getVecIdent(interp::VecIdent *c) const;
	interp::VecIdent *getVecIdent(domain::VecIdent *d) const;

	void putFloatIdent(interp::FloatIdent *key, domain::FloatIdent *i);
	domain::FloatIdent *getFloatIdent(interp::FloatIdent *c) const;
	interp::FloatIdent *getFloatIdent(domain::FloatIdent *d) const;

// Expr

	domain::VecExpr *getVecExpr(interp::VecExpr* c) const;
	interp::VecExpr *getVecExpr(domain::VecExpr* d) const;

	domain::FloatExpr *getFloatExpr(interp::FloatExpr* c) const;
	interp::FloatExpr *getFloatExpr(domain::FloatExpr* d) const;

/*	void putVecLitExpr(interp::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(interp::VecLitExpr c) const;
	interp::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/

	void putVecVarExpr(interp::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(interp::VecVarExpr* c) const;
	interp::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void putFloatVarExpr(interp::FloatVarExpr *n, domain::FloatVarExpr *e);
	domain::FloatVarExpr *getFloatVarExpr(interp::FloatVarExpr* c) const;
	interp::FloatVarExpr *getFloatVarExpr(domain::FloatVarExpr* d) const;

	void putVecVecAddExpr(interp::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(interp::VecVecAddExpr* c) const;
	interp::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

	void putVecScalarMulExpr(interp::VecScalarMulExpr *n, domain::VecScalarMulExpr* e);
	domain::VecScalarMulExpr *getVecScalarMulExpr(interp::VecScalarMulExpr* n) const;
	interp::VecScalarMulExpr *getVecScalarMulExpr(domain::VecScalarMulExpr* e) const;

	void putFloatFloatAddExpr(interp::FloatFloatAddExpr *n, domain::FloatFloatAddExpr *e);
	domain::FloatFloatAddExpr *getFloatFloatAddExpr(interp::FloatFloatAddExpr* c) const;
	interp::FloatFloatAddExpr *getFloatFloatAddExpr(domain::FloatFloatAddExpr* d) const;

	void putFloatFloatMulExpr(interp::FloatFloatMulExpr *n, domain::FloatFloatMulExpr *e);
	domain::FloatFloatMulExpr *getFloatFloatMulExpr(interp::FloatFloatMulExpr* c) const;
	interp::FloatFloatMulExpr *getFloatFloatMulExpr(domain::FloatFloatMulExpr* d) const;


	// KEVIN: Added for VecParenExpr horizontal module
	void putVecParenExpr(interp::VecParenExpr *n, domain::VecParenExpr *e);
	domain::VecParenExpr *getVecParenExpr(interp::VecParenExpr* c) const;
	interp::VecParenExpr *getVecParenExpr(domain::VecParenExpr* d) const;

	void putFloatParenExpr(interp::FloatParenExpr *n, domain::FloatParenExpr *e);
	domain::FloatParenExpr *getFloatParenExpr(interp::FloatParenExpr* c) const;
	interp::FloatParenExpr *getFloatParenExpr(domain::FloatParenExpr* d) const;

// Vector

	void putVector_Lit(interp::Vector *ast, domain::Vector_Lit *v);
	domain::Vector_Lit *getVector_Lit(interp::Vector_Lit* c) const;
	interp::Vector_Lit *getVector_Lit(domain::Vector_Lit* d) const;

	void putVector_Expr(interp::Vector *ast, domain::Vector_Expr *v);
	domain::Vector_Expr *getVector_Expr(interp::Vector_Expr* c) const;
	interp::Vector_Expr *getVector_Expr(domain::Vector_Expr* d) const;

	interp::Vector *getVector(domain::Vector* v);
	domain::Vector *getVector(interp::Vector* v);

// Def

	void putVector_Def(interp::Vector_Def *vardecl_wrapper, domain::Vector_Def *b);
	domain::Vector_Def *getVector_Def(interp::Vector_Def* c) const;
	interp::Vector_Def *getVector_Def(domain::Vector_Def* d) const;

	void putFloat_Lit(interp::Float* ast, domain::Float_Lit *v);
	domain::Float_Lit *getFloat_Lit(interp::Float_Lit* c) const;
	interp::Float_Lit *getFloat_Lit(domain::Float_Lit* d) const;

	void putFloat_Expr(interp::Float *ast, domain::Float_Expr *v);
	domain::Float_Expr *getFloat_Expr(interp::Float_Expr* c) const;
	interp::Float_Expr *getFloat_Expr(domain::Float_Expr* d) const;

	interp::Float* getFloat(domain::Float* v);
	domain::Float* getFloat(interp::Float* v);

	void putFloat_Def(interp::Float_Def *vardecl_wrapper, domain::Float_Def *b);
	domain::Float_Def* getFloat_Def(interp::Float_Def* c) const;
	interp::Float_Def* getFloat_Def(domain::Float_Def* d) const;

	void dump() const;

  private:
	/* 
	We implement an domainretation as a collection of typed maps. 
	The keys are "Code Coordinate" objects, which, in turn, are 
	currently just containers for pointers to AST nodes, basically
	just adding operator==() and hash functions.
	*/
 
	std::unordered_map <interp::VecIdent*,	domain::VecIdent*	> 	interp2domain_VecIdent;
	std::unordered_map <interp::VecExpr*, 	domain::VecExpr*	> 	interp2domain_VecExpr;
	std::unordered_map <interp::Vector*, 	domain::Vector*		> 	interp2domain_Vector;
	std::unordered_map <interp::Vector_Def*,domain::Vector_Def*	> 	interp2domain_Vector_Def;

	std::unordered_map <interp::FloatIdent*,domain::FloatIdent* >	interp2domain_FloatIdent;
	std::unordered_map <interp::FloatExpr*, domain::FloatExpr*	>	interp2domain_FloatExpr;
	std::unordered_map <interp::Float*, domain::Float*			>	interp2domain_Float;
	std::unordered_map <interp::Float_Def*, domain::Float_Def*	>	interp2domain_Float_Def;

	std::unordered_map<domain::VecIdent*, 	interp::VecIdent*	> 	domain2interp_VecIdent;
	std::unordered_map<domain::VecExpr*, 	interp::VecExpr*	> 	domain2interp_VecExpr;
	std::unordered_map<domain::Vector*, 	interp::Vector*		> 	domain2interp_Vector;
	std::unordered_map<domain::Vector_Def*, interp::Vector_Def*	> 	domain2interp_Vector_Def;

	std::unordered_map<domain::FloatIdent*, interp::FloatIdent*	> 	domain2interp_FloatIdent;
	std::unordered_map<domain::FloatExpr*, 	interp::FloatExpr*	> 	domain2interp_FloatExpr;
	std::unordered_map<domain::Float*, 		interp::Float*		> 	domain2interp_Float;
	std::unordered_map<domain::Float_Def*, 	interp::Float_Def*	> 	domain2interp_Float_Def;
};

} // namespace

#endif