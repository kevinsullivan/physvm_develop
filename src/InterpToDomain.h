#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "Domain.h"
#include "Interp.h"

#include <unordered_map>

namespace interp2domain {

class InterpToDomain
{
  public:

// Ident

	void putVecIdent(interp::VecIdent *key, domain::VecIdent *i);
	domain::VecIdent *getVecIdent(interp::VecIdent *c) const;
	interp::VecIdent *getVecIdent(domain::VecIdent *d) const;

// Expr

	domain::VecExpr *getVecExpr(interp::VecExpr* c);
	interp::VecExpr *getVecExpr(domain::VecExpr* d) const;

/*	void putVecLitExpr(interp::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(interp::VecLitExpr c) const;
	interp::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/

	void putVecVarExpr(interp::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(interp::VecVarExpr* c) const;
	interp::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void putVecVecAddExpr(interp::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(interp::VecVecAddExpr* c) const;
	interp::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

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

	std::unordered_map<domain::VecIdent*, 	interp::VecIdent*	> 	domain2interp_VecIdent;
	std::unordered_map<domain::VecExpr*, 	interp::VecExpr*	> 	domain2interp_VecExpr;
	std::unordered_map<domain::Vector*, 	interp::Vector*		> 	domain2interp_Vector;
	std::unordered_map<domain::Vector_Def*, interp::Vector_Def*	> 	domain2interp_Vector_Def;
};

} // namespace

#endif