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

	void putScalarIdent(interp::ScalarIdent *key, domain::ScalarIdent *i);
	domain::ScalarIdent *getScalarIdent(interp::ScalarIdent *c) const;
	interp::ScalarIdent *getScalarIdent(domain::ScalarIdent *d) const;

	void putTransformIdent(interp::TransformIdent *key, domain::TransformIdent *i);
	domain::TransformIdent *getTransformIdent(interp::TransformIdent *c) const;
	interp::TransformIdent *getTransformIdent(domain::TransformIdent *d) const;
// Expr

	domain::VecExpr *getVecExpr(interp::VecExpr* c) const;
	interp::VecExpr *getVecExpr(domain::VecExpr* d) const;

	domain::ScalarExpr *getScalarExpr(interp::ScalarExpr* c) const;
	interp::ScalarExpr *getScalarExpr(domain::ScalarExpr* d) const;

	domain::TransformExpr *getTransformExpr(interp::TransformExpr* c) const;
	interp::TransformExpr *getTransformExpr(domain::TransformExpr* d) const;

/*	void putVecLitExpr(interp::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(interp::VecLitExpr c) const;
	interp::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/

	void putVecVarExpr(interp::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(interp::VecVarExpr* c) const;
	interp::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void putScalarVarExpr(interp::ScalarVarExpr *n, domain::ScalarVarExpr *e);
	domain::ScalarVarExpr *getScalarVarExpr(interp::ScalarVarExpr* c) const;
	interp::ScalarVarExpr *getScalarVarExpr(domain::ScalarVarExpr* d) const;

	void putTransformVarExpr(interp::TransformVarExpr *n, domain::TransformVarExpr *e);
	domain::TransformVarExpr *getTransformVarExpr(interp::TransformVarExpr* c) const;
	interp::TransformVarExpr *getTransformVarExpr(domain::TransformVarExpr* d) const;

	void putVecVecAddExpr(interp::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(interp::VecVecAddExpr* c) const;
	interp::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

	void putVecScalarMulExpr(interp::VecScalarMulExpr *n, domain::VecScalarMulExpr* e);
	domain::VecScalarMulExpr *getVecScalarMulExpr(interp::VecScalarMulExpr* n) const;
	interp::VecScalarMulExpr *getVecScalarMulExpr(domain::VecScalarMulExpr* e) const;

	void putTransformVecApplyExpr(interp::TransformVecApplyExpr *n, domain::TransformVecApplyExpr* e);
	domain::TransformVecApplyExpr *getTransformVecApplyExpr(interp::TransformVecApplyExpr* n) const;
	interp::TransformVecApplyExpr *getTransformVecApplyExpr(domain::TransformVecApplyExpr* e) const;

	void putScalarScalarAddExpr(interp::ScalarScalarAddExpr *n, domain::ScalarScalarAddExpr *e);
	domain::ScalarScalarAddExpr *getScalarScalarAddExpr(interp::ScalarScalarAddExpr* c) const;
	interp::ScalarScalarAddExpr *getScalarScalarAddExpr(domain::ScalarScalarAddExpr* d) const;

	void putScalarScalarMulExpr(interp::ScalarScalarMulExpr *n, domain::ScalarScalarMulExpr *e);
	domain::ScalarScalarMulExpr *getScalarScalarMulExpr(interp::ScalarScalarMulExpr* c) const;
	interp::ScalarScalarMulExpr *getScalarScalarMulExpr(domain::ScalarScalarMulExpr* d) const;

	void putTransformTransformComposeExpr(interp::TransformTransformComposeExpr *n, domain::TransformTransformComposeExpr *e);
	domain::TransformTransformComposeExpr *getTransformTransformComposeExpr(interp::TransformTransformComposeExpr* c) const;
	interp::TransformTransformComposeExpr *getTransformTransformComposeExpr(domain::TransformTransformComposeExpr* d) const;

	// KEVIN: Added for VecParenExpr horizontal module
	void putVecParenExpr(interp::VecParenExpr *n, domain::VecParenExpr *e);
	domain::VecParenExpr *getVecParenExpr(interp::VecParenExpr* c) const;
	interp::VecParenExpr *getVecParenExpr(domain::VecParenExpr* d) const;

	void putScalarParenExpr(interp::ScalarParenExpr *n, domain::ScalarParenExpr *e);
	domain::ScalarParenExpr *getScalarParenExpr(interp::ScalarParenExpr* c) const;
	interp::ScalarParenExpr *getScalarParenExpr(domain::ScalarParenExpr* d) const;

	void putTransformParenExpr(interp::TransformParenExpr *n, domain::TransformParenExpr *e);
	domain::TransformParenExpr *getTransformParenExpr(interp::TransformParenExpr* c) const;
	interp::TransformParenExpr *getTransformParenExpr(domain::TransformParenExpr* d) const;

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

	void putVector_Assign(interp::Vector_Assign *var_wrapper, domain::Vector_Assign *b);
	domain::Vector_Assign *getVector_Assign(interp::Vector_Assign* c) const;
	interp::Vector_Assign *getVector_Assign(domain::Vector_Assign* d) const;

	void putScalar_Lit(interp::Scalar* ast, domain::Scalar_Lit *v);
	domain::Scalar_Lit *getScalar_Lit(interp::Scalar_Lit* c) const;
	interp::Scalar_Lit *getScalar_Lit(domain::Scalar_Lit* d) const;

	void putScalar_Expr(interp::Scalar *ast, domain::Scalar_Expr *v);
	domain::Scalar_Expr *getScalar_Expr(interp::Scalar_Expr* c) const;
	interp::Scalar_Expr *getScalar_Expr(domain::Scalar_Expr* d) const;

	interp::Scalar* getScalar(domain::Scalar* v);
	domain::Scalar* getScalar(interp::Scalar* v);

	void putScalar_Def(interp::Scalar_Def *vardecl_wrapper, domain::Scalar_Def *b);
	domain::Scalar_Def* getScalar_Def(interp::Scalar_Def* c) const;
	interp::Scalar_Def* getScalar_Def(domain::Scalar_Def* d) const;

	void putScalar_Assign(interp::Scalar_Assign *var_wrapper, domain::Scalar_Assign *b);
	domain::Scalar_Assign* getScalar_Assign(interp::Scalar_Assign* c) const;
	interp::Scalar_Assign* getScalar_Assign(domain::Scalar_Assign* d) const;

	void putTransform_Lit(interp::Transform* ast, domain::Transform_Lit *v);
	domain::Transform_Lit *getTransform_Lit(interp::Transform_Lit* c) const;
	interp::Transform_Lit *getTransform_Lit(domain::Transform_Lit* d) const;

	void putTransform_Expr(interp::Transform *ast, domain::Transform_Expr *v);
	domain::Transform_Expr *getTransform_Expr(interp::Transform_Expr* c) const;
	interp::Transform_Expr *getTransform_Expr(domain::Transform_Expr* d) const;

	interp::Transform* getTransform(domain::Transform* v);
	domain::Transform* getTransform(interp::Transform* v);

	void putTransform_Def(interp::Transform_Def *vardecl_wrapper, domain::Transform_Def *b);
	domain::Transform_Def* getTransform_Def(interp::Transform_Def* c) const;
	interp::Transform_Def* getTransform_Def(domain::Transform_Def* d) const;

	void putTransform_Assign(interp::Transform_Assign *var_wrapper, domain::Transform_Assign *b);
	domain::Transform_Assign* getTransform_Assign(interp::Transform_Assign* c) const;
	interp::Transform_Assign* getTransform_Assign(domain::Transform_Assign* d) const;
	

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
	std::unordered_map <interp::Vector_Assign*,domain::Vector_Assign*> 	interp2domain_Vector_Assign;

	std::unordered_map <interp::ScalarIdent*,domain::ScalarIdent* >	interp2domain_ScalarIdent;
	std::unordered_map <interp::ScalarExpr*, domain::ScalarExpr*	>	interp2domain_ScalarExpr;
	std::unordered_map <interp::Scalar*, domain::Scalar*			>	interp2domain_Scalar;
	std::unordered_map <interp::Scalar_Def*, domain::Scalar_Def*	>	interp2domain_Scalar_Def;
	std::unordered_map <interp::Scalar_Assign*, domain::Scalar_Assign*>	interp2domain_Scalar_Assign;

	std::unordered_map <interp::TransformIdent*,domain::TransformIdent* >	interp2domain_TransformIdent;
	std::unordered_map <interp::TransformExpr*, domain::TransformExpr*	>	interp2domain_TransformExpr;
	std::unordered_map <interp::Transform*, domain::Transform*			>	interp2domain_Transform;
	std::unordered_map <interp::Transform_Def*, domain::Transform_Def*	>	interp2domain_Transform_Def;
	std::unordered_map <interp::Transform_Assign*, domain::Transform_Assign*>	interp2domain_Transform_Assign;

	std::unordered_map<domain::VecIdent*, 	interp::VecIdent*	> 	domain2interp_VecIdent;
	std::unordered_map<domain::VecExpr*, 	interp::VecExpr*	> 	domain2interp_VecExpr;
	std::unordered_map<domain::Vector*, 	interp::Vector*		> 	domain2interp_Vector;
	std::unordered_map<domain::Vector_Def*, interp::Vector_Def*	> 	domain2interp_Vector_Def;
	std::unordered_map<domain::Vector_Assign*, interp::Vector_Assign*> 	domain2interp_Vector_Assign;

	std::unordered_map<domain::ScalarIdent*, interp::ScalarIdent*	> 	domain2interp_ScalarIdent;
	std::unordered_map<domain::ScalarExpr*, 	interp::ScalarExpr*	> 	domain2interp_ScalarExpr;
	std::unordered_map<domain::Scalar*, 		interp::Scalar*		> 	domain2interp_Scalar;
	std::unordered_map<domain::Scalar_Def*, 	interp::Scalar_Def*	> 	domain2interp_Scalar_Def;
	std::unordered_map<domain::Scalar_Assign*, 	interp::Scalar_Assign*> 	domain2interp_Scalar_Assign;

	std::unordered_map<domain::TransformIdent*, interp::TransformIdent*	> 	domain2interp_TransformIdent;
	std::unordered_map<domain::TransformExpr*, 	interp::TransformExpr*	> 	domain2interp_TransformExpr;
	std::unordered_map<domain::Transform*, 		interp::Transform*		> 	domain2interp_Transform;
	std::unordered_map<domain::Transform_Def*, 	interp::Transform_Def*	> 	domain2interp_Transform_Def;
	std::unordered_map<domain::Transform_Assign*, 	interp::Transform_Assign*> 	domain2interp_Transform_Assign;
};

} // namespace

#endif