#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include <iostream>
#include "Coords.h"
#include "Domain.h"

namespace oracle {

class Oracle
{
public:
	virtual domain::Space &getSpaceForVecIdent(coords::VecIdent *v) = 0;
	virtual domain::Space& getSpaceForVecVarExpr(coords::VecExpr *coords) = 0;
	virtual domain::Space &getSpaceForAddExpression(coords::VecExpr *mem, coords::VecExpr *arg) = 0;

	// KEVIN: Added for VecParenExpr module
	virtual domain::Space &getSpaceForVecParenExpr(coords::VecExpr *expr_coords) = 0;
	
	virtual domain::Space& getSpaceForVector_Expr(coords::VecExpr *expr_coords) = 0; 
	virtual domain::Space& getSpaceForVector_Lit(coords::Vector_Lit *coords) = 0;
	
	virtual domain::Space &getSpaceForScalarIdent(coords::ScalarIdent *v) = 0;
	virtual domain::Space& getSpaceForScalarVarExpr(coords::ScalarExpr *coords) = 0;
	virtual domain::Space &getSpaceForMulExpression(coords::VecExpr *vec, coords::ScalarExpr *flt) = 0;

	// KEVIN: Added for VecParenExpr module
	virtual domain::Space &getSpaceForScalarParenExpr(coords::ScalarExpr *expr_coords) = 0;
	
	virtual domain::Space& getSpaceForScalar_Expr(coords::ScalarExpr *expr_coords) = 0; 
	virtual domain::Space& getSpaceForScalar_Lit(coords::Scalar_Lit *coords) = 0;

	virtual domain::Space& getSpaceForScalarAddExpression(coords::ScalarExpr *lhs, coords::ScalarExpr *rhs) = 0;
	virtual domain::Space& getSpaceForScalarMulExpression(coords::ScalarExpr *lhs, coords::ScalarExpr *rhs) = 0;

	virtual domain::MapSpace &getSpaceForTransformIdent(coords::TransformIdent *v) = 0;
	virtual domain::MapSpace& getSpaceForTransformVarExpr(coords::TransformExpr *coords) = 0;
	virtual domain::MapSpace &getSpaceForTransformParenExpr(coords::TransformExpr *expr_coords) = 0;
	virtual domain::Space& getSpaceForTransformApplyExpression(coords::TransformExpr *lhs, coords::VecExpr *rhs) = 0;
	virtual domain::MapSpace& getSpaceForTransformComposeExpression(coords::TransformExpr *lhs, coords::TransformExpr *rhs) = 0;

	virtual domain::MapSpace& getSpaceForTransform_Expr(coords::TransformExpr *expr_coords) = 0; 
	virtual domain::MapSpace& getSpaceForTransform_Lit(coords::Transform_Lit *coords) = 0;
};

} // namespace

#endif