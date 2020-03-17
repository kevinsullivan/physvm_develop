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
	
	virtual domain::Space &getSpaceForFloatIdent(coords::FloatIdent *v) = 0;
	virtual domain::Space& getSpaceForFloatVarExpr(coords::FloatExpr *coords) = 0;
	virtual domain::Space &getSpaceForMulExpression(coords::FloatExpr *flt, coords::VecExpr *vec) = 0;

	// KEVIN: Added for VecParenExpr module
	virtual domain::Space &getSpaceForFloatParenExpr(coords::FloatExpr *expr_coords) = 0;
	
	virtual domain::Space& getSpaceForFloat_Expr(coords::FloatExpr *expr_coords) = 0; 
	virtual domain::Space& getSpaceForFloat_Lit(coords::Float_Lit *coords) = 0;
};

} // namespace

#endif