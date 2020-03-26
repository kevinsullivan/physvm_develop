#ifndef ORACLE_ASKALL_H
#define ORACLE_ASKALL_H

#include "Oracle.h"
#include "Domain.h"

namespace oracle {

class Oracle_AskAll : public Oracle 
{
public:
	Oracle_AskAll(domain::Domain* d) : dom_(d) {}; 

	domain::Space &getSpace();


	domain::Space& getSpaceForVecIdent(coords::VecIdent* v) {
		std::string query = "Space for vector identifier, ";
		query += v->toString();
		query += " at ";
		query += v->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(coords::VecExpr *var)  {
		std::string query = "Space for vector variable expression, ";
		query += var->toString();
		query += " at ";
		query += var->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForAddExpression(coords::VecExpr *mem, coords::VecExpr *arg)
	{
		std::string query = "";
		query += "Space for vector expression, add ";
		query += mem->toString();
		query += " ";
		query += arg->toString();
		query += ", at ";
		query += mem->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecParenExpr(coords::VecExpr *expr) {
		std::string query = "Space for vector parenthesized expression, ";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForVector_Expr(coords::VecExpr *expr) {
		std::string query = "Space for vector constructed from expression, \n";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}



	domain::Space& getSpaceForVector_Lit(coords::Vector_Lit *lit) {
		std::string query = "Space for vector constructed from literal, ";
		query += lit->toString();
		query += " at ";
		query += lit->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}
	

	domain::Space& getSpaceForFloatIdent(coords::FloatIdent* v) {
		std::string query = "Space for float identifier, ";
		query += v->toString();
		query += " at ";
		query += v->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForFloatVarExpr(coords::FloatExpr *var)  {
		std::string query = "Space for float variable expression, ";
		query += var->toString();
		query += " at ";
		query += var->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForMulExpression(coords::VecExpr *vec, coords::FloatExpr *flt)
	{
		std::string query = "";
		query += "Space for float scalar times vector expression, mul ";
		query += flt->toString();
		query += " ";
		query += vec->toString();
		query += ", at ";
		query += vec->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

		domain::Space& getSpaceForFloatAddExpression(coords::FloatExpr *lhs, coords::FloatExpr *rhs)
	{
		std::string query = "";
		query += "Space for float expression, add ";
		query += lhs->toString();
		query += " ";
		query += rhs->toString();
		query += ", at ";
		query += lhs->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}
		domain::Space& getSpaceForFloatMulExpression(coords::FloatExpr *lhs, coords::FloatExpr *rhs)
	{
		std::string query = "";
		query += "Space for float expression, mul ";
		query += lhs->toString();
		query += " ";
		query += rhs->toString();
		query += ", at ";
		query += lhs->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForFloatParenExpr(coords::FloatExpr *expr) {
		std::string query = "Space for float parenthesized expression, ";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForFloat_Expr(coords::FloatExpr *expr) {
		std::string query = "Space for float constructed from expression, \n";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}



	domain::Space& getSpaceForFloat_Lit(coords::Float_Lit *lit) {
		std::string query = "Space for float constructed from literal, ";
		query += lit->toString();
		query += " at ";
		query += lit->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}
private:
	domain::Domain* dom_;
};

} // namespace

#endif