#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

namespace coords2domain {

class CoordsToDomain
{
  public:
	void putIdentifierInterp(const coords::VecIdent *key, domain::Identifier *bi);
	const domain::Identifier *getIdentifierInterp(const coords::VecIdent *key);

	// ??? delete ???
	/*
	void putVectorInterp(const VectorASTNode& n, VecVarExpr& v);
	VecVarExpr* getVectorInterp(const VectorASTNode& n);
	*/

	void putLitInterp(const coords::LitASTNode &n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(const coords::LitASTNode &n) const;

	void putExpressionInterp(const coords::ExprASTNode *n, domain::Expr *e);
	domain::Expr *getExpressionInterp(const coords::ExprASTNode* n);

	void putBindingInterp(coords::BindingASTNode *vardecl_wrapper, domain::Binding &b);
	const domain::Binding *getBindingInterp(const coords::BindingASTNode* vardecl_wrapper);

	void dumpExpressions() const {
		for (auto it = interpExpression.begin(); it != interpExpression.end(); ++it) {
			//std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
			cerr << "InterpExpr!\n";
		}
		std::cerr << std::endl;
	}

  private:
	/* 
	We implement an interpretation as a collection of typed maps. The keys are "Code Coordinate" objects, which, in turn, are currently just containers for pointers to 
	AST nodes, adding operator==() and hash functions.
	*/
	unordered_map<coords::VecIdent, domain::Identifier *, coords::IdentifierASTNodeHasher> interpIdent;
	unordered_map<const coords::ExprASTNode, domain::Expr *, coords::ExprASTNodeHasher> interpExpression;
	unordered_map<coords::BindingASTNode, domain::Binding *, coords::BindingASTNodeHasher> interpBinding;
};

} // namespace

#endif