#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "CodeCoords.h"
#include "Domain.h"

#include <unordered_map>

using namespace domain;

class CodeToDomain
{
  public:
	void putIdentifierInterp(const IdentifierASTNode *key, domain::Identifier *bi);
	const domain::Identifier *getIdentifierInterp(const IdentifierASTNode *key);

	// ??? delete ???
	/*
	void putVectorInterp(const VectorASTNode& n, VecVarExpr& v);
	VecVarExpr* getVectorInterp(const VectorASTNode& n);
	*/

	void putLitInterp(const LitASTNode &n, VecLitExpr &v);
	VecLitExpr *getLitInterp(const LitASTNode &n) const;

	void putExpressionInterp(const ExprASTNode *n, const domain::Expr *e);
	const domain::Expr *getExpressionInterp(const ExprASTNode* n);

	void putBindingInterp(BindingASTNode *vardecl_wrapper, Binding &b);
	const Binding *getBindingInterp(const BindingASTNode* vardecl_wrapper);

	void dumpExpressions() const {
		for (auto it = interpExpression.begin(); it != interpExpression.end(); ++it) {
			//std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
			cerr << "InterpExpr!\n";
		}
		std::cerr << std::endl;
	}

  private:
	/* 
	We implement an interpretation as a collection of typed maps. The keys are "Code Coordinate" objects, which, in 
	turn, are currently just containers for pointers to AST
	nodes, adding operator==() and hash functions.
	*/
	unordered_map<IdentifierASTNode, domain::Identifier *, IdentifierASTNodeHasher> interpIdent;
	unordered_map<const ExprASTNode, const domain::Expr *, ExprASTNodeHasher> interpExpression;
	unordered_map<BindingASTNode, domain::Binding *, BindingASTNodeHasher> interpBinding;
};

#endif