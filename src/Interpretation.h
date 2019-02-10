#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "CodeCoordinate.h"
#include "Bridge.h"

#include <unordered_map>

using namespace std;
using namespace bridge;

class Interpretation
{
  public:
	void putIdentInterp(const IdentifierASTNode &key, bridge::Identifier &bi);
	const bridge::Identifier *getIdentInterp(const IdentifierASTNode &key);

	// ??? delete ???
	/*
	void putVectorInterp(const VectorASTNode& n, VecVarExpr& v);
	VecVarExpr* getVectorInterp(const VectorASTNode& n);
	*/

	void putLitInterp(const LitASTNode &n, VecLitExpr &v);
	VecLitExpr *getLitInterp(const LitASTNode &n);

	void putExpressionInterp(const ExprASTNode &n, const bridge::Expr &e);
	const bridge::Expr *getExpressionInterp(const ExprASTNode &n);

	void putBindingInterp(BindingASTNode *vardecl_wrapper, Binding &b);
	Binding *getBindingInterp(BindingASTNode &vardecl_wrapper);

	void dumpExpressions() {
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
	unordered_map<IdentifierASTNode, bridge::Identifier *, IdentifierASTNodeHasher> interpIdent;
	unordered_map<const ExprASTNode, const bridge::Expr *, ExprASTNodeHasher> interpExpression;
	unordered_map<BindingASTNode, bridge::Binding *, BindingASTNodeHasher> interpBinding;
};

#endif