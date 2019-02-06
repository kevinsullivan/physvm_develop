#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include<iostream>
#include "CodeCoordinate.h"
#include "Bridge.h"

#include <unordered_map>

using namespace std;
using namespace bridge;

class Interpretation {
public:

	void putIdentifier(const VarDecl* vardecl, bridge::Identifier& bi);

	const bridge::Identifier* getIdentifier();

	// Add a vector tuple to the interpretation
	// Precondition: key not already defined in map
	// Postcondition: map' = map + (n,v) 
	void putVectorInterp(const VectorASTNode& n, VecVarExpr& v);

	// Lookup existing association in map
	// Precondition: key defined in map
	// Postcondition: result as associated abstract vector value
	VecVarExpr* getVectorInterp(const VectorASTNode& n);


	// Add a vector tuple to the interpretation
	// Precondition: key not already defined in map
	// Postcondition: map' = map + (n,v) 
	void putLitInterp(const LitASTNode& n, VecLitExpr& v);

	// Lookup existing association in map
	// Precondition: key defined in map
	// Postcondition: result as associated abstract vector value
	VecLitExpr* getLitInterp(const LitASTNode& n);

	// As above but for expressions
	void putExpressionInterp(const ExprASTNode& n, VecAddExpr& e);

	// As above but for expressions
	VecAddExpr* getExpressionInterp(const ExprASTNode& n);

	// As above but for variable declaration bindings
	void putBindingInterp(const VarDecl *vardecl, const Binding& b);

	// As above but for expressions
	Binding* getBindingInterp(const VarDecl& vardecl);

private:
	// We implement an interpretation as a collection of typed maps
	unordered_map<LitASTNode, VecLitExpr*, LitASTNodeHasher> interpLit;
	unordered_map<VectorASTNode, VecVarExpr*, VectorASTNodeHasher> interpVector;
	unordered_map<ExprASTNode, VecAddExpr*, ExprASTNodeHasher> interpExpression;
	unordered_map<VectorVarDeclNode, Identifier*, VectorVarDeclNodeHasher> interpIdentifier;

//	and now for bindings
//	unordered_map<VectorVarDeclNode, Identifier*, VectorVarDeclNodeHasher> interpIdentifier;
};

#endif