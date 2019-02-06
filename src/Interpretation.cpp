#include "Interpretation.h"

#include <iostream>

using namespace std;


void Interpretation::putLitInterp(const LitASTNode& n, VecLitExpr& v) {
    interpLit.insert(std::make_pair(n,&v));
    cerr << "Put Lit Interp.\n";
}

VecLitExpr* Interpretation::getLitInterp(const LitASTNode& n) {
    return interpLit[n];
    cerr << "Get Lit Interp.\n";
}

void Interpretation::putVectorInterp(const VectorASTNode& n, VecVarExpr& av) {
    interpVector.insert(std::make_pair(n,&av));

    // TEST! DELETE THIS
    // cerr << "av inserted = " << &av << "\n";
    // cerr << "av lookuped = " << getVectorInterp(n) << "\n";
}

VecVarExpr* Interpretation::getVectorInterp(const VectorASTNode& n) {
    return interpVector[n];
}

void Interpretation::putExpressionInterp(const ExprASTNode& n, VecAddExpr& e) {
    interpExpression.emplace(n, &e);
}

VecAddExpr* Interpretation::getExpressionInterp(const ExprASTNode& n) {
   return interpExpression[n]; 
}

void Interpretation::putIdentifier(const VarDecl* vardecl, bridge::Identifier& bi) {
    
    std::cerr << "In interpretation::putIdentifier. STUB.\n";
}

const bridge::Identifier* Interpretation::getIdentifier() {
    std::cerr << "In interpretation::getIdentifier. STUB.\n";
    return NULL;
}

/*
Interpretation.cpp: At global scope:
Interpretation.cpp:37:71: error: 'void bridge::putBindingInterp(const clang::VarDecl*, const bridge::Binding&)' should have been declared inside 'bridge'
 void bridge::putBindingInterp(const VarDecl *vardecl, const Binding& b)
                                                                       ^
Interpretation.cpp:42:57: error: 'bridge::Binding* bridge::getBindingInterp(const clang::VarDecl&)' should have been declared inside 'bridge'
 Binding* bridge::getBindingInterp(const VarDecl& vardecl) {
*/      

void Interpretation::putBindingInterp(const VarDecl *vardecl, const Binding& b)
{
    cerr << "Interpretation::putBindingInterp called but stubbed out.\n";
}

Binding* Interpretation::getBindingInterp(const VarDecl& vardecl) {
    cerr << "Interpretation::getBindingInterp called but stubbed out. Returning NULL.\n";
    return NULL;
}
