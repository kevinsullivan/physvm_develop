#include "Interpretation.h"

#include <iostream>

using namespace std;


void Interpretation::putIdentInterp(const VarDeclASTNode& key, bridge::Identifier& v) {
    interpIdent.insert(std::make_pair(key,&v));
    cerr << "Put Ident Interp.\n";
}

const bridge::Identifier* Interpretation::getIdentInterp(const VarDeclASTNode& n) 
{
    return interpIdent[n];
    cerr << "Get Ident Interp.\n";
}

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

void Interpretation::putIdentifier(VarDeclASTNode* vardecl_container_key, bridge::Identifier& bi) {
    std::cerr << "In interpretation::putIdentifier. STUB.\n";
}

const bridge::Identifier* Interpretation::getIdentifier(VarDeclASTNode* key) {
    std::cerr << "In interpretation::getIdentifier. STUB.\n";
    return NULL;
}

void Interpretation::putBindingInterp(const VarDecl *vardecl, const Binding& b)
{
    cerr << "Interpretation::putBindingInterp called but stubbed out.\n";
}

Binding* Interpretation::getBindingInterp(const VarDecl& vardecl) {
    cerr << "Interpretation::getBindingInterp called but stubbed out. Returning NULL.\n";
    return NULL;
}
