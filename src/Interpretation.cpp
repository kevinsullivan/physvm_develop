#include "Interpretation.h"

#include <iostream>

using namespace std;

/*************
 * Identifiers
 *************/

void Interpretation::putIdentInterp(const VarDeclASTNode& key, bridge::Identifier& v) {
    interpIdent.insert(std::make_pair(key,&v));
    //cerr << "Put Ident Interp.\n";
}

const bridge::Identifier* Interpretation::getIdentInterp(const VarDeclASTNode& n) 
{
    return interpIdent[n];
    cerr << "Get Ident Interp.\n";
}

/****************
 * Add Expression
 ****************/

void Interpretation::putExpressionInterp(const ExprASTNode& n, bridge::Expr& e) {
//    interpExpression.emplace(n, &e);
    interpExpression.insert(std::make_pair(n, &e));
}

bridge::Expr* Interpretation::getExpressionInterp(const ExprASTNode& n) {
   return interpExpression[n]; 
}

/*********
 * Binding
 *********/

// TODO: Make first arg a reference &
void Interpretation::putBindingInterp(VarDeclASTNode *key, Binding& b)
{
    interpBinding.insert(std::make_pair(*key,&b));
    //cerr << "Interpretation::putBindingInterp called but stubbed out.\n";
}

Binding* Interpretation::getBindingInterp(VarDeclASTNode& key) {
   return interpBinding[key];     
   //cerr << "Interpretation::getBindingInterp called but stubbed out. Returning NULL.\n";
}
