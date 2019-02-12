#include "Interpretation.h"

#include <iostream>

using namespace std;

/*************
 * Identifiers
 *************/

void Interpretation::putIdentifierInterp(const IdentifierASTNode *key, bridge::Identifier *v) {
    cerr << "Interpretation::putIdentifierInterp: " << key->toString() << "\n";
    interpIdent.insert(std::make_pair(*key, v));
    //cerr << "Put Ident Interp.\n";
}

const bridge::Identifier* Interpretation::getIdentifierInterp(const IdentifierASTNode* n) 
{
    return interpIdent[*n];
    cerr << "Get Ident Interp.\n";
}

/****************
 * Add Expression
 ****************/

void Interpretation::putExpressionInterp(const ExprASTNode* n, const bridge::Expr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

const bridge::Expr* Interpretation::getExpressionInterp
        (const ExprASTNode* n)  {
   return interpExpression[*n]; 
}

/*********
 * Binding
 *********/

// TODO: Make first arg a reference &
void Interpretation::putBindingInterp(BindingASTNode *key, Binding& b)
{
    interpBinding.insert(std::make_pair(*key,&b));
    //cerr << "Interpretation::putBindingInterp called but stubbed out.\n";
}


const Binding* Interpretation::getBindingInterp(const BindingASTNode* key)  {
   return interpBinding[*key];     
   //cerr << "Interpretation::getBindingInterp called but stubbed out. Returning NULL.\n";
}
