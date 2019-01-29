#include <vector>
#include <iostream>
#include "Checker.h"
#include "Bridge.h"

using namespace std;
using namespace bridge;
 
// Space class member function implementation
string Space::getName(){return name_;}


// Expr class member function implementation
const Space& Expr::getSpace(){return space_;}



// VecVarExpr class member function implementation
const Space& VecVarExpr::getVecVarSpace(){ return space_;}


// VecAddExpr class member function implementation

const Expr& VecAddExpr::getVecAddExprArgL(){return arg_left_;}
const Expr& VecAddExpr::getVecAddExprArgR(){return arg_right_;}


const Space& VecAddExpr::getVecAddExprDefaultSpace(){
	return space_;
}

// Bridge class member function implementation

// Add new space,, s, to domain
// Precondition: true
// Postcondition: 
//	spaces' = spaces + s and
//  return value = reference to s
Space& Bridge::addSpace(const string& name) {
    Space* s = new Space(name);
    spaces.push_back(*s);
    return *s;
}

// Add new vector, v, in space s, to domain
// Precondition: s is already in spaces
// Postcondition: vectors' = vectors + v
VecVarExpr& Bridge::addVecVarExpr(Space& s, const clang::Stmt* ast){
    VecVarExpr *v = new VecVarExpr(s,ast);
    vectors.push_back(*v);
    return *v;
}

// Add new plus expression, e, to domain
// Precondition: v1 and v2 already in vectors
// Postcondition: expressions' = expressions + e
//	where e has v1 and v2 as its arguments
VecAddExpr& Bridge::addVecAddExpr(Space& s,const clang::Stmt* ast,
					Expr& v1, Expr& v2) {

	VecAddExpr* expr = new VecAddExpr(s, ast, v1, v2);
	expressions.push_back(*expr);
	return *expr;
	
}


// Check domain for consistency
// Precondition: true
// Postcondition: return value true indicates presence of inconsistencies
// Implementation: Call Lean-specific checking code below (make virtual)
bool Bridge::isConsistent() {
    Checker* c = new Checker(*this);
    bool result = c->Check();
    delete c;
    return result;
}

vector<Space>& Bridge::getAllSpaces() {
    return spaces;
}

