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

// VecLitExpr class member function implementation
void VecLitExpr::addFloatLit(float num){
    litVal.push_back(num);
}


// VecVarExpr class member function implementation
const Space& VecVarExpr::getVecVarSpace(){ return space_;}


// VecAddExpr class member function implementation

const Expr& VecAddExpr::getVecAddExprArgL(){return arg_left_;}
const Expr& VecAddExpr::getVecAddExprArgR(){return arg_right_;}


const Space& VecAddExpr::getVecAddExprDefaultSpace(){
	return space_;
}
// Binding class member function implementation

const VecVarExpr& Binding::getIdentifier(){return identifier_;}

// LitExprBinding class member function implementation



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
    identifiers.push_back(*v);
    return *v;
}

VecLitExpr& Bridge::addVecLitExpr(Space& s){
    VecLitExpr *vle = new VecLitExpr(s);
    litexpressions.push_back(*vle);
    return *vle;
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

LitExprBinding& Bridge::addLitExprBinding(const VecVarExpr& identifier, 
                                const VecLitExpr& litexpression)
{
    LitExprBinding * bd = new LitExprBinding(identifier, litexpression);
    litbindings.push_back(*bd);
    cerr<<"Added binding for lit expression!"<<endl;
    return *bd;
}

VecAddExprBinding& Bridge::addVecAddExprBinding(const VecVarExpr& identifier, 
                                const VecAddExpr& expression)
{
    VecAddExprBinding* bd = new VecAddExprBinding(identifier,expression);
    exprbindings.push_back(* bd);
    cerr<<"Added binding for add expression!"<<endl;
    return *bd;
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

