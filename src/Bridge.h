#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
//#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <vector>
#include <string>

using namespace std;

namespace bridge {

// Definition for Space class 
class Space {
public:
	Space() : name_("") {};
	Space(string name) : name_(name) {};
	string getName();

private:
	string name_;
};


/*
Abstract superclass for augmented expressions.
*/
class Expr {
public:
    Expr(const Space& s) : space_(s) {}
    const Space& getSpace() {return space_;}
private:
    const Space& space_;
};

/*
class VecLitExpr : Expr {
public:
    VecLitExpr();
};
*/

class VecVarExpr : Expr {
public:
    VecVarExpr(Space& s, const clang::Stmt& ast) : Expr(s),space_(s), ast_(ast) {}
private:
	const Space& space_;
    const clang::Stmt& ast_;
};

class VecAddExpr : Expr {
public:
   VecAddExpr(
        Space& s, 
        const clang::Stmt& ast,
        const Expr& arg_left,
        const Expr& arg_right
        ) : Expr(s), ast_(ast), arg_left_(arg_left), arg_right_(arg_right) {}
    VecAddExpr();
private:
    const clang::Stmt& ast_;
    const Expr& arg_left_;
    const Expr& arg_right_;
};

// Definition for Domain class 
class Bridge {

public:

	// Add new space,, s, to domain
	// Precondition: true
	// Postcondition: 
	//	spaces' = spaces + s and
	//  return value = reference to s
	Space& addSpace(const string& name);

	// Add new vector, v, in space s, to domain
	// Precondition: s is already in spaces
	// Postcondition: vectors' = vectors + v
	VecVarExpr& addVecVarExpr(Space& s, const clang::Stmt& ast);

	// Add new plus expression, e, to domain
	// Precondition: v1 and v2 already in vectors
	// Postcondition: expressions' = expressions + e
	//	where e has v1 and v2 as its arguments
	VecAddExpr& addVecAddExpr(VecVarExpr& v1, VecVarExpr& v2);
	
    // TODO: Move this into separate type-checker "Client"
    // Check domain for consistency
	// Precondition: true
	// Postcondition: return value true indicates presence of inconsistencies
	bool isConsistent();

	/*
	Methods by which clients can learn what's in this domain.
	*/

private:
	vector<Space> spaces;
	vector<Expr> expressions;
};

} // end namespace

#endif