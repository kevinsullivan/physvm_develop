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
    const Space& getSpace();
protected:
    const Space& space_;
};


class VecLitExpr : Expr {
public:
    VecLitExpr(Space& s):Expr(s){}
    void addFloatLit(float num);
private:
	std::vector<float> litVal;
	// const Space& space_;
};


class VecVarExpr : public Expr {
public:
    VecVarExpr(Space& s, const clang::Stmt* ast) : Expr(s), ast_(ast) {}
    const Space& getVecVarSpace();

private:
	// const Space& space_;
    const clang::Stmt* ast_;
};

class VecAddExpr : public Expr {
public:
   VecAddExpr(
        Space& s, 
        const clang::Stmt* ast,
        const Expr& arg_left,
        const Expr& arg_right
        ) : Expr(s), ast_(ast), arg_left_(arg_left), arg_right_(arg_right) {}
    VecAddExpr();

    // get methods for projecting two arguments
	const Expr& getVecAddExprArgL();
	const Expr& getVecAddExprArgR();

	// get the default space for this VecAddExpr using the space of the arg_left_
	const Space& getVecAddExprDefaultSpace();
private:
    const clang::Stmt* ast_;
    const Expr& arg_left_;
    const Expr& arg_right_;
};

class Binding{
public:
	Binding(const VecVarExpr& identifier):
			identifier_(identifier){}
	// Binding(const VecVarExpr& identifier): identifier_(identifier), expression_(0){}
const VecVarExpr& getIdentifier();

private:
	const VecVarExpr& identifier_;
};

class LitExprBinding:public Binding{
public:
	LitExprBinding(const VecVarExpr& vve ,
		const VecLitExpr& vle):Binding(vve),expression_(vle){}

private:
	const VecLitExpr& expression_;
};

class VecAddExprBinding:public Binding{
public:
	VecAddExprBinding(const VecVarExpr& vve, 
		const VecAddExpr& vae):Binding(vve), expression_(vae){}

private:
	const VecAddExpr& expression_;
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
	VecVarExpr& addVecVarExpr(Space& s, const clang::Stmt* ast);

	VecLitExpr& addVecLitExpr(Space& s);
	// Add new plus expression, e, to domain
	// Precondition: v1 and v2 already in vectors
	// Postcondition: expressions' = expressions + e
	//	where e has v1 and v2 as its arguments
	VecAddExpr& addVecAddExpr(Space& s,const clang::Stmt* ast,Expr& v1, Expr& v2);
	
    // TODO: Move this into separate type-checker "Client"
    // Check domain for consistency
	// Precondition: true
	// Postcondition: return value true indicates presence of inconsistencies

	LitExprBinding& addLitExprBinding(const VecVarExpr& identifier, const VecLitExpr& expression);
	VecAddExprBinding& addVecAddExprBinding(const VecVarExpr& identifier, const VecAddExpr& litexpression);

	bool isConsistent();

	/*
	Methods by which clients can learn what's in this domain.
	*/

	vector<Space>& getAllSpaces();

private:
	vector<Space> spaces;
	// lvalues
	vector<VecVarExpr> identifiers;

	// rvalues
	vector<VecLitExpr> litexpressions;
	vector<VecAddExpr> expressions;

	// bindings
	vector<LitExprBinding> litbindings;
	vector<VecAddExprBinding> exprbindings;
};

} // end namespace

#endif