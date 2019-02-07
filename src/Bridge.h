#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "CodeCoordinate.h"

using namespace std;

namespace bridge {

/*
Named space. Later on this will become a full-fledged Euclidean space object.
*/
class Space {
public:
	Space() : name_("") {};
	Space(string name) : name_(name) {};
	string getName();

private:
	string name_;
};


/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class Identifier {
public:
	Identifier(Space& space, const VarDeclASTNode* vardecl);
/*	string getNameAsString() 
	{ return vardecl_->getNameAsString(); }
*/
private:
	Space& space_;
	const VarDeclASTNode* vardecl_;
	string name_;

};

class Expr {
public:
    Expr(const Space& s) : space_(s) {}
    const Space& getSpace();
protected:
    const Space& space_;
};


class VecLitExpr : public Expr {
public:
    VecLitExpr(Space& s, const LitASTNode* ast) : space_(s), Expr(s) { ast_ = ast; }
    void addFloatLit(float num);
private:
	//std::vector<float> litVal;
	const LitASTNode* ast_;
	const Space& space_;
};


/*
BIG TODO : Have Bridge objects connect back to ast ***containers***, as in VecLitExpr here.
*/

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

	const Expr& getVecAddExprArgL();
	const Expr& getVecAddExprArgR();

	// get the default space for this VecAddExpr using the space of the arg_left_
	const Space& getVecAddExprDefaultSpace();
private:
    const clang::Stmt* ast_;
    const Expr& arg_left_;
    const Expr& arg_right_;
};

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* Identifier and Expression objects being bound.
*/
class Binding {
public:

	Binding(VarDeclASTNode* ast_wrapper, const bridge::Identifier& identifier, const bridge::Expr& expr):
			ast_wrapper_(ast_wrapper), identifier_(identifier), expr_(expr) {}
	const VarDeclASTNode* getVarDecl() {return ast_wrapper_; } 
	const bridge::Expr& getDomExpr() { return expr_; }
	const bridge::Identifier& getIdentifier();
private:
	const VarDeclASTNode* ast_wrapper_;
	const Identifier& identifier_;
	const Expr& expr_;
};

/*
A Bridge is a lifted version of selected code represented as a collection 
of C++ objects. It should be isomorphic to the domain, and domain models 
(e.g., in Lean) should be producible using a Bridge as an input.
*/

// Definition for Domain class 

class Bridge {
public:
	Space& addSpace(const string& name);
	Expr& addLitExpr(Space& s, const LitASTNode* ast);		/* BIG TODO: Fix others */
	Identifier& addIdentifier(Space& s, const VarDeclASTNode* ast);
	Expr& addVecAddExpr(
		bridge::Space&, const clang::Stmt*, const bridge::Expr&, const bridge::Expr&);
	Binding& addBinding(VarDeclASTNode* vardecl, const Identifier& identifier, const Expr& expression);
	bool isConsistent();
	vector<Space>& getAllSpaces();
private:
	vector<Space> spaces;
	vector<VecVarExpr> identifiers;
	vector<Expr> expressions;
	vector<Binding> bindings;
};

} // end namespace

#endif