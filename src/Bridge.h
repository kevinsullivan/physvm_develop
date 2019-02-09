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
	string getName() const;
    friend ostream & operator << (ostream &out, const Space &s)
	{ 
    out << s.getName(); 
    return out; 
	} 
private:
	string name_;
};


/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class Identifier {
public:
	Identifier(Space& space, const IdentifierASTNode* vardecl);
	Space* getSpace() { return space_; }
	string getName() const;
/*	string getNameAsString() 
	{ return vardecl_->getNameAsString(); }
*/
private:
	Space* space_;
	const IdentifierASTNode* vardecl_;
	string name_;

};

// TODO - Change name of this class? BridgeExpr?
class Expr {
public:
    Expr(const Space& s, const ExprASTNode* ast) : space_(s), ast_(ast) {}
    const Space& getSpace();
	virtual string toString() const {
		if (ast_ != NULL) {
			//cerr << "Bridge::Expr::toString: ExprASTNode pointer is " << std::hex << ast_ << "\n";
			return ast_->toString();
		}
		else {
			return "bridge.Expr:toString() NULL ast_\n";	
		}
	}
protected:
    const Space& space_;
	const ExprASTNode* ast_;
};


class VecLitExpr : public Expr {
public:
    VecLitExpr(Space& s, const LitASTNode* ast) : Expr(s, ast) { }
    void addFloatLit(float num);
private:
};


/*
BIG TODO : Have Bridge objects connect back to ast ***containers***, as in VecLitExpr here.
*/

class VecVarExpr : public Expr {
public:
    VecVarExpr(Space& s, const ExprASTNode* ast) : bridge::Expr(s, ast) {}
private:
};


class VecAddExpr : public Expr {
public:
   VecAddExpr(
        Space& s, 
        const ExprASTNode* ast,
        const Expr& arg_left,
        const Expr& arg_right
        ) : Expr(s, ast), arg_left_(arg_left), arg_right_(arg_right) {	
	}

	const Expr& getVecAddExprArgL();
	const Expr& getVecAddExprArgR();

	// get the default space for this VecAddExpr using the space of the arg_left_
	//const Space& getVecAddExprDefaultSpace();
private:
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
	Binding(BindingASTNode* ast_wrapper, const bridge::Identifier& identifier, const bridge::Expr& expr):
			ast_wrapper_(ast_wrapper), identifier_(identifier), expr_(expr) {}
	const BindingASTNode* getVarDecl() {return ast_wrapper_; } 
	const bridge::Expr& getDomExpr() { return expr_; }
	const bridge::Identifier& getIdentifier();
	string toString() const {
		return identifier_.getName() + " := " + expr_.toString();
	}
private:
	const BindingASTNode* ast_wrapper_;
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
	//VecLitExpr& addLitExpr(Space& s, const LitASTNode* ast);		/* BIG TODO: Fix others */
	Identifier& addIdentifier(Space& s, const IdentifierASTNode* ast);
	Expr& addVecVarExpr(const ExprASTNode* ast);
	Expr& addVecLitExpr(Space& s, ExprASTNode* e);
	Expr& addVecAddExpr(Space& s, ExprASTNode* e, bridge::Expr& left_, bridge:: Expr& right_);
	Binding& addBinding(BindingASTNode* vardecl, const Identifier& identifier, const Expr& expression);

	void dumpExpressions(); // print contents on cerr
	void dumpIdentifiers(); // print contents on cerr
	void dumpBindings(); // print contents on cerr

	bool isConsistent();
	vector<Space>& getAllSpaces();
private:
	vector<Space> spaces;
	vector<Identifier> identifiers;
	vector<Expr*> expressions;
	vector<Binding> bindings;
};

} // end namespace

#endif