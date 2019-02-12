#ifndef domain_H
#define domain_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "CodeCoords.h"

using namespace std;

namespace domain {
	
/*
Named space. Later on this will become a full-fledged Euclidean space object.
*/
class Space {
public:
	Space() : name_("") {};
	Space(string name) : name_(name) {};
	string getName() const;
	string toString() const { return getName(); } 
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
	Identifier(Space& space, const coords::IdentifierASTNode* vardecl) : space_(&space), vardecl_(vardecl) {}
	Space* getSpace() const { return space_; }
	const coords::IdentifierASTNode* getVarDeclWrapper() const { return vardecl_; }
	string toString() const { return getName(); }
	string getName() const;
private:
	Space* space_;
	const coords::IdentifierASTNode* vardecl_;
};

// TODO - Change name of this class? DomainExpr?
class Expr {
public:
    Expr(const Space& s, const coords::ExprASTNode* ast) : space_(s), ast_(ast) {}
	const coords::ExprASTNode* getExprASTNode() const { return ast_; }
    const Space& getSpace() const;
	virtual string toString() const {
		if (ast_ != NULL) {
			//cerr << "Domain::Expr::toString: coords::ExprASTNode pointer is " << std::hex << ast_ << "\n";
			return "(" + ast_->toString() + " : " + space_.getName() + ")";
		}
		else {
			return "domain.Expr:toString() NULL ast_\n";	
		}
	}
protected:
    const Space& space_;
	const coords::ExprASTNode* ast_;
};


class VecLitExpr : public Expr {
public:
    VecLitExpr(Space& s, const coords::LitASTNode* ast) : Expr(s, ast) { }
    void addFloatLit(float num);
	virtual string toString() const {
		return "(" + ast_->toString() + " : " + getSpace().toString() + ")";
	}
private:
};


/*
BIG TODO : Have Domain objects connect back to ast ***containers***, as in VecLitExpr here.
*/
// Note: No printing of space, as it's inferred
class VecVarExpr : public Expr {
public:
    VecVarExpr(Space& s, const coords::ExprASTNode* ast) : domain::Expr(s, ast) {}
	virtual string toString() const {
		return "(" + ast_->toString() + " )";
	}
private:
};


class VecAddExpr : public Expr {
public:
   VecAddExpr(
        Space& s, 
        const coords::ExprASTNode* ast,
        const Expr& arg_left,
        const Expr& arg_right
        ) : Expr(s, ast), arg_left_(arg_left), arg_right_(arg_right) {	
	}

	const Expr& getVecAddExprArgL();
	const Expr& getVecAddExprArgR();

	virtual string toString() const {
		return "(add " + arg_left_.toString() + " " + arg_right_.toString() + ")";
	}

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
	Binding(const BindingASTNode* ast_wrapper, const domain::Identifier* identifier, const domain::Expr* expr):
			ast_wrapper_(ast_wrapper), identifier_(identifier), expr_(expr) {}
	const BindingASTNode* getVarDecl() const {return ast_wrapper_; } 
	const domain::Expr* getDomExpr() const { return expr_; }
	const domain::Identifier* getIdentifier() { return identifier_; }
	string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
	const BindingASTNode* ast_wrapper_;
	const Identifier* identifier_;
	const Expr* expr_;
};

/*
A Domain is a lifted version of selected code represented as a collection 
of C++ objects. It should be isomorphic to the dom, and dom models 
(e.g., in Lean) should be producible using a Domain as an input.
*/

// Definition for Domain class 

class Domain {
public:
	Space& addSpace(const string& name);
	//VecLitExpr& addLitExpr(Space& s, const coords::LitASTNode* ast);		/* BIG TODO: Fix others */
	Identifier* addIdentifier(Space& s, const coords::IdentifierASTNode* ast);
	Expr& addVecVarExpr(const VarDeclRefASTNode* ast);
	Expr* addVecLitExpr(Space& s, const coords::LitASTNode* e);
	Expr& addVecAddExpr(Space& s, VectorAddExprASTNode* e, const dom::Expr& left_, const domain:: Expr& right_);
	Binding& addBinding(const BindingASTNode* vardecl, const Identifier* identifier, const Expr* expression);
	void dump() {
		cerr << "Domain expressions:\n";
		dumpExpressions(); // print contents on cerr
		cerr << "Domain Identifiers\n";
		dumpIdentifiers(); // print contents on cerr
		cerr << "Domain Bindings\n";
		dumpBindings(); // print contents on cerr
	}
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