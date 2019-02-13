#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "Coords.h"

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
	Identifier(Space& space, const coords::VecIdent* vardecl) : space_(&space), vardecl_(vardecl) {}
	Space* getSpace() const { return space_; }
	const coords::VecIdent* getVarDeclWrapper() const { return vardecl_; }
	string toString() const { return getName(); }
	string getName() const;
private:
	Space* space_;
	const coords::VecIdent* vardecl_;
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


// Expr?? It's a Ctor
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
        Space& s, const coords::ExprASTNode* ast, Expr *mem, Expr *arg) : 
			Expr(s, ast), arg_(arg), mem_(mem) {	
	}

	const Expr& getMemberExpr();
	const Expr& getArgExpr();

	virtual string toString() const {
		return "(add " + mem_->toString() + " " + arg_.toString() + ")";
	}

	// get the default space for this VecAddExpr using the space of the arg_left_
	//const Space& getVecAddExprDefaultSpace();
private:
    Expr* arg_left_;
    Expr* arg_right_;
};

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* Identifier and Expression objects being bound.
*/
class Binding {
public:
	Binding(const coords::BindingASTNode* ast_wrapper, const domain::Identifier* identifier, const domain::Expr* expr):
			ast_wrapper_(ast_wrapper), identifier_(identifier), expr_(expr) {}
	const coords::BindingASTNode* getVarDecl() const {return ast_wrapper_; } 
	const domain::Expr* getDomExpr() const { return expr_; }
	const domain::Identifier* getIdentifier() { return identifier_; }
	string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
	const coords::BindingASTNode* ast_wrapper_;
	const Identifier* identifier_;
	const Expr* expr_;
};

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* Identifier and Expression objects being bound.
*/

class domain::Vector  {
public:
	Vector(Space& s, const coords::AddConstructASTNode* coords, domain::Expr* expr):
		space_(&s), coords_(coords), expr_(expr) { tag_ = domain::EXPR; }
	bool isExpr() { return (tag_ == domain::EXPR); } 
	bool isLit() { return (tag_ == domain::LIT); } 
	Space* getSpace() {return space_; }
	const coords::VectorASTNode* getVector() const {return ast_wrapper_; } 
	const domain::Vector* getDomVector() const { return expr_; }
	string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
//	const Space* space_; // INFER
	const coords::AddConstructASTNode* coords_;
	const domain::VecCtorType tag_;
	const domain::Expr* expr_; // child
};

/*
A Domain is a lifted version of selected code represented as a collection 
of C++ objects. It should be isomorphic to the domain, and domain models 
(e.g., in Lean) should be producible using a Domain as an input.
*/

// Definition for Domain class 

class Domain {
public:
	Space& addSpace(const string& name);
	//VecLitExpr& addLitExpr(Space& s, const coords::coords::LitASTNode* ast);		/* BIG TODO: Fix others */
	Identifier* addIdentifier(Space& s, const coords::VecIdent* ast);
	Expr& addVecVarExpr(const coords::VarDeclRefASTNode* ast);
	// should be addVecLit*Ctor*, with contained lit data 
	Expr* addVecLitExpr(Space& s, const coords::LitASTNode* e);
	Expr* addVecAddExpr(Space& s, coords::VectorAddExprASTNode* e, domain::Expr& left_, domain::Expr& right_);
	// coords for container, domain object for child, lit | expr
	// if lit, child is -- empty? -- else coords and domain Expr
	Vector* addVector(coords VectorASTNode* v, domain::Expr *vec);
	Binding& addBinding(const coords::BindingASTNode* vardecl, const Identifier* identifier, const Expr* expression);
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
	vector<Vector*> vectors;
};

} // end namespace

#endif