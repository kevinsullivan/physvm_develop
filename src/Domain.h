#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "Coords.h"

//using namespace std;

/*
- Space
- Ident
- Expr
- Value
- Defn
*/

namespace domain {


// 
class Space;

// Ident
class VecIdent;
// Expr
class VecExpr;
class VecLitExpr;
class VecVarExpr;
class VecVecAddExpr;
// Value
class Vector;
class Vector_Lit;
class Vector_Expr;
class Vector_Var;
// Def
class VecDef;

// Definition for Domain class 

class Domain {
public:
// Space
	Space& mkSpace(const std::string& name);
	std::vector<Space>& getAllSpaces();

// Idents
	VecIdent* mkVecIdent(Space& s, const coords::VecIdent* ast);
	VecExpr* mkVecVarExpr(Space& s, const coords::VecVarExpr* ast);


// Exprs
	VecExpr* mkVecLitExpr(Space& s, const coords::VecLitExpr* e);
	VecExpr* mkVecVarExpr(Space& s, const coords::VecLitExpr* e);		-- KEVIN
	VecExpr* mkVecVecAddExpr(Space& s, coords::VecVecAddExpr* e, domain::VecExpr* left_, domain::VecExpr* right_);

// Values

	Vector* mkVector_Lit(coords::Vector* v/*, domain::VecExpr *vec*/);
	//Vector* mkVector_Var(coords::Vector* v/*, domain::VecExpr *vec*/);
	Vector* mkVector_Expr(coords::Vector* v, domain::VecExpr *vec);

// Defs
	VecDef& mkVecDef(const coords::VecDef* vardecl, const VecIdent* identifier, const VecExpr* expression);


// Client
	bool isConsistent();

// Details
	void dump();
	void dumpExpressions(); // print contents on std::cerr
	void dumpVecIdents(); // print contents on std::cerr
	void dumpVecDefs(); // print contents on std::cerr

private:
	std::vector<Space> spaces;
	std::vector<VecIdent> idents;
	std::vector<VecExpr*> exprs;
	std::vector<VecDef> defs;
	std::vector<Vector*> vectors;
};
	
/*
Named space. Later on this will become a full-fledged Euclidean space object.
*/
class Space {
public:
	Space() : name_("") {};
	Space(std::string name) : name_(name) {};
	std::string getName() const;
	std::string toString() const { return getName(); } 
private:
	std::string name_;
};


/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent {
public:
	VecIdent(Space& space, const coords::VecIdent* vardecl) : space_(&space), vardecl_(vardecl) {}
	Space* getSpace() const { return space_; }
	const coords::VecIdent* getVarDeclWrapper() const { return vardecl_; }
	std::string toString() const { return getName(); }
	std::string getName() const;
private:
	Space* space_;
	const coords::VecIdent* vardecl_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr {
public:
    VecExpr(const Space& s, const coords::VecExpr* ast) : space_(s), ast_(ast) {}
	const coords::VecExpr* getVecExpr() const { return ast_; }
    const Space& getSpace() const;
	virtual std::string toString() const {
		if (ast_ != NULL) {
			//std::cerr << "Domain::VecExpr::toString: coords::VecVecExpr pointer is " << std::hex << ast_ << "\n";
			return "(" + ast_->toString() + " : " + space_.getName() + ")";
		}
		else {
			return "domain.VecExpr:toString() NULL ast_\n";	
		}
	}
	const coords::VecExpr* getCoords() {
		return ast_;
	}
protected:
    const Space& space_;
	const coords::VecExpr* ast_;	// TODO: Call it coords_
};


// VecExpr?? It's a Ctor
class VecLitExpr : public VecExpr {
public:
    VecLitExpr(Space& s, const coords::VecLitExpr* ast) : VecExpr(s, ast) { }
    void addFloatLit(float num);
	virtual std::string toString() const {
		return "(" + ast_->toString() + " : " + getSpace().toString() + ")";
	}
private:
};


/*
BIG TODO : Have Domain objects connect back to ast ***containers***, as in VecLitExpr here.
*/
// Note: No printing of space, as it's inferred
class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space& s, const coords::VecExpr* ast) : domain::VecExpr(s, ast) {}
	virtual std::string toString() const {
		return "(" + ast_->toString() + " )";
	}
private:
};


class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space& s, const coords::VecExpr* ast, VecExpr *mem, VecExpr *arg) : 
			VecExpr(s, ast), arg_(arg), mem_(mem) {	
	}

	const VecExpr& getMemberVecExpr();
	const VecExpr& getArgVecExpr();

	virtual std::string toString() const {
		return "(add " + mem_->toString() + " " + arg_->toString() + ")";
	}

	// get the default space for this VecAddVecExpr using the space of the arg_left_
	//const Space& getVecVecAddExprDefaultSpace();
private:
    VecExpr* arg_;
    VecExpr* mem_;
};

/*
This is a sum type capable of representing different kinds of fully constructed vectors.
*/
class Vector  {
public:
	Vector(const Space& s, const coords::Vector* coords, VecCtorType tag) :
		space_(&s), coords_(coords), tag_(tag) { 
	}
	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	bool isVar { return (tag_ == VEC_EXPR); } 
	const Space* getSpace() {return space_; }
	const coords::Vector* getCoords() const {return coords_; } 

	// precondition tag_ == VEC_EXPR
	const domain::VecExpr* getVecExpr() const { 
		if (tag_ != VEC_EXPR) {
			std::cerr << "domain::Vector::getVecExpr: Error. Wrong union discriminator.\n";
		}
		return expr_; }

	virtual std::string toString() const {
		return "domain::Vector::toString: Error. Should not be called. Abstract.\n";
	}
private:
	const Space* space_; // INFER?
	const coords::Vector* coords_; 
	const domain::VecExpr* expr_; // only valid if tag_ == VEC_EXPR
	VecCtorType tag_;
};



class Vector_Lit : public Vector {
public:
	Vector_Lit(const Space& s, const coords::Vector* coords) :
		space_(&s), coords_(coords), tag_(VEC_LIT) { 
	}
	std::string toString() const {
		return "domain::Vector_Lit::toString: STUB.\n";
	}
};



/*
Todo: Rename to reflect
*/
class Vector_Expr : public Vector  {
public:
	Vector_Expr(const Space& s, const coords::Vector* coords, domain::VecExpr* expr) :
		space_(&s), coords_(coords), tag_(VEC_EXPR), expr_(expr) { 
	}
	const domain::VecExpr* getVecExpr() const { return expr_; }
	std::string toString() const {
		return expr_->toString();
	}
private:
	const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

/*
Future?

class Vector_Var : public Vector {
public:
	Vector_Var(const Space& s, const coords::Vector* coords, domain::VecVarExpr* expr) :
		space_(&s), coords_(coords), expr_(expr), tag_(VEC_VAR) { 
	}
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	bool isLit() { return (tag_ == VEC_LIT); } 
	const Space* getSpace() {return space_; }
	//
	// TODO: Normalize coords out of this class
	//
	const coords::Vector* getCoords() const {return coords_; } 
	const domain::VecExpr* getVecExpr() const { return expr_; }

	std::string toString() const {
		return expr_->toString();
	}
private:
	const Space* space_; // INFER?
	const coords::Vector* coords_; 
	const domain::VecExpr* expr_; // child
	VecCtorType tag_;
};
*/

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* VecIdent and Expression objects being bound.
*/
class VecDef {
public:
	VecDef(const coords::VecDef* ast_wrapper, const domain::VecIdent* identifier, const domain::VecExpr* expr):
			ast_wrapper_(ast_wrapper), identifier_(identifier), expr_(expr) {}
	const coords::VecDef* getVarDecl() const {return ast_wrapper_; } 
	const domain::VecExpr* getVecExpr() const { return expr_; }
	const domain::VecIdent* getVecIdent() { return identifier_; }
	std::string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
	const coords::VecDef* ast_wrapper_;
	const VecIdent* identifier_;
	const VecExpr* expr_;
};

/*
Domain representation of binding of identifier to expression.
*/
enum VecCtorType {VEC_EXPR, VEC_LIT, VEC_VAR, VEC_NONE } ; 




/*
A Domain is a lifted version of selected code represented as a collection 
of C++ objects. It should be isomorphic to the domain, and domain models 
(e.g., in Lean) should be producible using a Domain as an input.
*/



} // end namespace

#endif