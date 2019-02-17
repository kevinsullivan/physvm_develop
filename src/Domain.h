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


class Space;
class VecIdent;
class VecExpr;
class VecLitExpr;
class VecVarExpr;
class VecVecAddExpr;
class Vector;
class Vector_Lit;
class Vector_Expr;
class Vector_Var;
class Vector_Def;

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
	VecExpr* mkVecVarExpr(Space& s, const coords::VecLitExpr* e);		// KEVIN
	VecExpr* mkVecVecAddExpr(Space& s, coords::VecVecAddExpr* e, domain::VecExpr* left_, domain::VecExpr* right_);

// Values

	Vector* mkVector_Lit(coords::Vector* v/*, domain::VecExpr *vec*/);
	//Vector* mkVector_Var(coords::Vector* v/*, domain::VecExpr *vec*/);
	Vector* mkVector_Expr(coords::Vector* v, domain::VecExpr *vec);

// Defs
	Vector_Def& mkVector_Def(const coords::Vector_Def* vardecl, const VecIdent* identifier, const VecExpr* expression);


// Client
	bool isConsistent();

// Details
	void dump();
	void dumpExpressions(); // print contents on std::cerr
	void dumpVecIdents(); // print contents on std::cerr
	void dumpVector_Defs(); // print contents on std::cerr

private:
	std::vector<Space> spaces;
	std::vector<VecIdent> idents;
	std::vector<VecExpr*> exprs;
	std::vector<Vector_Def> defs;
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
Superclass implementing core of backmapping from domain
objects to their coordinates. It should be an injection.
*/
class ToCoords {
public:
	ToCoordscoords::Coords *c) : coords_(c) {}
	coords::Coords* getBaseCoords() { return coords_; }
private:
	coords::Coords* coords_;
}
/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent : public ToCode {
public:
	VecIdent(Space& space, const coords::VecIdent* c) : ToCoords(c), space_(&space) {}
	Space* getSpace() const { return space_; }
	const coords::VecIdent* getCoords() const { 
		return static_cast<:VecIdent*>getBaseCoords(); 
	}
	std::string toString() const { return getName(); }
	std::string getName() const;
private:
	Space* space_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr  : public ToCode {
public:
    VecExpr(const Space& s, const coords::VecExpr* c) : ToCoords(c), space_(s) {}
	const coords::VecExpr* Coords() const { 
		return static_cast<:VecExpr*>getBaseCoords();
	}
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
protected:
    const Space& space_;
};


// No need for this in current implementation
class VecLitExpr : public VecExpr {}


class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space& s, const coords::VecVarExpr* c) : domain::VecExpr(s, c) {}
	virtual std::string toString() const {
		return "(" + ast_->toString() + " )";
	}
	const coords::VecVarExpr* getCoords() {
		return static_cast<VecVarExpr*>coords_;	// from VecExpr superclass
	}
private:
};


class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space& s, const coords::VecAddAddExpr* c, domain::VecExpr *mem, domain::VecExpr *arg) : 
			domain::VecExpr(s, c), arg_(arg), mem_(mem) {	
	}
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();
	const coords::VecVarExpr* getCoords() {
		return static_cast<VecVecAddExpr*>coords_;	// from VecExpr superclass
	}
	virtual std::string toString() const {
		return "(add " + mem_->toString() + " " + arg_->toString() + ")";
	}

	// get the default space for this VecAddVecExpr using the space of the arg_left_
	//const Space& getVecVecAddExprDefaultSpace();
private:
    domain::VecExpr* arg_;
    domain::VecExpr* mem_;
};

/*
This is a sum type capable of representing different kinds of fully constructed vectors.
*/
class Vector : public ToCode   {
public:
	Vector(const Space& s, const coords::Vector* coords, VecCtorType tag) :
		ToCoords(c), space_(&s), tag_(tag) { 
	}
	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	bool isVar() { return (tag_ == VEC_VAR); } 
	const Space* getSpace() {return space_; }

	// TODO: Consider subclass discriminator?
	const coords::Vector* getCoords() const {
		return static_cast<Vector*>coords_; 
	} 
	virtual std::string toString() const {
		return "domain::Vector::toString: Error. Should not be called. Abstract.\n";
	}
private:
	const Space* space_; // INFER?
	VecCtorType tag_;
};



class Vector_Lit : public Vector {
public:
	Vector_Lit(const Space& s, const coords::Vector* c) :
		Vector(s, c, VEC_LIT) { 
	}
	const coords::Vector* getCoords() const {
		return static_cast<Vector_Lit*>coords_; 
	} 

	std::string toString() const {
		return "domain::Vector_Lit::toString: STUB.\n";
	}
};



/*
Todo: Domain vector constructed from domain vector expression 
*/
class Vector_Expr : public Vector  {
public:
	Vector_Expr(const Space& s, const coords::Vector* c, domain::VecExpr* expr) :
		ToCoords(c), Vector(s, coords, VEC_EXPR), expr_(expr) { 
	}
	const domain::VecExpr* getVecExpr() const { return expr_; }
	const coords::Vector* getCoords() const {
		return static_cast<Vector_Expr*>coords_; 
	} 
	std::string toString() const {
		return expr_->toString();
	}
private:
	const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

// Future
class Vector_Var : public Vector {}

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* VecIdent and Expression objects being bound.
*/
class Vector_Def : public ToCode  {
public:
	Vector_Def(const coords::Vector_Def* c, const domain::VecIdent* identifier, const domain::VecExpr* expr):
			ToCoords(c), identifier_(identifier), expr_(expr) {}
	const coords::Vector_Def* getVarDecl() const {return ast_wrapper_; } 
	const domain::VecExpr* getVecExpr() const { return expr_; }
	const domain::VecIdent* getVecIdent() { return identifier_; }
	const coords::Vector_Def* getCoords() const {
		return static_cast<Vector_Def*>coords_; 
	} 
	std::string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
	const coords::Vector_Def* ast_wrapper_;
	// TODO: Inconsistency: Ref by coords here, to domain objs above
	const VecIdent* identifier_;
	const VecExpr* expr_;
};

/*
Domain representation of binding of identifier to expression.
*/
enum VecCtorType {VEC_EXPR, VEC_LIT, VEC_VAR, VEC_NONE } ; 


} // end namespace

#endif