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
//class VecLitExpr;
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
	VecIdent* mkVecIdent(Space& s, coords::VecIdent* ast);

// Exprs
//	VecExpr* mkVecLitExpr(Space& s, const coords::VecLitExpr* e);
	VecVarExpr* mkVecVarExpr(Space& s, coords::VecVarExpr* ast);
	VecVecAddExpr* mkVecVecAddExpr(Space& s, coords::VecVecAddExpr* e, coords::VecExpr* left_, coords::VecExpr* right_);

// Values

	Vector_Lit* mkVector_Lit(Space& space, coords::Vector* v/*, domain::VecExpr *vec*/);
	//Vector* mkVector_Var(coords::Vector* v/*, domain::VecExpr *vec*/);
	Vector_Expr* mkVector_Expr(Space& space, coords::Vector* v, coords::VecExpr *vec);

// Defs
	Vector_Def* mkVector_Def(coords::Vector_Def* vardecl, coords::VecIdent* identifier, coords::VecExpr* expression);


// Client
	bool isConsistent();

// Details
	void dump();
	void dumpExpressions(); // print contents on std::cerr
	void dumpVecIdents(); // print contents on std::cerr
	void dumpVector_Defs(); // print contents on std::cerr

private:
	std::vector<Space*> spaces;
	std::vector<VecIdent*> idents;
	std::vector<VecExpr*> exprs;
	std::vector<Vector_Def*> defs;
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
	ToCoords(coords::Coords *c) : coords_(c) {}
	coords::Coords* getBaseCoords() const { return coords_; }
private:
	coords::Coords* coords_;
};
/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent : public ToCoords {
public:
	VecIdent(Space& space, coords::VecIdent* c) : ToCoords(c), space_(&space) {}
	Space* getSpace() const { return space_; }
	coords::VecIdent* getCoords() const { 
		return static_cast<coords::VecIdent*>(getBaseCoords()); // TODO: accessor
	}
	std::string toString() const { return getName(); }
	std::string getName() const;
private:
	Space* space_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr  : public ToCoords {
public:
    VecExpr(const Space& s, coords::VecExpr* c) : ToCoords(c), space_(s) {}
	coords::VecExpr* getCoords() const { 
		return static_cast<coords::VecExpr*>(getBaseCoords());
	}
    const Space& getSpace() const;
	virtual std::string toString() const {
		if (getCoords()  != NULL) {
			//std::cerr << "Domain::VecExpr::toString: coords::VecVecExpr pointer is " << std::hex << ast_ << "\n";
			return "(" + getCoords()->toString() + " : " + space_.getName() + ")";
		}
		else {
			return "domain.VecExpr:toString() NULL ast_\n";	
		}
	}
protected:
    const Space& space_;
};


// No need for this in current implementation
// class VecLitExpr : public VecExpr {};


class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space& s, coords::VecVarExpr* c) : domain::VecExpr(s, c) {}
	virtual std::string toString() const {
		return "(" + getCoords()->toString() + " )";
	}
	coords::VecVarExpr* getCoords() const {
		return static_cast<coords::VecVarExpr*>(getBaseCoords());	// from VecExpr superclass
	}
private:
};

// TODO replace direct access to coords_ with use of accessor throughout
//
class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space& s, coords::VecVecAddExpr* c, domain::VecExpr *mem, domain::VecExpr *arg) : 
			domain::VecExpr(s, c), arg_(arg), mem_(mem) {	
	}
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();

	coords::VecVecAddExpr* getCoords() {
		return static_cast<coords::VecVecAddExpr*>(getBaseCoords());	// from VecExpr superclass
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

enum VecCtorType {VEC_EXPR, VEC_LIT, VEC_VAR, VEC_NONE } ; 


class Vector : public ToCoords   {
public:
	Vector(const Space& s, coords::Vector* c, VecCtorType tag) :
		ToCoords(c), space_(&s), tag_(tag) { 
	}
	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	bool isVar() { return (tag_ == VEC_VAR); } 
	const Space* getSpace() {return space_; }

	// TODO: Consider subclass discriminator?
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector*>(getBaseCoords()); 
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
	Vector_Lit(const Space& s, coords::Vector* c) :
		Vector(s, c, VEC_LIT) { 
	}
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector_Lit*>(getBaseCoords()); 
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
	Vector_Expr(const Space& s, coords::Vector* c, domain::VecExpr* e) :
		Vector(s, c, VEC_EXPR), expr_(e) { 
	}
	const domain::VecExpr* getVecExpr() const { return expr_; }
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector_Expr*>(getBaseCoords()); 
	} 
	std::string toString() const {
		return expr_->toString();
	}
private:
	const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

// Future
class Vector_Var : public Vector {
	Vector_Var() : Vector(*new Space(""), NULL, VEC_NONE ) { 
		std::cerr << "Domain::Vector_Var::Vector_Var: Error. Not implemented.\n";
	}
};

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* VecIdent and Expression objects being bound.
*/
class Vector_Def : public ToCoords  {
public:
	Vector_Def(coords::Vector_Def* c, domain::VecIdent* identifier, domain::VecExpr* expr):
			ToCoords(c), identifier_(identifier), expr_(expr) {}
	//const coords::Vector_Def* getVarDecl() const {return ast_wrapper_; } 
	const domain::VecExpr* getVecExpr() const { return expr_; }
	const domain::VecIdent* getVecIdent() { return identifier_; }
	coords::Vector_Def* getCoords() const {
		return static_cast<coords::Vector_Def*>(getBaseCoords()); 
	} 
	std::string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
private:
	// TODO: Inconsistency: Ref by coords here, to domain objs above
	//const coords::Vector_Def* ast_wrapper_;
	const VecIdent* identifier_;
	const VecExpr* expr_;
};


} // end namespace

#endif