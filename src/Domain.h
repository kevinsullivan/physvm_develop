#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "Coords.h"

#include <g3log/g3log.hpp>



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
	std::vector<Space*>& getSpaces();

// Idents

	VecIdent* mkVecIdent(Space& s);
	std::vector<VecIdent *> &getVecIdents() { return idents;  }

	// Exprs
	std::vector<VecExpr *> &getVecExprs() { return exprs;  }

	// Create a variable object in the domain 
	// Details available via externally represented backmappings
	//
	VecVarExpr* mkVecVarExpr(Space& s);

	// Create a vector-vector-add expression, mem-expr.add(arg-expr) object in domain
	// Precondition: sub-expressions mem-expr and arg-expr are already in domain
	//
	VecVecAddExpr* mkVecVecAddExpr(Space& s, domain::VecExpr* , domain::VecExpr* right_);

// Values
	std::vector<Vector *> &getVectors() { return vectors;  }

	// Constructed literal vector value
	//
	Vector_Lit* mkVector_Lit(Space& space);

	// Constructed vector from variable expression
	//
	Vector* mkVector_Var(Space& s /*coords::Vector* v, domain::VecExpr *vec*/);

	// Constructed vector from vector-valued expression
	//
	Vector_Expr* mkVector_Expr(Space& space/*, coords::Vector* v*/, domain::VecExpr *vec);

// Defs

	// Binding of identifier to contsructed vector
	//
	Vector_Def* mkVector_Def(/*ast::Vector_Def* vardecl,*/ domain::VecIdent* identifier, domain::VecExpr* expression);
	std::vector<Vector_Def*> &getVectorDefs() { return defs; }

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
	std::vector<Vector*> vectors;
	std::vector<Vector_Def*> defs;
};
	
/*
Named space. Later on this will become a full-fledged Euclidean space object.
*/
class Space {
public:
	Space() : name_("") {};
	Space(std::string name) : name_(name) {};
	std::string getName() const;
	std::string toString() const {
		return getName(); 
	}
  private:
	std::string name_;
};


/*
Superclass implementing core of backmapping from domain
objects to their coordinates. It should be an injection.

class ToCoords {
public:
	ToCoords(coords::Coords *c) : coords_(c) {}
	coords::Coords* getBaseCoords() const { return coords_; }
private:
	coords::Coords* coords_;
};
*/


/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent {
public:
	VecIdent(Space& space) : space_(&space) {}
	Space* getSpace() const { return space_; }
/*
	coor	std::vector<Vector_Def*> defs;
ds::VecIdent* getCoords() const { 
		return static_cast<coords::VecIdent*>(getBaseCoords()); // TODO: accessor
	}

	std::string toString() const { return getName(); }
	std::string getName() const;
*/
private:
	Space* space_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr  {
public:
    VecExpr(Space& s) : space_(s) {}
    const Space& getSpace() const;
/*	virtual std::string toString() const {
		if (getCoords()  != NULL) {
			//LOG(DEBUG) <<"Domain::VecExpr::toString: coords::VecVecExpr pointer is " << std::hex << ast_ << "\n";
			return "(" + getCoords()->toString() + " : " + space_.getName() + ")";
		}
		else {
			return "domain.VecExpr:toString() NULL ast_\n";	
		}
	}
*/
protected:
    const Space& space_;
};


// No need for this in current implementation
// class VecLitExpr : public VecExpr {};


class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space& s) : VecExpr(s) {}
/*
	virtual std::string toString() const {
		return "(" + getCoords()->toString() + " )";
	}

	coords::VecVarExpr* getCoords() const {
		return static_cast<coords::VecVarExpr*>(getBaseCoords());	// from VecExpr superclass
	}
*/
private:
};

// TODO replace direct access to coords_ with use of accessor throughout
//
class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space& s, domain::VecExpr *mem, domain::VecExpr *arg) : 
			domain::VecExpr(s), arg_(arg), mem_(mem) {	
	}
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();

/*	coords::VecVecAddExpr* getCoords() {
		return static_cast<coords::VecVecAddExpr*>(getBaseCoords());	// from VecExpr superclass
	}

	virtual std::string toString() const {
		return "(add " + mem_->toString() + " " + arg_->toString() + ")";
	}
*/
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

// Superclass for construced vector values
//
class Vector   {
public:
	Vector(const Space& s, VecCtorType tag) :
		space_(&s), tag_(tag) { 
	}
	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	bool isVar() { return (tag_ == VEC_VAR); } 
	const Space* getSpace() {return space_; }

/*
	// TODO: Consider subclass discriminator?
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector*>(getBaseCoords()); 
	} 
	virtual std::string toString() const {
		return "domain::Vector::toString: Error. Should not be called. Abstract.\n";
	}
*/
private:
	const Space* space_; // INFER?
	VecCtorType tag_;
};



// Constructed literal vector value
//
class Vector_Lit : public Vector {
public:
	Vector_Lit(const Space& s) :
		Vector(s, VEC_LIT) { 
	}
/*
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector_Lit*>(getBaseCoords()); 
	} 

	std::string toString() const {
		return "domain::Vector_Lit::toString: STUB.\n";
	}
*/
};



/*
Todo: Domain vector constructed from domain vector expression 
*/
// Constructed vector value from vector-valued expression
//
class Vector_Expr : public Vector  {
public:
	Vector_Expr(const Space& s, domain::VecExpr* e) :
		Vector(s, VEC_EXPR), expr_(e) { 
	}
	const domain::VecExpr* getVecExpr() const { return expr_; }
/*
	coords::Vector* getCoords() const {
		return static_cast<coords::Vector_Expr*>(getBaseCoords()); 
	} 
	std::string toString() const {
		return expr_->toString();
	}
*/
private:
	const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

// Constructed vector from vector-valued variable expression
//
class Vector_Var : public Vector {
	Vector_Var() : Vector(*new Space(""), VEC_NONE ) { 
		LOG(DEBUG) <<"Domain::Vector_Var::Vector_Var: Error. Not implemented.\n";
	}
};

/*
Domain representation of binding of identifier to expression.
Takes clang::VarDecl establishing binding (in a wrapper) and 
the *domain* VecIdent and Expression objects being bound.
*/
class Vector_Def  {
public:
	Vector_Def(domain::VecIdent* identifier, domain::VecExpr* expr): 
			identifier_(identifier), expr_(expr) {}
	//const coords::Vector_Def* getVarDecl() const {return ast_wrapper_; } 
	const domain::VecExpr* getVecExpr() const { return expr_; }
	const domain::VecIdent* getVecIdent() { return identifier_; }
/*
	coords::Vector_Def* getCoords() const {
		return static_cast<coords::Vector_Def*>(getBaseCoords()); 
	} 
	std::string toString() const {
		return "def " + identifier_->toString() + " := " + expr_->toString();
	}
*/
private:
	// TODO: Inconsistency: Ref by coords here, to domain objs above
	//const coords::Vector_Def* ast_wrapper_;
	const VecIdent* identifier_;
	const VecExpr* expr_;
};


} // end namespace

#endif