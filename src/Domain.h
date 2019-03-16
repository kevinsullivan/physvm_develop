#ifndef BRIDGE_H
#define BRIDGE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "AST.h"
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

// KEVIN ADDING FOR HORIZONTAL MODULE
class VecParenExpr;

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


	// KEVIN: For new VecParenExpr horizontal module
	//
	VecParenExpr *mkVecParenExpr(Space &s, domain::VecExpr *);

	// Values
	std::vector<Vector *> &getVectors() { return vectors;  }

	// Constructed literal vector value
	//
	Vector_Lit* mkVector_Lit(Space& space, float x, float y, float z); 

	// Constructed vector from variable expression
	//
	Vector* mkVector_Var(Space& s /*coords::Vector* v, domain::VecExpr *vec*/);

	// Constructed vector from vector-valued expression
	//
	Vector_Expr* mkVector_Expr(Space& space/*, coords::Vector* v*/, domain::VecExpr *vec);

// Defs

	// Binding of identifier to contsructed vector
	//
	Vector_Def* mkVector_Def(/*ast::Vector_Def* vardecl,*/ domain::VecIdent* identifier, domain::Vector* vec);
	std::vector<Vector_Def*> &getVectorDefs() { return defs; }

// Client -- Separated from Domain
//	bool isConsistent();

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
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent {
public:
	VecIdent(Space& space) : space_(&space) {}
	Space* getSpace() const { return space_; }
	// TODO: Reconsider abstracting away of name
private:
	Space* space_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr  {
public:
    VecExpr(Space& s) : space_(s) {}
    const Space& getSpace() const;
		// virtual std::string toString() const;
	protected:
    const Space& space_;
};



class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space& s) : VecExpr(s) {}
		// virtual std::string toString() const;
	private:
};

class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space& s, domain::VecExpr *mem, domain::VecExpr *arg) : 
			domain::VecExpr(s), arg_(arg), mem_(mem) {	
	}
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();
	// virtual std::string toString() const;
	// const Space& getVecVecAddExprDefaultSpace();
private:
    domain::VecExpr* arg_;
    domain::VecExpr* mem_;
};


class VecParenExpr : public VecExpr  {
public:
		VecParenExpr(Space &s, domain::VecExpr *e) : domain::VecExpr(s), expr_(e) {}
		const domain::VecExpr* getVecExpr() const { return expr_; }
		//std::string toString() const; 
private:
		const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

/*
This is a sum type capable of representing different kinds of 
fully constructed vectors.
*/

enum VecCtorType {VEC_EXPR, VEC_LIT, /*VEC_VAR,*/ VEC_NONE } ; 

class Vector   {
public:
	Vector(const Space& s, VecCtorType tag) :
		space_(&s), tag_(tag) { 
	}
	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	//bool isVar() { return (tag_ == VEC_VAR); } -- a kind of expression
	const Space* getSpace() {return space_; }
	// virtual std::string toString() const {
private:
	const Space* space_; // TODO: INFER?
	VecCtorType tag_;
};


// Constructed literal vector value
//
// TODO: Replace float with domain::scalar
//
class Vector_Lit : public Vector {
public:
	Vector_Lit(const Space& s, float x, float y, float z) :
		Vector(s, VEC_LIT), x_(x), y_(y), z_(z) {
	}
	float getX() { return x_; }
	float getY() { return y_; }
	float getZ() { return z_; }
private:
  float x_;
  float y_;
  float z_;
};

// Constructed vector value from vector-valued expression
//
class Vector_Expr : public Vector  {
public:
	Vector_Expr(const Space& s, domain::VecExpr* e) :
		Vector(s, VEC_EXPR), expr_(e) { 
	}

	const domain::VecExpr* getVecExpr() const { return expr_; }
	std::string toString() const;
private:
	const domain::VecExpr* expr_; // vec expr from which vector is constructed
};


// TODO: This is unnecessary, as variable expressions are just expressions
// and expressions are already taken care of?
//
class Vector_Var : public Vector {
	Vector_Var() : Vector(*new Space(""), VEC_EXPR ) { 
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
	Vector_Def(domain::VecIdent* id, domain::Vector* vec): 
			id_(id), vec_(vec) {}
	const domain::Vector* getVector() const { return vec_; }
	const domain::VecIdent* getIdent() { return id_; }
	// std::string toString() const;
private:
	const VecIdent* id_;
	const Vector* vec_;
};


} // end namespace

#endif