#ifndef BRIDGE_H
#define BRIDGE_H

#ifndef leanInferenceWildcard
#define leanInferenceWildcard "_"
#endif

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>

#include "AST.h"
#include "Coords.h"

//#include <g3log/g3log.hpp>


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

class FloatIdent;
class FloatExpr;
//class VecLitExpr;
class VecVarExpr;
class VecVecAddExpr;

class VecScalarMulExpr;
class FloatVarExpr;

// KEVIN ADDING FOR HORIZONTAL MODULE
class VecParenExpr;

class FloatParenExpr;

class Vector;
class Vector_Lit;
class Vector_Expr;
class Vector_Var;
class Vector_Def;

class Float;
class Float_Lit;
class Float_Expr;
class Float_Var;
class Float_Def;




// Definition for Domain class 

class Domain {
public:
// Space
	Space& mkSpace(const std::string& name);
	std::vector<Space*>& getSpaces();

// Idents

	VecIdent* mkVecIdent(Space* s);
	VecIdent* mkVecIdent();
	std::vector<VecIdent *> &getVecIdents() { return idents;  }

	// Exprs
	std::vector<VecExpr *> &getVecExprs() { return exprs;  }

	FloatIdent* mkFloatIdent(Space* s);
	FloatIdent* mkFloatIdent();
	std::vector<FloatIdent*> &getFloatIdents() { return float_idents; }

	FloatExpr* mkFloatExpr(Space* s);
	FloatExpr* mkFloatExpr();
	std::vector<FloatExpr *> &getFloatExprs() { return float_exprs; }

	// Create a variable object in the domain 

	// Details available via externally represented backmappings
	//
	VecVarExpr* mkVecVarExpr(Space* s);
	VecVarExpr* mkVecVarExpr();

	FloatVarExpr* mkFloatVarExpr(Space* s);
	FloatVarExpr* mkFloatVarExpr();

	// Create a vector-vector-add expression, mem-expr.add(arg-expr) object in domain
	// Precondition: sub-expressions mem-expr and arg-expr are already in domain
	//
	VecVecAddExpr* mkVecVecAddExpr(Space* s, domain::VecExpr* left_, domain::VecExpr* right_);
	VecVecAddExpr* mkVecVecAddExpr(domain::VecExpr* left_, domain::VecExpr* right_);

	VecScalarMulExpr* mkVecScalarMulExpr(Space* s, domain::FloatExpr* flt_, domain::VecExpr* vec_);
	VecScalarMulExpr* mkVecScalarMulExpr(domain::Float_Expr* flt_, domain::VecExpr* vec_);

	// KEVIN: For new VecParenExpr horizontal module
	//
	VecParenExpr* mkVecParenExpr(Space *s, domain::VecExpr *);
	VecParenExpr* mkVecParenExpr(domain::VecExpr*);

	// Values
	std::vector<Vector *> &getVectors() { return vectors;  }

	// Constructed literal vector value
	//
	Vector_Lit* mkVector_Lit(Space* space, float x, float y, float z); 
	Vector_Lit* mkVector_Lit(float x, float y, float z);

	// Constructed vector from variable expression
	//
	Vector* mkVector_Var(Space* s /*coords::Vector* v, domain::VecExpr *vec*/);
	Vector* mkVector_Var();

	// Constructed vector from vector-valued expression
	//
	Vector_Expr* mkVector_Expr(Space* space/*, coords::Vector* v*/, domain::VecExpr *vec);
	Vector_Expr* mkVector_Expr(domain::VecExpr *vec);

	std::vector<Float *> &getFloats() { return floats; }


	Float_Lit* mkFloat_Lit(Space* space, float scalar);
	Float_Lit* mkFloat_Lit(float scalar);

	Float* mkFloat_Var(Space* s);
	Float* mkFloat_Var();

	Float_Expr* mkFloat_Expr(Space* space, domain::FloatExpr *vec);
	Float_Expr* mkFloat_Expr(domain::FloatExpr *vec);


// Defs

	// Binding of identifier to contsructed vector
	//
	Vector_Def* mkVector_Def(/*ast::Vector_Def* vardecl,*/ domain::VecIdent* identifier, domain::Vector* vec);
	std::vector<Vector_Def*> &getVectorDefs() { return defs; }


	Float_Def* mkFloat_Def(domain::FloatIdent* identifier, domain::Float* vec);
	std::vector<Float_Def*> &getFloatDefs() { return float_defs; }

// Client -- Separated from Domain
//	bool isConsistent();
private:
	std::vector<Space*> spaces;
	std::vector<VecIdent*> idents;
	std::vector<VecExpr*> exprs;
	std::vector<FloatIdent*> float_idents;
	std::vector<FloatExpr*> float_exprs;
	std::vector<Vector*> vectors;
	std::vector<Vector_Def*> defs;
	std::vector<Float*> floats;
	std::vector<Float_Def*> float_defs;
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

union SpaceContainer{
		SpaceContainer() { setDefault(); }//this->inferenceSymbol = leanInferenceWildcard; }
		~SpaceContainer(){
			space = nullptr;
			inferenceSymbol = nullptr;
		}
    domain::Space* space;
    std::string* inferenceSymbol;

		void setDefault(){
			//this->space = nullptr;
			this->inferenceSymbol = new std::string("_");
		}

		void setSpace(Space* space){
			if(space){
				this->space = space;
			}
			else{
				this->inferenceSymbol = new std::string("_");
			}
		}

		std::string toString(){
			if (*this->inferenceSymbol == "_"){
				return *this->inferenceSymbol;
			}
			else{
				return this->space->toString();
			}
		}
};



/*
The next set of definitions provides a basis for representing code 
expressions lifted to domain expressions.
*/

class VecIdent {
public:
	VecIdent(Space& space) : space_(&space) {}
	VecIdent() { this->spaceContainer_ = new SpaceContainer(); }// this->spaceContainer_-> }
	Space* getSpace() const { return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }

	void setSpace(Space* space);
	// TODO: Reconsider abstracting away of name
private:
	Space* space_;
	SpaceContainer* spaceContainer_;
};

// TODO - Change name of this class? DomainExpr?
class VecExpr  {
public:
    VecExpr(Space* s) : space_(s) {}
		VecExpr() { this->spaceContainer_ = new SpaceContainer(); }
    Space* getSpace() const { return space_; };
		SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
		void setSpace(Space* s);
		// virtual std::string toString() const;
	protected:
    Space* space_;
		SpaceContainer* spaceContainer_;
};

class FloatIdent {
public:
	FloatIdent(Space& space) : space_(&space) {}
	FloatIdent() { this->spaceContainer_ = new SpaceContainer(); }// this->spaceContainer_-> }
	Space* getSpace() const { return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }

	void setSpace(Space* space);
	// TODO: Reconsider abstracting away of name
private:
	Space* space_;
	SpaceContainer* spaceContainer_;
};

class FloatExpr {
public:
	FloatExpr(Space* s) : space_(s) {}
	FloatExpr() { this->spaceContainer_ = new SpaceContainer(); }
	Space* getSpace() const { return space_; };
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
	void setSpace(Space* s);

	protected:
		Space* space_;
		SpaceContainer* spaceContainer_;
};



class VecVarExpr : public VecExpr {
public:
    VecVarExpr(Space* s) : VecExpr(s) {}
		VecVarExpr() : VecExpr() {}
		// virtual std::string toString() const;
	private:
};

class FloatVarExpr : public FloatExpr {
public:
    FloatVarExpr(Space* s) : FloatExpr(s) {}
		FloatVarExpr() : FloatExpr() {}
		// virtual std::string toString() const;
	private:
};

class VecVecAddExpr : public VecExpr {
public:
   VecVecAddExpr(
        Space* s, domain::VecExpr *mem, domain::VecExpr *arg) : 
			domain::VecExpr(s), arg_(arg), mem_(mem) {	}
	 VecVecAddExpr(domain::VecExpr *mem, domain::VecExpr *arg) :
	 		domain::VecExpr(), arg_(arg), mem_(mem) { }
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();
	// virtual std::string toString() const;
	// const Space& getVecVecAddExprDefaultSpace();
private:
    domain::VecExpr* arg_;
    domain::VecExpr* mem_;
};

class VecScalarMulExpr : public VecExpr {
	VecScalarMulExpr(
		Space* s, domain::VecExpr *vec, domain::FloatExpr *flt) :
			domain::VecExpr(), vec_(vec), flt_(flt) {	}
	VecScalarMulExpr(
		domain::VecExpr *vec, domain::FloatExpr *flt) :
			domain::VecExpr(), vec_(vec), flt_(flt) {	}
	private:
		domain::VecExpr* vec_;
		domain::FloatExpr* flt_;

};


class FloatParenExpr : public FloatExpr  {
public:
		FloatParenExpr(Space *s, domain::FloatExpr *e) : domain::FloatExpr(s), expr_(e) {}
		FloatParenExpr(domain::FloatExpr *e) : domain::FloatExpr(), expr_(e) {}
		const domain::FloatExpr* getFloatExpr() const { return expr_; }
		//std::string toString() const; 
private:
		const domain::FloatExpr* expr_; // vec expr from which vector is constructed
};


class VecParenExpr : public VecExpr  {
public:
		VecParenExpr(Space *s, domain::VecExpr *e) : domain::VecExpr(s), expr_(e) {}
		VecParenExpr(domain::VecExpr *e) : domain::VecExpr(), expr_(e) {}
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
		space_(&s), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }
	Vector(VecCtorType tag) : space_(nullptr), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }

	bool isLit() { return (tag_ == VEC_LIT); } 
	bool isExpr() { return (tag_ == VEC_EXPR); } 
	//bool isVar() { return (tag_ == VEC_VAR); } -- a kind of expression
	const Space* getSpace() {return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
	void setSpace(Space* space);
	// virtual std::string toString() const {
private:
	const Space* space_; // TODO: INFER?
	SpaceContainer* spaceContainer_;
	VecCtorType tag_;
};

enum FloatCtorType {FLOAT_EXPR, FLOAT_LIT, /*VEC_VAR,*/ FLOAT_NONE } ; 
class Float{
public:
	Float(const Space& s, FloatCtorType tag) :
		space_(&s), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }
	Float(FloatCtorType tag) : space_(nullptr), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }

	bool isLit() { return (tag_ == FLOAT_LIT); } 
	bool isExpr() { return (tag_ == FLOAT_EXPR); } 
	//bool isVar() { return (tag_ == VEC_VAR); } -- a kind of expression
	const Space* getSpace() {return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
	void setSpace(Space* space);
	// virtual std::string toString() const {
private:
	const Space* space_; // TODO: INFER?
	SpaceContainer* spaceContainer_;
	FloatCtorType tag_;
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

	Vector_Lit(float x, float y, float z) : Vector(VEC_LIT), x_(x), y_(y), z_(z) {}

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

	Vector_Expr(domain::VecExpr* e) : Vector(VEC_EXPR) {}

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
		//LOG(DEBUG) <<"Domain::Vector_Var::Vector_Var: Error. Not implemented.\n";
	}
};

class Float_Lit : public Float {
public:
	Float_Lit(const Space& s, float scalar) :
		Float(s, FLOAT_LIT), scalar_(scalar) {
	}

	Float_Lit(float scalar) : Float(FLOAT_LIT), scalar_(scalar){}

	float getScalar() { return scalar_; }
private:
  float scalar_;
};

// Constructed vector value from vector-valued expression
//
class Float_Expr : public Float  {
public:
	Float_Expr(const Space& s, domain::FloatExpr* e) :
		Float(s, FLOAT_EXPR), expr_(e) { 
	}

	Float_Expr(domain::FloatExpr* e) : Float(FLOAT_EXPR) {}

	const domain::FloatExpr* getFloatExpr() const { return expr_; }
	std::string toString() const;
private:
	const domain::FloatExpr* expr_; // vec expr from which vector is constructed
};

class Float_Var : public Float {
	Float_Var() : Float(*new Space(""), FLOAT_EXPR ) { 
		//LOG(DEBUG) <<"Domain::Vector_Var::Vector_Var: Error. Not implemented.\n";
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


class Float_Def  {
public:
	Float_Def(domain::FloatIdent* id, domain::Float* flt): 
			id_(id), flt_(flt) {}
	const domain::Float* getFloat() const { return flt_; }
	const domain::FloatIdent* getIdent() { return id_; }
	// std::string toString() const;
private:
	const FloatIdent* id_;
	const Float* flt_;
};




} // end namespace

#endif