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

#include <g3log/g3log.hpp>


using namespace std;

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

class ScalarIdent;
class ScalarExpr;
//class VecLitExpr;
class VecVarExpr;
class VecVecAddExpr;

class VecScalarMulExpr;
class ScalarVarExpr;

class VecWrapper;
class ScalarWrapper;

// KEVIN ADDING FOR HORIZONTAL MODULE
class VecParenExpr;

class ScalarParenExpr;

class Vector;
class Vector_Lit;
class Vector_Expr;
class Vector_Var;
class Vector_Def;
class Vector_Assign;

class Scalar;
class Scalar_Lit;
class Scalar_Expr;
class Scalar_Var;
class Scalar_Def;
class Scalar_Assign;

class ScalarScalarAddExpr;
class ScalarScalarMulExpr;




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

	ScalarIdent* mkScalarIdent(Space* s);
	ScalarIdent* mkScalarIdent();
	std::vector<ScalarIdent*> &getScalarIdents() { return float_idents; }

	TransformIdent* mkTransformIdent(Space* s);
	TransformIdent* mkTransformIdent();
	std::vector<TransformIdent*> &getTransformIdents() { return tfm_idents; }

	// Exprs
	std::vector<VecExpr *> &getVecExprs() { return exprs;  }

	ScalarExpr* mkScalarExpr(Space* s);
	ScalarExpr* mkScalarExpr();
	std::vector<ScalarExpr *> &getScalarExprs() { return float_exprs; }

	std::vector<TransformExpr *> &getTransformExprs() { return transform_exprs; }

	// Create a variable object in the domain 

	VecWrapper* mkVecWrapper(Space* s, domain::VecExpr* expr);
	VecWrapper* mkVecWrapper(domain::VecExpr* expr);

	ScalarWrapper* mkScalarWrapper(Space* s, domain::ScalarExpr* expr);
	ScalarWrapper* mkScalarWrapper(domain::ScalarExpr* expr);

	TransformWrapper* mkTransformWrapper(Space* s, domain::TransformExpr* expr);
	TransformWrapper* mkTransformWrapper(domain::TransformExpr* expr);

	// Details available via externally represented backmappings
	//
	VecVarExpr* mkVecVarExpr(Space* s);
	VecVarExpr* mkVecVarExpr();

	ScalarVarExpr* mkScalarVarExpr(Space* s);
	ScalarVarExpr* mkScalarVarExpr();

	TransformVarExpr* mkTransformVarExpr(Space* s);
	TransformVarExpr* mkTransformVarExpr();

	// Create a vector-vector-add expression, mem-expr.add(arg-expr) object in domain
	// Precondition: sub-expressions mem-expr and arg-expr are already in domain
	//
	VecVecAddExpr* mkVecVecAddExpr(Space* s, domain::VecExpr* left_, domain::VecExpr* right_);
	VecVecAddExpr* mkVecVecAddExpr(domain::VecExpr* left_, domain::VecExpr* right_);

	VecScalarMulExpr* mkVecScalarMulExpr(Space* s, domain::VecExpr *vec, domain::ScalarExpr *flt);
	VecScalarMulExpr* mkVecScalarMulExpr(domain::VecExpr *vec, domain::ScalarExpr *flt);

	ScalarScalarAddExpr* mkScalarScalarAddExpr(Space* s, domain::ScalarExpr* left_, domain::ScalarExpr* right_);
	ScalarScalarAddExpr* mkScalarScalarAddExpr(domain::ScalarExpr* left_, domain::ScalarExpr* right_);

	ScalarScalarMulExpr* mkScalarScalarMulExpr(Space* s, domain::ScalarExpr* left_, domain::ScalarExpr* right_);
	ScalarScalarMulExpr* mkScalarScalarMulExpr(domain::ScalarExpr* left_, domain::ScalarExpr* right_);

	TransformVecApplyExpr* mkTransformVecApplyExpr(Space* s, domain::TransformExpr* left_, domain::VecExpr* right_);
	TransformVecApplyExpr* mkTransformVecApplyExpr(domain::TransformExpr* left_, domain::VecExpr* right_);

	TransformTransformComposeExpr* mkTransformTransformComposeExpr(Space* s, domain::TransformExpr* left_, domain::TransformExpr* right_);
	TransformTransformComposeExpr* mkTransformTransformComposeExpr(domain::TransformExpr* left_, domain::TransformExpr* right_);


	// Paren Exprs
	//
	VecParenExpr* mkVecParenExpr(Space *s, domain::VecExpr *);
	VecParenExpr* mkVecParenExpr(domain::VecExpr*);

	ScalarParenExpr* mkScalarParenExpr(Space *s, domain::ScalarExpr *);
	ScalarParenExpr* mkScalarParenExpr(domain::ScalarExpr*);

	TransformParenExpr* mkTransformParenExpr(Space* s, domain::TransformExpr *);
	TransformParenExpr* mkTransformParenExpr(domain::TransformExpr*);

	// Values
	std::vector<Vector *> &getVectors() { return vectors;  }
	std::vector<Scalar *> &getScalars() { return floats; }
	std::vector<Transform *> &getTransforms() { return transforms; }

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


	Scalar_Lit* mkScalar_Lit(Space* space, float scalar);
	Scalar_Lit* mkScalar_Lit(float scalar);

	Scalar* mkScalar_Var(Space* s);
	Scalar* mkScalar_Var();

	Scalar_Expr* mkScalar_Expr(Space* space, domain::ScalarExpr *vec);
	Scalar_Expr* mkScalar_Expr(domain::ScalarExpr *vec);


	Transform_Lit* mkTransform_Lit(Space* space, 
		float t11, float t12, float t13,
		float t21, float t22, float t23,
		float t31, float t32, float t33);
	Transform_Lit* mkTransform_Lit(float Transform);

	Transform* mkTransform_Var(Space* s);
	Transform* mkTransform_Var();

	Transform_Expr* mkTransform_Expr(Space* space, domain::TransformExpr *vec);
	Transform_Expr* mkTransform_Expr(domain::TransformExpr *vec);

// Defs

	// Binding of identifier to contsructed vector
	//
	Vector_Def* mkVector_Def(/*ast::Vector_Def* vardecl,*/ domain::VecIdent* identifier, domain::Vector* vec);
	std::vector<Vector_Def*> &getVectorDefs() { return defs; }


	Scalar_Def* mkScalar_Def(domain::ScalarIdent* identifier, domain::Scalar* vec);
	std::vector<Scalar_Def*> &getScalarDefs() { return float_defs; }


	Transform_Def* mkTransform_Def(domain::TransformIdent* identifier, domain::Transform* vec);
	std::vector<Transform_Def*> &getTransformDefs() { return float_defs; }



	Vector_Assign* mkVector_Assign(/*ast::Vector_Assign* vardecl,*/ domain::VecVarExpr* identifier, domain::Vector* vec);
	std::vector<Vector_Assign*> &getVectorAssigns() { return assigns; }


	Scalar_Assign* mkScalar_Assign(domain::ScalarVarExpr* identifier, domain::Scalar* vec);
	std::vector<Scalar_Assign*> &getScalarAssigns() { return float_assigns; }

	Transform_Assign* mkTransform_Assign(domain::TransformVarExpr* identifier, domain::Transform* vec);
	std::vector<Transform_Assign*> &getTransformAssigns() { return float_assigns; }
// Client -- Separated from Domain
//	bool isConsistent();
private:
	std::vector<Space*> spaces;
	std::vector<VecIdent*> idents;
	std::vector<VecExpr*> exprs;
	std::vector<ScalarIdent*> float_idents;
	std::vector<ScalarExpr*> float_exprs;
	std::vector<TransformIdent*> tfm_idents;
	std::vector<TransformExpr*> tfm_exprs;
	std::vector<Vector*> vectors;
	std::vector<Vector_Def*> defs;
	std::vector<Vector_Assign*> assigns;
	std::vector<Scalar*> floats;
	std::vector<Scalar_Def*> float_defs;
	std::vector<Scalar_Assign*> float_assigns;
	std::vector<Transform*> transforms;
	std::vector<Transform_Def*> transform_defs;
	std::vector<Transform_Assign*> transform_assigns;
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
	virtual ~VecExpr(){}
		VecExpr() { this->spaceContainer_ = new SpaceContainer(); }
    Space* getSpace() const { return space_; };
		SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
		void setSpace(Space* s);
		// virtual std::string toString() const;
	protected:
    Space* space_;
		SpaceContainer* spaceContainer_;
};

class ScalarIdent {
public:
	ScalarIdent(Space& space) : space_(&space) {}
	ScalarIdent() { this->spaceContainer_ = new SpaceContainer(); }// this->spaceContainer_-> }
	Space* getSpace() const { return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }

	void setSpace(Space* space);
	// TODO: Reconsider abstracting away of name
private:
	Space* space_;
	SpaceContainer* spaceContainer_;
};

class ScalarExpr {
public:
	ScalarExpr(Space* s) : space_(s) {}
	virtual ~ScalarExpr(){}
	ScalarExpr() { this->spaceContainer_ = new SpaceContainer(); }
	Space* getSpace() const { return space_; };
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
	void setSpace(Space* s);

	protected:
		Space* space_;
		SpaceContainer* spaceContainer_;
};

class TransformIdent {
public:
	TransformIdent(Space& space) : space_(&space) {}
	TransformIdent() { this->spaceContainer_ = new SpaceContainer(); }// this->spaceContainer_-> }
	Space* getSpace() const { return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }

	void setSpace(Space* space);
	// TODO: Reconsider abstracting away of name
private:
	Space* space_;
	SpaceContainer* spaceContainer_;
};

class TransformExpr {
public:
	TransformExpr(Space* s) : space_(s) {}
	virtual ~TransformExpr(){}
	TransformExpr() { this->spaceContainer_ = new SpaceContainer(); }
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
	virtual ~VecVarExpr(){}
		// virtual std::string toString() const;
	private:
};

class ScalarVarExpr : public ScalarExpr {
public:
    ScalarVarExpr(Space* s) : ScalarExpr(s) {}
		ScalarVarExpr() : ScalarExpr() {}
	virtual ~ScalarVarExpr(){}
		// virtual std::string toString() const;
	private:
};

class TransformVarExpr : public TransformExpr {
public:
    TransformVarExpr(Space* s) : TransformExpr(s) {}
		TransformVarExpr() : TransformExpr() {}
	virtual ~TransformVarExpr(){}
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
	virtual ~VecVecAddExpr(){}
	domain::VecExpr *getMemberVecExpr();
	domain::VecExpr *getArgVecExpr();
	// virtual std::string toString() const;
	// const Space& getVecVecAddExprDefaultSpace();
private:
    domain::VecExpr* arg_;
    domain::VecExpr* mem_;
};

class VecScalarMulExpr : public VecExpr {
public:
	VecScalarMulExpr(
		Space* s, domain::VecExpr *vec, domain::ScalarExpr *flt) :
			domain::VecExpr(), vec_(vec), flt_(flt) {	}
	VecScalarMulExpr(
		domain::VecExpr *vec, domain::ScalarExpr *flt) :
			domain::VecExpr(), vec_(vec), flt_(flt) {	}
	domain::VecExpr *getVecExpr();
	domain::ScalarExpr *getScalarExpr();
	
	virtual ~VecScalarMulExpr(){}
	private:
		domain::VecExpr* vec_;
		domain::ScalarExpr* flt_;

};


class ScalarScalarAddExpr : public ScalarExpr {
public:
   ScalarScalarAddExpr(
        Space* s, domain::ScalarExpr *lhs, domain::ScalarExpr *rhs) : 
			domain::ScalarExpr(s), lhs_(lhs), rhs_(rhs) {	}
	 ScalarScalarAddExpr(domain::ScalarExpr *lhs, domain::ScalarExpr *rhs) :
	 		domain::ScalarExpr(), lhs_(lhs), rhs_(rhs) { }
	
	virtual ~ScalarScalarAddExpr(){}
	domain::ScalarExpr *getLHSScalarExpr();
	domain::ScalarExpr *getRHSScalarExpr();
	// virtual std::string toString() const;
	// const Space& getScalarScalarAddExprDefaultSpace();
private:
    domain::ScalarExpr* lhs_;
    domain::ScalarExpr* rhs_;
};

class ScalarScalarMulExpr : public ScalarExpr {
public:
   	ScalarScalarMulExpr(
        Space* s, domain::ScalarExpr *lhs, domain::ScalarExpr *rhs) : 
			domain::ScalarExpr(s), lhs_(lhs), rhs_(rhs) {	}
	ScalarScalarMulExpr(domain::ScalarExpr *lhs, domain::ScalarExpr *rhs) :
	 		domain::ScalarExpr(), lhs_(lhs), rhs_(rhs) { }
	
	virtual ~ScalarScalarMulExpr(){}
	domain::ScalarExpr *getLHSScalarExpr();
	domain::ScalarExpr *getRHSScalarExpr();
	// virtual std::string toString() const;
	// const Space& getScalarScalarAddExprDefaultSpace();
private:
    domain::ScalarExpr* lhs_;
    domain::ScalarExpr* rhs_;
};


class TransformVecApplyExpr : public VecExpr {
public:
   	TransformVecApplyExpr(
        Space* s, domain::TransformExpr *lhs, domain::VecExpr *rhs) : 
			domain::VecExpr(s), lhs_(lhs), rhs_(rhs) {	}
	TransformVecApplyExpr(domain::TransformExpr *lhs, domain::VecExpr *rhs) :
	 		domain::VecExpr(), lhs_(lhs), rhs_(rhs) { }
	
	virtual ~TransformVecApplyExpr(){}
	domain::TransformExpr *getLHSTransformExpr();
	domain::VecExpr *getRHSVecExpr();
	// virtual std::string toString() const;
	// const Space& getScalarScalarAddExprDefaultSpace();
private:
    domain::TransformExpr* lhs_;
    domain::VecExpr* rhs_;
};


class TransformTransformComposeExpr : public TransformExpr {
public:
   	TransformTransformComposeExpr(
        Space* s, domain::TransformExpr *lhs, domain::TransformExpr *rhs) : 
			domain::TransformExpr(s), lhs_(lhs), rhs_(rhs) {	}
	TransformTransformComposeExpr(domain::TransformExpr *lhs, domain::TransformExpr *rhs) :
	 		domain::TransformExpr(), lhs_(lhs), rhs_(rhs) { }
	
	virtual ~TransformTransformComposeExpr(){}
	domain::TransformExpr *getLHSTransformExpr();
	domain::TransformExpr *getRHSTransformExpr();
	// virtual std::string toString() const;
	// const Space& getScalarScalarAddExprDefaultSpace();
private:
    domain::TransformExpr* lhs_;
    domain::TransformExpr* rhs_;
};

class VecParenExpr : public VecExpr  {
public:
		VecParenExpr(Space *s, domain::VecExpr *e) : domain::VecExpr(s), expr_(e) {}
		VecParenExpr(domain::VecExpr *e) : domain::VecExpr(), expr_(e) {}
		
		virtual ~VecParenExpr(){}
		const domain::VecExpr* getVecExpr() const { return expr_; }
		//std::string toString() const; 
private:
		const domain::VecExpr* expr_; // vec expr from which vector is constructed
};

class ScalarParenExpr : public ScalarExpr  {
public:
		ScalarParenExpr(Space *s, domain::ScalarExpr *e) : domain::ScalarExpr(s), expr_(e) {}
		ScalarParenExpr(domain::ScalarExpr *e) : domain::ScalarExpr(), expr_(e) {}
		
		virtual ~ScalarParenExpr(){}
		const domain::ScalarExpr* getScalarExpr() const { return expr_; }
		//std::string toString() const; 
private:
		const domain::ScalarExpr* expr_; // vec expr from which vector is constructed
};


class TransformParenExpr : public TransformExpr  {
public:
		TransformParenExpr(Space *s, domain::TransformExpr *e) : domain::TransformExpr(s), expr_(e) {}
		TransformParenExpr(domain::TransformExpr *e) : domain::TransformExpr(), expr_(e) {}
		
		virtual ~TransformParenExpr(){}
		const domain::TransformExpr* getTransformExpr() const { return expr_; }
		//std::string toString() const; 
private:
		const domain::TransformExpr* expr_; // vec expr from which vector is constructed
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

enum ScalarCtorType {FLOAT_EXPR, FLOAT_LIT, /*VEC_VAR,*/ FLOAT_NONE } ; 
class Scalar{
public:
	Scalar(const Space& s, ScalarCtorType tag) :
		space_(&s), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }
	Scalar(ScalarCtorType tag) : space_(nullptr), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }

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
	ScalarCtorType tag_;
};

enum TransformCtorType {TFM_EXPR, TFM_LIT, TFM_NONE } ; 
class Transform{
public:
	Transform(const Space& s, TransformCtorType tag) :
		space_(&s), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }
	Transform(TransformCtorType tag) : space_(nullptr), tag_(tag)  { this->spaceContainer_ = new SpaceContainer(); }

	bool isLit() { return (tag_ == TFM_LIT); } 
	bool isExpr() { return (tag_ == TFM_EXPR); } 
	//bool isVar() { return (tag_ == VEC_VAR); } -- a kind of expression
	const Space* getSpace() {return space_; }
	SpaceContainer* getSpaceContainer() const { return this->spaceContainer_; }
	void setSpace(Space* space);
	// virtual std::string toString() const {
private:
	const Space* space_; // TODO: INFER?
	SpaceContainer* spaceContainer_;
	TransformCtorType tag_;
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
		LOG(DBUG) <<"Domain::Vector_Var::Vector_Var: Error. Not implemented.\n";
	}
};

class Scalar_Lit : public Scalar {
public:
	Scalar_Lit(const Space& s, float scalar) :
		Scalar(s, FLOAT_LIT), scalar_(scalar) {
	}

	Scalar_Lit(float scalar) : Scalar(FLOAT_LIT), scalar_(scalar){}

	float getScalar() { return scalar_; }
private:
  float scalar_;
};

// Constructed vector value from vector-valued expression
//
class Scalar_Expr : public Scalar  {
public:
	Scalar_Expr(const Space& s, domain::ScalarExpr* e) :
		Scalar(s, FLOAT_EXPR), expr_(e) { 
	}

	Scalar_Expr(domain::ScalarExpr* e) : Scalar(FLOAT_EXPR) {}

	const domain::ScalarExpr* getScalarExpr() const { return expr_; }
	std::string toString() const;
private:
	const domain::ScalarExpr* expr_; // vec expr from which vector is constructed
};

class Scalar_Var : public Scalar {
	Scalar_Var() : Scalar(*new Space(""), FLOAT_EXPR ) { 
		LOG(DBUG) <<"Domain::Scalar_Var::Scalar_-Var: Error. Not implemented.\n";
	}
};


class Transform_Lit : public Transform {
public:
	Transform_Lit(const Space& s, float Transform) :
		Transform(s, TFM_LIT), Transform_(Transform) {
	}

	Transform_Lit(float Transform) : Transform(TFM_LIT), Transform_(Transform){}

	float getTransform() { return Transform_; }
private:
  float Transform_;
};

// Constructed vector value from vector-valued expression
//
class Transform_Expr : public Transform  {
public:
	Transform_Expr(const Space& s, domain::TransformExpr* e) :
		Transform(s, TFM_EXPR), expr_(e) { 
	}

	Transform_Expr(domain::TransformExpr* e) : Transform(TFM_EXPR) {}

	const domain::TransformExpr* getTransformExpr() const { return expr_; }
	std::string toString() const;
private:
	const domain::TransformExpr* expr_; // vec expr from which vector is constructed
};

class Transform_Var : public Transform {
	Transform_Var() : Transform(*new Space(""), TFM_EXPR ) { 
		LOG(DBUG) <<"Domain::Transform_Var::Transform_-Var: Error. Not implemented.\n";
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


class Scalar_Def  {
public:
	Scalar_Def(domain::ScalarIdent* id, domain::Scalar* flt): 
			id_(id), flt_(flt) {}
	const domain::Scalar* getScalar() const { return flt_; }
	const domain::ScalarIdent* getIdent() { return id_; }
	// std::string toString() const;
private:
	const ScalarIdent* id_;
	const Scalar* flt_;
};


class Transform_Def  {
public:
	Transform_Def(domain::TransformIdent* id, domain::Transform* tfm): 
			id_(id), flt_(flt) {}
	const domain::Transform* getTransform() const { return flt_; }
	const domain::TransformIdent* getIdent() { return id_; }
	// std::string toString() const;
private:
	const TransformIdent* id_;
	const Transform* tfm_;
};

class Vector_Assign  {
public:
	Vector_Assign(domain::VecVarExpr* id, domain::Vector* vec): 
			id_(id), vec_(vec) {}
	const domain::Vector* getVector() const { return vec_; }
	const domain::VecVarExpr* getVarExpr() { return id_; }
	// std::string toString() const;
private:
	const VecVarExpr* id_;
	const Vector* vec_;
};


class Scalar_Assign  {
public:
	Scalar_Assign(domain::ScalarVarExpr* id, domain::Scalar* flt): 
			id_(id), flt_(flt) {}
	const domain::Scalar* getScalar() const { return flt_; }
	const domain::ScalarVarExpr* getVarExpr() { return id_; }
	// std::string toString() const;
private:
	const ScalarVarExpr* id_;
	const Scalar* flt_;
};

class Transform_Assign  {
public:
	Transform_Assign(domain::TransformVarExpr* id, domain::Transform* tfm): 
			id_(id), flt_(flt) {}
	const domain::Transform* getTransform() const { return tfm_; }
	const domain::TransformVarExpr* getVarExpr() { return id_; }
	// std::string toString() const;
private:
	const TransformVarExpr* id_;
	const Transform* tfm_;
};




} // end namespace

#endif