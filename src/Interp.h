#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only

#include "Coords.h"
#include "AST.h"
#include "Domain.h"


namespace interp2domain
{
    class InterpToDomain;
}
#ifndef INTERP2DOMAIN_H
#include "InterpToDomain.h"
#endif

namespace interp{

std::string getEnvName();
std::string getLastEnv();

class Interp;
class Space;
class MeasurementSystem;
class AxisOrientation;
class DerivedSpace;
class Frame;

class PROGRAM;
class SEQ_GLOBALSTMT;
class GLOBALSTMT;
class STMT;
class COMPOUND_STMT;
class FUNC_DECL;
class VOID_FUNC_DECL_STMT;
class MAIN_FUNC_DECL_STMT;
class WHILE;
class WHILE_BOOL_EXPR_STMT;
class TRY;
class TRY_STMT;
class DECLARE;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR;
class DECL_REAL4_VAR_REAL4_EXPR;
class DECL_BOOL_VAR_BOOL_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class DECL_REALMATRIX4_VAR;
class DECL_REAL4_VAR;
class DECL_BOOL_VAR;
class ASSIGN;
class ASNR1_REAL1_VAR_REAL1_EXPR;
class ASNR3_REAL3_VAR_REAL3_EXPR;
class ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR;
class REXPR;
class LEXPR;
class BOOL_EXPR;
class REF_BOOL_VAR;
class REALMATRIX4_EXPR;
class REF_REALMATRIX4_VAR;
class MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR;
class REAL4_EXPR;
class REF_REAL4_VAR;
class ADD_REAL4_EXPR_REAL4_EXPR;
class MUL_REAL4_EXPR_REAL4_EXPR;
class REAL3_EXPR;
class REF_REAL3_VAR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class LMUL_REAL1_EXPR_REAL3_EXPR;
class RMUL_REAL3_EXPR_REAL1_EXPR;
class TMUL_REALMATRIX4_EXPR_REAL3_EXPR;
class REAL3_LEXPR;
class LREF_REAL3_VAR;
class REAL1_EXPR;
class REF_REAL1_VAR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class BOOL_VAR_IDENT;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REAL4_VAR_IDENT;
class REALMATRIX4_VAR_IDENT;
class REAL4_LITERAL;
class REAL4_EMPTY;
class REAL3_LITERAL;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_EMPTY;
class REAL1_LITERAL;
class REAL1_LIT;
class REALMATRIX4_LITERAL;
class REALMATRIX4_EMPTY;
class REALMATRIX4_EMPTY2_REALMATRIX4_EXPR;
class R4R3_LIT_REAL4_EXPR_REAL3_EXPR;
class SINK;
class IGNORE;
class BOOL_LITERAL;
class BOOL_LIT;


class Interp
{
public:
  Interp(coords::Coords *c, domain::DomainObject *d);
  Interp(){};
  virtual std::string toString() const { return "Not Implemented -- don't call this!!";};
  virtual std::string toDefString() const { return "Don't call this either!";};
  //friend class Interp;
//protected:
  coords::Coords *coords_;
  domain::DomainObject *dom_;
};


class Space : public Interp
{
public:
    Space(domain::Space* s) : s_(s) {};
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string getVarExpr() const;
    virtual std::string getEvalExpr() const;
//protected:
    domain::Space* s_;
};

class DerivedSpace : public Space
{
public:
    DerivedSpace(domain::DerivedSpace* s, Space* base1, Space* base2) : Space(s), base_1(base1), base_2(base2) {};
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;

    Space* getBase1() const {
        return this->base_1;
    }

    Space* getBase2() const {
        return this->base_2;
    }

protected:
    interp::Space *base_1,*base_2;

};

class MeasurementSystem : public Interp
{
public :
    MeasurementSystem(domain::MeasurementSystem* ms) : ms_(ms){};
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
protected:
    domain::MeasurementSystem* ms_;
};

class AxisOrientation : public Interp
{
public :
    AxisOrientation(domain::AxisOrientation* ax) : ax_(ax){};
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
protected:
    domain::AxisOrientation* ax_;
};

class Frame : public Interp
{
public:
    Frame(domain::Frame* f, interp::Space* sp) : f_(f), sp_(sp) {};
    Frame(domain::Frame* f, interp::Space* sp, interp::MeasurementSystem* ms, interp::AxisOrientation* ax) : f_(f), sp_(sp), ms_(ms), ax_(ax) {};
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
//protected:
    domain::Frame* f_;
    interp::Space* sp_;
    interp::MeasurementSystem* ms_;
    interp::AxisOrientation* ax_;
};





class PROGRAM : public Interp {
public:
    PROGRAM(coords::PROGRAM* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class SEQ_GLOBALSTMT : public PROGRAM {
public:
    SEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* coords, domain::DomainObject* dom, std::vector<GLOBALSTMT*> operands);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
        std::vector<interp::AxisOrientation*> axes,
        std::vector<std::string> axisnames,
        std::vector<interp::Frame*> framelinks, 
        std::vector<string> framenames, 
        interp2domain::InterpToDomain* i2d,
        bool before);
    void link(std::vector<GLOBALSTMT*> operands);
    //friend class Interp;              
    
protected:
	
    std::vector<interp::GLOBALSTMT*> operands_;

};



class GLOBALSTMT : public Interp {
public:
    GLOBALSTMT(coords::GLOBALSTMT* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class STMT : public Interp {
public:
    STMT(coords::STMT* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class COMPOUND_STMT : public STMT {
public:
    COMPOUND_STMT(coords::COMPOUND_STMT* coords, domain::DomainObject* dom, std::vector<STMT*> operands);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
        std::vector<interp::AxisOrientation*> axes,
        std::vector<std::string> axisnames,
        std::vector<interp::Frame*> framelinks, 
        std::vector<string> framenames, 
        interp2domain::InterpToDomain* i2d,
        bool before);
    void link(std::vector<STMT*> operands);
    //friend class Interp;              
    
protected:
	
    std::vector<interp::STMT*> operands_;

};



class FUNC_DECL : public GLOBALSTMT {
public:
    FUNC_DECL(coords::FUNC_DECL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class VOID_FUNC_DECL_STMT : public FUNC_DECL {
public:
    VOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* coords, domain::DomainObject* dom ,interp::STMT *operand1 );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
     
     

    interp::STMT *getOperand1() const { return operand_1; }; 
protected:
	interp::STMT *operand_1;
};



class MAIN_FUNC_DECL_STMT : public FUNC_DECL {
public:
    MAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* coords, domain::DomainObject* dom ,interp::STMT *operand1 );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
     
     

    interp::STMT *getOperand1() const { return operand_1; }; 
protected:
	interp::STMT *operand_1;
};



class WHILE : public STMT {
public:
    WHILE(coords::WHILE* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class WHILE_BOOL_EXPR_STMT : public WHILE {
public:
    WHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* coords, domain::DomainObject* dom ,interp::BOOL_EXPR *operand1,interp::STMT *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::BOOL_EXPR *getOperand1() const { return operand_1; }; 
interp::STMT *getOperand2() const { return operand_2; }; 
protected:
	interp::BOOL_EXPR *operand_1;
	interp::STMT *operand_2;
};



class TRY : public STMT {
public:
    TRY(coords::TRY* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class TRY_STMT : public TRY {
public:
    TRY_STMT(coords::TRY_STMT* coords, domain::DomainObject* dom ,interp::STMT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::STMT *getOperand1() const { return operand_1; }; 
protected:
	interp::STMT *operand_1;
};



class DECLARE : public STMT {
public:
    DECLARE(coords::DECLARE* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class DECL_REAL1_VAR_REAL1_EXPR : public DECLARE {
public:
    DECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL1_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL1_VAR_IDENT *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class DECL_REAL3_VAR_REAL3_EXPR : public DECLARE {
public:
    DECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL3_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL3_VAR_IDENT *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR : public DECLARE {
public:
    DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_VAR_IDENT *operand1,interp::REALMATRIX4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REALMATRIX4_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REALMATRIX4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REALMATRIX4_VAR_IDENT *operand_1;
	interp::REALMATRIX4_EXPR *operand_2;
};



class DECL_REAL4_VAR_REAL4_EXPR : public DECLARE {
public:
    DECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL4_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REAL4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL4_VAR_IDENT *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class DECL_BOOL_VAR_BOOL_EXPR : public DECLARE {
public:
    DECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* coords, domain::DomainObject* dom ,interp::BOOL_VAR_IDENT *operand1,interp::BOOL_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::BOOL_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::BOOL_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::BOOL_VAR_IDENT *operand_1;
	interp::BOOL_EXPR *operand_2;
};



class DECL_REAL1_VAR : public DECLARE {
public:
    DECL_REAL1_VAR(coords::DECL_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL1_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class DECL_REAL3_VAR : public DECLARE {
public:
    DECL_REAL3_VAR(coords::DECL_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL3_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class DECL_REALMATRIX4_VAR : public DECLARE {
public:
    DECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REALMATRIX4_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REALMATRIX4_VAR_IDENT *operand_1;
};



class DECL_REAL4_VAR : public DECLARE {
public:
    DECL_REAL4_VAR(coords::DECL_REAL4_VAR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL4_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL4_VAR_IDENT *operand_1;
};



class DECL_BOOL_VAR : public DECLARE {
public:
    DECL_BOOL_VAR(coords::DECL_BOOL_VAR* coords, domain::DomainObject* dom ,interp::BOOL_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::BOOL_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::BOOL_VAR_IDENT *operand_1;
};



class ASSIGN : public STMT {
public:
    ASSIGN(coords::ASSIGN* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class ASNR1_REAL1_VAR_REAL1_EXPR : public ASSIGN {
public:
    ASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL1_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL1_VAR_IDENT *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class ASNR3_REAL3_VAR_REAL3_EXPR : public ASSIGN {
public:
    ASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REAL3_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL3_VAR_IDENT *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR : public ASSIGN {
public:
    ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_VAR_IDENT *operand1,interp::REALMATRIX4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::REALMATRIX4_VAR_IDENT *getOperand1() const { return operand_1; }; 
interp::REALMATRIX4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REALMATRIX4_VAR_IDENT *operand_1;
	interp::REALMATRIX4_EXPR *operand_2;
};



class REXPR : public STMT {
public:
    REXPR(coords::REXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class LEXPR : public STMT {
public:
    LEXPR(coords::LEXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class BOOL_EXPR : public REXPR {
public:
    BOOL_EXPR(coords::BOOL_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class REF_BOOL_VAR : public BOOL_EXPR {
public:
    REF_BOOL_VAR(coords::REF_BOOL_VAR* coords, domain::DomainObject* dom ,interp::BOOL_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    interp::BOOL_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::BOOL_VAR_IDENT *operand_1;
};



class REALMATRIX4_EXPR : public REXPR {
public:
    REALMATRIX4_EXPR(coords::REALMATRIX4_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class REF_REALMATRIX4_VAR : public REALMATRIX4_EXPR {
public:
    REF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REALMATRIX4_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REALMATRIX4_VAR_IDENT *operand_1;
};



class MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR : public REALMATRIX4_EXPR {
public:
    MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_EXPR *operand1,interp::REALMATRIX4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REALMATRIX4_EXPR *getOperand1() const { return operand_1; }; 
interp::REALMATRIX4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REALMATRIX4_EXPR *operand_1;
	interp::REALMATRIX4_EXPR *operand_2;
};



class REAL4_EXPR : public REXPR {
public:
    REAL4_EXPR(coords::REAL4_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class REF_REAL4_VAR : public REAL4_EXPR {
public:
    REF_REAL4_VAR(coords::REF_REAL4_VAR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL4_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL4_VAR_IDENT *operand_1;
};



class ADD_REAL4_EXPR_REAL4_EXPR : public REAL4_EXPR {
public:
    ADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL4_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL4_EXPR *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class MUL_REAL4_EXPR_REAL4_EXPR : public REAL4_EXPR {
public:
    MUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL4_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL4_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL4_EXPR *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class REAL3_EXPR : public REXPR {
public:
    REAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class REF_REAL3_VAR : public REAL3_EXPR {
public:
    REF_REAL3_VAR(coords::REF_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL3_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class ADD_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    ADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL3_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class LMUL_REAL1_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    LMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL1_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class RMUL_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    RMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL3_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class TMUL_REALMATRIX4_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    TMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REALMATRIX4_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REALMATRIX4_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class REAL3_LEXPR : public LEXPR {
public:
    REAL3_LEXPR(coords::REAL3_LEXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class LREF_REAL3_VAR : public REAL3_LEXPR {
public:
    LREF_REAL3_VAR(coords::LREF_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL3_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class REAL1_EXPR : public REXPR {
public:
    REAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class REF_REAL1_VAR : public REAL1_EXPR {
public:
    REF_REAL1_VAR(coords::REF_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL1_VAR_IDENT *getOperand1() const { return operand_1; }; 
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class ADD_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    ADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL1_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class MUL_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    MUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL1_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class BOOL_VAR_IDENT : public Interp {
public:
    BOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL1_VAR_IDENT : public Interp {
public:
    REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL3_VAR_IDENT : public Interp {
public:
    REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL4_VAR_IDENT : public Interp {
public:
    REAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REALMATRIX4_VAR_IDENT : public Interp {
public:
    REALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL4_LITERAL : public Interp {
public:
    REAL4_LITERAL(coords::REAL4_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const{ return "";}; 
    virtual std::string toAlgebraString() const{ return "";};             
};



class REAL4_EMPTY : public REAL4_LITERAL {
public:
    REAL4_EMPTY(coords::REAL4_EMPTY* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};



class REAL3_LITERAL : public REAL3_EXPR {
public:
    REAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const override{ return "";}; 
    virtual std::string toAlgebraString() const override{ return "";};             
};



class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL3_LITERAL {
public:
    REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2,interp::REAL1_EXPR *operand3 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL1_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL1_EXPR *getOperand2() const { return operand_2; }; 
interp::REAL1_EXPR *getOperand3() const { return operand_3; }; 
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
	interp::REAL1_EXPR *operand_3;
};



class REAL3_EMPTY : public REAL3_LITERAL {
public:
    REAL3_EMPTY(coords::REAL3_EMPTY* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};



class REAL1_LITERAL : public REAL1_EXPR {
public:
    REAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const override{ return "";}; 
    virtual std::string toAlgebraString() const override{ return "";};             
};



class REAL1_LIT : public REAL1_LITERAL {
public:
    REAL1_LIT(coords::REAL1_LIT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};



class REALMATRIX4_LITERAL : public REALMATRIX4_EXPR {
public:
    REALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
    virtual std::string toEvalString() const override{ return "";}; 
    virtual std::string toAlgebraString() const override{ return "";};             
};



class REALMATRIX4_EMPTY : public REALMATRIX4_LITERAL {
public:
    REALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};



class REALMATRIX4_EMPTY2_REALMATRIX4_EXPR : public REALMATRIX4_LITERAL {
public:
    REALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX4_EXPR *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REALMATRIX4_EXPR *getOperand1() const { return operand_1; }; 
protected:
	interp::REALMATRIX4_EXPR *operand_1;
};



class R4R3_LIT_REAL4_EXPR_REAL3_EXPR : public REALMATRIX4_LITERAL {
public:
    R4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    interp::REAL4_EXPR *getOperand1() const { return operand_1; }; 
interp::REAL3_EXPR *getOperand2() const { return operand_2; }; 
protected:
	interp::REAL4_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class SINK : public Interp {
public:
    SINK(coords::SINK* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class IGNORE : public SINK {
public:
    IGNORE(coords::IGNORE* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    
protected:
	
};



class BOOL_LITERAL : public BOOL_EXPR {
public:
    BOOL_LITERAL(coords::BOOL_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;
    virtual std::string toDefString() const override;
    //friend class Interp;  
     
                 
};



class BOOL_LIT : public BOOL_LITERAL {
public:
    BOOL_LIT(coords::BOOL_LIT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toDefString() const override;
     
     
    
    
protected:
	
};


} // namespace coords

#endif