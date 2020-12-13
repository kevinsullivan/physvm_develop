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
class DECLARE;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class REXPR;
class LEXPR;
class REAL3_EXPR;
class REF_REAL3_VAR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class LMUL_REAL1_EXPR_REAL3_EXPR;
class RMUL_REAL3_EXPR_REAL1_EXPR;
class REAL3_LEXPR;
class LREF_REAL3_VAR;
class REAL1_EXPR;
class REF_REAL1_VAR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REAL3_LITERAL;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_EMPTY;
class REAL1_LITERAL;
class REAL1_LIT;


class Interp
{
public:
  Interp(coords::Coords *c, domain::DomainObject *d);
  Interp(){};
  std::string toString() const { return "Not Implemented -- don't call this!!";};
  //friend class Interp;
//protected:
  coords::Coords *coords_;
  domain::DomainObject *dom_;
};


class Space : public Interp
{
public:
    Space(domain::Space* s) : s_(s) {};
    virtual std::string toString() const;
    virtual std::string getVarExpr() const;
    virtual std::string getEvalExpr() const;
//protected:
    domain::Space* s_;
};

class DerivedSpace : public Space
{
public:
    DerivedSpace(domain::DerivedSpace* s, Space* base1, Space* base2) : Space(s), base_1(base1), base_2(base2) {};
    virtual std::string toString() const;

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
    std::string toString() const;
protected:
    domain::MeasurementSystem* ms_;
};

class Frame : public Interp
{
public:
    Frame(domain::Frame* f, interp::Space* sp) : f_(f), sp_(sp) {};
    Frame(domain::Frame* f, interp::Space* sp, interp::MeasurementSystem* ms) : f_(f), sp_(sp), ms_(ms) {};
    std::string toString() const;
//protected:
    domain::Frame* f_;
    interp::Space* sp_;
    interp::MeasurementSystem* ms_;
};





class PROGRAM : public Interp {
public:
    PROGRAM(coords::PROGRAM* coords, domain::DomainObject* dom);
    virtual std::string toString() const;

    //friend class Interp;  
     
                 
};



class SEQ_GLOBALSTMT : public PROGRAM {
public:
    SEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* coords, domain::DomainObject* dom, std::vector<GLOBALSTMT*> operands);
    virtual std::string toString() const override;
    virtual std::string toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
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
    virtual std::string toString() const;

    //friend class Interp;  
     
                 
};



class STMT : public Interp {
public:
    STMT(coords::STMT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;

    //friend class Interp;  
     
                 
};



class COMPOUND_STMT : public STMT {
public:
    COMPOUND_STMT(coords::COMPOUND_STMT* coords, domain::DomainObject* dom, std::vector<STMT*> operands);
    virtual std::string toString() const override;
    virtual std::string toStringLinked(
        std::vector<interp::Space*> links, 
        std::vector<std::string> names, 
        std::vector<interp::MeasurementSystem*> msystems,
        std::vector<std::string> msnames,
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

    //friend class Interp;  
     
                 
};



class VOID_FUNC_DECL_STMT : public FUNC_DECL {
public:
    VOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* coords, domain::DomainObject* dom ,interp::STMT *operand1 );
    virtual std::string toString() const;
     
     

    
protected:
	interp::STMT *operand_1;
};



class MAIN_FUNC_DECL_STMT : public FUNC_DECL {
public:
    MAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* coords, domain::DomainObject* dom ,interp::STMT *operand1 );
    virtual std::string toString() const;
     
     

    
protected:
	interp::STMT *operand_1;
};



class DECLARE : public STMT {
public:
    DECLARE(coords::DECLARE* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
     
                 
};



class DECL_REAL1_VAR_REAL1_EXPR : public DECLARE {
public:
    DECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
     
     
    
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class DECL_REAL3_VAR_REAL3_EXPR : public DECLARE {
public:
    DECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
     
     
    
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class DECL_REAL1_VAR : public DECLARE {
public:
    DECL_REAL1_VAR(coords::DECL_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
     
     
    
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class DECL_REAL3_VAR : public DECLARE {
public:
    DECL_REAL3_VAR(coords::DECL_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
     
     
    
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class REXPR : public STMT {
public:
    REXPR(coords::REXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
     
                 
};



class LEXPR : public STMT {
public:
    LEXPR(coords::LEXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
     
                 
};



class REAL3_EXPR : public REXPR {
public:
    REAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
    virtual std::string toEvalString() const { return "";}; 
    virtual std::string toAlgebraString() const { return "";};             
};



class REF_REAL3_VAR : public REAL3_EXPR {
public:
    REF_REAL3_VAR(coords::REF_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class ADD_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    ADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class LMUL_REAL1_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    LMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class RMUL_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    RMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class REAL3_LEXPR : public LEXPR {
public:
    REAL3_LEXPR(coords::REAL3_LEXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
    virtual std::string toEvalString() const { return "";}; 
    virtual std::string toAlgebraString() const { return "";};             
};



class LREF_REAL3_VAR : public REAL3_LEXPR {
public:
    LREF_REAL3_VAR(coords::LREF_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class REAL1_EXPR : public REXPR {
public:
    REAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
    virtual std::string toEvalString() const { return "";}; 
    virtual std::string toAlgebraString() const { return "";};             
};



class REF_REAL1_VAR : public REAL1_EXPR {
public:
    REF_REAL1_VAR(coords::REF_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class ADD_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    ADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class MUL_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    MUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class REAL1_VAR_IDENT : public Interp {
public:
    REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL3_VAR_IDENT : public Interp {
public:
    REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const;
    virtual std::string toEvalString() const ; 
    virtual std::string toAlgebraString() const ; 

    
protected:
	
};



class REAL3_LITERAL : public REAL3_EXPR {
public:
    REAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
    virtual std::string toEvalString() const { return "";}; 
    virtual std::string toAlgebraString() const { return "";};             
};



class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL3_LITERAL {
public:
    REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2,interp::REAL1_EXPR *operand3 );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
	interp::REAL1_EXPR *operand_3;
};



class REAL3_EMPTY : public REAL3_LITERAL {
public:
    REAL3_EMPTY(coords::REAL3_EMPTY* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};



class REAL1_LITERAL : public REAL1_EXPR {
public:
    REAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const override;

    //friend class Interp;  
    virtual std::string toEvalString() const { return "";}; 
    virtual std::string toAlgebraString() const { return "";};             
};



class REAL1_LIT : public REAL1_LITERAL {
public:
    REAL1_LIT(coords::REAL1_LIT* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    virtual std::string toEvalString() const override; 
    virtual std::string toAlgebraString() const override; 
    
    
protected:
	
};


} // namespace coords

#endif