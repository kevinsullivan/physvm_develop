#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only

#include "Coords.h"
#include "AST.h"
#include "Domain.h"

namespace interp{

class Interp;
class Space;
class Frame;

class STMT;
class COMPOUND_STMT;
class IFCOND;
class IFTHEN_EXPR_STMT;
class IFTHENELSEIF_EXPR_STMT_IFCOND;
class IFTHENELSE_EXPR_STMT_STMT;
class EXPR;
class ASSIGNMENT;
class ASSIGN_REAL1_VAR_REAL1_EXPR;
class ASSIGN_REAL3_VAR_REAL3_EXPR;
class ASSIGN_REAL4_VAR_REAL4_EXPR;
class ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR;
class DECLARE;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REAL4_VAR_REAL4_EXPR;
class DECL_REALMATRIX_VAR_REALMATRIX_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class DECL_REAL4_VAR;
class DECL_REALMATRIX_VAR;
class REAL1_EXPR;
class PAREN_REAL1_EXPR;
class INV_REAL1_EXPR;
class NEG_REAL1_EXPR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class SUB_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class DIV_REAL1_EXPR_REAL1_EXPR;
class REF_REAL1_VAR;
class REAL3_EXPR;
class PAREN_REAL3_EXPR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class SUB_REAL3_EXPR_REAL3_EXPR;
class INV_REAL3_EXPR;
class NEG_REAL3_EXPR;
class MUL_REAL3_EXPR_REAL1_EXPR;
class MUL_REALMATRIX_EXPR_REAL3_EXPR;
class DIV_REAL3_EXPR_REAL1_EXPR;
class REF_REAL3_VAR;
class REAL4_EXPR;
class PAREN_REAL4_EXPR;
class ADD_REAL4_EXPR_REAL4_EXPR;
class MUL_REAL4_EXPR_REAL1_EXPR;
class REF_REAL4_VAR;
class REALMATRIX_EXPR;
class PAREN_REALMATRIX_EXPR;
class MUL_REALMATRIX_EXPR_REALMATRIX_EXPR;
class REF_EXPR_REALMATRIX_VAR;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REAL4_VAR_IDENT;
class REALMATRIX_VAR_IDENT;
class REAL1_LITERAL;
class REAL1_LITERAL1;
class REAL3_LITERAL;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_LITERAL3;
class REAL4_LITERAL;
class REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL4_LITERAL4;
class REALMATRIX_LITERAL;
class REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR;
class REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REALMATRIX_LITERAL9;


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
    std::string toString() const;
protected:
    domain::Space* s_;
};

class Frame : public Interp
{
public:
    Frame(domain::Frame* f) : f_(f) {};
    std::string toString() const;
protected:
    domain::Frame* f_;
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
    virtual std::string toString() const;
    virtual std::string toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before);
    void link(std::vector<STMT*> operands);
    //friend class Interp;              
    
protected:
	
    std::vector<interp::STMT*> operands_;

};



class IFCOND : public STMT {
public:
    IFCOND(coords::IFCOND* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class IFTHEN_EXPR_STMT : public IFCOND {
public:
    IFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* coords, domain::DomainObject* dom ,interp::EXPR *operand1,interp::STMT *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::EXPR *operand_1;
	interp::STMT *operand_2;
};



class IFTHENELSEIF_EXPR_STMT_IFCOND : public IFCOND {
public:
    IFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* coords, domain::DomainObject* dom ,interp::EXPR *operand1,interp::STMT *operand2,interp::IFCOND *operand3 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::EXPR *operand_1;
	interp::STMT *operand_2;
	interp::IFCOND *operand_3;
};



class IFTHENELSE_EXPR_STMT_STMT : public IFCOND {
public:
    IFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* coords, domain::DomainObject* dom ,interp::EXPR *operand1,interp::STMT *operand2,interp::STMT *operand3 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::EXPR *operand_1;
	interp::STMT *operand_2;
	interp::STMT *operand_3;
};



class EXPR : public STMT {
public:
    EXPR(coords::EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class ASSIGNMENT : public STMT {
public:
    ASSIGNMENT(coords::ASSIGNMENT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class ASSIGN_REAL1_VAR_REAL1_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class ASSIGN_REAL3_VAR_REAL3_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class ASSIGN_REAL4_VAR_REAL4_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_VAR_IDENT *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX_VAR_IDENT *operand1,interp::REALMATRIX_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_VAR_IDENT *operand_1;
	interp::REALMATRIX_EXPR *operand_2;
};



class DECLARE : public STMT {
public:
    DECLARE(coords::DECLARE* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class DECL_REAL1_VAR_REAL1_EXPR : public DECLARE {
public:
    DECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class DECL_REAL3_VAR_REAL3_EXPR : public DECLARE {
public:
    DECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class DECL_REAL4_VAR_REAL4_EXPR : public DECLARE {
public:
    DECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_VAR_IDENT *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class DECL_REALMATRIX_VAR_REALMATRIX_EXPR : public DECLARE {
public:
    DECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX_VAR_IDENT *operand1,interp::REALMATRIX_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_VAR_IDENT *operand_1;
	interp::REALMATRIX_EXPR *operand_2;
};



class DECL_REAL1_VAR : public DECLARE {
public:
    DECL_REAL1_VAR(coords::DECL_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class DECL_REAL3_VAR : public DECLARE {
public:
    DECL_REAL3_VAR(coords::DECL_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class DECL_REAL4_VAR : public DECLARE {
public:
    DECL_REAL4_VAR(coords::DECL_REAL4_VAR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_VAR_IDENT *operand_1;
};



class DECL_REALMATRIX_VAR : public DECLARE {
public:
    DECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* coords, domain::DomainObject* dom ,interp::REALMATRIX_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_VAR_IDENT *operand_1;
};



class REAL1_EXPR : public EXPR {
public:
    REAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class PAREN_REAL1_EXPR : public REAL1_EXPR {
public:
    PAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
};



class INV_REAL1_EXPR : public REAL1_EXPR {
public:
    INV_REAL1_EXPR(coords::INV_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
};



class NEG_REAL1_EXPR : public REAL1_EXPR {
public:
    NEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
};



class ADD_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    ADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class SUB_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    SUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class MUL_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    MUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class DIV_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    DIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class REF_REAL1_VAR : public REAL1_EXPR {
public:
    REF_REAL1_VAR(coords::REF_REAL1_VAR* coords, domain::DomainObject* dom ,interp::REAL1_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_VAR_IDENT *operand_1;
};



class REAL3_EXPR : public EXPR {
public:
    REAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class PAREN_REAL3_EXPR : public REAL3_EXPR {
public:
    PAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
};



class ADD_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    ADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class SUB_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    SUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class INV_REAL3_EXPR : public REAL3_EXPR {
public:
    INV_REAL3_EXPR(coords::INV_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
};



class NEG_REAL3_EXPR : public REAL3_EXPR {
public:
    NEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
};



class MUL_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    MUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class MUL_REALMATRIX_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    MUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX_EXPR *operand1,interp::REAL3_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
};



class DIV_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    DIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class REF_REAL3_VAR : public REAL3_EXPR {
public:
    REF_REAL3_VAR(coords::REF_REAL3_VAR* coords, domain::DomainObject* dom ,interp::REAL3_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_VAR_IDENT *operand_1;
};



class REAL4_EXPR : public EXPR {
public:
    REAL4_EXPR(coords::REAL4_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class PAREN_REAL4_EXPR : public REAL4_EXPR {
public:
    PAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_EXPR *operand_1;
};



class ADD_REAL4_EXPR_REAL4_EXPR : public REAL4_EXPR {
public:
    ADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1,interp::REAL4_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_EXPR *operand_1;
	interp::REAL4_EXPR *operand_2;
};



class MUL_REAL4_EXPR_REAL1_EXPR : public REAL4_EXPR {
public:
    MUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL4_EXPR *operand1,interp::REAL1_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
};



class REF_REAL4_VAR : public REAL4_EXPR {
public:
    REF_REAL4_VAR(coords::REF_REAL4_VAR* coords, domain::DomainObject* dom ,interp::REAL4_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL4_VAR_IDENT *operand_1;
};



class REALMATRIX_EXPR : public EXPR {
public:
    REALMATRIX_EXPR(coords::REALMATRIX_EXPR* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class PAREN_REALMATRIX_EXPR : public REALMATRIX_EXPR {
public:
    PAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX_EXPR *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_EXPR *operand_1;
};



class MUL_REALMATRIX_EXPR_REALMATRIX_EXPR : public REALMATRIX_EXPR {
public:
    MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* coords, domain::DomainObject* dom ,interp::REALMATRIX_EXPR *operand1,interp::REALMATRIX_EXPR *operand2 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_EXPR *operand_1;
	interp::REALMATRIX_EXPR *operand_2;
};



class REF_EXPR_REALMATRIX_VAR : public REALMATRIX_EXPR {
public:
    REF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* coords, domain::DomainObject* dom ,interp::REALMATRIX_VAR_IDENT *operand1 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REALMATRIX_VAR_IDENT *operand_1;
};



class REAL1_VAR_IDENT : public Interp {
public:
    REAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL3_VAR_IDENT : public Interp {
public:
    REAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL4_VAR_IDENT : public Interp {
public:
    REAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REALMATRIX_VAR_IDENT : public Interp {
public:
    REALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL1_LITERAL : public REAL1_EXPR {
public:
    REAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL1_LITERAL1 : public REAL1_LITERAL {
public:
    REAL1_LITERAL1(coords::REAL1_LITERAL1* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	
};



class REAL3_LITERAL : public REAL3_EXPR {
public:
    REAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL3_LITERAL {
public:
    REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2,interp::REAL1_EXPR *operand3 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
	interp::REAL1_EXPR *operand_3;
};



class REAL3_LITERAL3 : public REAL3_LITERAL {
public:
    REAL3_LITERAL3(coords::REAL3_LITERAL3* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	
};



class REAL4_LITERAL : public REAL4_EXPR {
public:
    REAL4_LITERAL(coords::REAL4_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL4_LITERAL {
public:
    REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2,interp::REAL1_EXPR *operand3,interp::REAL1_EXPR *operand4 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
	interp::REAL1_EXPR *operand_3;
	interp::REAL1_EXPR *operand_4;
};



class REAL4_LITERAL4 : public REAL4_LITERAL {
public:
    REAL4_LITERAL4(coords::REAL4_LITERAL4* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	
};



class REALMATRIX_LITERAL : public REALMATRIX_EXPR {
public:
    REALMATRIX_LITERAL(coords::REALMATRIX_LITERAL* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
    //friend class Interp;              
};



class REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* coords, domain::DomainObject* dom ,interp::REAL3_EXPR *operand1,interp::REAL3_EXPR *operand2,interp::REAL3_EXPR *operand3 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL3_EXPR *operand_1;
	interp::REAL3_EXPR *operand_2;
	interp::REAL3_EXPR *operand_3;
};



class REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coords, domain::DomainObject* dom ,interp::REAL1_EXPR *operand1,interp::REAL1_EXPR *operand2,interp::REAL1_EXPR *operand3,interp::REAL1_EXPR *operand4,interp::REAL1_EXPR *operand5,interp::REAL1_EXPR *operand6,interp::REAL1_EXPR *operand7,interp::REAL1_EXPR *operand8,interp::REAL1_EXPR *operand9 );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	interp::REAL1_EXPR *operand_1;
	interp::REAL1_EXPR *operand_2;
	interp::REAL1_EXPR *operand_3;
	interp::REAL1_EXPR *operand_4;
	interp::REAL1_EXPR *operand_5;
	interp::REAL1_EXPR *operand_6;
	interp::REAL1_EXPR *operand_7;
	interp::REAL1_EXPR *operand_8;
	interp::REAL1_EXPR *operand_9;
};



class REALMATRIX_LITERAL9 : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* coords, domain::DomainObject* dom  );
    virtual std::string toString() const override ;
    //friend class Interp;              
    
protected:
	
};


} // namespace coords

#endif