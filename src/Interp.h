#ifndef INTERP_H
#define INTERP_H

#include <cstddef>
#include <iostream> // for cheap logging only

#include "Coords.h"
#include "AST.h"
#include "Domain.h"

namespace interp{

std::string getEnvName();
std::string getLastEnv();

class Interp;
class Space;
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
protected:
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

class Frame : public Interp
{
public:
    Frame(domain::Frame* f) : f_(f) {};
    std::string toString() const;
protected:
    domain::Frame* f_;
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
    virtual std::string toString() const;
    virtual std::string toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before);
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
    virtual std::string toString() const;
    virtual std::string toStringLinked(std::vector<interp::Space*> links, std::vector<std::string> names, std::vector<interp::Frame*> framelinks, std::vector<string> framenames, bool before);
    void link(std::vector<STMT*> operands);
    //friend class Interp;              
    
protected:
	
    std::vector<interp::STMT*> operands_;

};



class FUNC_DECL : public GLOBALSTMT {
public:
    FUNC_DECL(coords::FUNC_DECL* coords, domain::DomainObject* dom);
    virtual std::string toString() const;
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


} // namespace coords

#endif