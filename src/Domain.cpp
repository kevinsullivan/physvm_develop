#include <vector>
#include <iostream>
#include "Checker.h"
#include "Domain.h"

#include <g3log/g3log.hpp>



using namespace std;
using namespace domain;


/******
* Space
******/

Space &Domain::mkSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(s);
    //LOG(DEBUG) <<"Added space to domain at address " << std::hex << s << "\n";
    return *s;
}

/*
// TODO: STUB
// precondition: variable already interpreted
Space &Domain::getSpaceOfVarExpr(const coords::VecExpr *ast)
{
    // look up variable (ast) in identifiers table
    // Space& s = getSpaceOf(ast,identifiers);
    // return s;

    // get and return the space assigned to that object
    //LOG(DEBUG) <<"STUB: Domain: getSpaceOfVarExpr in Domain.cpp\n";
    return *new Space("_");
}
*/

std::vector<Space*> &Domain::getSpaces() 
{
    return spaces; 
}


// TODO: MOVE THIS STUFF
std::string Space::getName() const { return name_; }

const Space &domain::VecExpr::getSpace() const { return space_; }



/****
Ident
****/


VecIdent *Domain::mkVecIdent(Space &s)
{
    VecIdent *id = new VecIdent(s);
    idents.push_back(id);
    return id;
}


/*
std::string VecIdent::getName() const
{
    LOG(DEBUG) <<"VecIdent::getName(): vardecl_  addr is STUB\n"; // << std::hex << vardecl_->getVarDecl() << "\n";
    return "VecIdent::getName: STUB\n";//"(" + getCoords()->toString() + " : " + getCoords()->space_->getName() + ")";
}
*/


/****
 Expr
****/

/*
domain::VecLitExpr *Domain::mkVecLitExpr(Space &s, const coords::VecLitExpr *e)
{
    domain::VecExpr *be = new domain::VecExpr(s, e);
    //LOG(DEBUG) <<"Adding Vec Lit Expr to domain, address " << std::hex << be << " dump before is ... \n";
    //dump();
    exprs.push_back(be);
    //LOG(DEBUG) <<"... dump after is ...\n";
    //dump();
    return be;
}
*/

domain::VecVarExpr *Domain::mkVecVarExpr(Space &s)
{
    domain::VecVarExpr *var = new domain::VecVarExpr(s);
    //LOG(DEBUG) <<"Adding Vec Var Expr to domain, address " << std::hex << var << ": " << var->toString() << "\n";
    //dump();
    exprs.push_back(var);
    //LOG(DEBUG) <<"... dump after is ...\n";
    //dump();
    return var;
}

domain::VecVecAddExpr *Domain::mkVecVecAddExpr(Space &s, domain::VecExpr *mem, domain::VecExpr *arg)
{
    domain::VecVecAddExpr *be = new domain::VecVecAddExpr(s, mem, arg);
    exprs.push_back(be);
    //LOG(DEBUG) <<"Domain::mkVecVecAddExpr:: Add. Coords are "
    //    << std::hex << e << " Domain VecExpr at " << std::hex << be << "\n";
    //LOG(DEBUG) <<"Domain::mkVecVecAddExpr:: VecExpr string is " << be->toString() << "\n";
    return be;
}

domain::VecExpr *VecVecAddExpr::getMemberVecExpr()
{
    return mem_;
}

domain::VecExpr *VecVecAddExpr::getArgVecExpr()
{
    return arg_;
}

/******
* Value
*******/

Vector_Lit* Domain::mkVector_Lit(Space& space, float x, float y, float z) {
    Vector_Lit* vec = new domain::Vector_Lit(space, x, y, z); 
    vectors.push_back(vec); 
    return vec;
}


Vector_Expr* Domain::mkVector_Expr(Space& s, domain::VecExpr* exp) {
    Vector_Expr* vec = new domain::Vector_Expr(s, exp);
    vectors.push_back(vec);
    return vec;
}

/*
Vector* Domain::mkVector_Var(Space& s, coords::Vector* coords, domain::Expr* exp) {
    Vector* vec = new domain::Vector_Var(space, coords, expr);
    vectors.push_back(vec);
    return vec;
}
*/


/****
* Def
*****/


// TODO: Should be binding to Vector, not Expr
// 
Vector_Def *Domain::mkVector_Def(domain::VecIdent* i, domain::Vector* v)
{
    LOG(DEBUG) <<"Domain::mkVector_Def ";
//    LOG(DEBUG) <<"identifier is " << i->toString();
//    LOG(DEBUG) <<" expression is " << e->toString() << "\n";
    Vector_Def *bd = new Vector_Def(i, v);  
    defs.push_back(bd); 
    return bd;
}

/********
* Details
********/


// TODO: Use pointers everywhere here?
void Domain::dumpVecIdents()
{
    for (auto i: idents ){
        LOG(DEBUG) <<"Domain::dumpVecIdents: An identifier (STUB)\n";
    }
}

void Domain::dumpExpressions()
{
    for (auto e: exprs ){
        LOG(DEBUG) <<"Domain::dumpVecExpressions. An expression. (STUB).\n";
    }
}

void Domain::dumpVector_Defs()
{
    for (auto b: defs ){
        LOG(DEBUG) <<"Domain::dumpVector_Defs. A def. (STUB)\n";
    }
}

void Domain::dump() {
    LOG(DEBUG) <<"Domain expressions:\n";
    dumpExpressions(); // print contents on std::cerr
    LOG(DEBUG) <<"Domain VecIdents\n";
    dumpVecIdents(); // print contents on std::cerr
    LOG(DEBUG) <<"Domain Vector_Defs\n";
    dumpVector_Defs(); // print contents on std::cerr
}




// Check domain for consistency
// Precondition: true
// Postcondition: return value true indicates presence of inconsistencies
// Implementation: Call Lean-specific checking code below (make virtual)
bool Domain::isConsistent()
{
    Checker *c = new Checker(*this);
    bool result = c->Check();
    delete c;
    return result;
}

