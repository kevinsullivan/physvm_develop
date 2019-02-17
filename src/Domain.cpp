#include <vector>
#include <iostream>
#include "Checker.h"
#include "Domain.h"

using namespace std;
using namespace domain;


/******
* Space
******/

Space &Domain::mkSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(*s);
    //std::cerr << "Added space to domain at address " << std::hex << s << "\n";
    return *s;
}


// TODO: STUB
// precondition: variable already interpreted
Space &getSpaceOfVarExpr(const coords::VecExpr *ast)
{
    // look up variable (ast) in identifiers table
    // Space& s = getSpaceOf(ast,identifiers);
    // return s;

    // get and return the space assigned to that object
    //std::cerr << "STUB: Domain: getSpaceOfVarExpr in Domain.cpp\n";
    return *new Space("_");
}

vector<Space> &Domain::getAllSpaces()
{
    return spaces;
}


// TODO: MOVE THIS STUFF
std::string Space::getName() const { return name_; }

const Space &domain::VecExpr::getSpace() const { return space_; }



/****
Ident
****/


VecIdent *Domain::mkVecIdent(Space &s, const coords::VecIdent *ast)
{
    VecIdent *id = new VecIdent(s, ast);
    idents.push_back(*id);
    return id;
}


std::string VecIdent::getName() const
{
    std::cerr << "VecIdent::getName(): vardecl_  addr is " << std::hex << vardecl_->getVarDecl() << "\n";
    return "(" + vardecl_->toString() + " : " + space_->getName() + ")";
}

/****
 Expr
****/


domain::VecExpr *Domain::mkVecLitExpr(Space &s, const coords::VecLitExpr *e)
{
    domain::VecExpr *be = new domain::VecExpr(s, e);
    //std::cerr << "Adding Vec Lit Expr to domain, address " << std::hex << be << " dump before is ... \n";
    //dump();
    exprs.push_back(be);
    //std::cerr << "... dump after is ...\n";
    //dump();
    return be;
}

domain::VecExpr *Domain::mkVecVarExpr(Space &s, const coords::VecVarExpr *ast)
{
    domain::VecExpr *var = new domain::VecExpr(s, ast);
    std::cerr << "Adding Vec Var Expr to domain, address " << std::hex << var << ": " << var->toString() << "\n";
    //dump();
    exprs.push_back(var);
    //std::cerr << "... dump after is ...\n";
    //dump();
    return var;
}

domain::VecExpr *Domain::mkVecVecAddExpr(Space &s, coords::VecVecAddExpr *e, domain::VecExpr *mem, domain::VecExpr *arg)
{
    domain::VecExpr *be = new domain::VecVecAddExpr(s, e, mem, arg);
    exprs.push_back(be);
    std::cerr << "Domain::mkVecVecAddExpr:: Add. Coords are "
        << std::hex << e << " Domain VecExpr at " << std::hex << be << "\n";
    std::cerr << "Domain::mkVecVecAddExpr:: VecExpr string is " << be->toString() << "\n";
    return *be;
}

const domain::VecExpr &VecVecAddExpr::getVecVecAddExprArgL()
{
    return arg_left_;
}

const domain::VecExpr &VecVecAddExpr::getVecVecAddExprArgR()
{
    return arg_right_;
}

/******
* Value
*******/

Vector* Domain::mkVector_Lit(Space& space, coords::Vector* coords) {
    Vector* vec = new domain::Vector_Lit(space, coords);
    vectors.push_back(*vec);
    return vec;
}

Vector* Domain::mkVector_Expr(Space& s, coords::Vector* coords, domain::Expr* exp) {
    Vector* vec = new domain::Vector_Expr(space, coords, expr);
    vectors.push_back(*vec);
    return vec;
}

/*
Vector* Domain::mkVector_Var(Space& s, coords::Vector* coords, domain::Expr* exp) {
    Vector* vec = new domain::Vector_Var(space, coords, expr);
    vectors.push_back(*vec);
    return vec;
}
*/


/****
* Def
*****/


// TODO: Should be binding to Vector, not Expr
// 
Vector_Def &Domain::mkVector_Def(const coords::Vector_Def *v, const VecIdent* i, const domain::VecExpr* e)
{
    std::cerr << "Domain::mkVector_Def ";
    std::cerr << "identifier is " << i->toString();
    std::cerr << " expression is " << e->toString() << "\n";
    Vector_Def *bd = new Vector_Def(v, i, e);
    defs.push_back(*bd);
    return *bd;
}

/********
* Details
********/


// TODO: Use pointers everywhere here?
void Domain::dumpIdentifiers()
{
    for (auto i: idents ){
        std::cerr << i.toString() << "\n";
    }
}

void Domain::dumpExpressions()
{
    for (auto e: exprs ){
        std::cerr << e->toString() << "\n";
    }
}

void Domain::dumpVector_Defs()
{
    for (auto b: defs ){
        std::cerr << b.toString() << "\n";
    }
}

void Domain::dump() {
    std::cerr << "Domain expressions:\n";
    dumpExpressions(); // print contents on std::cerr
    std::cerr << "Domain VecIdents\n";
    dumpVecIdents(); // print contents on std::cerr
    std::cerr << "Domain Vector_Defs\n";
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

