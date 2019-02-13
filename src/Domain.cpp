#include <vector>
#include <iostream>
#include "Checker.h"
#include "Domain.h"

using namespace std;
using namespace domain;

string Space::getName() const { return name_; }

const Space &domain::Expr::getSpace() const { return space_; }


string Identifier::getName() const
{
    cerr << "Identifier::getName(): vardecl_  addr is " << std::hex << vardecl_->getVarDecl() << "\n";
    return "(" + vardecl_->toString() + " : " + space_->getName() + ")";
}

// TODO: currently UNUSED
void VecLitExpr::addFloatLit(float num)
{
    cerr << "Stub: add floats to litvalexpr\n";
}

const domain::Expr &VecAddExpr::getVecAddExprArgL()
{
    return arg_left_;
}

const domain::Expr &VecAddExpr::getVecAddExprArgR()
{
    return arg_right_;
}

/*const Identifier &Binding::getIdentifier()
{
    return identifier_;
}
*/

Space &Domain::addSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(*s);
    //cerr << "Added space to domain at address " << std::hex << s << "\n";
    return *s;
}


domain::Expr *Domain::addVecLitExpr(Space &s, const coords::LitASTNode *e)
{
    domain::Expr *be = new domain::Expr(s, e);
    //cerr << "Adding Vec Lit Expr to domain, address " << std::hex << be << " dump before is ... \n";
    //dump();
    expressions.push_back(be);
    //cerr << "... dump after is ...\n";
    //dump();
    return be;
}

// precondition: variable already interpreted
Space &getSpaceOfVarExpr(const coords::ExprASTNode *ast)
{
    // look up variable (ast) in identifiers table
    // Space& s = getSpaceOf(ast,identifiers);
    // return s;

    // get and return the space assigned to that object
    //cerr << "STUB: Domain: getSpaceOfVarExpr in Domain.cpp\n";
    return *new Space("_");
}

// TODO: Change arg type to be more precise
domain::Expr &Domain::addVecVarExpr(const coords::VarDeclRefASTNode *ast)
{
    Space &s = getSpaceOfVarExpr(ast);
    domain::Expr *be = new domain::Expr(s, ast);
    cerr << "Adding Vec Var Expr to domain, address " << std::hex << be << ": " << be->toString() << "\n";
    //dump();
    expressions.push_back(be);
    //cerr << "... dump after is ...\n";
    //dump();
    return *be;
}

domain::Expr *Domain::addVecAddExpr(Space &s, coords::VectorAddExprASTNode *e, domain::Expr *mem, domain::Expr *arg)
{
    domain::Expr *be = new domain::VecAddExpr(s, e, mem, arg);
    expressions.push_back(be);
    cerr << "Domain::addVecAddExpr:: Add. Coords are "
        << std::hex << e << " Domain Expr at " << std::hex << be << "\n";
    cerr << "Domain::addVecAddExpr:: Expr string is " << be->toString() << "\n";
    return *be;
}

Identifier *Domain::addIdentifier(Space &s, const coords::VecIdent *ast)
{
    Identifier *id = new Identifier(s, ast);
    identifiers.push_back(*id);
    return id;
}

// TODO: Should be binding to Vector, not Expr
// 
Binding &Domain::addBinding(const coords::BindingASTNode *v, const Identifier* i, const domain::Expr* e)
{
    cerr << "Domain::addBinding ";
    cerr << "identifier is " << i->toString();
    cerr << " expression is " << e->toString() << "\n";
    Binding *bd = new Binding(v, i, e);
/*
Domain.cpp:116:38: error: no matching function for call to 'domain::Binding::Binding(const coords::BindingASTNode*&, const domain::Identifier*&, const domain::Expr*&)'
     Binding *bd = new Binding(v, i, e);
                                      ^
*/
    bindings.push_back(*bd);
    return *bd;
}

Vector* Domain::addVector(coords VectorASTNode* coords, domain::Expr *expr) {
    Vector* vec = new Vector(coords, expr);
    vectors.push_back(*vec);
}


// TODO: Use pointers everywhere here?
void Domain::dumpIdentifiers()
{
    for (auto i: identifiers ){
        cerr << i.toString() << "\n";
    }
}

void Domain::dumpExpressions()
{
    for (auto e: expressions ){
        cerr << e->toString() << "\n";
    }
}

void Domain::dumpBindings()
{
    for (auto b: bindings ){
        cerr << b.toString() << "\n";
    }
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

vector<Space> &Domain::getAllSpaces()
{
    return spaces;
}
