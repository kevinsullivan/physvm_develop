#include <vector>
#include <iostream>
#include "Checker.h"
#include "Bridge.h"

using namespace std;
using namespace bridge;

string Space::getName() const { return name_; }

const Space &bridge::Expr::getSpace() const { return space_; }

Identifier::Identifier(Space &space, const IdentifierASTNode *vardecl) : space_(&space), vardecl_(vardecl)
{
}

string Identifier::getName() const
{
    return "(" + vardecl_->getVarDecl()->getNameAsString() + " : " + space_->getName() + ")";
}

string Identifier::toString() const
{
    return getName();
}

// TODO: currently UNUSED
void VecLitExpr::addFloatLit(float num)
{
    cerr << "Stub: add floats to litvalexpr\n";
}

const bridge::Expr &VecAddExpr::getVecAddExprArgL()
{
    return arg_left_;
}

const bridge::Expr &VecAddExpr::getVecAddExprArgR()
{
    return arg_right_;
}

const Identifier &Binding::getIdentifier()
{
    return identifier_;
}

Space &Bridge::addSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(*s);
    //cerr << "Added space to domain bridge at address " << std::hex << s << "\n";
    return *s;
}


bridge::Expr &Bridge::addVecLitExpr(Space &s, LitASTNode *e)
{
    bridge::Expr *be = new bridge::Expr(s, e);
    //cerr << "Adding Vec Lit Expr to domain, address " << std::hex << be << " dump before is ... \n";
    //dump();
    expressions.push_back(be);
    //cerr << "... dump after is ...\n";
    //dump();
    return *be;
}

// precondition: variable already interpreted
Space &getSpaceOfVarExpr(const ExprASTNode *ast)
{
    // look up variable (ast) in identifiers table
    // Space& s = getSpaceOf(ast,identifiers);
    // return s;

    // get and return the space assigned to that object
    //cerr << "STUB: Bridge: getSpaceOfVarExpr in Bridge.cpp\n";
    return *new Space("_");
}

// TODO: Change arg type to be more precise
bridge::Expr &Bridge::addVecVarExpr(const VarDeclRefASTNode *ast)
{
    Space &s = getSpaceOfVarExpr(ast);
    bridge::Expr *be = new bridge::Expr(s, ast);
    //cerr << "Adding Vec Var Expr to domain, address " << std::hex << be << " dump before is ... \n";
    //dump();
    expressions.push_back(be);
    //cerr << "... dump after is ...\n";
    //dump();
    return *be;
}

bridge::Expr &Bridge::addVecAddExpr(Space &s, VectorAddExprASTNode *e, bridge::Expr &left, bridge::Expr &right)
{
    bridge::Expr *be = new bridge::VecAddExpr(s, e, left, right);
    expressions.push_back(be);
    return *be;
}

Identifier &Bridge::addIdentifier(Space &s, const IdentifierASTNode *ast)
{
    Identifier *id = new Identifier(s, ast);
    identifiers.push_back(*id);
    return *id;
}

Binding &Bridge::addBinding(BindingASTNode *v, const Identifier &i,
                            const bridge::Expr &e)
{
    Binding *bd = new Binding(v, i, e);
    bindings.push_back(*bd);
    return *bd;
}

// TODO: Use pointers everywhere here?
void Bridge::dumpIdentifiers()
{
    for (auto i: identifiers ){
        cerr << i.toString() << "\n";
    }
}

void Bridge::dumpExpressions()
{
    for (auto e: expressions ){
        cerr << e->toString() << "\n";
    }
}

void Bridge::dumpBindings()
{
    for (auto b: bindings ){
        cerr << b.toString() << "\n";
    }
}

// Check domain for consistency
// Precondition: true
// Postcondition: return value true indicates presence of inconsistencies
// Implementation: Call Lean-specific checking code below (make virtual)
bool Bridge::isConsistent()
{
    Checker *c = new Checker(*this);
    bool result = c->Check();
    delete c;
    return result;
}

vector<Space> &Bridge::getAllSpaces()
{
    return spaces;
}
