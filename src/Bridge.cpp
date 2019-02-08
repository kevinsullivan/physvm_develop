#include <vector>
#include <iostream>
#include "Checker.h"
#include "Bridge.h"

using namespace std;
using namespace bridge;

string Space::getName() const { return name_; }

const Space &bridge::Expr::getSpace() { return space_; }

Identifier::Identifier(Space &space, const VarDeclASTNode *vardecl) : space_(&space), vardecl_(vardecl)
{
}

string Identifier::getName()
{
    return vardecl_->getVarDecl()->getNameAsString();
}
// UNUSED -- fix
// VecLitExpr class member function implementation
void VecLitExpr::addFloatLit(float num)
{
    cerr << "Stub: add floats to litvalexpr\n";
}

// VecVarExpr class member function implementation
// const Space& VecVarExpr::getVecVarSpace(){ return space_;}

// VecAddExpr class member function implementation

// forward references
const bridge::Expr &VecAddExpr::getVecAddExprArgL()
{
    return arg_left_;
}

const bridge::Expr &VecAddExpr::getVecAddExprArgR()
{
    return arg_right_;
}

// FOR STUBS. Fix/Remove.
//
//const Space& VecAddExpr::getVecAddExprDefaultSpace(){
//	return space_;
//}

// Binding class member function implementation
//
const Identifier &Binding::getIdentifier()
{
    return identifier_;
}

Space &Bridge::addSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(*s);
    cerr << "Added space to domain bridge at address " << std::hex << s << "\n";
    return *s;
}

/*
BIG TODO : Rewrite all routines here to take AST container nodes,
as illustrated in addLitExpr just below.
*/

/*
// Add new vector, v, in space s, to domain
// Precondition: s is already in spaces
// Postcondition: vectors' = vectors + v
bridge::VecLitExpr& Bridge::addLitExpr(Space& s, const LitASTNode* ast) {
    VecLitExpr *v = new VecLitExpr(s,ast);
    expressions.push_back(*v);
    cerr << "Added Vec Lit Expr to domain bridge at address " << std::hex << v << "\n";
    return *v;
}
*/

// precondition: variable already interpreted
Space &getSpaceOfVarExpr(const ExprASTNode *ast)
{
    // look up variable (ast) in identifiers table
    // Space& s = getSpaceOf(ast,identifiers);
    // return s;

    // get and return the space assigned to that object
    cerr << "STUB: Bridge: getSpaceOfVarExpr in Bridge.cpp\n";
    return *new Space("");
}

bridge::Expr &Bridge::addVecLitExpr(Space &s, ExprASTNode *e)
{
    bridge::Expr *be = new bridge::Expr(s, e);
    cerr << "Adding Vec Lit Expr to domain, address " << std::hex << be << " dump before is ... \n";
    dump();
    expressions.push_back(be);
    cerr << "... dump after is ...\n";
    dump();
    return *be;
}

bridge::Expr &Bridge::addVecVarExpr(const ExprASTNode *ast)
{
    Space &s = getSpaceOfVarExpr(ast);
    bridge::Expr *be = new bridge::Expr(s, ast);
    cerr << "Adding Vec Var Expr to domain, address " << std::hex << be << " dump before is ... \n";
    dump();
    expressions.push_back(be);
    cerr << "... dump after is ...\n";
    dump();
    return *be;
}

bridge::Expr &Bridge::addVecAddExpr(Space &s, ExprASTNode *e, bridge::Expr &left, bridge::Expr &right)
{
    bridge::Expr *be = new bridge::VecAddExpr(s, e, left, right);
    cerr << "Adding Vec Add Expr to domain, address " << std::hex << be << " dump before is ... \n";
    dump();
    expressions.push_back(be);
    cerr << "... dump after is ... \n";
    dump();
    return *be;
}

Identifier &Bridge::addIdentifier(Space &s, const VarDeclASTNode *ast)
{
    Identifier *id = new Identifier(s, ast);
    identifiers.push_back(*id);
    cerr << "Added Identifier to domain bridge at address "
         << id << "\n";
    return *id;
}

Binding &Bridge::addBinding(VarDeclASTNode *v, const Identifier &i,
                            const bridge::Expr &e)
{
    Binding *bd = new Binding(v, i, e);
    bindings.push_back(*bd);
    cerr << "Added binding from ident at " << std::hex << &i << " to expr at " << std::hex << &e << " into domain bridge" << endl;
    return *bd;
}

void Bridge::dump()
{
    cerr << "BRIDGE DUMP:\n";
    for (auto e: expressions ){
        cerr << "Dumping expr at " << std::hex << e << "\n";
    	if (e != NULL) {
             cerr << e->toString() << "\n";
        }
        else {
            cerr << "Bridge::dump():: NULL Expr pointer!\n";
        }
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
