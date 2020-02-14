/*
Establish interpretations for AST nodes:

-  get any required information from oracle 
-  create coordinates for object
-  update ast-coord bijections
-  create corresponding domain object
-  update coord-domain bijection
-  create element-wise inter object
-  update maps: coords-interp, interp-domain
*/

// TODO: These two can be integrated
#include "Interpretation.h"
#include "Interp.h"
#include "CoordsToInterp.h"
#include "InterpToDomain.h"
#include "Oracle_AskAll.h"    // default oracle

#include <g3log/g3log.hpp>

using namespace interp;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle_AskAll(domain_); 
    /* 
    context_ can only be set later, once Clang starts parse
    */
    ast2coords_ = new ast2coords::ASTToCoords(); 
    coords2dom_ = new coords2domain::CoordsToDomain();
    coords2interp_ = new coords2interp::CoordsToInterp();
    interp2domain_ = new interp2domain::InterpToDomain();
}

/******
* Ident
******/

void Interpretation::mkVecIdent(ast::VecIdent *ast)
{
  coords::VecIdent *coords = ast2coords_->mkVecIdent(ast, context_);
  LOG(DEBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::VecIdent *dom = domain_->mkVecIdent();
  coords2dom_->putVecIdent(coords, dom);
  interp::VecIdent *interp = new interp::VecIdent(coords, dom);
  coords2interp_->putVecIdent(coords, interp);
  interp2domain_->putVecIdent(interp, dom);
}


/*****
* Expr
*****/


void Interpretation::mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/) {
    coords::VecVarExpr *coords = ast2coords_->mkVecVarExpr(ast, context_);
    LOG(DEBUG) << "Interpretation::mkVecVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    //domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::VecVarExpr *dom = domain_->mkVecVarExpr();
    coords2dom_->PutVecVarExpr(coords, dom);
    interp::VecVarExpr *interp = new interp::VecVarExpr(coords,dom);
    coords2interp_->putVecVarExpr(coords, interp);
    interp2domain_->putVecVarExpr(interp,dom);
}


void Interpretation::mkVecVecAddExpr(ast::VecVecAddExpr *add_ast, const ast::VecExpr *mem_expr, const ast::VecExpr *arg_expr) {
  coords::VecExpr *mem_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(mem_expr));
  coords::VecExpr *arg_coords = static_cast<coords::VecExpr*>
                                  (ast2coords_->getStmtCoords(arg_expr));
  LOG(DEBUG) << "Interpretation::mkVecVecAddExpr. ast=" << std::hex << add_ast << "\n";
  if (mem_coords == NULL || arg_coords == NULL) {
    LOG(FATAL) <<"Interpretation::mkVecVecAddExpr: bad coordinates. Mem coords "
            << std::hex << mem_coords << " arg coords "
            << std::hex << arg_coords << "\n";
  }
  coords::VecVecAddExpr *coords = ast2coords_->mkVecVecAddExpr(add_ast, context_, mem_coords, arg_coords);
  //domain::Space &space = oracle_->getSpaceForAddExpression(mem_coords, arg_coords);
  domain::VecExpr *dom_mem_expr = coords2dom_->getVecExpr(mem_coords);
  domain::VecExpr *dom_arg_expr = coords2dom_->getVecExpr(arg_coords);
  if (dom_mem_expr == NULL || dom_arg_expr == NULL) {
    LOG(DEBUG) <<"Interpretation::mkVecVecAddExpr: bad domain exprs. Mem "
              << std::hex << dom_mem_expr << " Arg "
              << std::hex << dom_arg_expr << "\n";
  }
  domain::VecVecAddExpr *dom = domain_->mkVecVecAddExpr(dom_mem_expr, dom_arg_expr);
  coords2dom_->PutVecVecAddExpr(coords, dom);
  LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Coords: " << mem_coords->toString() << "\n";
  LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Coords: " << arg_coords->toString() << "\n";

  interp::Interp *mem_interp = coords2interp_->getVecExpr(mem_coords);  // dyn type's toString not being called
  std::string mi_str = mem_interp->toString();
  LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Mem_Interp: " << mi_str << "\n";
  interp::Interp *arg_interp = coords2interp_->getVecExpr(arg_coords);
  LOG(DEBUG) << "Interpretation::mkVecVecAddExpr: Arg_Interp: " << arg_interp->toString() << "\n";
  interp::VecVecAddExpr *interp = new interp::VecVecAddExpr(coords, dom, mem_interp, arg_interp);
  coords2interp_->putVecVecAddExpr(coords, interp); 
  interp2domain_->putVecVecAddExpr(interp,dom);
}


void Interpretation::mkVecParenExpr(ast::VecParenExpr *ast, ast::VecExpr *expr) { 
    coords::VecParenExpr *coords = ast2coords_->mkVecParenExpr(ast, context_, expr);   
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr));
    LOG(DEBUG) << 
      "Interpretation::mkVecParenExpr. ast=" << 
      std::hex << ast << ", " << coords->toString() << 
      "expr = " << expr_coords->toString() << "\n";
    //domain::Space &space = oracle_->getSpaceForVecParenExpr(coords);
    domain::VecExpr *dom_expr = coords2dom_->getVecExpr(expr_coords);
    domain::VecParenExpr *dom = domain_->mkVecParenExpr(dom_expr);
    coords2dom_->PutVecParenExpr(coords, dom);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::VecParenExpr *interp = new interp::VecParenExpr(coords, dom, expr_interp);
    coords2interp_->putVecParenExpr(coords, interp);  
    interp2domain_->putVecParenExpr(interp,dom);
} 


/*******
* Vector
*******/

/*
Vectors are fully "constructed" objects. We're seeing a bit of Clang AST
design showing through here, as clang separated things like function appl
expressions and objects constructed from them.
*/

void Interpretation::mkVector_Lit(ast::Vector_Lit *ast, float x, float y, float z) {
    coords::Vector_Lit *coords = ast2coords_->mkVector_Lit(ast, context_, x, y, z);  
    //domain::Space& s = oracle_->getSpaceForVector_Lit(coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::Vector_Lit *dom = domain_->mkVector_Lit(x, y, z);
    coords2dom_->putVector_Lit(coords, dom); 
    interp::Vector_Lit *interp = new interp::Vector_Lit(coords, dom);
    coords2interp_->putVector_Lit(coords, interp);
    interp2domain_->putVector_Lit(interp,dom);
}

void Interpretation::mkVector_Expr(
      ast::Vector_Expr *ctor_ast, ast::VecExpr* expr_ast/*, clang::ASTContext *c*/) {
    coords::Vector_Expr *ctor_coords = ast2coords_->mkVector_Expr(ctor_ast, context_, expr_ast);
    coords::VecExpr *expr_coords = static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(expr_ast));
    //domain::Space& s = oracle_->getSpaceForVector_Expr(expr_coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::VecExpr *expr_dom = coords2dom_->getVecExpr(expr_coords);
    domain::Vector_Expr *dom_vec = domain_->mkVector_Expr(expr_dom); 
    coords2dom_->putVector_Expr(ctor_coords, dom_vec);
    interp::VecExpr *expr_interp = coords2interp_->getVecExpr(expr_coords);
    interp::Vector_Expr *interp = new interp::Vector_Expr(ctor_coords, dom_vec, expr_interp);
    coords2interp_->putVector_Expr(ctor_coords, interp);
    interp2domain_->putVector_Expr(interp, dom_vec);
}

/****
* Def
*****/

/****
 * Note: Have made decision that main communicates with Interpretation in terms
 * of coords objects alone, not in terms of interp, oracle, or domain objects.
 * */

void Interpretation::mkVector_Def(ast::Vector_Def *def_ast,  
                                  ast::VecIdent *id_ast, 
                                  ast::VecExpr *expr_ast)
{
    coords::VecIdent *id_coords = static_cast<coords::VecIdent *>
      (ast2coords_->getDeclCoords(id_ast));
    coords::Vector *vec_coords = static_cast<coords::Vector *>
      (ast2coords_->getStmtCoords(expr_ast));
    coords::Vector_Def *def_coords = ast2coords_->mkVector_Def(def_ast, context_, id_coords, vec_coords);
    domain::VecIdent *vec_ident = coords2dom_->getVecIdent(id_coords);
    /*
    Here there is some subtlety. We don't know if what was left in our
    interpretation by previous work was a Vector_Lit or a Vector_Expr.
    So we check first for a Vector_Expr
    */
    domain::Vector *vec = coords2dom_->getVector(vec_coords);
    domain::Vector_Def* dom_vec_def = 
      domain_->mkVector_Def(vec_ident, vec); 
    coords2dom_->putVector_Def(def_coords, dom_vec_def);
    interp::VecIdent *id_interp = coords2interp_->getVecIdent(id_coords);
    interp::Vector *vec_interp = coords2interp_->getVector(vec_coords);
    interp::Vector_Def *interp = new interp::Vector_Def(def_coords, dom_vec_def, id_interp, vec_interp);
    coords2interp_->putVector_Def(def_coords, interp);
    interp2domain_->putVector_Def(interp, dom_vec_def);
}

// private
// Precondition: coords2domain_ is defined for exp
//
domain::VecExpr* Interpretation::getVecExpr(ast::VecExpr* ast) {
    // we use these objects as key for query purposes
    coords::VecExpr *coords = 
        static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(ast));
    domain::VecExpr* dom = coords2dom_->getVecExpr(coords);
    if (!dom) {
        LOG(DEBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
    }
    return dom;
}

/******
 * 
 * TODO: Replace all this with direct calls to interp objects
 * TODO: Move checker-specific unparsing to separate client class.
 * ****/

// private
std::string Interpretation::toString_Spaces() {
  int index = 0;
  std::string retval = "";
  std::vector<domain::Space *> &s = domain_->getSpaces();
  for (std::vector<domain::Space *>::iterator it = s.begin(); it != s.end(); ++it)
    retval = retval.append("def ")
                 .append((*it)->toString()) 
                 .append(" : peirce.space := peirce.space.mk ")
                 .append(std::to_string(index++)) 
                 .append("\n");
  return retval;
}

// TODO: Private
//
std::string Interpretation::toString_Idents() {
    std::string retval = "";
    std::vector<domain::VecIdent*> &id = domain_->getVecIdents();
    for (std::vector<domain::VecIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
        coords::VecIdent* coords = coords2dom_->getVecIdent(*it);
        interp::VecIdent *interp = coords2interp_->getVecIdent(coords);
        retval = retval.append(interp->toString());
        retval = retval.append("\n"); 
    }
    return retval;
}

// TODO: Factor toPrint (printing) out of coords, put here in, or in client of, interpretation
//
std::string Interpretation::toString_Exprs() {
  std::string retval = "";
  std::vector<domain::VecExpr*> &id = domain_->getVecExprs();
  for (std::vector<domain::VecExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::VecExpr* coords = coords2dom_->getVecExpr(*it);
      interp::VecExpr *interp = coords2interp_->getVecExpr(coords);
      retval = retval.append(interp->toString());
      retval = retval.append("\n");
  }
  return retval;
}

std::string Interpretation::toString_Vectors() {
  std::string retval = "";
  std::vector<domain::Vector*> &id = domain_->getVectors();
  for (std::vector<domain::Vector *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Vector* coords = coords2dom_->getVector(*it);
      interp::Vector *interp = coords2interp_->getVector(coords);   
      retval = retval
      .append("(")
      .append(interp->toString())
      .append(" : vec ")
      .append((*it)->getSpace()->toString())
      .append(")\n");
  }
  return retval;
}

std::string Interpretation::toString_Defs() {
  std::string retval = "";
  std::vector<domain::Vector_Def*> &id = domain_->getVectorDefs();
  for (std::vector<domain::Vector_Def *>::iterator it = id.begin(); it != id.end(); ++it) {
      coords::Vector_Def* coords = coords2dom_->getVector_Def(*it);
      interp::Vector_Def *interp = coords2interp_->getVector_Def(coords);
      retval = retval.append(interp->toString()).append("\n");
  }
  return retval;
}

void Interpretation::setAll_Spaces() {
  auto vecIdents = domain_->getVecIdents();
  auto vecExprs = domain_->getVecExprs();
  auto vecs = domain_->getVectors();
  auto vecDefs = domain_->getVectorDefs();

  for(auto beg = vecIdents.begin(); beg != vecIdents.end(); beg++)
  {
   /* coords::VecIdent *coords = ast2coords_->mkVecIdent(ast, context_);
  LOG(DEBUG) << "Interpretation::mkVecIdent. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
  //domain::Space &space = oracle_->getSpaceForVecIdent(coords);
  domain::VecIdent *dom = domain_->mkVecIdent();
  coords2dom_->putVecIdent(coords, dom);
  interp::VecIdent *interp = new interp::VecIdent(coords, dom);
  coords2interp_->putVecIdent(coords, interp);
  interp2domain_->putVecIdent(interp, dom);
*/

    auto p = *beg;

    coords::VecIdent *coords = coords2dom_->getVecIdent(*beg);
    domain::Space& space = oracle_->getSpaceForVecIdent(coords);
    p->setSpace(&space);

  }

  for(auto beg = vecExprs.begin(); beg != vecExprs.end(); beg++)
  {
    /*
    coords::VecVarExpr *coords = ast2coords_->mkVecVarExpr(ast, context_);
    LOG(DEBUG) << "Interpretation::mkVecVarExpr. ast=" << std::hex << ast << ", " << coords->toString() << "\n";
    //ast->dump();
    domain::Space &space = oracle_->getSpaceForVecVarExpr(coords);
    domain::VecVarExpr *dom = domain_->mkVecVarExpr(space);
    coords2dom_->PutVecVarExpr(coords, dom);
    interp::VecVarExpr *interp = new interp::VecVarExpr(coords,dom);
    coords2interp_->putVecVarExpr(coords, interp);
    interp2domain_->putVecVarExpr(interp,dom);

    */
    auto ve = *beg;

    auto vve = (domain::VecVarExpr*)ve;
    auto vpr = (domain::VecParenExpr*)ve;
    auto vvae = (domain::VecVecAddExpr*)ve;

    coords::VecExpr *coords = coords2dom_->getVecExpr(*beg);

    auto cvve = (coords::VecVarExpr*)coords;
    auto cvvpr = (coords::VecParenExpr*)coords;
    auto cvvae = (coords::VecVecAddExpr*)coords;

    if(vve)
    {

      domain::Space& space = oracle_->getSpaceForVecVarExpr(coords);
      ve->setSpace(&space);
    }
    else if(vpr)
    {

      domain::Space& space = oracle_->getSpaceForVecParenExpr(coords);
      ve->setSpace(&space);
    }
    else if(vvae)
    {
      auto left = (coords::VecExpr*) cvvae->getLeft();
      auto right = (coords::VecExpr*) cvvae->getRight();

      domain::Space& space = oracle_->getSpaceForAddExpression(left, right);
      ve->setSpace(&space);
    }
    
  }

  for(auto beg = vecs.begin(); beg != vecs.end(); beg++)
  {
    /*
    coords::Vector_Lit *coords = ast2coords_->mkVector_Lit(ast, context_, x, y, z);  
    //domain::Space& s = oracle_->getSpaceForVector_Lit(coords);  //*new domain::Space("Interpretation::mkVector_Expr:: Warning. Using Stub Space\n.");
    domain::Vector_Lit *dom = domain_->mkVector_Lit(x, y, z);
    coords2dom_->putVector_Lit(coords, dom); 
    interp::Vector_Lit *interp = new interp::Vector_Lit(coords, dom);
    coords2interp_->putVector_Lit(coords, interp);
    interp2domain_->putVector_Lit(interp,dom);
    */
    auto vec = *beg;

    auto vl = (domain::Vector_Lit*)vec;
    auto ve = (domain::Vector_Expr*)vec;

    if(vl)
    {
      coords::Vector_Lit* cvl = coords2dom_->getVector_Lit(vl);

      domain::Space& s = oracle_->getSpaceForVector_Lit(cvl);
      vec->setSpace(&s);
    }
    else if(ve)
    {
      coords::Vector_Expr* cve = coords2dom_->getVector_Expr(ve);
      domain::Space& s = oracle_->getSpaceForVector_Expr(cve);
      vec->setSpace(&s);
    }

  }
  //not required for these
  for(auto beg = vecDefs.begin(); beg != vecDefs.end(); beg++)
  {
    auto vd = *beg;

    int i = 1;
  }

}


