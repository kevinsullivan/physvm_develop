
#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

#include "AST.h"
#include "clang/AST/AST.h"
#include "Coords.h"

#include <memory>

#include <iostream>

/*
This relational class maps Clang AST nodes to code coordinates
in our ontology. We want a single base type for all coordinates. 
Clang does not have a single base type for all AST nodes. This is
a special case of the broader reality that we will want to have
code coordinates for diverse types of code elements. So we will
need multiple function types, from various code element types to
our uniform (base class for) code coordinates. Coords subclasses
add specialized state and behavior corresponding to their concrete
code element types.

Note: At present, the only kind of Clang AST nodes that we need
are Stmt nodes. Stmt is a deep base class for Clang AST nodes,
including clang::Expr, clang::DeclRefExpr, clang:MemberCallExpr,
and so forth. So the current class is overbuilt in a sense; but
we design it as we have to show the intended path to generality.

To use this class, apply the mk methods to Clang AST nodes of 
the appropriate types. These methods create Coord objects of the
corresponding types, wrape the AST nodes in the Coords objects,
update the relational map, and return the constructed Coords. 
Client code is responsible for deleting (TBD).

Also note that Vector_Lit doesn't have a sub-expression.
*/

namespace ast2coords {

/*
When generating interpretation, we know subtypes of vector expressions
(literal, variable, function application), and so do not need and should
not use a generic putter. So here there are no superclass mkVecExpr or
Vector mk oprations. 
*/

class ASTToCoords
{
public:

    ASTToCoords();

    void setASTState(coords::Coords* coords, clang::Stmt* stmt, clang::ASTContext* c);
    void setASTState(coords::Coords* coords, clang::Decl* decl, clang::ASTContext* c);


	coords::SEQ_GLOBALSTMT* mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT* ast, clang::ASTContext* c, std::vector<coords::GLOBALSTMT*> operands );

	coords::COMPOUND_STMT* mkCOMPOUND_STMT(const ast::COMPOUND_STMT* ast, clang::ASTContext* c, std::vector<coords::STMT*> operands );

	coords::VOID_FUNC_DECL_STMT* mkVOID_FUNC_DECL_STMT(const ast::VOID_FUNC_DECL_STMT* ast, clang::ASTContext* c,coords::STMT* operand1);

	coords::MAIN_FUNC_DECL_STMT* mkMAIN_FUNC_DECL_STMT(const ast::MAIN_FUNC_DECL_STMT* ast, clang::ASTContext* c,coords::STMT* operand1);

	coords::DECL_REAL1_VAR_REAL1_EXPR* mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,coords::REAL1_EXPR* operand2);

	coords::DECL_REAL3_VAR_REAL3_EXPR* mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,coords::REAL3_EXPR* operand2);

	coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(const ast::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX4_VAR_IDENT* operand1,coords::REALMATRIX4_EXPR* operand2);

	coords::DECL_REAL4_VAR_REAL4_EXPR* mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,coords::REAL4_EXPR* operand2);

	coords::DECL_REAL1_VAR* mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1);

	coords::DECL_REAL3_VAR* mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1);

	coords::DECL_REALMATRIX4_VAR* mkDECL_REALMATRIX4_VAR(const ast::DECL_REALMATRIX4_VAR* ast, clang::ASTContext* c,coords::REALMATRIX4_VAR_IDENT* operand1);

	coords::DECL_REAL4_VAR* mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1);

	coords::REF_REALMATRIX4_VAR* mkREF_REALMATRIX4_VAR(const ast::REF_REALMATRIX4_VAR* ast, clang::ASTContext* c,coords::REALMATRIX4_VAR_IDENT* operand1);

	coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* mkMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(const ast::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX4_EXPR* operand1,coords::REALMATRIX4_EXPR* operand2);

	coords::REF_REAL4_VAR* mkREF_REAL4_VAR(const ast::REF_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::ADD_REAL4_EXPR_REAL4_EXPR* mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL4_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::MUL_REAL4_EXPR_REAL4_EXPR* mkMUL_REAL4_EXPR_REAL4_EXPR(const ast::MUL_REAL4_EXPR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL4_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::REF_REAL3_VAR* mkREF_REAL3_VAR(const ast::REF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::ADD_REAL3_EXPR_REAL3_EXPR* mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::LMUL_REAL1_EXPR_REAL3_EXPR* mkLMUL_REAL1_EXPR_REAL3_EXPR(const ast::LMUL_REAL1_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::RMUL_REAL3_EXPR_REAL1_EXPR* mkRMUL_REAL3_EXPR_REAL1_EXPR(const ast::RMUL_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(const ast::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX4_EXPR* operand1,coords::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::LREF_REAL3_VAR* mkLREF_REAL3_VAR(const ast::LREF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::REF_REAL1_VAR* mkREF_REAL1_VAR(const ast::REF_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,std::shared_ptr<float> value0);

	coords::ADD_REAL1_EXPR_REAL1_EXPR* mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0);

	coords::MUL_REAL1_EXPR_REAL1_EXPR* mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0);

	coords::REAL1_VAR_IDENT* mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT* ast, clang::ASTContext* c,std::shared_ptr<float> value0);

	coords::REAL3_VAR_IDENT* mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::REAL4_VAR_IDENT* mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::REALMATRIX4_VAR_IDENT* mkREALMATRIX4_VAR_IDENT(const ast::REALMATRIX4_VAR_IDENT* ast, clang::ASTContext* c);

	coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,coords::REAL1_EXPR* operand4,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::REAL4_EMPTY* mkREAL4_EMPTY(const ast::REAL4_EMPTY* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2,std::shared_ptr<float> value3);

	coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::REAL3_EMPTY* mkREAL3_EMPTY(const ast::REAL3_EMPTY* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);

	coords::REAL1_LIT* mkREAL1_LIT(const ast::REAL1_LIT* ast, clang::ASTContext* c,std::shared_ptr<float> value0);

	coords::REALMATRIX4_EMPTY* mkREALMATRIX4_EMPTY(const ast::REALMATRIX4_EMPTY* ast, clang::ASTContext* c);

    // TODO -- Have these routines return more specific subclass objects
    coords::Coords *getStmtCoords(const clang::Stmt *s) {
        return stmt_coords->find(s)->second;
    }

    coords::Coords *getDeclCoords(const clang::Decl *d) {
        return decl_coords->find(d)->second;
    }


	bool existsStmtCoords(const clang::Stmt* s) {
		return stmt_coords->find(s) != stmt_coords->end();
	}

	bool existsDeclCoords(const clang::Decl *d) {
		return decl_coords->find(d) != decl_coords->end();
	}



    /*
    !!!! I NEED THESE BADLY. MOVING TO PUBLIC !!!!
    */
    std::unordered_map<const clang::Stmt *, coords::Coords *> *stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> *decl_coords;
    std::unordered_map<coords::Coords *,const clang::Stmt *> *coords_stmt;
    std::unordered_map<coords::Coords *,const clang::Decl *> *coords_decl;

 private:
    void overrideStmt2Coords(const clang::Stmt *s, coords::Coords *c);
    void overrideDecl2Coords(const clang::Decl*, coords::Coords *c);
    void overrideCoords2Stmt(coords::Coords *c, const clang::Stmt *s);
    void overrideCoords2Decl(coords::Coords *c, const clang::Decl *d);
    /*
    std::unordered_map<const clang::Stmt *, coords::Coords *> stmt_coords;
    std::unordered_map<const clang::Decl *, coords::Coords *> decl_coords;
    std::unordered_map<coords::Coords *,const clang::Stmt *> coords_stmt;
    std::unordered_map<coords::Coords *,const clang::Decl *> coords_decl;
    */
    
};


} // namespace

#endif


