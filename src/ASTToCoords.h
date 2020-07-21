
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

	coords::MAIN_STMT* mkMAIN_STMT(const ast::MAIN_STMT* ast, clang::ASTContext* c,coords::STMT* operand1);

	coords::FUNCTION_STMT* mkFUNCTION_STMT(const ast::FUNCTION_STMT* ast, clang::ASTContext* c,coords::STMT* operand1);

	coords::COMPOUND_STMT* mkCOMPOUND_STMT(const ast::COMPOUND_STMT* ast, clang::ASTContext* c, std::vector<coords::STMT*> operands );

	coords::IFTHEN_EXPR_STMT* mkIFTHEN_EXPR_STMT(const ast::IFTHEN_EXPR_STMT* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2);

	coords::IFTHENELSEIF_EXPR_STMT_IFCOND* mkIFTHENELSEIF_EXPR_STMT_IFCOND(const ast::IFTHENELSEIF_EXPR_STMT_IFCOND* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2,coords::IFCOND* operand3);

	coords::IFTHENELSE_EXPR_STMT_STMT* mkIFTHENELSE_EXPR_STMT_STMT(const ast::IFTHENELSE_EXPR_STMT_STMT* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2,coords::STMT* operand3);

	coords::ASSIGN_REAL1_VAR_REAL1_EXPR* mkASSIGN_REAL1_VAR_REAL1_EXPR(const ast::ASSIGN_REAL1_VAR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,coords::REAL1_EXPR* operand2);

	coords::ASSIGN_REAL3_VAR_REAL3_EXPR* mkASSIGN_REAL3_VAR_REAL3_EXPR(const ast::ASSIGN_REAL3_VAR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,coords::REAL3_EXPR* operand2);

	coords::ASSIGN_REAL4_VAR_REAL4_EXPR* mkASSIGN_REAL4_VAR_REAL4_EXPR(const ast::ASSIGN_REAL4_VAR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,coords::REAL4_EXPR* operand2);

	coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* mkASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1,coords::REALMATRIX_EXPR* operand2);

	coords::DECL_REAL1_VAR_REAL1_EXPR* mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,coords::REAL1_EXPR* operand2);

	coords::DECL_REAL3_VAR_REAL3_EXPR* mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,coords::REAL3_EXPR* operand2);

	coords::DECL_REAL4_VAR_REAL4_EXPR* mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,coords::REAL4_EXPR* operand2);

	coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1,coords::REALMATRIX_EXPR* operand2);

	coords::DECL_REAL1_VAR* mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1);

	coords::DECL_REAL3_VAR* mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1);

	coords::DECL_REAL4_VAR* mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1);

	coords::DECL_REALMATRIX_VAR* mkDECL_REALMATRIX_VAR(const ast::DECL_REALMATRIX_VAR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1);

	coords::PAREN_REAL1_EXPR* mkPAREN_REAL1_EXPR(const ast::PAREN_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1);

	coords::INV_REAL1_EXPR* mkINV_REAL1_EXPR(const ast::INV_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1);

	coords::NEG_REAL1_EXPR* mkNEG_REAL1_EXPR(const ast::NEG_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1);

	coords::ADD_REAL1_EXPR_REAL1_EXPR* mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::SUB_REAL1_EXPR_REAL1_EXPR* mkSUB_REAL1_EXPR_REAL1_EXPR(const ast::SUB_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::MUL_REAL1_EXPR_REAL1_EXPR* mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::DIV_REAL1_EXPR_REAL1_EXPR* mkDIV_REAL1_EXPR_REAL1_EXPR(const ast::DIV_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::REF_REAL1_VAR* mkREF_REAL1_VAR(const ast::REF_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1);

	coords::PAREN_REAL3_EXPR* mkPAREN_REAL3_EXPR(const ast::PAREN_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1);

	coords::ADD_REAL3_EXPR_REAL3_EXPR* mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2);

	coords::SUB_REAL3_EXPR_REAL3_EXPR* mkSUB_REAL3_EXPR_REAL3_EXPR(const ast::SUB_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2);

	coords::INV_REAL3_EXPR* mkINV_REAL3_EXPR(const ast::INV_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1);

	coords::NEG_REAL3_EXPR* mkNEG_REAL3_EXPR(const ast::NEG_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1);

	coords::MUL_REAL3_EXPR_REAL1_EXPR* mkMUL_REAL3_EXPR_REAL1_EXPR(const ast::MUL_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* mkMUL_REALMATRIX_EXPR_REAL3_EXPR(const ast::MUL_REALMATRIX_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1,coords::REAL3_EXPR* operand2);

	coords::DIV_REAL3_EXPR_REAL1_EXPR* mkDIV_REAL3_EXPR_REAL1_EXPR(const ast::DIV_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::REF_REAL3_VAR* mkREF_REAL3_VAR(const ast::REF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1);

	coords::PAREN_REAL4_EXPR* mkPAREN_REAL4_EXPR(const ast::PAREN_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1);

	coords::ADD_REAL4_EXPR_REAL4_EXPR* mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL4_EXPR* operand2);

	coords::MUL_REAL4_EXPR_REAL1_EXPR* mkMUL_REAL4_EXPR_REAL1_EXPR(const ast::MUL_REAL4_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL1_EXPR* operand2);

	coords::REF_REAL4_VAR* mkREF_REAL4_VAR(const ast::REF_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1);

	coords::PAREN_REALMATRIX_EXPR* mkPAREN_REALMATRIX_EXPR(const ast::PAREN_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1);

	coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* mkMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(const ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1,coords::REALMATRIX_EXPR* operand2);

	coords::REF_EXPR_REALMATRIX_VAR* mkREF_EXPR_REALMATRIX_VAR(const ast::REF_EXPR_REALMATRIX_VAR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1);

	coords::REAL1_VAR_IDENT* mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT* ast, clang::ASTContext* c);

	coords::REAL3_VAR_IDENT* mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT* ast, clang::ASTContext* c);

	coords::REAL4_VAR_IDENT* mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT* ast, clang::ASTContext* c);

	coords::REALMATRIX_VAR_IDENT* mkREALMATRIX_VAR_IDENT(const ast::REALMATRIX_VAR_IDENT* ast, clang::ASTContext* c);

	coords::REAL1_LITERAL1* mkREAL1_LITERAL1(const ast::REAL1_LITERAL1* ast, clang::ASTContext* c,double value1);

	coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3);

	coords::REAL3_LITERAL3* mkREAL3_LITERAL3(const ast::REAL3_LITERAL3* ast, clang::ASTContext* c,double value1,double value2,double value3);

	coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,coords::REAL1_EXPR* operand4);

	coords::REAL4_LITERAL4* mkREAL4_LITERAL4(const ast::REAL4_LITERAL4* ast, clang::ASTContext* c,double value1,double value2,double value3,double value4);

	coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* mkREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(const ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2,coords::REAL3_EXPR* operand3);

	coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* mkREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,coords::REAL1_EXPR* operand4,coords::REAL1_EXPR* operand5,coords::REAL1_EXPR* operand6,coords::REAL1_EXPR* operand7,coords::REAL1_EXPR* operand8,coords::REAL1_EXPR* operand9);

	coords::REALMATRIX_LITERAL9* mkREALMATRIX_LITERAL9(const ast::REALMATRIX_LITERAL9* ast, clang::ASTContext* c,double value1,double value2,double value3,double value4,double value5,double value6,double value7,double value8,double value9);

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


