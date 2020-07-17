
#include "ASTToCoords.h"
#include <g3log/g3log.hpp>

#include<iostream>
#include<exception>
#include<memory>
#include<string>

#include "llvm/Support/Casting.h"
/*
Create Coords object for given AST node and update AST-to_Coords
mappings. Currently this means just the ast2coords unorderedmaps,
one for Clang AST objects inheriting from Stmt, and one for Clang
AST objects inheriting from Decl. We maintain both forward and
backwards maps. See AST.h for the translations.
*/
using namespace ast2coords;

void ASTToCoords::setASTState(coords::Coords* coords, clang::Stmt* stmt, clang::ASTContext* c)
{
    auto range = stmt->getSourceRange();
    auto begin = c->getFullLoc(range.getBegin());
    auto end = c->getFullLoc(range.getEnd());

    coords->state_ = new coords::ASTState(
        "",
        "",
        "",
        (clang::dyn_cast<clang::DeclRefExpr>(stmt)) ? (clang::dyn_cast<clang::DeclRefExpr>(stmt))->getDecl()->getNameAsString() : "",
        begin.getSpellingLineNumber(),
        begin.getSpellingColumnNumber(),
        end.getSpellingLineNumber(),
        end.getSpellingColumnNumber()
    );
    /*
    coords->state_.file_id_ = new std::string("");
    coords->state_.file_name_ = "";
    coords->state_.file_path_ = "";

    coords->state_.name_ = 
        ((clang::DeclRefExpr*) stmt) ? ((clang::DeclRefExpr*) stmt)->getDecl()->getNameAsString() : "";


    coords->state_.begin_line_no_ = begin.getSpellingLineNumber();
    coords->state_.begin_col_no_ = begin.getSpellingColumnNumber();
    coords->state_.end_line_no_ = end.getSpellingLineNumber();
    coords->state_.end_col_no_ = end.getSpellingColumnNumber();
    */
}

void ASTToCoords::setASTState(coords::Coords* coords, clang::Decl* decl, clang::ASTContext* c)
{
    auto range = decl->getSourceRange();
    auto begin = c->getFullLoc(range.getBegin());
    auto end = c->getFullLoc(range.getEnd());

    coords->state_ = new coords::ASTState(
        "",
        "",
        "",
        (clang::dyn_cast<clang::NamedDecl>(decl)) ? (clang::dyn_cast<clang::NamedDecl>(decl))->getNameAsString() : "",
        begin.getSpellingLineNumber(),
        begin.getSpellingColumnNumber(),
        end.getSpellingLineNumber(),
        end.getSpellingColumnNumber()
    );
    /*
    coords->state_.file_id_ = "";
    coords->state_.file_name_ = "";
    coords->state_.file_path_ = "";

    coords->state_.name_ = ((clang::NamedDecl*) decl) ? ((clang::NamedDecl*) decl)->getNameAsString() : "";

    coords->state_.begin_line_no_ = begin.getSpellingLineNumber();
    coords->state_.begin_col_no_ = begin.getSpellingColumnNumber();
    coords->state_.end_line_no_ = end.getSpellingLineNumber();
    coords->state_.end_col_no_ = end.getSpellingColumnNumber();
    */
}

ASTToCoords::ASTToCoords() {
   this->stmt_coords = new std::unordered_map<const clang::Stmt*, coords::Coords*>();
   this->decl_coords = new std::unordered_map<const clang::Decl*, coords::Coords*>();
   this->coords_stmt = new std::unordered_map<coords::Coords*,const clang::Stmt*>();
   this->coords_decl = new std::unordered_map<coords::Coords*,const clang::Decl*>();
}


     coords::COMPOUND_STMT* ASTToCoords::mkCOMPOUND_STMT(const ast::COMPOUND_STMT* ast, clang::ASTContext* c, std::vector<coords::STMT*> operands ){
        coords::COMPOUND_STMT* coord = new coords::COMPOUND_STMT(operands);
        ast::COMPOUND_STMT* unconst_ast = const_cast<ast::COMPOUND_STMT*>(ast);

        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::IFTHEN_EXPR_STMT* ASTToCoords::mkIFTHEN_EXPR_STMT(const ast::IFTHEN_EXPR_STMT* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2){
        coords::IFTHEN_EXPR_STMT* coord = new coords::IFTHEN_EXPR_STMT(operand1,operand2);
        ast::IFTHEN_EXPR_STMT* unconst_ast = const_cast<ast::IFTHEN_EXPR_STMT*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::IFTHENELSEIF_EXPR_STMT_IFCOND* ASTToCoords::mkIFTHENELSEIF_EXPR_STMT_IFCOND(const ast::IFTHENELSEIF_EXPR_STMT_IFCOND* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2,coords::IFCOND* operand3){
        coords::IFTHENELSEIF_EXPR_STMT_IFCOND* coord = new coords::IFTHENELSEIF_EXPR_STMT_IFCOND(operand1,operand2,operand3);
        ast::IFTHENELSEIF_EXPR_STMT_IFCOND* unconst_ast = const_cast<ast::IFTHENELSEIF_EXPR_STMT_IFCOND*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::IFTHENELSE_EXPR_STMT_STMT* ASTToCoords::mkIFTHENELSE_EXPR_STMT_STMT(const ast::IFTHENELSE_EXPR_STMT_STMT* ast, clang::ASTContext* c,coords::EXPR* operand1,coords::STMT* operand2,coords::STMT* operand3){
        coords::IFTHENELSE_EXPR_STMT_STMT* coord = new coords::IFTHENELSE_EXPR_STMT_STMT(operand1,operand2,operand3);
        ast::IFTHENELSE_EXPR_STMT_STMT* unconst_ast = const_cast<ast::IFTHENELSE_EXPR_STMT_STMT*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ASSIGN_REAL1_VAR_REAL1_EXPR* ASTToCoords::mkASSIGN_REAL1_VAR_REAL1_EXPR(const ast::ASSIGN_REAL1_VAR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,coords::REAL1_EXPR* operand2){
        coords::ASSIGN_REAL1_VAR_REAL1_EXPR* coord = new coords::ASSIGN_REAL1_VAR_REAL1_EXPR(operand1,operand2);
        ast::ASSIGN_REAL1_VAR_REAL1_EXPR* unconst_ast = const_cast<ast::ASSIGN_REAL1_VAR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ASSIGN_REAL3_VAR_REAL3_EXPR* ASTToCoords::mkASSIGN_REAL3_VAR_REAL3_EXPR(const ast::ASSIGN_REAL3_VAR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,coords::REAL3_EXPR* operand2){
        coords::ASSIGN_REAL3_VAR_REAL3_EXPR* coord = new coords::ASSIGN_REAL3_VAR_REAL3_EXPR(operand1,operand2);
        ast::ASSIGN_REAL3_VAR_REAL3_EXPR* unconst_ast = const_cast<ast::ASSIGN_REAL3_VAR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ASSIGN_REAL4_VAR_REAL4_EXPR* ASTToCoords::mkASSIGN_REAL4_VAR_REAL4_EXPR(const ast::ASSIGN_REAL4_VAR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,coords::REAL4_EXPR* operand2){
        coords::ASSIGN_REAL4_VAR_REAL4_EXPR* coord = new coords::ASSIGN_REAL4_VAR_REAL4_EXPR(operand1,operand2);
        ast::ASSIGN_REAL4_VAR_REAL4_EXPR* unconst_ast = const_cast<ast::ASSIGN_REAL4_VAR_REAL4_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* ASTToCoords::mkASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1,coords::REALMATRIX_EXPR* operand2){
        coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* coord = new coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(operand1,operand2);
        ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* unconst_ast = const_cast<ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL1_VAR_REAL1_EXPR* ASTToCoords::mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,coords::REAL1_EXPR* operand2){
        coords::DECL_REAL1_VAR_REAL1_EXPR* coord = new coords::DECL_REAL1_VAR_REAL1_EXPR(operand1,operand2);
        ast::DECL_REAL1_VAR_REAL1_EXPR* unconst_ast = const_cast<ast::DECL_REAL1_VAR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL3_VAR_REAL3_EXPR* ASTToCoords::mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,coords::REAL3_EXPR* operand2){
        coords::DECL_REAL3_VAR_REAL3_EXPR* coord = new coords::DECL_REAL3_VAR_REAL3_EXPR(operand1,operand2);
        ast::DECL_REAL3_VAR_REAL3_EXPR* unconst_ast = const_cast<ast::DECL_REAL3_VAR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL4_VAR_REAL4_EXPR* ASTToCoords::mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1,coords::REAL4_EXPR* operand2){
        coords::DECL_REAL4_VAR_REAL4_EXPR* coord = new coords::DECL_REAL4_VAR_REAL4_EXPR(operand1,operand2);
        ast::DECL_REAL4_VAR_REAL4_EXPR* unconst_ast = const_cast<ast::DECL_REAL4_VAR_REAL4_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* ASTToCoords::mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1,coords::REALMATRIX_EXPR* operand2){
        coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* coord = new coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR(operand1,operand2);
        ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* unconst_ast = const_cast<ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL1_VAR* ASTToCoords::mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1){
        coords::DECL_REAL1_VAR* coord = new coords::DECL_REAL1_VAR(operand1);
        ast::DECL_REAL1_VAR* unconst_ast = const_cast<ast::DECL_REAL1_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL3_VAR* ASTToCoords::mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1){
        coords::DECL_REAL3_VAR* coord = new coords::DECL_REAL3_VAR(operand1);
        ast::DECL_REAL3_VAR* unconst_ast = const_cast<ast::DECL_REAL3_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REAL4_VAR* ASTToCoords::mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1){
        coords::DECL_REAL4_VAR* coord = new coords::DECL_REAL4_VAR(operand1);
        ast::DECL_REAL4_VAR* unconst_ast = const_cast<ast::DECL_REAL4_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DECL_REALMATRIX_VAR* ASTToCoords::mkDECL_REALMATRIX_VAR(const ast::DECL_REALMATRIX_VAR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1){
        coords::DECL_REALMATRIX_VAR* coord = new coords::DECL_REALMATRIX_VAR(operand1);
        ast::DECL_REALMATRIX_VAR* unconst_ast = const_cast<ast::DECL_REALMATRIX_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::PAREN_REAL1_EXPR* ASTToCoords::mkPAREN_REAL1_EXPR(const ast::PAREN_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1){
        coords::PAREN_REAL1_EXPR* coord = new coords::PAREN_REAL1_EXPR(operand1);
        ast::PAREN_REAL1_EXPR* unconst_ast = const_cast<ast::PAREN_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::INV_REAL1_EXPR* ASTToCoords::mkINV_REAL1_EXPR(const ast::INV_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1){
        coords::INV_REAL1_EXPR* coord = new coords::INV_REAL1_EXPR(operand1);
        ast::INV_REAL1_EXPR* unconst_ast = const_cast<ast::INV_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::NEG_REAL1_EXPR* ASTToCoords::mkNEG_REAL1_EXPR(const ast::NEG_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1){
        coords::NEG_REAL1_EXPR* coord = new coords::NEG_REAL1_EXPR(operand1);
        ast::NEG_REAL1_EXPR* unconst_ast = const_cast<ast::NEG_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ADD_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::ADD_REAL1_EXPR_REAL1_EXPR* coord = new coords::ADD_REAL1_EXPR_REAL1_EXPR(operand1,operand2);
        ast::ADD_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::ADD_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::SUB_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkSUB_REAL1_EXPR_REAL1_EXPR(const ast::SUB_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::SUB_REAL1_EXPR_REAL1_EXPR* coord = new coords::SUB_REAL1_EXPR_REAL1_EXPR(operand1,operand2);
        ast::SUB_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::SUB_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::MUL_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::MUL_REAL1_EXPR_REAL1_EXPR* coord = new coords::MUL_REAL1_EXPR_REAL1_EXPR(operand1,operand2);
        ast::MUL_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::MUL_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DIV_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkDIV_REAL1_EXPR_REAL1_EXPR(const ast::DIV_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::DIV_REAL1_EXPR_REAL1_EXPR* coord = new coords::DIV_REAL1_EXPR_REAL1_EXPR(operand1,operand2);
        ast::DIV_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::DIV_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REF_REAL1_VAR* ASTToCoords::mkREF_REAL1_VAR(const ast::REF_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1){
        coords::REF_REAL1_VAR* coord = new coords::REF_REAL1_VAR(operand1);
        ast::REF_REAL1_VAR* unconst_ast = const_cast<ast::REF_REAL1_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::PAREN_REAL3_EXPR* ASTToCoords::mkPAREN_REAL3_EXPR(const ast::PAREN_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1){
        coords::PAREN_REAL3_EXPR* coord = new coords::PAREN_REAL3_EXPR(operand1);
        ast::PAREN_REAL3_EXPR* unconst_ast = const_cast<ast::PAREN_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ADD_REAL3_EXPR_REAL3_EXPR* ASTToCoords::mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2){
        coords::ADD_REAL3_EXPR_REAL3_EXPR* coord = new coords::ADD_REAL3_EXPR_REAL3_EXPR(operand1,operand2);
        ast::ADD_REAL3_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::ADD_REAL3_EXPR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::SUB_REAL3_EXPR_REAL3_EXPR* ASTToCoords::mkSUB_REAL3_EXPR_REAL3_EXPR(const ast::SUB_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2){
        coords::SUB_REAL3_EXPR_REAL3_EXPR* coord = new coords::SUB_REAL3_EXPR_REAL3_EXPR(operand1,operand2);
        ast::SUB_REAL3_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::SUB_REAL3_EXPR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::INV_REAL3_EXPR* ASTToCoords::mkINV_REAL3_EXPR(const ast::INV_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1){
        coords::INV_REAL3_EXPR* coord = new coords::INV_REAL3_EXPR(operand1);
        ast::INV_REAL3_EXPR* unconst_ast = const_cast<ast::INV_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::NEG_REAL3_EXPR* ASTToCoords::mkNEG_REAL3_EXPR(const ast::NEG_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1){
        coords::NEG_REAL3_EXPR* coord = new coords::NEG_REAL3_EXPR(operand1);
        ast::NEG_REAL3_EXPR* unconst_ast = const_cast<ast::NEG_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::MUL_REAL3_EXPR_REAL1_EXPR* ASTToCoords::mkMUL_REAL3_EXPR_REAL1_EXPR(const ast::MUL_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::MUL_REAL3_EXPR_REAL1_EXPR* coord = new coords::MUL_REAL3_EXPR_REAL1_EXPR(operand1,operand2);
        ast::MUL_REAL3_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::MUL_REAL3_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* ASTToCoords::mkMUL_REALMATRIX_EXPR_REAL3_EXPR(const ast::MUL_REALMATRIX_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1,coords::REAL3_EXPR* operand2){
        coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* coord = new coords::MUL_REALMATRIX_EXPR_REAL3_EXPR(operand1,operand2);
        ast::MUL_REALMATRIX_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::DIV_REAL3_EXPR_REAL1_EXPR* ASTToCoords::mkDIV_REAL3_EXPR_REAL1_EXPR(const ast::DIV_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::DIV_REAL3_EXPR_REAL1_EXPR* coord = new coords::DIV_REAL3_EXPR_REAL1_EXPR(operand1,operand2);
        ast::DIV_REAL3_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::DIV_REAL3_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REF_REAL3_VAR* ASTToCoords::mkREF_REAL3_VAR(const ast::REF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1){
        coords::REF_REAL3_VAR* coord = new coords::REF_REAL3_VAR(operand1);
        ast::REF_REAL3_VAR* unconst_ast = const_cast<ast::REF_REAL3_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::PAREN_REAL4_EXPR* ASTToCoords::mkPAREN_REAL4_EXPR(const ast::PAREN_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1){
        coords::PAREN_REAL4_EXPR* coord = new coords::PAREN_REAL4_EXPR(operand1);
        ast::PAREN_REAL4_EXPR* unconst_ast = const_cast<ast::PAREN_REAL4_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::ADD_REAL4_EXPR_REAL4_EXPR* ASTToCoords::mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL4_EXPR* operand2){
        coords::ADD_REAL4_EXPR_REAL4_EXPR* coord = new coords::ADD_REAL4_EXPR_REAL4_EXPR(operand1,operand2);
        ast::ADD_REAL4_EXPR_REAL4_EXPR* unconst_ast = const_cast<ast::ADD_REAL4_EXPR_REAL4_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::MUL_REAL4_EXPR_REAL1_EXPR* ASTToCoords::mkMUL_REAL4_EXPR_REAL1_EXPR(const ast::MUL_REAL4_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL4_EXPR* operand1,coords::REAL1_EXPR* operand2){
        coords::MUL_REAL4_EXPR_REAL1_EXPR* coord = new coords::MUL_REAL4_EXPR_REAL1_EXPR(operand1,operand2);
        ast::MUL_REAL4_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::MUL_REAL4_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REF_REAL4_VAR* ASTToCoords::mkREF_REAL4_VAR(const ast::REF_REAL4_VAR* ast, clang::ASTContext* c,coords::REAL4_VAR_IDENT* operand1){
        coords::REF_REAL4_VAR* coord = new coords::REF_REAL4_VAR(operand1);
        ast::REF_REAL4_VAR* unconst_ast = const_cast<ast::REF_REAL4_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::PAREN_REALMATRIX_EXPR* ASTToCoords::mkPAREN_REALMATRIX_EXPR(const ast::PAREN_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1){
        coords::PAREN_REALMATRIX_EXPR* coord = new coords::PAREN_REALMATRIX_EXPR(operand1);
        ast::PAREN_REALMATRIX_EXPR* unconst_ast = const_cast<ast::PAREN_REALMATRIX_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* ASTToCoords::mkMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(const ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* ast, clang::ASTContext* c,coords::REALMATRIX_EXPR* operand1,coords::REALMATRIX_EXPR* operand2){
        coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* coord = new coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(operand1,operand2);
        ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* unconst_ast = const_cast<ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REF_EXPR_REALMATRIX_VAR* ASTToCoords::mkREF_EXPR_REALMATRIX_VAR(const ast::REF_EXPR_REALMATRIX_VAR* ast, clang::ASTContext* c,coords::REALMATRIX_VAR_IDENT* operand1){
        coords::REF_EXPR_REALMATRIX_VAR* coord = new coords::REF_EXPR_REALMATRIX_VAR(operand1);
        ast::REF_EXPR_REALMATRIX_VAR* unconst_ast = const_cast<ast::REF_EXPR_REALMATRIX_VAR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REAL1_VAR_IDENT* ASTToCoords::mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT* ast, clang::ASTContext* c){
        coords::REAL1_VAR_IDENT* coord = new coords::REAL1_VAR_IDENT();
        ast::REAL1_VAR_IDENT* unconst_ast = const_cast<ast::REAL1_VAR_IDENT*>(ast);
 
        if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }
        /*if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }*/
        return coord;
    }
    
     coords::REAL3_VAR_IDENT* ASTToCoords::mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT* ast, clang::ASTContext* c){
        coords::REAL3_VAR_IDENT* coord = new coords::REAL3_VAR_IDENT();
        ast::REAL3_VAR_IDENT* unconst_ast = const_cast<ast::REAL3_VAR_IDENT*>(ast);
 
        if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }
        /*if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }*/
        return coord;
    }
    
     coords::REAL4_VAR_IDENT* ASTToCoords::mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT* ast, clang::ASTContext* c){
        coords::REAL4_VAR_IDENT* coord = new coords::REAL4_VAR_IDENT();
        ast::REAL4_VAR_IDENT* unconst_ast = const_cast<ast::REAL4_VAR_IDENT*>(ast);
 
        if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }
        /*if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }*/
        return coord;
    }
    
     coords::REALMATRIX_VAR_IDENT* ASTToCoords::mkREALMATRIX_VAR_IDENT(const ast::REALMATRIX_VAR_IDENT* ast, clang::ASTContext* c){
        coords::REALMATRIX_VAR_IDENT* coord = new coords::REALMATRIX_VAR_IDENT();
        ast::REALMATRIX_VAR_IDENT* unconst_ast = const_cast<ast::REALMATRIX_VAR_IDENT*>(ast);
 
        if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }
        /*if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }*/
        return coord;
    }
    
     coords::REAL1_LITERAL1* ASTToCoords::mkREAL1_LITERAL1(const ast::REAL1_LITERAL1* ast, clang::ASTContext* c,double value1){
        coords::REAL1_LITERAL1* coord = new coords::REAL1_LITERAL1(value1);
        ast::REAL1_LITERAL1* unconst_ast = const_cast<ast::REAL1_LITERAL1*>(ast);
        //bad Clang! bad!
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3){
        coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coord = new coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(operand1,operand2,operand3);
        ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REAL3_LITERAL3* ASTToCoords::mkREAL3_LITERAL3(const ast::REAL3_LITERAL3* ast, clang::ASTContext* c,double value1,double value2,double value3){
        coords::REAL3_LITERAL3* coord = new coords::REAL3_LITERAL3(value1,value2,value3);
        ast::REAL3_LITERAL3* unconst_ast = const_cast<ast::REAL3_LITERAL3*>(ast);
        //bad Clang! bad!
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,coords::REAL1_EXPR* operand4){
        coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coord = new coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(operand1,operand2,operand3,operand4);
        ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REAL4_LITERAL4* ASTToCoords::mkREAL4_LITERAL4(const ast::REAL4_LITERAL4* ast, clang::ASTContext* c,double value1,double value2,double value3,double value4){
        coords::REAL4_LITERAL4* coord = new coords::REAL4_LITERAL4(value1,value2,value3,value4);
        ast::REAL4_LITERAL4* unconst_ast = const_cast<ast::REAL4_LITERAL4*>(ast);
        //bad Clang! bad!
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* ASTToCoords::mkREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(const ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2,coords::REAL3_EXPR* operand3){
        coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* coord = new coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(operand1,operand2,operand3);
        ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,coords::REAL1_EXPR* operand4,coords::REAL1_EXPR* operand5,coords::REAL1_EXPR* operand6,coords::REAL1_EXPR* operand7,coords::REAL1_EXPR* operand8,coords::REAL1_EXPR* operand9){
        coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coord = new coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(operand1,operand2,operand3,operand4,operand5,operand6,operand7,operand8,operand9);
        ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(ast);
 
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
     coords::REALMATRIX_LITERAL9* ASTToCoords::mkREALMATRIX_LITERAL9(const ast::REALMATRIX_LITERAL9* ast, clang::ASTContext* c,double value1,double value2,double value3,double value4,double value5,double value6,double value7,double value8,double value9){
        coords::REALMATRIX_LITERAL9* coord = new coords::REALMATRIX_LITERAL9(value1,value2,value3,value4,value5,value6,value7,value8,value9);
        ast::REALMATRIX_LITERAL9* unconst_ast = const_cast<ast::REALMATRIX_LITERAL9*>(ast);
        //bad Clang! bad!
        /*if (auto dc = clang::dyn_cast<clang::NamedDecl>(unconst_ast)){
            clang::NamedDecl* unconst_dc = const_cast<clang::NamedDecl*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideDecl2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Decl(coord, dc);     // Use Clang canonical addresses?
        }*/
        if (auto dc = clang::dyn_cast<clang::Stmt>(unconst_ast)){
            clang::Stmt* unconst_dc = const_cast<clang::Stmt*>(dc);
            setASTState(coord, unconst_dc, c);
            overrideStmt2Coords(dc, coord);     // Use Clang canonical addresses? 
            overrideCoords2Stmt(coord, dc);     // Use Clang canonical addresses?  
        }
        return coord;
    }
    
//using namespace std;
void ASTToCoords::overrideStmt2Coords(const clang::Stmt *s, coords::Coords *c) {
    stmt_coords->insert(std::make_pair(s, c));
}



void ASTToCoords::overrideDecl2Coords(const clang::Decl *d, coords::Coords *c) {
    
    decl_coords->insert(std::make_pair(d, c));
}



void ASTToCoords::overrideCoords2Stmt(coords::Coords *c, const clang::Stmt *s) {
    
    coords_stmt->insert(std::make_pair(c, s));
}



void ASTToCoords::overrideCoords2Decl(coords::Coords *c, const clang::Decl *d) {
    
    coords_decl->insert(std::make_pair(c, d));
}
