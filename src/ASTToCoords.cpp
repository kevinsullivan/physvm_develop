
#include "ASTToCoords.h"
#include <g3log/g3log.hpp>

#include <iostream>
#include <exception>
#include <memory>
#include <string>
#include <memory>

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


coords::SEQ_GLOBALSTMT* ASTToCoords::mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT* ast, clang::ASTContext* c, std::vector<coords::GLOBALSTMT*> operands ){
    coords::SEQ_GLOBALSTMT* coord = new coords::SEQ_GLOBALSTMT(operands);
    ast::SEQ_GLOBALSTMT* unconst_ast = const_cast<ast::SEQ_GLOBALSTMT*>(ast);

    coord->state_ = new coords::ASTState(
        "",
        "",
        "",
        "",
        0,
        0,
        0,
        0
    );

    return coord;
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

coords::VOID_FUNC_DECL_STMT* ASTToCoords::mkVOID_FUNC_DECL_STMT(const ast::VOID_FUNC_DECL_STMT* ast, clang::ASTContext* c,coords::STMT* operand1){
    coords::VOID_FUNC_DECL_STMT* coord = new coords::VOID_FUNC_DECL_STMT(operand1);
    ast::VOID_FUNC_DECL_STMT* unconst_ast = const_cast<ast::VOID_FUNC_DECL_STMT*>(ast);


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

coords::MAIN_FUNC_DECL_STMT* ASTToCoords::mkMAIN_FUNC_DECL_STMT(const ast::MAIN_FUNC_DECL_STMT* ast, clang::ASTContext* c,coords::STMT* operand1){
    coords::MAIN_FUNC_DECL_STMT* coord = new coords::MAIN_FUNC_DECL_STMT(operand1);
    ast::MAIN_FUNC_DECL_STMT* unconst_ast = const_cast<ast::MAIN_FUNC_DECL_STMT*>(ast);


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
