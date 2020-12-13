
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
    //ast::SEQ_GLOBALSTMT* unconst_ast = const_cast<ast::SEQ_GLOBALSTMT*>(ast);

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

coords::REF_REAL3_VAR* ASTToCoords::mkREF_REAL3_VAR(const ast::REF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::REF_REAL3_VAR* coord = new coords::REF_REAL3_VAR(operand1, value0, value1, value2);
    ast::REF_REAL3_VAR* unconst_ast = const_cast<ast::REF_REAL3_VAR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::ADD_REAL3_EXPR_REAL3_EXPR* ASTToCoords::mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::ADD_REAL3_EXPR_REAL3_EXPR* coord = new coords::ADD_REAL3_EXPR_REAL3_EXPR(operand1,operand2, value0, value1, value2);
    ast::ADD_REAL3_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::ADD_REAL3_EXPR_REAL3_EXPR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::LMUL_REAL1_EXPR_REAL3_EXPR* ASTToCoords::mkLMUL_REAL1_EXPR_REAL3_EXPR(const ast::LMUL_REAL1_EXPR_REAL3_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL3_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::LMUL_REAL1_EXPR_REAL3_EXPR* coord = new coords::LMUL_REAL1_EXPR_REAL3_EXPR(operand1,operand2, value0, value1, value2);
    ast::LMUL_REAL1_EXPR_REAL3_EXPR* unconst_ast = const_cast<ast::LMUL_REAL1_EXPR_REAL3_EXPR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::RMUL_REAL3_EXPR_REAL1_EXPR* ASTToCoords::mkRMUL_REAL3_EXPR_REAL1_EXPR(const ast::RMUL_REAL3_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL3_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::RMUL_REAL3_EXPR_REAL1_EXPR* coord = new coords::RMUL_REAL3_EXPR_REAL1_EXPR(operand1,operand2, value0, value1, value2);
    ast::RMUL_REAL3_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::RMUL_REAL3_EXPR_REAL1_EXPR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::LREF_REAL3_VAR* ASTToCoords::mkLREF_REAL3_VAR(const ast::LREF_REAL3_VAR* ast, clang::ASTContext* c,coords::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::LREF_REAL3_VAR* coord = new coords::LREF_REAL3_VAR(operand1, value0, value1, value2);
    ast::LREF_REAL3_VAR* unconst_ast = const_cast<ast::LREF_REAL3_VAR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::REF_REAL1_VAR* ASTToCoords::mkREF_REAL1_VAR(const ast::REF_REAL1_VAR* ast, clang::ASTContext* c,coords::REAL1_VAR_IDENT* operand1,std::shared_ptr<float> value0){
    coords::REF_REAL1_VAR* coord = new coords::REF_REAL1_VAR(operand1, value0);
    ast::REF_REAL1_VAR* unconst_ast = const_cast<ast::REF_REAL1_VAR*>(ast);
	//coord->setValue(value0,0);
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

coords::ADD_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0){
    coords::ADD_REAL1_EXPR_REAL1_EXPR* coord = new coords::ADD_REAL1_EXPR_REAL1_EXPR(operand1,operand2, value0);
    ast::ADD_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::ADD_REAL1_EXPR_REAL1_EXPR*>(ast);
	//coord->setValue(value0,0);
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

coords::MUL_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,std::shared_ptr<float> value0){
    coords::MUL_REAL1_EXPR_REAL1_EXPR* coord = new coords::MUL_REAL1_EXPR_REAL1_EXPR(operand1,operand2, value0);
    ast::MUL_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::MUL_REAL1_EXPR_REAL1_EXPR*>(ast);
	//coord->setValue(value0,0);
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

coords::REAL1_VAR_IDENT* ASTToCoords::mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT* ast, clang::ASTContext* c,std::shared_ptr<float> value0){
    coords::REAL1_VAR_IDENT* coord = new coords::REAL1_VAR_IDENT( value0);
    ast::REAL1_VAR_IDENT* unconst_ast = const_cast<ast::REAL1_VAR_IDENT*>(ast);
	//coord->setValue(value0,0);


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

coords::REAL3_VAR_IDENT* ASTToCoords::mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::REAL3_VAR_IDENT* coord = new coords::REAL3_VAR_IDENT( value0, value1, value2);
    ast::REAL3_VAR_IDENT* unconst_ast = const_cast<ast::REAL3_VAR_IDENT*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);


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

coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ASTToCoords::mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* ast, clang::ASTContext* c,coords::REAL1_EXPR* operand1,coords::REAL1_EXPR* operand2,coords::REAL1_EXPR* operand3,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* coord = new coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(operand1,operand2,operand3, value0, value1, value2);
    ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* unconst_ast = const_cast<ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::REAL3_EMPTY* ASTToCoords::mkREAL3_EMPTY(const ast::REAL3_EMPTY* ast, clang::ASTContext* c,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2){
    coords::REAL3_EMPTY* coord = new coords::REAL3_EMPTY( value0, value1, value2);
    ast::REAL3_EMPTY* unconst_ast = const_cast<ast::REAL3_EMPTY*>(ast);
	//coord->setValue(value0,0);
	//coord->setValue(value1,1);
	//coord->setValue(value2,2);
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

coords::REAL1_LIT* ASTToCoords::mkREAL1_LIT(const ast::REAL1_LIT* ast, clang::ASTContext* c,std::shared_ptr<float> value0){
    coords::REAL1_LIT* coord = new coords::REAL1_LIT( value0);
    ast::REAL1_LIT* unconst_ast = const_cast<ast::REAL1_LIT*>(ast);
	//coord->setValue(value0,0);
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
