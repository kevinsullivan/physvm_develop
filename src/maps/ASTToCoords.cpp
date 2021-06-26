
#include "ASTToCoords.h"
//#include "AST.h"
//#include <g3log/g3log.hpp>

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
using namespace ast;

void ASTToCoords::setASTState(coords::Coords* coords, std::shared_ptr<ast::NodeContainer> astNode, clang::ASTContext* c)
{
    if(astNode->ASTTag_ == ASTTag::Stmt__){
        auto stmt = astNode->ASTNode_.Stmt_;
        auto range = stmt->getSourceRange();
        auto begin = c->getFullLoc(range.getBegin());
        auto end = c->getFullLoc(range.getEnd());
        clang::LangOptions lopt;
        clang::SourceLocation b = c->getSourceManager().getSpellingLoc(range.getBegin());
        clang::SourceLocation e = c->getSourceManager().getSpellingLoc(range.getEnd());

        auto code = std::string(c->getSourceManager().getCharacterData(b),
            c->getSourceManager().getCharacterData(e)-c->getSourceManager().getCharacterData(b));
        
        if (auto dc = clang::dyn_cast<clang::DeclRefExpr>(stmt))
        {
            code = dc->getFoundDecl()->getNameAsString();
        }

        code = code == "" ? "No Source Snip Available" : code;
        auto name = (clang::dyn_cast<clang::DeclRefExpr>(stmt)) ? (clang::dyn_cast<clang::DeclRefExpr>(stmt))->getDecl()->getNameAsString() : "";
        if(auto dc = clang::dyn_cast<clang::DeclStmt>(stmt))
        {
            auto decl = dc->getSingleDecl();
            name = (clang::dyn_cast<clang::NamedDecl>(decl)) ? (clang::dyn_cast<clang::NamedDecl>(decl))->getNameAsString() : "";
        }

            
        coords->state_ = new coords::ASTState(
            "",
            "",
            "",
            name,
            code,
            begin.getSpellingLineNumber(),
            begin.getSpellingColumnNumber(),
            end.getSpellingLineNumber(),
            end.getSpellingColumnNumber()
        );
    }
    else if(astNode->ASTTag_ == ASTTag::VarDecl__ || astNode->ASTTag_ == ASTTag::FuncDecl__){
        const clang::Decl* decl;
        if(astNode->ASTTag_ == ASTTag::VarDecl__)
            decl = clang::dyn_cast<clang::Decl>(astNode->ASTNode_.VarDecl_);
        else
            decl = clang::dyn_cast<clang::Decl>(astNode->ASTNode_.FuncDecl_);

        auto range = decl->getSourceRange();
        auto begin = c->getFullLoc(range.getBegin());
        auto end = c->getFullLoc(range.getEnd());
        clang::LangOptions lopt;
        clang::SourceLocation b = c->getSourceManager().getSpellingLoc(range.getBegin());
        clang::SourceLocation e = c->getSourceManager().getSpellingLoc(range.getEnd());
        //auto sm = c->getSourceManager();
        auto code = std::string(c->getSourceManager().getCharacterData(b),
            c->getSourceManager().getCharacterData(e)-c->getSourceManager().getCharacterData(b));
        code = code == "" ? "No Source Snip Available" : code;
        
        coords->state_ = new coords::ASTState(
            "",
            "",
            "",
            (clang::dyn_cast<clang::NamedDecl>(decl)) ? (clang::dyn_cast<clang::NamedDecl>(decl))->getNameAsString() : "",
            code,
            begin.getSpellingLineNumber(),
            begin.getSpellingColumnNumber(),
            end.getSpellingLineNumber(),
            end.getSpellingColumnNumber()
        );
    }
    else if(astNode->ASTTag_ == ASTTag::ConsDecl__){
        auto code = astNode->ASTNode_.ConsDecl_->getQualifiedNameAsString();

        coords->state_ = new coords::ASTState(
            "",
            "",
            "",
            code,
            code,
            0,0,0,0
        );
    }
    else if(astNode->ASTTag_ == ASTTag::ParamDecl__){
        auto code = astNode->ASTNode_.ParamDecl_->getNameAsString();
        coords->state_ = new coords::ASTState(
            "",
            "",
            "",
            code,
            code,
            0,0,0,0
        );

    }
    else{
    }
}

ASTToCoords::ASTToCoords() {
};
//enum class ASTTag { UnitDecl__, FuncDecl__, Stmt__, VarDecl__, ConsDecl__, ParamDecl__ };
bool ASTToCoords::put(std::shared_ptr<ast::NodeContainer> astNode, coords::Coords* coords_){
    if(astNode->ASTTag_==ASTTag::Stmt__){
        stmt_edges[astNode->ASTNode_.Stmt_] = coords_;
        return true;;
    }
    else if(astNode->ASTTag_==ASTTag::VarDecl__){
				var_edges[astNode->ASTNode_.VarDecl_] = coords_;
                return true;
    }
    if(astNode->ASTTag_==ASTTag::FuncDecl__){
				func_edges[astNode->ASTNode_.FuncDecl_] = coords_;
                return true;
    }
    if(astNode->ASTTag_==ASTTag::UnitDecl__){
				unit_edges[astNode->ASTNode_.UnitDecl_] = coords_;
                return true;
    }
    if(astNode->ASTTag_==ASTTag::ConsDecl__){
				cons_edges[astNode->ASTNode_.ConsDecl_] = coords_;
                return true;
    }
    if(astNode->ASTTag_==ASTTag::ParamDecl__){
				param_edges[astNode->ASTNode_.ParamDecl_] = coords_;
                return true;
    }
    else{
        return false;
    }
}


