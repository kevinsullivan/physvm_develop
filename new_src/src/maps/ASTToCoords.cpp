
#include "ASTToCoords.h"
//#include "AST.h"
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
using namespace ast;

void ASTToCoords::setASTState(coords::Coords* coords, std::shared_ptr<ast::NodeContainer> astNode, clang::ASTContext* c)
{
    if(astNode->ASTTag_ == ASTTag::Stmt__){
        auto stmt = astNode->ASTNode_.Stmt_;
        auto range = stmt->getSourceRange();
        auto begin = c->getFullLoc(range.getBegin());
        auto end = c->getFullLoc(range.getEnd());
        clang::LangOptions lopt;
        clang::SourceLocation b = c->getSourceManager().getSpellingLoc(range.getBegin());//(d->getLocStart()), _e(d->getLocEnd());
        clang::SourceLocation e = c->getSourceManager().getSpellingLoc(range.getEnd());
        //auto sm = c->getSourceManager();
        auto code = std::string(c->getSourceManager().getCharacterData(b),
            c->getSourceManager().getCharacterData(e)-c->getSourceManager().getCharacterData(b));
        
        if (auto dc = clang::dyn_cast<clang::DeclRefExpr>(stmt))
        {
            code = dc->getFoundDecl()->getNameAsString();
        }
        //std::cout<<code<<"\n";
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
        clang::SourceLocation b = c->getSourceManager().getSpellingLoc(range.getBegin());//(d->getLocStart()), _e(d->getLocEnd());
        clang::SourceLocation e = c->getSourceManager().getSpellingLoc(range.getEnd());//(clang::Lexer::getLocForEndOfToken(_e, 0, c->getSourceManager(), lopt));
        //auto sm = c->getSourceManager();
        auto code = std::string(c->getSourceManager().getCharacterData(b),
            c->getSourceManager().getCharacterData(e)-c->getSourceManager().getCharacterData(b));
        //std::cout<<code<<"\n";
        code = code == "" ? "No Source Snip Available" : code;
        //decl->dump();
        //std::cout<<((clang::dyn_cast<clang::NamedDecl>(decl)) ? (clang::dyn_cast<clang::NamedDecl>(decl))->getNameAsString() : "")<<"\n";
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
}
/*
void ASTToCoords::setASTState(coords::Coords* coords, clang::Decl* decl, clang::ASTContext* c)
{
    auto range = decl->getSourceRange();
    auto begin = c->getFullLoc(range.getBegin());
    auto end = c->getFullLoc(range.getEnd());
    clang::LangOptions lopt;
    clang::SourceLocation b = c->getSourceManager().getSpellingLoc(range.getBegin());//(d->getLocStart()), _e(d->getLocEnd());
    clang::SourceLocation e = c->getSourceManager().getSpellingLoc(range.getEnd());//(clang::Lexer::getLocForEndOfToken(_e, 0, c->getSourceManager(), lopt));
    //auto sm = c->getSourceManager();
    auto code = std::string(c->getSourceManager().getCharacterData(b),
        c->getSourceManager().getCharacterData(e)-c->getSourceManager().getCharacterData(b));
    //std::cout<<code<<"\n";
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
    /*
    coords->state_.file_id_ = "";
    coords->state_.file_name_ = "";
    coords->state_.file_path_ = "";

    coords->state_.name_ = ((clang::NamedDecl*) decl) ? ((clang::NamedDecl*) decl)->getNameAsString() : "";

    coords->state_.begin_line_no_ = begin.getSpellingLineNumber();
    coords->state_.begin_col_no_ = begin.getSpellingColumnNumber();
    coords->state_.end_line_no_ = end.getSpellingLineNumber();
    coords->state_.end_col_no_ = end.getSpellingColumnNumber();
    
}*/

ASTToCoords::ASTToCoords() {
};

std::string TagConversion[] = {"UnitDecl", "FuncDecl", "Stmt", "VarDecl"};
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
    else{
        return false;
    }
    /*
    switch(astNode->ASTTag_){
			case ASTTag::Stmt__:
                std::cout<<"stmt case";
				stmt_edges[astNode->ASTNode_.Stmt_] = coords_;
			    return true;;
			case ASTTag::VarDecl__:
                std::cout<<"var case";
				var_edges[astNode->ASTNode_.VarDecl_] = coords_;
                return true;
			case ASTTag::FuncDecl__:
                std::cout<<"func case";
				func_edges[astNode->ASTNode_.FuncDecl_] = coords_;
                return true;
			case ASTTag::UnitDecl__:
                std::cout<<"unit case";
				unit_edges[astNode->ASTNode_.UnitDecl_] = coords_;
                return true;
		}
        
    return false;
    */
}


