#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "Interpretation.h"


#include "StatementProductionMatcher.h"
#include "VectorExprMatcher.h"
#include "ScalarExprMatcher.h"

#include <iostream>

#include "ASTToCoords.h"
/*
    virtual void Traverse() = 0;
    virtual void BuildRepresentation() = 0;
    virtual StatementMatcher GetStatementMatcher() = 0;
    virtual void run(const MatchFinder::MatchResult &Result) = 0;

    
STMT := VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | VEC_EXPR | SCALAR_EXPR | DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR
*/


void StatementProductionMatcher::search(){
    StatementMatcher scalarDecl =
        declStmt(has(varDecl(
            allOf(hasType(asString("float")),anyOf(has(expr().bind("ScalarDeclRV")), has(binaryOperator().bind("ScalarDeclRV")))))
                .bind("ScalarVarDecl")))
                .bind("ScalarDeclStatement");
    StatementMatcher vectorDecl =
       declStmt(has(varDecl(allOf(hasType(asString("class Vec")),anyOf(
           has(expr().bind("VectorDeclRV")),
           has(exprWithCleanups().bind("VectorDeclRV"))
           ))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
           //cxxConstructExpr(allOf(hasType(asString("class Vec")),has(expr().bind("VectorDeclRV")))))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
    StatementMatcher floatExpr = 
        expr(hasType(asString("float"))).bind("ScalarExprStatement");
    StatementMatcher vectorExpr = 
        expr(hasType(asString("class Vec"))).bind("VectorExprStatement");
    StatementMatcher scalarAssign =
        binaryOperator(allOf(
            hasOperatorName("="),
            has(declRefExpr(hasType(asString("float"))).bind("ScalarAssignLV")), 
            hasRHS(expr().bind("ScalarAssignRV"))
        )).bind("ScalarAssignStatement");
    StatementMatcher vectorAssign = 
        cxxOperatorCallExpr(allOf(hasOverloadedOperatorName("="),
            has(declRefExpr(hasType(asString("class Vec"))).bind("VectorAssignLV")), has(expr().bind("VectorAssignRV")))).bind("VectorAssignmentStatement");

    localFinder_.addMatcher(scalarDecl, this);
    localFinder_.addMatcher(vectorDecl, this);
    localFinder_.addMatcher(floatExpr, this);
    localFinder_.addMatcher(vectorExpr, this);
    localFinder_.addMatcher(scalarAssign, this);
    localFinder_.addMatcher(vectorAssign, this);
};

void StatementProductionMatcher::run(const MatchFinder::MatchResult &Result){
    
    const auto scalarDecl = Result.Nodes.getNodeAs<clang::DeclStmt>("ScalarDeclStatement");
    const auto scalarVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("ScalarVarDecl");
    const auto scalarDeclRV = Result.Nodes.getNodeAs<clang::Expr>("ScalarDeclRV");
    const auto vectorDecl = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorDeclStatement");
    const clang::VarDecl* vectorVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("VectorVarDecl");
    const auto vectorDeclRV = Result.Nodes.getNodeAs<clang::Expr>("VectorDeclRV");
    const auto floatExpr = Result.Nodes.getNodeAs<clang::Expr>("ScalarExprStatement");
    const auto vecExpr = Result.Nodes.getNodeAs<clang::Expr>("VectorExprStatement");
    const auto scalarAssign = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignStatement");
    const auto scalarAssignLV = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignLV");
    const auto scalarAssignRV = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignRV");
    const auto vectorAssign = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignmentStatement");
    const auto vectorAssignLV = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignLV");
    const auto vectorAssignRV = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignRV");


    if(scalarDecl or scalarVarDecl or scalarDeclRV){
        if(scalarDecl and scalarVarDecl and scalarDeclRV){
            this->interp_->mkFloatIdent(scalarVarDecl);
            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*scalarDeclRV);
            this->interp_->mkFloat_Def(scalarDecl, scalarVarDecl, exprMatcher.getChildExprStore());
        }
        else{
            //log error
        }
    }
    else if(vectorDecl or vectorVarDecl or vectorDeclRV){
        if(vectorDecl and vectorVarDecl and vectorDeclRV){

            this->interp_->mkVecIdent(vectorVarDecl);
            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*vectorDeclRV);
            std::cout<<"matched vector decl"<<std::endl;
            vectorDecl->dump();
            vectorDeclRV->dump();
            this->interp_->mkVector_Def(vectorDecl, vectorVarDecl, exprMatcher.getChildExprStore());

        }
        else{
            //log error
        }
    }
    else if(floatExpr){
            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*floatExpr);

    }
    else if(vecExpr){
            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*vecExpr);


    }
    else if(scalarAssign or scalarAssignLV or scalarAssignRV){
        if(scalarAssign and scalarAssignLV and scalarAssignRV){
            //NOT IMPLEMENTED IN BACKEND
        }
        else{
            //log error
        }
    }
    else if(vectorAssign or vectorAssignLV or vectorAssignRV){
        if(vectorAssign and vectorAssignLV and vectorAssignRV){
            //NOT IMPLEMENTED IN BACKEND
        }
        else{
            //log error
        }
    }

};