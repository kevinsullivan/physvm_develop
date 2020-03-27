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
    
    StatementMatcher vectorExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");

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
            hasType(asString("float")),
            hasOperatorName("="),
            hasLHS(expr().bind("ScalarAssignLHS")),
            hasRHS(expr().bind("ScalarAssignRHS"))
        )).bind("ScalarAssign");
    StatementMatcher vectorAssign = 
        cxxOperatorCallExpr(allOf(
            hasType(asString("class Vec")),
            hasOverloadedOperatorName("="),
            hasArgument(0, expr(asType(asString("class Vec"))).bind("VectorAssignLHS")), 
            hasArgument(1, expr(asType(asString("class Vec"))).bind("VectorAssignRHS"))
        )).bind("VectorAssign");

    localFinder_.addMatcher(vectorExprWithCleanups, this);

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

    
    const auto scalarAssign = Result.Nodes.getNodeAs<clang::BinaryOperator>("ScalarAssign");
    const auto scalarAssignLHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignLHS");
    const auto scalarAssignRHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignRHS");

    const auto vectorAssign = Result.Nodes.getNodeAs<clang::CXXOperatorCallExpr>("VectorAssign");
    const auto vectorAssignLHS = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignLHS");
    const auto vectorAssignRHS = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignRHS");

    const auto exprWithCleanupsDiscard = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");


    if(scalarDecl or scalarVarDecl or scalarDeclRV){
        if(scalarDecl and scalarVarDecl and scalarDeclRV){
            this->interp_->mkFloatIdent(scalarVarDecl);
            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*scalarDeclRV);
            exprMatcher.getChildExprStore()->dump();
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
    else if(exprWithCleanupsDiscard){
        StatementProductionMatcher innerMatcher{this->context_, this->interp_};
        innerMatcher.search();
        innerMatcher.visit(*exprWithCleanupsDiscard->getSubExpr());

    }
    else if(scalarAssign or scalarAssignLHS or scalarAssignRHS){
        if(scalarAssign and scalarAssignLHS and scalarAssignRHS){
            ScalarExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*scalarAssignLHS);
            ScalarExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*scalarAssignRHS);

            interp_->mkFloat_Assign(scalarAssign, (clang::DeclRefExpr*)lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());

            this->childExprStore_ = (clang::Expr*)scalarAssign;
        }
        else{
            //log error
        }
    }
    else if(vectorAssign or vectorAssignLHS or vectorAssignRHS){
        if(vectorAssign and vectorAssignLHS and vectorAssignRHS){
            VectorExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*vectorAssignLHS);
            VectorExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*vectorAssignRHS);

            std::cout<<"lhs"<<std::endl;
            vectorAssignLHS->dump();
            lhsMatcher.getChildExprStore()->dump();
            std::cout<<"rhs"<<std::endl;
            vectorAssignRHS->dump();
            rhsMatcher.getChildExprStore()->dump();

            interp_->mkVector_Assign(vectorAssign, (clang::DeclRefExpr*)lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());

           //this->childExprStore_ = vectorAssign;
        }
        else{
            //log error
        }
    }

};