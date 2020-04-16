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
STMT := VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | VEC_EXPR | SCALAR_EXPR | DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR
*/


void StatementProductionMatcher::search(){
    
    StatementMatcher vectorExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");//fluff node to discard

    StatementMatcher scalarDecl =
        declStmt(has(varDecl(
            allOf(hasType(realFloatingPointType()),anyOf(has(expr().bind("ScalarDeclRV")), has(binaryOperator().bind("ScalarDeclRV")))))
                .bind("ScalarVarDecl")))
                .bind("ScalarDeclStatement");
    StatementMatcher vectorDecl =
       declStmt(has(varDecl(allOf(hasType(asString("class Vec")),anyOf(
           has(expr().bind("VectorDeclRV")),
           has(exprWithCleanups().bind("VectorDeclRV"))
           ))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
    StatementMatcher floatExpr = 
        expr(hasType(realFloatingPointType())).bind("ScalarExprStatement");
    StatementMatcher vectorExpr = 
        expr(hasType(asString("class Vec"))).bind("VectorExprStatement");
    StatementMatcher scalarAssign = 
        binaryOperator(allOf(
            hasType(realFloatingPointType()),
            hasOperatorName("="),
            hasLHS(expr().bind("ScalarAssignLHS")),
            hasRHS(expr().bind("ScalarAssignRHS"))
        )).bind("ScalarAssign");
    StatementMatcher vectorAssign = 
        cxxOperatorCallExpr(allOf(
            hasType(asString("class Vec")),
            hasOverloadedOperatorName("="),
            hasArgument(0, expr(hasType(asString("class Vec"))).bind("VectorAssignLHS")), 
            hasArgument(1, expr(hasType(asString("class Vec"))).bind("VectorAssignRHS"))
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


    if(scalarDecl or scalarVarDecl or scalarDeclRV){//matches Scalar variable declaration
        if(scalarDecl and scalarVarDecl and scalarDeclRV){
            this->interp_->mkScalarIdent(scalarVarDecl);
            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*scalarDeclRV);
            this->interp_->mkScalar_Def(scalarDecl, scalarVarDecl, exprMatcher.getChildExprStore());
        }
        else{
            //log error
        }
    }
    else if(vectorDecl or vectorVarDecl or vectorDeclRV){//matches Vector variable declaration
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
    else if(floatExpr){//matches Scalar expressions
        ScalarExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*floatExpr);

    }
    else if(vecExpr){//matches Vector expressions
        VectorExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*vecExpr);

    }
    else if(exprWithCleanupsDiscard){//matches fluff node to discard
        StatementProductionMatcher innerMatcher{this->context_, this->interp_};
        innerMatcher.search();
        innerMatcher.visit(*exprWithCleanupsDiscard->getSubExpr());

    }
    else if(scalarAssign or scalarAssignLHS or scalarAssignRHS){//matches Scalar variable assignment
        if(scalarAssign and scalarAssignLHS and scalarAssignRHS){
            ScalarExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*scalarAssignLHS);
            ScalarExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*scalarAssignRHS);

            interp_->mkScalar_Assign(scalarAssign, (clang::DeclRefExpr*)lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());

            //we don't set this property in statements
            //this->childExprStore_ = (clang::Expr*)scalarAssign;
        }
        else{
            //log error
        }
    }
    else if(vectorAssign or vectorAssignLHS or vectorAssignRHS){//matches Vector variable assignment
        if(vectorAssign and vectorAssignLHS and vectorAssignRHS){
            VectorExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*vectorAssignLHS);
            VectorExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*vectorAssignRHS);

            interp_->mkVector_Assign(vectorAssign, (clang::DeclRefExpr*)lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());

           //this->childExprStore_ = (clang::Expr*)vectorAssign;
        }
        else{
            //log error
        }
    }

};