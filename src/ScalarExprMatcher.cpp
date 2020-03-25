#pragma once

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>


#include "ScalarExprMatcher.h"


/*

SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL

*/

void ScalarExprMatcher::search(){
    //this matcher has no meaning, unlike other productions, and is simply a hack to strip off the pesky ExprWithCleanups wrapper.
    StatementMatcher scalarExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher scalarImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard");



    //nice and valid without pointers!
    StatementMatcher scalarParenExpr =
        parenExpr(allOf(hasType(asString("float")),has(expr().bind("ScalarInnerExpr")))).bind("ScalarParenExpr");
    StatementMatcher scalarAddExpr =
        binaryOperator(allOf(hasOperatorName("+"),
            hasLHS(anyOf(implicitCastExpr(expr().bind("ScalarAddLHSExpr")),binaryOperator().bind("ScalarAddLHSExpr"))),
            hasRHS(anyOf(implicitCastExpr(expr().bind("ScalarAddRHSExpr")), binaryOperator().bind("ScalarAddRHSExpr")))));
    StatementMatcher scalarMulExpr =
        binaryOperator(allOf(hasOperatorName("*"),
            hasLHS(anyOf(implicitCastExpr(expr().bind("ScalarMulLHSExpr")),binaryOperator().bind("ScalarMulLHSExpr"))),
            hasRHS(anyOf(implicitCastExpr(expr().bind("ScalarMulRHSExpr")), binaryOperator().bind("ScalarMulRHSExpr")))));
    StatementMatcher scalarVar = 
        declRefExpr(anyOf(hasType(asString("float")), hasType(asString("double")))).bind("ScalarDeclRefExpr");
    StatementMatcher scalarLiteral =
        anyOf(
            floatLiteral().bind("ScalarLiteralExpr"),
            implicitCastExpr(has(floatLiteral().bind("ScalarLiteralExpr")))
        );
    localFinder_.addMatcher(scalarExprWithCleanups, this);
    localFinder_.addMatcher(scalarImplicitCastExpr, this);

    localFinder_.addMatcher(scalarParenExpr, this);
    localFinder_.addMatcher(scalarAddExpr, this);
    localFinder_.addMatcher(scalarMulExpr, this);
    localFinder_.addMatcher(scalarVar, this);
    localFinder_.addMatcher(scalarLiteral, this);
};

void ScalarExprMatcher::run(const MatchFinder::MatchResult &Result){
    const auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("ScalarParenExpr");
    const auto innerExpr = Result.Nodes.getNodeAs<clang::Expr>("ScalarInnerExpr");
    const auto addExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("ScalarAddExpr");
    const auto addMember = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddMember");
    const auto addArgument = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddArgument");
    const auto mulExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("ScalarAddExpr");
    const auto mulMember = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulMember");
    const auto mulArgument = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulArgument");
    const auto declRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("ScalarDeclRefExpr");
    const auto literal = Result.Nodes.getNodeAs<clang::Expr>("ScalarLiteralExpr");

    const auto scalarExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    const auto scalarImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");

    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
            interp_->mkFloatParenExpr(parenExpr, innerExpr);
        }
        else{
            //log error
        }
    }
    else if(addExpr or addMember or addArgument){
        if(addExpr and addMember and addArgument){
            //NOT IMPLEMENTED
            
            //interp_->mkFloat
        }
        else{
            //log error
        }
    }
    else if(mulExpr or mulMember or mulArgument){
        if(mulExpr and mulMember and mulArgument){
            //NOT IMPLEMENTED

        }
        else{
            //log error
        }
    }
    else if(declRefExpr){
        interp_->mkFloatVarExpr(declRefExpr);
    }
    else if(literal){
        interp_->mkFloat_Lit(literal, 0);
    }
    else if(scalarExprWithCleanups){
        ScalarExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*scalarExprWithCleanups->getSubExpr());
        interp_->mkFloatWrapperExpr(scalarExprWithCleanups, scalarExprWithCleanups->getSubExpr());
    }
    else if(scalarImplicitCastExpr){//this needs to run after literal expr, not all implicit cast has an expression beneath

        ScalarExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*scalarImplicitCastExpr->getSubExpr());
        interp_->mkFloatWrapperExpr(scalarImplicitCastExpr, scalarImplicitCastExpr->getSubExpr());
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }
};