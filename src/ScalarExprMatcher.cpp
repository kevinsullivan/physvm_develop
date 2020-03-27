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


    StatementMatcher scalarParenExpr =
        parenExpr(allOf(hasType(realFloatingPointType()),has(expr().bind("ScalarInnerExpr")))).bind("ScalarParenExpr");
    StatementMatcher scalarAddExpr =
        binaryOperator(allOf(hasOperatorName("+"),
            hasLHS(expr().bind("ScalarAddLHS")),
            hasRHS(expr().bind("ScalarAddRHS"))
            )).bind("ScalarAddExpr");
    StatementMatcher scalarMulExpr =
        binaryOperator(allOf(hasOperatorName("*"),
            hasLHS(expr().bind("ScalarMulLHS")),
            hasRHS(expr().bind("ScalarMulRHS"))
        )).bind("ScalarMulExpr");
    StatementMatcher scalarVar = 
        declRefExpr(hasType(realFloatingPointType())).bind("ScalarDeclRefExpr");
    StatementMatcher scalarLiteral =
        anyOf(
            floatLiteral().bind("ScalarLiteralExpr"),
            //implicitCastExpr(has(floatLiteral().bind("ScalarLiteralExpr"))),
            integerLiteral().bind("ScalarLiteralExpr")//,
           // implicitCastExpr(has(integerLiteral().bind("ScalarLiteralExpr")))
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
    const auto addExpr = Result.Nodes.getNodeAs<clang::BinaryOperator>("ScalarAddExpr");
    const auto addLHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddLHS");
    const auto addRHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddRHS");
    const auto mulExpr = Result.Nodes.getNodeAs<clang::BinaryOperator>("ScalarMulExpr");
    const auto mulLHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulLHS");
    const auto mulRHS = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulRHS");
    const auto declRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("ScalarDeclRefExpr");
    const auto literal = Result.Nodes.getNodeAs<clang::Expr>("ScalarLiteralExpr");


    const auto scalarExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    const auto scalarImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");

    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            ScalarExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
            interp_->mkFloatParenExpr(parenExpr, exprMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)parenExpr;
        }
        else{
            //log error
        }
    }
    else if(addExpr or addLHS or addRHS){
        if(addExpr and addLHS and addRHS){
            //NOT IMPLEMENTED
            //addExpr->dump();
            //addLHS->dump();
            //addRHS->dump();
            ScalarExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*addLHS);
            
            ScalarExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*addRHS);

            //std::cout<<"add debug..."<<std::endl;
            //lhsMatcher.getChildExprStore()->dump();
            //rhsMatcher.getChildExprStore()->dump();

            interp_->mkFloatFloatAddExpr(addExpr, lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)addExpr;
            //interp_->mkFloat
        }
        else{
            //log error
        }
    }
    else if(mulExpr or mulLHS or mulRHS){
        if(mulExpr and mulLHS and mulRHS){
            //NOT IMPLEMENTED
            ScalarExprMatcher lhsMatcher{this->context_, this->interp_};
            lhsMatcher.search();
            lhsMatcher.visit(*mulLHS);
            
            ScalarExprMatcher rhsMatcher{this->context_, this->interp_};
            rhsMatcher.search();
            rhsMatcher.visit(*mulRHS);

            interp_->mkFloatFloatMulExpr(mulExpr, lhsMatcher.getChildExprStore(), rhsMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)mulExpr;
        }
        else{
            //log error
        }
    }
    else if(declRefExpr){
        interp_->mkFloatVarExpr(declRefExpr);
        this->childExprStore_ = (clang::Expr*)declRefExpr;
    }
    else if(literal){
        interp_->mkFloat_Lit(literal, 0);
        this->childExprStore_ = (clang::Expr*)literal;
    }
    else if(scalarExprWithCleanups){
        ScalarExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*scalarExprWithCleanups->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(scalarImplicitCastExpr){//this needs to run after literal expr, not all implicit cast has an expression beneath

        ScalarExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*scalarImplicitCastExpr->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }
};