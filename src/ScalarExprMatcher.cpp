

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
        floatLiteral().bind("ScalarLiteralExpr");
    localFinder_.addMatcher(scalarExprWithCleanups, this);
    localFinder_.addMatcher(scalarImplicitCastExpr, this);

    localFinder_.addMatcher(scalarParenExpr, this);
    localFinder_.addMatcher(scalarAddExpr, this);
    localFinder_.addMatcher(scalarMulExpr, this);
    localFinder_.addMatcher(scalarVar, this);
    localFinder_.addMatcher(scalarLiteral, this);
};

void ScalarExprMatcher::run(const MatchFinder::MatchResult &Result){
    auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("ScalarParenExpr");
    auto innerExpr = Result.Nodes.getNodeAs<clang::Expr>("ScalarInnerExpr");
    auto addExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("ScalarAddExpr");
    auto addMember = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddMember");
    auto addArgument = Result.Nodes.getNodeAs<clang::Expr>("ScalarAddArgument");
    auto mulExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("ScalarAddExpr");
    auto mulMember = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulMember");
    auto mulArgument = Result.Nodes.getNodeAs<clang::Expr>("ScalarMulArgument");
    auto declRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("ScalarDeclRefExpr");
    auto literal = Result.Nodes.getNodeAs<clang::CXXTemporaryObjectExpr>("ScalarLiteralExpr");

    auto scalarExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    auto scalarImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");

    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){
            interp_->mkFloatParenExpr(parenExpr, innerExpr);

            ScalarExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
        }
        else{
            //log error
        }
    }
    else if(addExpr or addMember or addArgument){
        if(addExpr and addMember and addArgument){
            //NOT IMPLEMENTED ON BACKEND
            
            //interp_->mkFloat
        }
        else{
            //log error
        }
    }
    else if(mulExpr or mulMember or mulArgument){
        if(mulExpr and mulMember and mulArgument){
            //NOT IMPLEMENTED ON BACKEND+

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
        ScalarExprMatcher exprMatcher{this->context_};
        exprMatcher.search();
        exprMatcher.visit(*scalarExprWithCleanups->getSubExpr());
    }
    else if(scalarImplicitCastExpr){

        ScalarExprMatcher exprMatcher{this->context_};
        exprMatcher.search();
        exprMatcher.visit(*scalarImplicitCastExpr->getSubExpr());
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }
};