

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "VectorExprMatcher.h"
#include "ScalarExprMatcher.h"

/*
    virtual void Traverse() = 0;
    virtual void BuildRepresentation() = 0;
    virtual StatementMatcher GetStatementMatcher() = 0;
    virtual void run(const MatchFinder::MatchResult &Result) = 0;

    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL

*/


void VectorExprMatcher::search(){
    //this matcher has no meaning, unlike other productions, and is simply a hack to strip off the pesky ExprWithCleanups wrapper.
    StatementMatcher vectorExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher vectorImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard");

    //these are valid without pointers and functions.
    StatementMatcher vectorParenExpr =
        parenExpr(allOf(hasType(asString("class Vec")),has(expr().bind("VectorInnerExpr")))).bind("VectorParenExpr");
    StatementMatcher vectorAddExpr =
        cxxMemberCallExpr(allOf(
            hasType(asString("class Vec")),
            has(memberExpr(allOf(has(expr().bind("VectorAddMember")), member(hasName("vec_add"))))), 
            hasArgument(0,expr().bind("VectorAddArgument")))).bind("VectorAddExpr");
    StatementMatcher vectorMulExpr =
        cxxMemberCallExpr(allOf(
            hasType(asString("class Vec")),
            has(memberExpr(allOf(has(expr().bind("VectorMulMember")),member(hasName("vec_mul"))))), 
            hasArgument(0,expr().bind("VectorMulArgument")))).bind("VectorMulExpr");
    StatementMatcher vectorVar = 
        declRefExpr(hasType(asString("class Vec"))).bind("VectorDeclRefExpr");
    StatementMatcher vectorLiteral = 
        //anyOf(
        //    cxxConstructExpr(allOf(hasType(asString("class Vec")),hasDeclaration(namedDecl(hasName("void (float, float, float)"))))).bind("VectorLiteralExpr"),
            cxxConstructExpr(allOf(hasType(asString("class Vec")),argumentCountIs(3))).bind("VectorLiteral");

        //);

    localFinder_.addMatcher(vectorExprWithCleanups, this);
    localFinder_.addMatcher(vectorImplicitCastExpr, this);

    localFinder_.addMatcher(vectorParenExpr, this);
    localFinder_.addMatcher(vectorAddExpr, this);
    localFinder_.addMatcher(vectorMulExpr, this);
    localFinder_.addMatcher(vectorVar, this);
    localFinder_.addMatcher(vectorLiteral, this);

};

void VectorExprMatcher::run(const MatchFinder::MatchResult &Result){
    auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("VectorParenExpr");
    auto innerExpr = Result.Nodes.getNodeAs<clang::Expr>("VectorInnerExpr");
    auto vectorAddExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddExpr");
    auto vectorAddMember = Result.Nodes.getNodeAs<clang::Expr>("VectorAddMember");
    auto vectorAddArgument = Result.Nodes.getNodeAs<clang::Expr>("VectorAddArgument");
    auto vectorMulExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddExpr");
    auto vectorMulMember = Result.Nodes.getNodeAs<clang::Expr>("VectorMulMember");
    auto vectorMulArgument = Result.Nodes.getNodeAs<clang::Expr>("VectorMulArgument");
    auto vectorDeclRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("VectorDeclRefExpr");
    auto vectorLiteral = Result.Nodes.getNodeAs<clang::CXXTemporaryObjectExpr>("VectorLiteralExpr");

    auto vectorExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    auto vectorImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");

    Result.Nodes.getNodeAs<clang::Expr>("hello")->dump();

    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){
            interp_->mkVecParenExpr(parenExpr, innerExpr);

            VectorExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
        }
        else{
            //log error
        }
    }
    else if(vectorAddExpr or vectorAddMember or vectorAddArgument){
        if(vectorAddExpr and vectorAddMember and vectorAddArgument){
            
            VectorExprMatcher memMatcher{this->context_};
            memMatcher.search();
            memMatcher.visit(*vectorAddMember);
            VectorExprMatcher argMatcher{this->context_};
            argMatcher.search();
            argMatcher.visit(*vectorAddArgument);
            interp_->mkVecVecAddExpr(vectorAddExpr, vectorAddMember, vectorAddArgument);
        }
        else{
            //log error
        }
    }
    else if(vectorMulExpr or vectorMulMember or vectorMulArgument){
        if(vectorMulExpr and vectorMulMember and vectorMulArgument){
            VectorExprMatcher memMatcher{this->context_};
            memMatcher.search();
            memMatcher.visit(*vectorMulMember);
            ScalarExprMatcher argMatcher{this->context_};
            argMatcher.search();
            argMatcher.visit(*vectorMulArgument);
            interp_->mkVecScalarMulExpr(vectorMulExpr, vectorMulMember, vectorMulArgument);
        }
        else{
            //log error
        }
    }
    else if(vectorDeclRefExpr){
        interp_->mkVecVarExpr(vectorDeclRefExpr);
    }
    else if(vectorLiteral){
        interp_->mkVector_Lit(vectorLiteral, 0, 0, 0);
    }
    else if(vectorExprWithCleanups){
        VectorExprMatcher exprMatcher{this->context_};
        exprMatcher.search();
        exprMatcher.visit(*vectorExprWithCleanups->getSubExpr());
    }
    else if(vectorImplicitCastExpr){

        VectorExprMatcher exprMatcher{this->context_};
        exprMatcher.search();
        exprMatcher.visit(*vectorImplicitCastExpr->getSubExpr());
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }

};