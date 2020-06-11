
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "VectorExprMatcher.h"
#include "ScalarExprMatcher.h"
#include "TransformExprMatcher.h"

/*
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL | APPLY TRANSFORM_EXPR VEC_EXPR

*/


void VectorExprMatcher::search(){
    //this matcher has no meaning, unlike other productions, and is simply a hack to strip off the pesky ExprWithCleanups wrapper.
    StatementMatcher vectorExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher vectorImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard"); //could also potentially use ignoringImplicit(expr().bind).bind...but need to modify EVERY matcher to handle this, then
    StatementMatcher vectorCXXConstructExpr = //could also use isMoveConstructor / isCopyConstructor
        cxxConstructExpr(allOf(unless(argumentCountIs(3)),has(expr().bind("CXXConstructExprChild")))).bind("CXXConstructExprDiscard");
    StatementMatcher vectorCXXBindTemporaryExpr =
        cxxBindTemporaryExpr(has(expr().bind("CXXBindTemporaryExprChild"))).bind("CXXBindTemporaryExprDiscard");
    StatementMatcher vectorMaterializeTemporaryExpr =
        materializeTemporaryExpr(has(expr().bind("MaterializeTemporaryExprChild"))).bind("MaterializeTemporaryExprDiscard");
    

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
    StatementMatcher transformApplyExpr = 
        cxxMemberCallExpr(allOf(
            hasType(asString("class Vec")),
            has(memberExpr(allOf(has(expr().bind("TransformApplyMember")),member(hasName("apply"))))), 
            hasArgument(0,expr().bind("VecApplyArgument")))).bind("TransformApplyExpr");
    StatementMatcher vectorVar = 
        declRefExpr(hasType(asString("class Vec"))).bind("VectorDeclRefExpr");
    StatementMatcher vectorLiteral = 
        //anyOf(
        //    cxxConstructExpr(allOf(hasType(asString("class Vec")),hasDeclaration(namedDecl(hasName("void (float, float, float)"))))).bind("VectorLiteralExpr"),
            cxxConstructExpr(allOf(hasType(asString("class Vec")),argumentCountIs(3))).bind("VectorLiteralExpr");

        //);

    localFinder_.addMatcher(vectorExprWithCleanups, this);
    localFinder_.addMatcher(vectorImplicitCastExpr, this);
    localFinder_.addMatcher(vectorCXXConstructExpr, this);
    localFinder_.addMatcher(vectorCXXBindTemporaryExpr, this);
    localFinder_.addMatcher(vectorMaterializeTemporaryExpr, this);

    localFinder_.addMatcher(vectorParenExpr, this);
    localFinder_.addMatcher(vectorAddExpr, this);
    localFinder_.addMatcher(vectorMulExpr, this);
    localFinder_.addMatcher(transformApplyExpr, this);
    localFinder_.addMatcher(vectorVar, this);
    localFinder_.addMatcher(vectorLiteral, this);

};

void VectorExprMatcher::run(const MatchFinder::MatchResult &Result){
    const auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("VectorParenExpr");
    const auto innerExpr = Result.Nodes.getNodeAs<clang::Expr>("VectorInnerExpr");
    const auto vectorAddExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorAddExpr");
    const auto vectorAddMember = Result.Nodes.getNodeAs<clang::Expr>("VectorAddMember");
    const auto vectorAddArgument = Result.Nodes.getNodeAs<clang::Expr>("VectorAddArgument");
    const auto vectorMulExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("VectorMulExpr");
    const auto vectorMulMember = Result.Nodes.getNodeAs<clang::Expr>("VectorMulMember");
    const auto vectorMulArgument = Result.Nodes.getNodeAs<clang::Expr>("VectorMulArgument");
    const auto transformApplyExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("TransformApplyExpr");
    const auto transformApplyMember = Result.Nodes.getNodeAs<clang::Expr>("TransformApplyMember");
    const auto vectorApplyArgument = Result.Nodes.getNodeAs<clang::Expr>("VecApplyArgument");
    const auto vectorDeclRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("VectorDeclRefExpr");
    const auto vectorLiteral = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorLiteralExpr");

    auto vectorConstructExpr = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExprDiscard");
    auto vectorConstructExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXConstructExprChild");
    auto vectorExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    auto vectorImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");
    auto vectorBindTemporaryExpr = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExprDiscard");
    auto vectorBindTemporaryExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXBindTemporaryExprChild");
    auto vectorMaterializeTemporaryExpr = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExprDiscard");
    auto vectorMaterializeTemporaryChild = Result.Nodes.getNodeAs<clang::Expr>("MaterializeTemporaryExprChild");



    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
            interp_->mkVecParenExpr(parenExpr, exprMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)parenExpr;
            
        }
        else{
            //log error
        }
    }
    else if(vectorAddExpr or vectorAddMember or vectorAddArgument){
        if(vectorAddExpr and vectorAddMember and vectorAddArgument){
            
            VectorExprMatcher memMatcher{this->context_, this->interp_};
            memMatcher.search();
            memMatcher.visit(*vectorAddMember);
            VectorExprMatcher argMatcher{this->context_, this->interp_};
            argMatcher.search();
            argMatcher.visit(*vectorAddArgument);

            interp_->mkVecVecAddExpr(vectorAddExpr, memMatcher.getChildExprStore(), argMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)vectorAddExpr;
        }
        else{
            //log error
        }
    }
    else if(vectorMulExpr or vectorMulMember or vectorMulArgument){
        if(vectorMulExpr and vectorMulMember and vectorMulArgument){
            VectorExprMatcher memMatcher{this->context_, this->interp_};
            memMatcher.search();
            memMatcher.visit(*vectorMulMember);
            ScalarExprMatcher argMatcher{this->context_, this->interp_};
            argMatcher.search();
            argMatcher.visit(*vectorMulArgument);
            interp_->mkVecScalarMulExpr(vectorMulExpr, memMatcher.getChildExprStore(), argMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)vectorMulExpr;
        }
        else{
            //log error
        }
    }
    else if(transformApplyExpr or transformApplyMember or vectorApplyArgument)
    {
        if(transformApplyExpr and transformApplyMember and vectorApplyArgument){
            TransformExprMatcher memMatcher{this->context_, this->interp_};
            memMatcher.search();
            memMatcher.visit(*transformApplyMember);
            VectorExprMatcher argMatcher{this->context_, this->interp_};
            argMatcher.search();
            argMatcher.visit(*vectorApplyArgument);
            interp_->mkTransformVecApplyExpr(transformApplyExpr, memMatcher.getChildExprStore(), argMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)transformApplyExpr;
        }
        else{
            //log error
        }
    }
    else if(vectorDeclRefExpr){
        interp_->mkVecVarExpr(vectorDeclRefExpr);
        this->childExprStore_ = (clang::Expr*)vectorDeclRefExpr;
    }
    else if(vectorLiteral){
        interp_->mkVector_Lit(vectorLiteral, 0, 0, 0);
        this->childExprStore_ = (clang::Expr*)vectorLiteral;
    }
    else if(vectorExprWithCleanups){
        VectorExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*vectorExprWithCleanups->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
        
        //interp_->mkVecWrapperExpr(vectorExprWithCleanups, vectorExprWithCleanups->getSubExpr());
    }
    else if(vectorImplicitCastExpr){
        VectorExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*vectorImplicitCastExpr->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();

        //interp_->mkVecWrapperExpr(vectorImplicitCastExpr, vectorImplicitCastExpr->getSubExpr());
    }
    else if(vectorConstructExpr or vectorConstructExprChild){
        if(vectorConstructExpr and vectorConstructExprChild){
            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*vectorConstructExprChild);
            
            this->childExprStore_ = (clang::Expr*)exprMatcher.getChildExprStore();
            interp_->mkVector_Expr(vectorConstructExpr, exprMatcher.getChildExprStore());
        }
        else{
            //log error
        }
    }
    else if(vectorBindTemporaryExpr or vectorBindTemporaryExprChild){
        if(vectorBindTemporaryExpr and vectorBindTemporaryExprChild){
            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*vectorBindTemporaryExprChild);

            this->childExprStore_ = (clang::Expr*)exprMatcher.getChildExprStore();
            //no longer doing this!
            //interp_->mkVecWrapperExpr(vectorBindTemporaryExpr, vectorBindTemporaryExprChild);

        }
        else{
            //log error
        }
    }
    else if(vectorMaterializeTemporaryExpr and vectorMaterializeTemporaryChild){
        if(vectorMaterializeTemporaryExpr and vectorMaterializeTemporaryChild){
            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*vectorMaterializeTemporaryChild);

            this->childExprStore_ = exprMatcher.getChildExprStore();
            //interp_->mkVecWrapperExpr(vectorMaterializeTemporaryExpr, vectorMaterializeTemporaryChild);

        }
        else{
            //log error
        }
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }

};