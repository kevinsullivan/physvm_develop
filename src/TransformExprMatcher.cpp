
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"


#include "TransformExprMatcher.h"
#include "VectorExprMatcher.h"


/*
    TRANSFORM_EXPR := (TRANSFORM_EXPR) | COMPOSE TRANSFORM_EXPR TRANSFORM_EXPR | TRANSFORM_VAR | TRANSFORM_LITERAL
    TRANSFORM_LITERAL := VEC_EXPR VEC_EXPR VEC_EXPR
*/

void TransformExprMatcher::search(){
    StatementMatcher transformExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher transformImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard"); //could also potentially use ignoringImplicit(expr().bind).bind...but need to modify EVERY matcher to handle this, then
    StatementMatcher transformCXXConstructExpr = //could also use isMoveConstructor / isCopyConstructor
        cxxConstructExpr(allOf(unless(argumentCountIs(3)),has(expr().bind("CXXConstructExprChild")))).bind("CXXConstructExprDiscard");
    StatementMatcher transformCXXBindTemporaryExpr =
        cxxBindTemporaryExpr(has(expr().bind("CXXBindTemporaryExprChild"))).bind("CXXBindTemporaryExprDiscard");
    StatementMatcher transformMaterializeTemporaryExpr =
        materializeTemporaryExpr(has(expr().bind("MaterializeTemporaryExprChild"))).bind("MaterializeTemporaryExprDiscard");
    
    StatementMatcher transformParenExpr =
        parenExpr(allOf(hasType(asString("class Transform")),has(expr().bind("TransformInnerExpr")))).bind("TransformParenExpr");
    StatementMatcher transformVarExpr = 
        declRefExpr(hasType(asString("class Transform"))).bind("TransformDeclRefExpr");
    StatementMatcher transformLiteral = 
        //anyOf(
        //    cxxConstructExpr(allOf(hasType(asString("class Transform")),hasDeclaration(namedDecl(hasName("void (float, float, float)"))))).bind("TransformLiteralExpr"),
            cxxConstructExpr(allOf(
                hasType(asString("class Transform")),
                hasArgument(0, expr(hasType(asString("class Vec"))).bind("VecArg1")),
                hasArgument(1, expr(hasType(asString("class Vec"))).bind("VecArg2")),
                hasArgument(2, expr(hasType(asString("class Vec"))).bind("VecArg3"))
            )).bind("TransformLiteralExpr");

        //);
    StatementMatcher transformComposeExpr =
        cxxMemberCallExpr(allOf(
            hasType(asString("class Transform")),
            has(memberExpr(allOf(has(expr().bind("TransformComposeMember")), member(hasName("compose"))))), 
            hasArgument(0,expr().bind("TransformComposeArgument")))).bind("TransformComposeExpr");

    localFinder_.addMatcher(transformParenExpr, this);
    localFinder_.addMatcher(transformVarExpr, this);
    localFinder_.addMatcher(transformLiteral, this);
    localFinder_.addMatcher(transformComposeExpr, this);

    localFinder_.addMatcher(transformExprWithCleanups, this);
    localFinder_.addMatcher(transformImplicitCastExpr, this);
    localFinder_.addMatcher(transformCXXConstructExpr, this);
    localFinder_.addMatcher(transformCXXBindTemporaryExpr, this);
    localFinder_.addMatcher(transformMaterializeTemporaryExpr, this);    
};

void TransformExprMatcher::run(const MatchFinder::MatchResult &Result){
    const auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("TransformParenExpr");
    const auto innerExpr = Result.Nodes.getNodeAs<clang::Expr>("TransformInnerExpr");
    const auto transformComposeExpr = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("TransformComposeExpr");
    const auto transformComposeMember = Result.Nodes.getNodeAs<clang::Expr>("TransformComposeMember");
    const auto transformComposeArgument = Result.Nodes.getNodeAs<clang::Expr>("TransformComposeArgument");
    const auto transformDeclRefExpr = Result.Nodes.getNodeAs<clang::DeclRefExpr>("TransformDeclRefExpr");
    const auto transformLiteral = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("TransformLiteralExpr");
    const auto transformLiteralVecArg1 = Result.Nodes.getNodeAs<clang::Expr>("VecArg1");
    const auto transformLiteralVecArg2 = Result.Nodes.getNodeAs<clang::Expr>("VecArg2");
    const auto transformLiteralVecArg3 = Result.Nodes.getNodeAs<clang::Expr>("VecArg3");


    auto transformConstructExpr = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExprDiscard");
    auto transformConstructExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXConstructExprChild");
    auto transformExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    auto transformImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");
    auto transformBindTemporaryExpr = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExprDiscard");
    auto transformBindTemporaryExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXBindTemporaryExprChild");
    auto transformMaterializeTemporaryExpr = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExprDiscard");
    auto transformMaterializeTemporaryChild = Result.Nodes.getNodeAs<clang::Expr>("MaterializeTemporaryExprChild");

    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            TransformExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
            interp_->mkTransformParenExpr(parenExpr, exprMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)parenExpr;
            
        }
        else{
            //log error
        }
    }
    else if(transformComposeExpr or transformComposeMember or transformComposeArgument){
        if(transformComposeExpr and transformComposeMember and transformComposeArgument){
            
            TransformExprMatcher memMatcher{this->context_, this->interp_};
            memMatcher.search();
            memMatcher.visit(*transformComposeMember);
            TransformExprMatcher argMatcher{this->context_, this->interp_};
            argMatcher.search();
            argMatcher.visit(*transformComposeArgument);
            interp_->mkTransformTransformComposeExpr(transformComposeExpr, memMatcher.getChildExprStore(), argMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)transformComposeExpr;
        }
        else{
            //log error
        }
    }
    else if(transformDeclRefExpr){
        interp_->mkTransformVarExpr(transformDeclRefExpr);
        this->childExprStore_ = (clang::Expr*)transformDeclRefExpr;
    }
    else if(transformLiteral or transformLiteralVecArg1 or transformLiteralVecArg2 or transformLiteralVecArg3){
        VectorExprMatcher exprMatcher1{this->context_, this->interp_};
        exprMatcher1.search();
        exprMatcher1.visit(*transformLiteralVecArg1);
        VectorExprMatcher exprMatcher2{this->context_, this->interp_};
        exprMatcher2.search();
        exprMatcher2.visit(*transformLiteralVecArg2);
        VectorExprMatcher exprMatcher3{this->context_, this->interp_};
        exprMatcher3.search();
        exprMatcher3.visit(*transformLiteralVecArg3);

        interp_->mkTransform_Lit(transformLiteral, exprMatcher1.getChildExprStore(), exprMatcher2.getChildExprStore(), exprMatcher3.getChildExprStore());
        this->childExprStore_ = (clang::Expr*)transformLiteral;
    }
    else if(transformExprWithCleanups){
        TransformExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*transformExprWithCleanups->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
        
        //interp_->mkVecWrapperExpr(transformExprWithCleanups, transformExprWithCleanups->getSubExpr());
    }
    else if(transformImplicitCastExpr){
        TransformExprMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*transformImplicitCastExpr->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();

        //interp_->mkVecWrapperExpr(transformImplicitCastExpr, transformImplicitCastExpr->getSubExpr());
    }
    else if(transformConstructExpr or transformConstructExprChild){
        if(transformConstructExpr and transformConstructExprChild){
            TransformExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*transformConstructExprChild);
            
            this->childExprStore_ = (clang::Expr*)exprMatcher.getChildExprStore();

            interp_->mkTransform_Expr(transformConstructExpr, exprMatcher.getChildExprStore());
            //interp_->mkVecWrapperExpr(transformConstructExpr, transformConstructExprChild);
        }
        else{
            //log error
        }
    }
    else if(transformBindTemporaryExpr or transformBindTemporaryExprChild){
        if(transformBindTemporaryExpr and transformBindTemporaryExprChild){
            TransformExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*transformBindTemporaryExprChild);

            this->childExprStore_ = exprMatcher.getChildExprStore();
            //no longer doing this!
            //interp_->mkVecWrapperExpr(transformBindTemporaryExpr, transformBindTemporaryExprChild);

        }
        else{
            //log error
        }
    }
    else if(transformMaterializeTemporaryExpr and transformMaterializeTemporaryChild){
        if(transformMaterializeTemporaryExpr and transformMaterializeTemporaryChild){
            TransformExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*transformMaterializeTemporaryChild);

            this->childExprStore_ = exprMatcher.getChildExprStore();
            //interp_->mkVecWrapperExpr(transformMaterializeTemporaryExpr, transformMaterializeTemporaryChild);

        }
        else{
            //log error
        }
    }
    else{
        //this can occur if the compound statement calling this matcher is empty. if that is checked beforehand, then this state cannot occur, and thus, no match is an error.
    }
};