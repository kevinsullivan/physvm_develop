
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFQuaternionMatcher.h"

/*
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL | APPLY Scalar_EXPR VEC_EXPR

*/


void ROSTFQuaternionMatcher::search(){
    //this matcher has no meaning, unlike other productions, and is simply a hack to strip off the pesky ExprWithCleanups wrapper.
    /*StatementMatcher vectorExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher vectorImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard"); //could also potentially use ignoringImplicit(expr().bind).bind...but need to modify EVERY matcher to handle this, then
    StatementMatcher vectorCXXConstructExpr = //could also use isMoveConstructor / isCopyConstructor
        cxxConstructExpr(allOf(unless(argumentCountIs(3)),has(expr().bind("CXXConstructExprChild")))).bind("CXXConstructExprDiscard");
    StatementMatcher vectorCXXBindTemporaryExpr =
        cxxBindTemporaryExpr(has(expr().bind("CXXBindTemporaryExprChild"))).bind("CXXBindTemporaryExprDiscard");
    StatementMatcher vectorMaterializeTemporaryExpr =
        materializeTemporaryExpr(has(expr().bind("MaterializeTemporaryExprChild"))).bind("MaterializeTemporaryExprDiscard");
    */

};

void ROSTFQuaternionMatcher::run(const MatchFinder::MatchResult &Result){
/*
    auto vectorConstructExpr = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExprDiscard");
    auto vectorConstructExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXConstructExprChild");
    auto vectorExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");
    auto vectorImplicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");
    auto vectorBindTemporaryExpr = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExprDiscard");
    auto vectorBindTemporaryExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXBindTemporaryExprChild");
    auto vectorMaterializeTemporaryExpr = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExprDiscard");
    auto vectorMaterializeTemporaryChild = Result.Nodes.getNodeAs<clang::Expr>("MaterializeTemporaryExprChild");
*/

/*
    if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            VectorExprMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
           // interp_->mkVecParenExpr(parenExpr, exprMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)parenExpr;
            
        }
        else{
            //log error
        }
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
           // interp_->mkVector_Expr(vectorConstructExpr, exprMatcher.getChildExprStore());
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
*/
};