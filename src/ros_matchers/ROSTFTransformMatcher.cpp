
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFTransformMatcher.h"

/*
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL | APPLY TRANSFORM_EXPR VEC_EXPR

*/


void ROSTFTransformMatcher::search(){
    StatementMatcher exprWithCleanups_ = 
        exprWithCleanups(
            has(expr().bind("UsefulExpr"))).bind("ExprWithCleanups");
    StatementMatcher constructExpr_ = 
        cxxConstructExpr().bind("CXXConstructExpr");
    StatementMatcher materializeTemporaryExpr_ =
        materializeTemporaryExpr().bind("MaterializeTemporaryExpr");
    StatementMatcher implicitCastExpr_ =
        implicitCastExpr().bind("ImplicitCastExpr");
    StatementMatcher cxxBindTemporaryExpr_ =
        cxxBindTemporaryExpr().bind("CXXBindTemporaryExpr");
    StatementMatcher declRefExpr_ =
        declRefExpr().bind("DeclRefExpr");
    StatementMatcher cxxTemporaryObjectExpr_ =
        cxxTemporaryObjectExpr().bind("CXXTemporaryObjectExpr");
    StatementMatcher cxxOperatorCallExpr_ =
        cxxOperatorCallExpr().bind("CXXOperatorCallExpr");
    StatementMatcher parenExpr_ =
        parenExpr().bind("ParenExpr");

    localFinder_.addMatcher(parenExpr_, this);
    localFinder_.addMatcher(exprWithCleanups_, this);
    localFinder_.addMatcher(constructExpr_, this);
    localFinder_.addMatcher(materializeTemporaryExpr_, this);
    localFinder_.addMatcher(implicitCastExpr_, this);
    localFinder_.addMatcher(cxxBindTemporaryExpr_, this);
    localFinder_.addMatcher(declRefExpr_, this);
    localFinder_.addMatcher(cxxTemporaryObjectExpr_, this);
    localFinder_.addMatcher(cxxOperatorCallExpr_, this);
};

void ROSTFTransformMatcher::run(const MatchFinder::MatchResult &Result){
    auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
    auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
    auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
    auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
    auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    auto cxxTemporaryObjectExpr_ = Result.Nodes.getNodeAs<clang::CXXTemporaryObjectExpr>("CXXTemporaryObjectExpr");
    auto cxxOperatorCallExpr_ = Result.Nodes.getNodeAs<clang::CXXOperatorCallExpr>("CXXOperatorCallExpr");

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