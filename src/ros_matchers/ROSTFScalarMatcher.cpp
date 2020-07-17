
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFScalarMatcher.h"


void ROSTFScalarMatcher::search(){
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

void ROSTFScalarMatcher::run(const MatchFinder::MatchResult &Result){

    auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
    auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
    auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
    auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
    auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    auto cxxTemporaryObjectExpr_ = Result.Nodes.getNodeAs<clang::CXXTemporaryObjectExpr>("CXXTemporaryObjectExpr");
    auto cxxOperatorCallExpr_ = Result.Nodes.getNodeAs<clang::CXXOperatorCallExpr>("CXXOperatorCallExpr");
    auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");

    if(parenExpr_){
        ROSTFScalarMatcher inner{context_, interp_};
        inner.search();
        inner.visit(*parenExpr_->getSubExpr());
    }
    else if(exprWithCleanups_){
        ROSTFScalarMatcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*exprWithCleanups_->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(materializeTemporaryExpr_){
        ROSTFScalarMatcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(implicitCastExpr_){
        auto inner = implicitCastExpr_->getSubExpr();

        if(inner->getType().getAsString().find("tfScalar") != string::npos){

            ROSTFScalarMatcher exprMatcher{context_, interp_};
            exprMatcher.search();
            exprMatcher.visit(*implicitCastExpr_->getSubExpr());
            this->childExprStore_ = exprMatcher.getChildExprStore();
        }
        else{
            this->interp_->mkREAL1_LITERAL1(implicitCastExpr_);
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
        }

    }
    else if(cxxBindTemporaryExpr_){
        ROSTFScalarMatcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    
    else if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL1_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
        }
    }
    
    };
