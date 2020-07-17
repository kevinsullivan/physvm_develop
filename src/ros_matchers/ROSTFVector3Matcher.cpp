
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFVector3Matcher.h"
#include "ROSTFPointMatcher.h"
#include "ROSTFScalarMatcher.h"

/*
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL | APPLY TRANSFORM_EXPR VEC_EXPR

*/


void ROSTFVector3Matcher::search(){

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

void ROSTFVector3Matcher::run(const MatchFinder::MatchResult &Result){

    auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
    auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
    auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
    auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
    auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
    auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    auto cxxTemporaryObjectExpr_ = Result.Nodes.getNodeAs<clang::CXXTemporaryObjectExpr>("CXXTemporaryObjectExpr");
    auto cxxOperatorCallExpr_ = Result.Nodes.getNodeAs<clang::CXXOperatorCallExpr>("CXXOperatorCallExpr");
    auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
/*
    std::cout<<"BEGIN VECTOR MATCH\n";
    if(parenExpr_)
        parenExpr_->dump();
    if(cxxConstructExpr_)
        cxxConstructExpr_->dump();
    if(exprWithCleanups_)
        exprWithCleanups_->dump();
    if(materializeTemporaryExpr_)
        materializeTemporaryExpr_->dump();
    if(implicitCastExpr_)
        implicitCastExpr_->dump();
    if(cxxBindTemporaryExpr_)
        cxxBindTemporaryExpr_->dump();
    if(declRefExpr_)
        declRefExpr_->dump();
    if(cxxTemporaryObjectExpr_)
        cxxTemporaryObjectExpr_->dump();
    if(cxxOperatorCallExpr_)
        cxxOperatorCallExpr_->dump();
*/
    if(parenExpr_){
        ROSTFVector3Matcher inner{context_, interp_};
        inner.search();
        inner.visit(*parenExpr_->getSubExpr());
    }
    else if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFVector3Matcher vm{context_, interp_};
            vm.search();
            vm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = vm.getChildExprStore();
        }
        else if(cxxConstructExpr_->getNumArgs() == 3){
            //ROSTFVector3Matcher vm{context_, interp_};
            //vm.search();
            ROSTFScalarMatcher a1{context_, interp_};
            ROSTFScalarMatcher a2{context_, interp_};
            ROSTFScalarMatcher a3{context_, interp_};
            a1.search();
            a2.search();
            a3.search();
            a1.visit(*cxxConstructExpr_->getArg(1));
            a2.visit(*cxxConstructExpr_->getArg(2));
            a3.visit(*cxxConstructExpr_->getArg(3));
            interp_->mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(
                cxxConstructExpr_, 
                a1.getChildExprStore(), 
                a2.getChildExprStore(), 
                a3.getChildExprStore());
            this->childExprStore_ = (clang::Stmt*)cxxConstructExpr_;
        }
    }
    else if(exprWithCleanups_){
        ROSTFVector3Matcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*exprWithCleanups_->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(materializeTemporaryExpr_){
        ROSTFVector3Matcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(implicitCastExpr_){
        ROSTFVector3Matcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*implicitCastExpr_->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();

    }
    else if(cxxBindTemporaryExpr_){
        ROSTFVector3Matcher exprMatcher{context_, interp_};
        exprMatcher.search();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();
    }
    else if(cxxTemporaryObjectExpr_){
        auto decl_ = cxxTemporaryObjectExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFVector3Matcher vm{context_, interp_};
            vm.search();
            vm.visit(**cxxTemporaryObjectExpr_->getArgs());
            this->childExprStore_ = vm.getChildExprStore();
        }
        else if(cxxTemporaryObjectExpr_->getNumArgs() == 3){
            ROSTFScalarMatcher a1{context_, interp_};
            ROSTFScalarMatcher a2{context_, interp_};
            ROSTFScalarMatcher a3{context_, interp_};
            a1.search();
            a2.search();
            a3.search();
            a1.visit(*cxxTemporaryObjectExpr_->getArg(1));
            a2.visit(*cxxTemporaryObjectExpr_->getArg(2));
            a3.visit(*cxxTemporaryObjectExpr_->getArg(3));
            interp_->mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(
                cxxTemporaryObjectExpr_, 
                a1.getChildExprStore(), 
                a2.getChildExprStore(), 
                a3.getChildExprStore());
            this->childExprStore_ = (clang::Stmt*)cxxTemporaryObjectExpr_;
        }
    }
    else if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL3_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
        }
    }
    else if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name.find("-") != string::npos){
                auto left = cxxOperatorCallExpr_->getArg(0);
                auto right = cxxOperatorCallExpr_->getArg(1);
                /*std::cout<<"LEFT:";
                left->dump();
                std::cout<<"RIGHT:";
                right->dump();*/
                auto ltype = left->getType();
                auto rtype = right->getType();
                clang::Stmt* lexpr = nullptr;
                clang::Stmt* rexpr = nullptr;
                if(ltype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();

                }
                else if(ltype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();
                }
                
                if(rtype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();

                }
                else if(rtype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();
                }

                if(lexpr and rexpr){
                    this->interp_->mkSUB_REAL3_EXPR_REAL3_EXPR(cxxOperatorCallExpr_, lexpr, rexpr);
                    this->childExprStore_ = (clang::Stmt*) cxxOperatorCallExpr_;
                }
            }
            else if(name.find("+") != string::npos){
                auto left = cxxOperatorCallExpr_->getArg(0);
                auto right = cxxOperatorCallExpr_->getArg(1);
                auto ltype = left->getType();
                auto rtype = right->getType();
                clang::Stmt* lexpr = nullptr;
                clang::Stmt* rexpr = nullptr;
                if(ltype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();

                }
                else if(ltype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();
                }
                
                if(rtype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();

                }
                else if(rtype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();
                }

                if(lexpr and rexpr){
                    this->interp_->mkSUB_REAL3_EXPR_REAL3_EXPR(cxxOperatorCallExpr_, lexpr, rexpr);
                    this->childExprStore_ = (clang::Stmt*) cxxOperatorCallExpr_;
                }

            }
            else if(name.find("*") != string::npos){
                auto left = cxxOperatorCallExpr_->getArg(0);
                auto right = cxxOperatorCallExpr_->getArg(1);
                auto ltype = left->getType();
                auto rtype = right->getType();
                clang::Stmt* lexpr = nullptr;
                clang::Stmt* rexpr = nullptr;
                if(ltype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();

                }
                else if(ltype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();
                }
                
                if(rtype.getAsString().find("tf::Vector3") != string::npos){
                    ROSTFVector3Matcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();

                }
                else if(rtype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();
                }

                if(lexpr and rexpr){
                    this->interp_->mkSUB_REAL3_EXPR_REAL3_EXPR(cxxOperatorCallExpr_, lexpr, rexpr);
                    this->childExprStore_ = (clang::Stmt*) cxxOperatorCallExpr_;
                }

            }
            else if(name.find("/") != string::npos){
                auto left = cxxOperatorCallExpr_->getArg(0);
                auto right = cxxOperatorCallExpr_->getArg(1);
                auto ltype = left->getType();
                auto rtype = right->getType();
                clang::Stmt* lexpr = nullptr;
                clang::Stmt* rexpr = nullptr;
                if(ltype.getAsString().find("tfScalar") != string::npos){
                    ROSTFScalarMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();

                }
                else if(ltype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*left);
                    lexpr = exprMatcher.getChildExprStore();
                }
                
                if(rtype.getAsString().find("tfScalar") != string::npos){
                    ROSTFScalarMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();

                }
                else if(rtype.getAsString().find("tf::Point") != string::npos){
                    ROSTFPointMatcher exprMatcher{context_, interp_};
                    exprMatcher.search();
                    exprMatcher.visit(*right);
                    rexpr = exprMatcher.getChildExprStore();
                }

                if(lexpr and rexpr){
                    this->interp_->mkSUB_REAL3_EXPR_REAL3_EXPR(cxxOperatorCallExpr_, lexpr, rexpr);
                    this->childExprStore_ = (clang::Stmt*) cxxOperatorCallExpr_;
                }

            }
            else if(false){

            }
        }
    }

};