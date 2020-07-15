#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "../Interpretation.h"


#include "ROSStatementMatcher.h"
#include "ROSTFPointMatcher.h"
#include "ROSTFPoseMatcher.h"
#include "ROSTFQuaternionMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFVector3Matcher.h"

#include <string>


#include <iostream>

#include <memory>

#include "../ASTToCoords.h"
/*
STMT := 
    VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | TRANSFORM_EXPR
    VEC_EXPR | SCALAR_EXPR | TRANSFORM_EXPR
    DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR | DECL TRANSFORM_VAR = TRANSFORM_EXPR
*/


void ROSStatementMatcher::search(){
    
    StatementMatcher exprWithCleanups_ = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");//fluff node to discard

    StatementMatcher 
        decl_ = declStmt().bind("DeclStmt");
    StatementMatcher
        assign_ = anyOf(
            cxxOperatorCallExpr(
                hasOverloadedOperatorName("=")).bind("Assign"),
            binaryOperator(
                hasOperatorName("=")).bind("Assign")
        );

    StatementMatcher
        expr_ = expr().bind("ExprStmt");
    localFinder_.addMatcher(decl_, this);
    localFinder_.addMatcher(assign_, this);
    localFinder_.addMatcher(expr_, this);
};

void ROSStatementMatcher::run(const MatchFinder::MatchResult &Result){
    
    const auto declStmt = Result.Nodes.getNodeAs<clang::DeclStmt>("DeclStmt");

    const auto assignStmt = Result.Nodes.getNodeAs<clang::Expr>("Assign");

    const auto exprStmt = Result.Nodes.getNodeAs<clang::Expr>("ExprStmt");

    const auto exprWithCleanupsDiscard = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");


    /*auto getMatcher = [=](std::string typestr_){
        std::shared_ptr<BaseMatcher> mymatcher;
        
        if(typestr_.find("tf::Vector3") != string::npos){
            return 
        }
        else if(typestr_.find("tf::Quaternion") != string::npos){

        }
        else if(typestr_.find("tf::Point") != string::npos){

        }
        else if(typestr_.find("tf::Transform") != string::npos){

        }
        else if(typestr_.find("tfScalar")){

        }
        else if(typestr_.find("tf::Pose")){

        }

        return mymatcher;
    };*/
/*
    if(declStmt)
        declStmt->dump();
    else if(assignStmt)
        assignStmt->dump();
    else if(exprStmt)
        exprStmt->dump();
    */

    if(declStmt){
        if(declStmt->isSingleDecl()){
            if(auto vd = clang::dyn_cast<clang::VarDecl>(declStmt->getSingleDecl()))
            {
                auto typestr = ((clang::QualType)vd->getType()).getAsString();

                if(typestr.find("tf::Vector3") != string::npos){
                    if(vd->hasInit()){
                        ROSTFVector3Matcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        if(m.getChildExprStore()){
                            interp_->mkREAL3_VAR_IDENT(vd);
                            interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkREAL3_VAR_IDENT(vd);
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REAL3_VAR(declStmt, vd);
                    }
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);

                }
                else if(typestr.find("tf::Quaternion") != string::npos){
                    if(vd->hasInit()){
                        ROSTFQuaternionMatcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        if(m.getChildExprStore()){
                            interp_->mkREAL4_VAR_IDENT(vd);
                            interp_->mkDECL_REAL4_VAR_REAL4_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkREAL4_VAR_IDENT(vd);
                            interp_->mkDECL_REAL4_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REAL4_VAR(declStmt, vd);
                    }
                    
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
                }
                else if(typestr.find("tf::Point") != string::npos){
                    if(vd->hasInit()){
                        ROSTFPointMatcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        if(m.getChildExprStore()){
                            m.getChildExprStore()->dump();
                            interp_->mkREAL3_VAR_IDENT(vd);
                            interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkREAL3_VAR_IDENT(vd);
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REAL3_VAR(declStmt, vd);
                    }
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
                }
                else if(typestr.find("tf::Transform") != string::npos){
                    if(vd->hasInit()){
                        ROSTFTransformMatcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        interp_->mkREALMATRIX_VAR_IDENT(vd);
                        if(m.getChildExprStore()){
                            interp_->mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                    }
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);

                }
                else if(typestr.find("tfScalar") != string::npos){
                    if(vd->hasInit()){
                        ROSTFScalarMatcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if(m.getChildExprStore()){
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                    }
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
                }
                else if(typestr.find("tf::Pose") != string::npos){
                    if(vd->hasInit()){
                        ROSTFPoseMatcher m{this->context_, this->interp_};
                        m.search();
                        m.visit((*vd->getInit()));
                        interp_->mkREALMATRIX_VAR_IDENT(vd);
                        if(m.getChildExprStore()){
                            interp_->mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(declStmt, vd, m.getChildExprStore());
                        }
                        else{
                            interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                        }
                    }
                    else{
                        interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                    }
                    this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
                }
            }
        }
        else{
            bool anyfound = false;
            for(auto it = declStmt->decl_begin(); it != declStmt->decl_end();it++){
                if(auto vd = clang::dyn_cast<clang::VarDecl>(declStmt->getSingleDecl()))
                {
                    auto typestr = ((clang::QualType)vd->getType()).getAsString();

                    if(typestr.find("tf::Vector3") != string::npos){
                        if(vd->hasInit()){
                            ROSTFVector3Matcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }

                    }
                    else if(typestr.find("tf::Quaternion") != string::npos){
                        if(vd->hasInit()){
                            ROSTFQuaternionMatcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REAL4_VAR_REAL4_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REAL4_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REAL4_VAR(declStmt, vd);
                        }
                    }
                    else if(typestr.find("tf::Point") != string::npos){
                        if(vd->hasInit()){
                            ROSTFPointMatcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                    }
                    else if(typestr.find("tf::Transform") != string::npos){
                        if(vd->hasInit()){
                            ROSTFTransformMatcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                        }

                    }
                    else if(typestr.find("tfScalar")){
                        if(vd->hasInit()){
                            ROSTFTransformMatcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                    }
                    else if(typestr.find("tf::Pose")){
                        if(vd->hasInit()){
                            ROSTFPoseMatcher m{this->context_, this->interp_};
                            m.search();
                            m.visit((*vd->getInit()));
                            if(m.getChildExprStore()){
                                interp_->mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else{
                                interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                            }
                        }
                        else{
                            interp_->mkDECL_REALMATRIX_VAR(declStmt, vd);
                        }
                    }
                }
            }
            if(anyfound){
                this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
            }
        }

    }
    else if(assignStmt){
        //not implemented!!
    }
    else if(exprStmt){
        auto typestr = ((clang::QualType)exprStmt->getType()).getAsString();

        if(typestr.find("tf::Vector3") != string::npos){
            ROSTFVector3Matcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
        }
        else if(typestr.find("tf::Quaternion") != string::npos){
            ROSTFQuaternionMatcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
        }
        else if(typestr.find("tf::Point") != string::npos){
            ROSTFPointMatcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
        }
        else if(typestr.find("tf::Transform") != string::npos){
            ROSTFTransformMatcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());

        }
        else if(typestr.find("tfScalar") != string::npos){
            ROSTFTransformMatcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
            this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
        }
        else if(typestr.find("tf::Pose") != string::npos){
            ROSTFPoseMatcher m{this->context_, this->interp_};
            m.search();
            m.visit(*exprStmt);
            if(m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
        }
            
    }
    else if(exprWithCleanupsDiscard){//matches fluff node to discard
        ROSStatementMatcher innerMatcher{this->context_, this->interp_};
        innerMatcher.search();
        innerMatcher.visit(*exprWithCleanupsDiscard->getSubExpr());
            if(innerMatcher.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(innerMatcher.getChildExprStore());
    }
    else{
            //log error
    }

};