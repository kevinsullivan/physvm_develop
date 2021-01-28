
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "../Interpretation.h"

#include "ROSStatementMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "FloatMatcher.h"
#include "DoubleMatcher.h"
#include "IntMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTFPointMatcher.h"
#include "ROSTFTimeMatcher.h"
#include "ROSTFDurationMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSGeometryMsgsPointStampedMatcher.h"

#include <string>


#include <iostream>

#include <memory>

#include "../ASTToCoords.h"
/*
This manages all statements in Clang.
*/


void ROSStatementMatcher::setup(){

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
        ifStmt_ = ifStmt().bind("IfStmt");

    StatementMatcher
        cmpdStmt_ = compoundStmt().bind("CompoundStmt");

    StatementMatcher
        expr_ = expr().bind("ExprStmt");

    StatementMatcher
        returnStmt_ = returnStmt().bind("ReturnStmt");

    StatementMatcher 
        whileStmt_ = whileStmt().bind("WhileStmt");

    localFinder_.addMatcher(decl_, this);
    localFinder_.addMatcher(assign_, this);
    localFinder_.addMatcher(expr_, this);
    localFinder_.addMatcher(ifStmt_,this);
    localFinder_.addMatcher(cmpdStmt_, this);
    localFinder_.addMatcher(returnStmt_, this);
    localFinder_.addMatcher(whileStmt_, this);
};

void ROSStatementMatcher::run(const MatchFinder::MatchResult &Result){

    this->childExprStore_ = nullptr;

    const auto declStmt = Result.Nodes.getNodeAs<clang::DeclStmt>("DeclStmt");

    const auto assignStmt = Result.Nodes.getNodeAs<clang::Expr>("Assign");

    const auto exprStmt = Result.Nodes.getNodeAs<clang::Expr>("ExprStmt");

    const auto exprWithCleanupsDiscard = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");

    //const auto ifStmt_ = Result.Nodes.getNodeAs<clang::IfStmt>("IfStmt");

    const auto cmpdStmt_ = Result.Nodes.getNodeAs<clang::CompoundStmt>("CompoundStmt");

    //const auto returnStmt_ = Result.Nodes.getNodeAs<clang::ReturnStmt>("ReturnStmt");

    //const auto whileStmt_ = Result.Nodes.getNodeAs<clang::WhileStmt>("WhileStmt");

    /*
        if(declStmt)
            declStmt->dump();
        else if(assignStmt)
            assignStmt->dump();
        else if(exprStmt)
            exprStmt->dump();
        */
    /*
    if(whileStmt_){
        auto wcond = whileStmt_->getCond();
        auto wbody = whileStmt_->getBody();
        
        ROSBooleanMatcher condm{ this->context_, this->interp_};
        condm.setup();
        condm.visit(*wcond);

        if(!condm.getChildExprStore()){
            std::cout<<"Unable to parse If condition!!\n";
            wcond->dump();
            throw "Broken Parse";
        }

        ROSStatementMatcher bodym{ this->context_, this->interp_};
        bodym.setup();
        bodym.visit(*wbody);

        if(!bodym.getChildExprStore()){
            std::cout<<"Unable to parse If block!!\n";
            wbody->dump();
            throw "Broken Parse";
        }

        this->interp_->mkWHILE_BOOL_EXPR_STMT(whileStmt_, condm.getChildExprStore(), bodym.getChildExprStore());
        this->childExprStore_ = (clang::Stmt*)whileStmt_;
        return;

    }*/

    /*
    if(returnStmt_){
        auto _expr = returnStmt_->getRetValue();
        auto typestr = ((clang::QualType)_expr->getType()).getAsString();
        if(false){}
        
        else if (typestr.find("geometry_msgs::PointStamped") != string::npos){
            ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("ros::Duration") != string::npos){
            ROSTFDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("tf::Transform") != string::npos){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("tf::Vector3") != string::npos){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("tf::Point") != string::npos){
            ROSTFPointMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("ros::Time") != string::npos){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("tfScalar") != string::npos){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("double") != string::npos){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("float") != string::npos){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr.find("int") != string::npos){
            IntMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
    }*/

    if(cmpdStmt_){
        std::vector<const clang::Stmt*> stmts;

        for(auto st : cmpdStmt_->body()){
            ROSStatementMatcher stmti{this->context_,this->interp_};
            stmti.setup();
            stmti.visit(*st);
            if(stmti.getChildExprStore()){
                stmts.push_back(stmti.getChildExprStore());
            }
        }
        this->interp_->mkCOMPOUND_STMT(cmpdStmt_, stmts);
        this->childExprStore_ = (clang::Stmt*)cmpdStmt_;
        return;
        
    }

    
    if (declStmt)
    {
        if (declStmt->isSingleDecl())
        {
            if (auto vd = clang::dyn_cast<clang::VarDecl>(declStmt->getSingleDecl()))
             {
                auto typestr = ((clang::QualType)vd->getType()).getAsString();
                if(false){}

                else if (typestr.find("geometry_msgs::PointStamped") != string::npos){
                    interp_->mkREAL3_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("ros::Duration") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFDurationMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("tf::Transform") != string::npos){
                    interp_->mkREALMATRIX4_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFTransformMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REALMATRIX4_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REALMATRIX4_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("tf::Vector3") != string::npos){
                    interp_->mkREAL3_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFVector3Matcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("tf::Point") != string::npos){
                    interp_->mkREAL3_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFPointMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("ros::Time") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFTimeMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("tfScalar") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFScalarMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("double") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        DoubleMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("float") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        FloatMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr.find("int") != string::npos){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        IntMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
            }
        }
        else
        {
            bool anyfound = false;
            for (auto it = declStmt->decl_begin(); it != declStmt->decl_end(); it++)
            {
                if (auto vd = clang::dyn_cast<clang::VarDecl>(declStmt->getSingleDecl()))
                {
                    auto typestr = ((clang::QualType)vd->getType()).getAsString();
                    if(false){}
                
                    else if(typestr.find("geometry_msgs::PointStamped") != string::npos){
                        interp_->mkREAL3_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("ros::Duration") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFDurationMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("tf::Transform") != string::npos){
                        interp_->mkREALMATRIX4_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFTransformMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REALMATRIX4_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REALMATRIX4_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("tf::Vector3") != string::npos){
                        interp_->mkREAL3_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFVector3Matcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("tf::Point") != string::npos){
                        interp_->mkREAL3_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFPointMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL3_VAR_REAL3_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL3_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL3_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("ros::Time") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFTimeMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("tfScalar") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFScalarMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("double") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            DoubleMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("float") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            FloatMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr.find("int") != string::npos){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            IntMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                }
            }
            if (anyfound)
            {
                this->childExprStore_ = const_cast<clang::DeclStmt*>(declStmt);
                return;
            }
        }
    }
    else if (assignStmt)
    {
        //not implemented!!
    }
    else if (exprStmt)
    {
        auto typestr = ((clang::QualType)exprStmt->getType()).getAsString();
        
        if(typestr.find("geometry_msgs::PointStamped") != string::npos){
            ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("ros::Duration") != string::npos){
            ROSTFDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("tf::Transform") != string::npos){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("tf::Vector3") != string::npos){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("tf::Point") != string::npos){
            ROSTFPointMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("ros::Time") != string::npos){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("tfScalar") != string::npos){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("double") != string::npos){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("float") != string::npos){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
        if(typestr.find("int") != string::npos){
            IntMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore())
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
                
        }
    }


    else if (exprWithCleanupsDiscard)
    {//matches fluff node to discard
        ROSStatementMatcher innerMatcher{ this->context_, this->interp_};
        innerMatcher.setup();
        innerMatcher.visit(*exprWithCleanupsDiscard->getSubExpr());
        if (innerMatcher.getChildExprStore())
            this->childExprStore_ = const_cast<clang::Stmt*>(innerMatcher.getChildExprStore());
            return;
    }
    else
    {
        //log error
    }

};

