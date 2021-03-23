
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "../Interpretation.h"

#include "ROSStatementMatcher.h"
#include "ROSBooleanMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "FloatMatcher.h"
#include "DoubleMatcher.h"
#include "IntMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTFPointMatcher.h"
#include "ROSTFStampedPoint.h"
#include "ROSTFQuaternionMatcher.h"
#include "ROSTFTimeMatcher.h"
#include "ROSTFDurationMatcher.h"
#include "ROSRateMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFStampedTransform.h"
#include "ROSGeometryMsgsVector3StampedMatcher.h"
#include "ROSGeometryMsgsPointStampedMatcher.h"
#include "ROSVoid1Matcher.h"
#include "ROSVoid2Matcher.h"

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

    StatementMatcher
        forStmt_ = forStmt().bind("ForStmt");

    StatementMatcher
        tryStmt_ = cxxTryStmt().bind("TryStmt");

    localFinder_.addMatcher(decl_, this);
    localFinder_.addMatcher(assign_, this);
    localFinder_.addMatcher(expr_, this);
    localFinder_.addMatcher(ifStmt_,this);
    localFinder_.addMatcher(cmpdStmt_, this);
    localFinder_.addMatcher(returnStmt_, this);
    localFinder_.addMatcher(whileStmt_, this);
    localFinder_.addMatcher(forStmt_, this);
    localFinder_.addMatcher(tryStmt_, this);
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

    const auto whileStmt_ = Result.Nodes.getNodeAs<clang::WhileStmt>("WhileStmt");

    const auto forStmt_ = Result.Nodes.getNodeAs<clang::ForStmt>("ForStmt");

    const auto tryStmt_ = Result.Nodes.getNodeAs<clang::CXXTryStmt>("TryStmt");

    
    if(whileStmt_){
        auto wcond = whileStmt_->getCond();
        auto wbody = whileStmt_->getBody();
        
        ROSBooleanMatcher condm{ this->context_, this->interp_};
        condm.setup();
        condm.visit(*wcond);

        if(!condm.getChildExprStore()){
            std::cout<<"Unable to parse While condition!!\n";
            wcond->dump();
            throw "Broken Parse";
        }

        ROSStatementMatcher bodym{ this->context_, this->interp_};
        bodym.setup();
        bodym.visit(*wbody);

        if(!bodym.getChildExprStore()){
            std::cout<<"Unable to parse While block!!\n";
            wbody->dump();
            throw "Broken Parse";
        }

        this->interp_->mkWHILE_BOOL_EXPR_STMT(whileStmt_, condm.getChildExprStore(), bodym.getChildExprStore());
        this->childExprStore_ = (clang::Stmt*)whileStmt_;
        return;

    }

    if(forStmt_){
        auto wcond = forStmt_->getCond();
        auto wbody = forStmt_->getBody();
        
        ROSBooleanMatcher condm{ this->context_, this->interp_};
        condm.setup();
        condm.visit(*wcond);

        if(!condm.getChildExprStore()){
            std::cout<<"Unable to parse For condition!!\n";
            wcond->dump();
            throw "Broken Parse";
        }

        ROSStatementMatcher bodym{ this->context_, this->interp_};
        bodym.setup();
        bodym.visit(*wbody);

        if(!bodym.getChildExprStore()){
            std::cout<<"Unable to parse For block!!\n";
            wbody->dump();
            throw "Broken Parse";
        }

        this->interp_->mkFOR_BOOL_EXPR_STMT(forStmt_, condm.getChildExprStore(), bodym.getChildExprStore());
        this->childExprStore_ = (clang::Stmt*)forStmt_;
        return;
    }

    /*
    if(returnStmt_){
        auto _expr = returnStmt_->getRetValue();
        auto typestr = ((clang::QualType)_expr->getType()).getAsString();
        if(false){}
        
        else if (typestr == "geometry_msgs::Vector3Stamped" or typestr == "const geometry_msgs::Vector3Stamped"  or typestr == "class geometry_msgs::Vector3Stamped" /*typestr.find("geometry_msgs::Vector3Stamped") != string::npos) != string::npos){
            ROSGeometryMsgsVector3StampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "geometry_msgs::PointStamped" or typestr == "const geometry_msgs::PointStamped"  or typestr == "class geometry_msgs::PointStamped" /*typestr.find("geometry_msgs::PointStamped") != string::npos) != string::npos){
            ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>"  or typestr == "class tf::Stamped<tf::Point>" /*typestr.find("tf::Stamped<tf::Point>") != string::npos) != string::npos){
            ROSTFStampedPoint m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::StampedTransform" or typestr == "const tf::StampedTransform"  or typestr == "class tf::StampedTransform" /*typestr.find("tf::StampedTransform") != string::npos) != string::npos){
            ROSTFStampedTransform m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Quaternion" or typestr == "const tf::Quaternion"  or typestr == "class tf::Quaternion" /*typestr.find("tf::Quaternion") != string::npos) != string::npos){
            ROSTFQuaternionMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "ros::Duration" or typestr == "const ros::Duration"  or typestr == "class ros::Duration" /*typestr.find("ros::Duration") != string::npos) != string::npos){
            ROSTFDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Transform" or typestr == "const tf::Transform"  or typestr == "class tf::Transform" /*typestr.find("tf::Transform") != string::npos) != string::npos){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Vector3" or typestr == "const tf::Vector3"  or typestr == "class tf::Vector3" /*typestr.find("tf::Vector3") != string::npos) != string::npos){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Point" or typestr == "const tf::Point"  or typestr == "class tf::Point" /*typestr.find("tf::Point") != string::npos) != string::npos){
            ROSTFPointMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "ros::Time" or typestr == "const ros::Time"  or typestr == "class ros::Time" /*typestr.find("ros::Time") != string::npos) != string::npos){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "ros::Rate" or typestr == "const ros::Rate"  or typestr == "class ros::Rate" /*typestr.find("ros::Rate") != string::npos) != string::npos){
            ROSRateMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tfScalar" or typestr == "const tfScalar"  or typestr == "class tfScalar" /*typestr.find("tfScalar") != string::npos) != string::npos){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "double" or typestr == "const double"  or typestr == "class double" /*typestr.find("double") != string::npos) != string::npos){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "float" or typestr == "const float"  or typestr == "class float" /*typestr.find("float") != string::npos) != string::npos){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "bool" or typestr == "const bool"  or typestr == "class bool" /*typestr.find("bool") != string::npos) != string::npos){
            ROSBooleanMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "void" or typestr == "const void"  or typestr == "class void" /*typestr.find("void") != string::npos) != string::npos){
            ROSVoid1Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "void" or typestr == "const void"  or typestr == "class void" /*typestr.find("void") != string::npos) != string::npos){
            ROSVoid2Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "int" or typestr == "const int"  or typestr == "class int" /*typestr.find("int") != string::npos) != string::npos){
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
            else{
                auto current = st;
                std::vector<std::vector<clang::Stmt*>> stack;
                std::vector<int> recptr;

                /*search up to depth 3 for now. this is not sound, but a sound approach may lead to other issues
                */
                for(auto c1 : st->children()){
                    ROSStatementMatcher i1{this->context_,this->interp_};
                    i1.setup();
                    i1.visit(*c1);
                    if(i1.getChildExprStore()){
                        stmts.push_back(i1.getChildExprStore());
                    }
                    else{
                        for(auto c2 : c1->children()){
                            ROSStatementMatcher i2{this->context_,this->interp_};
                            i2.setup();
                            i2.visit(*c2);
                            if(i2.getChildExprStore()){
                                stmts.push_back(i2.getChildExprStore());
                            }
                            else{
                                for(auto c3 : c2->children()){
                                    ROSStatementMatcher i3{this->context_,this->interp_};
                                    i3.setup();
                                    i3.visit(*c3);
                                    if(i3.getChildExprStore()){
                                        stmts.push_back(i3.getChildExprStore());
                                    }
                                    else{
                                        for(auto c4 : c3->children()){
                                            ROSStatementMatcher i4{this->context_,this->interp_};
                                            i4.setup();
                                            i4.visit(*c4);
                                            if(i4.getChildExprStore()){
                                                stmts.push_back(i4.getChildExprStore());
                                            }
                                            else{
                                                
                                            }
                                        } 
                                    }
                                }
                            }
                        }
                    }
                }

                /*
                restart:
                std::vector<clang::Stmt*> current_stack;
                for(auto c : current->children()) current_stack.push_back(c);
                stack.push_back(current_stack);
                recptr.push_back(0);
                while(!stack.empty()){
                    for(int i = 0; i<stack.back().size();i++){
                        if(recptr.back() > i) continue;
                        auto c = 
                        ROSStatementMatcher inner{this->context_,this->interp_};
                        inner.setup();
                        inner.visit(*c);
                        if(inner.getChildExprStore()){
                            stmts.push_back(inner.getChildExprStore());
                            recptr.back()++;
                        }
                        else if(c->child_begin() != c->child_end()){
                            current = c;
                            goto restart;
                        }
                    }
                }
                */
                    
                    
                
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

                else if (typestr == "geometry_msgs::Vector3Stamped" or typestr == "const geometry_msgs::Vector3Stamped" or typestr == "class geometry_msgs::Vector3Stamped"/*typestr.find("geometry_msgs::Vector3Stamped") != string::npos*/){
                    interp_->mkREAL3_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSGeometryMsgsVector3StampedMatcher m{ this->context_, this->interp_};
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
            
                else if (typestr == "geometry_msgs::PointStamped" or typestr == "const geometry_msgs::PointStamped" or typestr == "class geometry_msgs::PointStamped"/*typestr.find("geometry_msgs::PointStamped") != string::npos*/){
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
            
                else if (typestr == "tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>" or typestr == "class tf::Stamped<tf::Point>"/*typestr.find("tf::Stamped<tf::Point>") != string::npos*/){
                    interp_->mkREAL3_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFStampedPoint m{ this->context_, this->interp_};
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
            
                else if (typestr == "tf::StampedTransform" or typestr == "const tf::StampedTransform" or typestr == "class tf::StampedTransform"/*typestr.find("tf::StampedTransform") != string::npos*/){
                    interp_->mkREALMATRIX4_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFStampedTransform m{ this->context_, this->interp_};
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
            
                else if (typestr == "tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion"/*typestr.find("tf::Quaternion") != string::npos*/){
                    interp_->mkREAL4_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSTFQuaternionMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_REAL4_VAR_REAL4_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_REAL4_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_REAL4_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration"/*typestr.find("ros::Duration") != string::npos*/){
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
            
                else if (typestr == "tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform"/*typestr.find("tf::Transform") != string::npos*/){
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
            
                else if (typestr == "tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3"/*typestr.find("tf::Vector3") != string::npos*/){
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
            
                else if (typestr == "tf::Point" or typestr == "const tf::Point" or typestr == "class tf::Point"/*typestr.find("tf::Point") != string::npos*/){
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
            
                else if (typestr == "ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time"/*typestr.find("ros::Time") != string::npos*/){
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
            
                else if (typestr == "ros::Rate" or typestr == "const ros::Rate" or typestr == "class ros::Rate"/*typestr.find("ros::Rate") != string::npos*/){
                    interp_->mkREAL1_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSRateMatcher m{ this->context_, this->interp_};
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
            
                else if (typestr == "tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar"/*typestr.find("tfScalar") != string::npos*/){
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
            
                else if (typestr == "double" or typestr == "const double" or typestr == "class double"/*typestr.find("double") != string::npos*/){
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
            
                else if (typestr == "float" or typestr == "const float" or typestr == "class float"/*typestr.find("float") != string::npos*/){
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
            
                else if (typestr == "bool" or typestr == "const bool" or typestr == "class bool"/*typestr.find("bool") != string::npos*/){
                    interp_->mkBOOL_VAR_IDENT(vd);
                    if (vd->hasInit())
                    {
                        ROSBooleanMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            interp_->mkDECL_BOOL_VAR_BOOL_EXPR(declStmt, vd, m.getChildExprStore());
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->mkDECL_BOOL_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        interp_->mkDECL_BOOL_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "int" or typestr == "const int" or typestr == "class int"/*typestr.find("int") != string::npos*/){
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
                
                    else if(typestr == "geometry_msgs::Vector3Stamped" or typestr == "const geometry_msgs::Vector3Stamped" or typestr == "class geometry_msgs::Vector3Stamped"/*typestr.find("geometry_msgs::Vector3Stamped") != string::npos*/){
                        interp_->mkREAL3_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSGeometryMsgsVector3StampedMatcher m{ this->context_, this->interp_};
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
                    else if(typestr == "geometry_msgs::PointStamped" or typestr == "const geometry_msgs::PointStamped" or typestr == "class geometry_msgs::PointStamped"/*typestr.find("geometry_msgs::PointStamped") != string::npos*/){
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
                    else if(typestr == "tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>" or typestr == "class tf::Stamped<tf::Point>"/*typestr.find("tf::Stamped<tf::Point>") != string::npos*/){
                        interp_->mkREAL3_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFStampedPoint m{ this->context_, this->interp_};
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
                    else if(typestr == "tf::StampedTransform" or typestr == "const tf::StampedTransform" or typestr == "class tf::StampedTransform"/*typestr.find("tf::StampedTransform") != string::npos*/){
                        interp_->mkREALMATRIX4_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFStampedTransform m{ this->context_, this->interp_};
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
                    else if(typestr == "tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion"/*typestr.find("tf::Quaternion") != string::npos*/){
                        interp_->mkREAL4_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSTFQuaternionMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_REAL4_VAR_REAL4_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_REAL4_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_REAL4_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr == "ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration"/*typestr.find("ros::Duration") != string::npos*/){
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
                    else if(typestr == "tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform"/*typestr.find("tf::Transform") != string::npos*/){
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
                    else if(typestr == "tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3"/*typestr.find("tf::Vector3") != string::npos*/){
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
                    else if(typestr == "tf::Point" or typestr == "const tf::Point" or typestr == "class tf::Point"/*typestr.find("tf::Point") != string::npos*/){
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
                    else if(typestr == "ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time"/*typestr.find("ros::Time") != string::npos*/){
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
                    else if(typestr == "ros::Rate" or typestr == "const ros::Rate" or typestr == "class ros::Rate"/*typestr.find("ros::Rate") != string::npos*/){
                        interp_->mkREAL1_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSRateMatcher m{ this->context_, this->interp_};
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
                    else if(typestr == "tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar"/*typestr.find("tfScalar") != string::npos*/){
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
                    else if(typestr == "double" or typestr == "const double" or typestr == "class double"/*typestr.find("double") != string::npos*/){
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
                    else if(typestr == "float" or typestr == "const float" or typestr == "class float"/*typestr.find("float") != string::npos*/){
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
                    else if(typestr == "bool" or typestr == "const bool" or typestr == "class bool"/*typestr.find("bool") != string::npos*/){
                        interp_->mkBOOL_VAR_IDENT(vd);
                        if (vd->hasInit())
                        {
                            ROSBooleanMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                interp_->mkDECL_BOOL_VAR_BOOL_EXPR(declStmt, vd, m.getChildExprStore());
                            }
                            else
                            {
                                interp_->mkDECL_BOOL_VAR(declStmt, vd);
                            }
                        }
                        else
                        {
                            interp_->mkDECL_BOOL_VAR(declStmt, vd);
                        }
                        anyfound = true;
                    }
                    else if(typestr == "int" or typestr == "const int" or typestr == "class int"/*typestr.find("int") != string::npos*/){
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
        
        if(typestr == "geometry_msgs::Vector3Stamped" or typestr == "const geometry_msgs::Vector3Stamped" or typestr == "class geometry_msgs::Vector3Stamped"/*typestr.find("geometry_msgs::Vector3Stamped") != string::npos*/){
            ROSGeometryMsgsVector3StampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "geometry_msgs::PointStamped" or typestr == "const geometry_msgs::PointStamped" or typestr == "class geometry_msgs::PointStamped"/*typestr.find("geometry_msgs::PointStamped") != string::npos*/){
            ROSGeometryMsgsPointStampedMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>" or typestr == "class tf::Stamped<tf::Point>"/*typestr.find("tf::Stamped<tf::Point>") != string::npos*/){
            ROSTFStampedPoint m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::StampedTransform" or typestr == "const tf::StampedTransform" or typestr == "class tf::StampedTransform"/*typestr.find("tf::StampedTransform") != string::npos*/){
            ROSTFStampedTransform m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion"/*typestr.find("tf::Quaternion") != string::npos*/){
            ROSTFQuaternionMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration"/*typestr.find("ros::Duration") != string::npos*/){
            ROSTFDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform"/*typestr.find("tf::Transform") != string::npos*/){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3"/*typestr.find("tf::Vector3") != string::npos*/){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tf::Point" or typestr == "const tf::Point" or typestr == "class tf::Point"/*typestr.find("tf::Point") != string::npos*/){
            ROSTFPointMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time"/*typestr.find("ros::Time") != string::npos*/){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "ros::Rate" or typestr == "const ros::Rate" or typestr == "class ros::Rate"/*typestr.find("ros::Rate") != string::npos*/){
            ROSRateMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar"/*typestr.find("tfScalar") != string::npos*/){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "double" or typestr == "const double" or typestr == "class double"/*typestr.find("double") != string::npos*/){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "float" or typestr == "const float" or typestr == "class float"/*typestr.find("float") != string::npos*/){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "bool" or typestr == "const bool" or typestr == "class bool"/*typestr.find("bool") != string::npos*/){
            ROSBooleanMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "void" or typestr == "const void" or typestr == "class void"/*typestr.find("void") != string::npos*/){
            ROSVoid1Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "void" or typestr == "const void" or typestr == "class void"/*typestr.find("void") != string::npos*/){
            ROSVoid2Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "int" or typestr == "const int" or typestr == "class int"/*typestr.find("int") != string::npos*/){
            IntMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
    }
    else if(tryStmt_){
        auto tryBlock = tryStmt_->getTryBlock();
        ROSStatementMatcher innerMatcher{ this->context_, this->interp_};
        innerMatcher.setup();
        innerMatcher.visit(*tryBlock);
        if (innerMatcher.getChildExprStore()){
            this->childExprStore_ = (clang::Stmt*)tryStmt_;//const_cast<clang::Stmt*>(innerMatcher.getChildExprStore());
            interp_->mkTRY_STMT(tryStmt_,innerMatcher.getChildExprStore());
            return;
        }
    }
    else if (exprWithCleanupsDiscard)
    {//matches fluff node to discard
        ROSStatementMatcher innerMatcher{ this->context_, this->interp_};
        innerMatcher.setup();
        innerMatcher.visit(*exprWithCleanupsDiscard->getSubExpr());
        if (innerMatcher.getChildExprStore()){
            this->childExprStore_ = const_cast<clang::Stmt*>(innerMatcher.getChildExprStore());
            return;
        }
    }
    else
    {
        //log error
    }

};

