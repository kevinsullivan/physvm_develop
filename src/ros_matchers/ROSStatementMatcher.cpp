
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "../Interpretation.h"

#include "ROSStatementMatcher.h"
#include "ROSBooleanMatcher.h"
#include "FloatMatcher.h"
#include "DoubleMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFTimeMatcher.h"
#include "ROSDurationMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTF2DurationMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "VoidMatcher.h"
#include "ROSGeometryPoseWithCovarianceStamped.h"
#include "ROSGeomQuaternion.h"
#include "ROSTFQuaternion.h"
#include "ROSTF2Quaternion.h"
#include "ROSTF2Vector3Matcher.h"
#include "ROSTF2TransformStamped.h"
#include "ROSTF2Transform.h"

#include <string>


#include <iostream>

#include <memory>

#include "../maps/ASTToCoords.h"
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

    StatementMatcher
        cxxMemberCallExpr_ = cxxMemberCallExpr().bind("CXXMemberCallExpr");

    //StatementMatcher
    //    functionDecl_ = functionDecl().bind("FunctionDecl");

    localFinder_.addMatcher(exprWithCleanups_,this);
    localFinder_.addMatcher(cxxMemberCallExpr_,this);
    localFinder_.addMatcher(decl_, this);
    localFinder_.addMatcher(assign_, this);
    localFinder_.addMatcher(expr_, this);
    localFinder_.addMatcher(ifStmt_,this);
    localFinder_.addMatcher(cmpdStmt_, this);
    localFinder_.addMatcher(returnStmt_, this);
    localFinder_.addMatcher(whileStmt_, this);
    localFinder_.addMatcher(forStmt_, this);
    localFinder_.addMatcher(tryStmt_, this);
    //localFinder_.addMatcher(functionDecl_, this);
    this->childExprStore_ = nullptr;
};

void ROSStatementMatcher::run(const MatchFinder::MatchResult &Result){
    if(this->childExprStore_ != nullptr){
        return;
    }

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

    const auto cxxMemberCallExpr_ = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
    
    //const auto functionDecl_ = Result.Nodes.getNodeAs<clang::FunctionDecl>("FunctionDecl");

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

        //this->interp_->mkWHILE_BOOL_EXPR_STMT(whileStmt_, condm.getChildExprStore(), bodym.getChildExprStore());
        interp_->buffer_operand(condm.getChildExprStore());
        interp_->buffer_operand(bodym.getChildExprStore());
        interp_->mkNode("WHILE_STMT", whileStmt_, false);
        
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

        //this->interp_->mkFOR_BOOL_EXPR_STMT(forStmt_, condm.getChildExprStore(), bodym.getChildExprStore());
        interp_->buffer_operand(condm.getChildExprStore());
        interp_->buffer_operand(bodym.getChildExprStore());
        interp_->mkNode("FOR_STMT",forStmt_,false); 
        this->childExprStore_ = (clang::Stmt*)forStmt_;
        return;
    }

    //if(functionDecl_){
        

    /*
    if(returnStmt_){
        auto _expr = returnStmt_->getRetValue();
        auto typestr = ((clang::QualType)_expr->getType()).getAsString();
        if(false){}
        
        else if (typestr == "geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped"  or typestr == "class geometry_msgs::PoseWithCovarianceStamped"  or typestr == "const class geometry_msgs::PoseWithCovarianceStamped"/*typestr.find("geometry_msgs::PoseWithCovarianceStamped") != string::npos) != string::npos){
            ROSGeometryPoseWithCovarianceStamped m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>"  or typestr == "class tf2::Stamped<tf2::Transform>"  or typestr == "const class tf2::Stamped<tf2::Transform>"/*typestr.find("tf2::Stamped<tf2::Transform>") != string::npos) != string::npos){
            ROSTF2TransformStamped m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion"  or typestr == "class geometry_msgs::Quaternion"  or typestr == "const class geometry_msgs::Quaternion"/*typestr.find("geometry_msgs::Quaternion") != string::npos) != string::npos){
            ROSGeomQuaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf2::Quaternion" or typestr == "const tf2::Quaternion"  or typestr == "class tf2::Quaternion"  or typestr == "const class tf2::Quaternion"/*typestr.find("tf2::Quaternion") != string::npos) != string::npos){
            ROSTF2Quaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Quaternion" or typestr == "const tf::Quaternion"  or typestr == "class tf::Quaternion"  or typestr == "const class tf::Quaternion"/*typestr.find("tf::Quaternion") != string::npos) != string::npos){
            ROSTFQuaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf2::Transform" or typestr == "const tf2::Transform"  or typestr == "class tf2::Transform"  or typestr == "const class tf2::Transform"/*typestr.find("tf2::Transform") != string::npos) != string::npos){
            ROSTF2Transform m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "ros::Duration" or typestr == "const ros::Duration"  or typestr == "class ros::Duration"  or typestr == "const class ros::Duration"/*typestr.find("ros::Duration") != string::npos) != string::npos){
            ROSDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf2::Duration" or typestr == "const tf2::Duration"  or typestr == "class tf2::Duration"  or typestr == "const class tf2::Duration"/*typestr.find("tf2::Duration") != string::npos) != string::npos){
            ROSTF2DurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Transform" or typestr == "const tf::Transform"  or typestr == "class tf::Transform"  or typestr == "const class tf::Transform"/*typestr.find("tf::Transform") != string::npos) != string::npos){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf2::Vector3" or typestr == "const tf2::Vector3"  or typestr == "class tf2::Vector3"  or typestr == "const class tf2::Vector3"/*typestr.find("tf2::Vector3") != string::npos) != string::npos){
            ROSTF2Vector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tf::Vector3" or typestr == "const tf::Vector3"  or typestr == "class tf::Vector3"  or typestr == "const class tf::Vector3"/*typestr.find("tf::Vector3") != string::npos) != string::npos){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "ros::Time" or typestr == "const ros::Time"  or typestr == "class ros::Time"  or typestr == "const class ros::Time"/*typestr.find("ros::Time") != string::npos) != string::npos){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "tfScalar" or typestr == "const tfScalar"  or typestr == "class tfScalar"  or typestr == "const class tfScalar"/*typestr.find("tfScalar") != string::npos) != string::npos){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "double" or typestr == "const double"  or typestr == "class double"  or typestr == "const class double"/*typestr.find("double") != string::npos) != string::npos){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "float" or typestr == "const float"  or typestr == "class float"  or typestr == "const class float"/*typestr.find("float") != string::npos) != string::npos){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "bool" or typestr == "const bool"  or typestr == "class bool"  or typestr == "const class bool"/*typestr.find("bool") != string::npos) != string::npos){
            ROSBooleanMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*_expr);
            if(m.getChildExprStore()){
                this->childExprStore_ = (clang::Stmt*)_expr;
            }
            return;
        }
            
        else if (typestr == "void" or typestr == "const void"  or typestr == "class void"  or typestr == "const class void"/*typestr.find("void") != string::npos) != string::npos){
            VoidMatcher m{ this->context_, this->interp_};
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
                //auto current = st;
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
        //this->interp_->mkCOMPOUND_STMT(cmpdStmt_, stmts);
        if(stmts.size()>0){
            interp_->buffer_body(stmts);
            interp_->mkNode("COMPOUND_STMT", cmpdStmt_);
            this->childExprStore_ = (clang::Stmt*)cmpdStmt_;
        }
        return;
        
    }

    
    auto vec_str = std::string("std::vector<");
    if (declStmt)
    {
        if (declStmt->isSingleDecl())
        {
            if (auto vd = clang::dyn_cast<clang::VarDecl>(declStmt->getSingleDecl()))
             {
                auto typestr = ((clang::QualType)vd->getType()).getAsString();
                if(false){}
                else if(typestr.substr(0,vec_str.length())==vec_str){
                    //std::cout<<typestr.substr(vec_str.length(), typestr.length()-vec_str.length()-1)<<"\n";
                    std::string param_type = typestr.substr(vec_str.length(), typestr.length()-vec_str.length()-1);
                    if(false){}                

                        else if(param_type == "operatorgeometry_msgs::PoseWithCovarianceStamped" or param_type =="geometry_msgs::PoseWithCovarianceStamped" or param_type == "const geometry_msgs::PoseWithCovarianceStamped" or param_type == "class geometry_msgs::PoseWithCovarianceStamped" or param_type == "const class geometry_msgs::PoseWithCovarianceStamped" or param_type ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4X4",vd, true);
                            if (vd->hasInit()){
                                //ROSGeometryPoseWithCovarianceStamped argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf2::Stamped<tf2::Transform>" or param_type =="tf2::Stamped<tf2::Transform>" or param_type == "const tf2::Stamped<tf2::Transform>" or param_type == "class tf2::Stamped<tf2::Transform>" or param_type == "const class tf2::Stamped<tf2::Transform>" or param_type ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4X4",vd, true);
                            if (vd->hasInit()){
                                //ROSTF2TransformStamped argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorgeometry_msgs::Quaternion" or param_type =="geometry_msgs::Quaternion" or param_type == "const geometry_msgs::Quaternion" or param_type == "class geometry_msgs::Quaternion" or param_type == "const class geometry_msgs::Quaternion" or param_type ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4",vd, true);
                            if (vd->hasInit()){
                                //ROSGeomQuaternion argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf2::Quaternion" or param_type =="tf2::Quaternion" or param_type == "const tf2::Quaternion" or param_type == "class tf2::Quaternion" or param_type == "const class tf2::Quaternion" or param_type ==  "::tf2::Quaternion_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4",vd, true);
                            if (vd->hasInit()){
                                //ROSTF2Quaternion argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf::Quaternion" or param_type =="tf::Quaternion" or param_type == "const tf::Quaternion" or param_type == "class tf::Quaternion" or param_type == "const class tf::Quaternion" or param_type ==  "::tf::Quaternion_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4",vd, true);
                            if (vd->hasInit()){
                                //ROSTFQuaternion argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf2::Transform" or param_type =="tf2::Transform" or param_type == "const tf2::Transform" or param_type == "class tf2::Transform" or param_type == "const class tf2::Transform" or param_type ==  "::tf2::Transform_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_R4X4",vd, true);
                            if (vd->hasInit()){
                                //ROSTF2Transform argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_R4X4",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorros::Duration" or param_type =="ros::Duration" or param_type == "const ros::Duration" or param_type == "class ros::Duration" or param_type == "const class ros::Duration" or param_type ==  "::ros::Duration_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSDurationMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf2::Duration" or param_type =="tf2::Duration" or param_type == "const tf2::Duration" or param_type == "class tf2::Duration" or param_type == "const class tf2::Duration" or param_type ==  "::tf2::Duration_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTF2DurationMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf::Transform" or param_type =="tf::Transform" or param_type == "const tf::Transform" or param_type == "class tf::Transform" or param_type == "const class tf::Transform" or param_type ==  "::tf::Transform_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL4X4_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTFTransformMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL4X4_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL4X4_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf2::Vector3" or param_type =="tf2::Vector3" or param_type == "const tf2::Vector3" or param_type == "class tf2::Vector3" or param_type == "const class tf2::Vector3" or param_type ==  "::tf2::Vector3_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL3_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTF2Vector3Matcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL3_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL3_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortf::Vector3" or param_type =="tf::Vector3" or param_type == "const tf::Vector3" or param_type == "class tf::Vector3" or param_type == "const class tf::Vector3" or param_type ==  "::tf::Vector3_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL3_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTFVector3Matcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL3_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL3_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorros::Time" or param_type =="ros::Time" or param_type == "const ros::Time" or param_type == "class ros::Time" or param_type == "const class ros::Time" or param_type ==  "::ros::Time_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTFTimeMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatortfScalar" or param_type =="tfScalar" or param_type == "const tfScalar" or param_type == "class tfScalar" or param_type == "const class tfScalar" or param_type ==  "::tfScalar_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSTFScalarMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatordouble" or param_type =="double" or param_type == "const double" or param_type == "class double" or param_type == "const class double" or param_type ==  "::double_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //DoubleMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorfloat" or param_type =="float" or param_type == "const float" or param_type == "class float" or param_type == "const class float" or param_type ==  "::float_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_REAL1_EXPR",vd, true);
                            if (vd->hasInit()){
                                //FloatMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_REAL1_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorbool" or param_type =="bool" or param_type == "const bool" or param_type == "class bool" or param_type == "const class bool" or param_type ==  "::bool_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_BOOL_EXPR",vd, true);
                            if (vd->hasInit()){
                                //ROSBooleanMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_BOOL_EXPR",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_BOOL_EXPR",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                        else if(param_type == "operatorvoid" or param_type =="void" or param_type == "const void" or param_type == "class void" or param_type == "const class void" or param_type ==  "::void_<allocator<void> >"){
                            
                            interp_->mkNode("IDENT_LIST_Void",vd, true);
                            if (vd->hasInit()){
                                //VoidMatcher argm{this->context_,this->interp_};
                                //argm.setup();
                               // argm.visit(*vd->getInit());
                               // auto argstmt = argm.getChildExprStore();
                               //interp_->buffer_operand(argstmt);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_Void",declStmt, false);
                                this->childExprStore_= (clang::Stmt*) declStmt;
                                return;
                            }
                            else{
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_LIST_Void",declStmt, false);
                                this->childExprStore_ = (clang::Stmt*) declStmt;
                                return;
                            }
                        }
                    
                }

                else if (typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4X4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSGeometryPoseWithCovarianceStamped m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4X4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4X4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTF2TransformStamped m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4X4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSGeomQuaternion m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTF2Quaternion m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTFQuaternion m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_R4X4",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTF2Transform m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_R4X4", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSDurationMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTF2DurationMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL4X4_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTFTransformMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL4X4_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL4X4_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL4X4_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL3_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTF2Vector3Matcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL3_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTFVector3Matcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTFTimeMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSTFScalarMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        DoubleMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        FloatMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_BOOL_EXPR",vd, true);
                    if (vd->hasInit())
                    {
                        ROSBooleanMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_BOOL_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_BOOL_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_BOOL_EXPR", declStmt);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                    //interp_->mk(vd);
                    interp_->mkNode("IDENT_Void",vd, true);
                    if (vd->hasInit())
                    {
                        VoidMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mk(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_INIT_Void", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_Void", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mk(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_Void", declStmt);
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
                
                    else if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4X4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSGeometryPoseWithCovarianceStamped m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4X4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTF2TransformStamped m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSGeomQuaternion m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTF2Quaternion m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTFQuaternion m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_R4X4",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTF2Transform m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_R4X4", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_R4X4", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSDurationMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTF2DurationMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL4X4_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTFTransformMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL4X4_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL4X4_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL4X4_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL3_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTF2Vector3Matcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL3_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL3_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTFVector3Matcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL3_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL3_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTFTimeMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSTFScalarMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            DoubleMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_REAL1_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            FloatMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_REAL1_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_BOOL_EXPR",vd, true);
                        if (vd->hasInit())
                        {
                            ROSBooleanMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_BOOL_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_BOOL_EXPR", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_BOOL_EXPR", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                        }
                        anyfound = true;
                    }
                    else if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                        //interp_->mk(vd);
                        
                        interp_->mkNode("IDENT_Void",vd, true);
                        if (vd->hasInit())
                        {
                            VoidMatcher m{ this->context_, this->interp_};
                            m.setup();
                            m.visit((*vd->getInit()));
                            if (m.getChildExprStore())
                            {
                                //interp_->mk(declStmt, vd, m.getChildExprStore());
                                interp_->buffer_operand(vd);
                                interp_->buffer_operand(m.getChildExprStore());
                                interp_->mkNode("DECL_INIT_Void", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                            else
                            {
                                //interp_->mk(declStmt, vd);
                                interp_->buffer_operand(vd);
                                interp_->mkNode("DECL_Void", declStmt);
                                this->childExprStore_ =  (clang::Stmt*)declStmt;
                            }
                        }
                        else
                        {
                            //interp_->mk(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_Void", declStmt);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
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
    else if (cxxMemberCallExpr_)
    {
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            auto obj= cxxMemberCallExpr_->getImplicitObjectArgument();
            auto objstr = ((clang::QualType)obj->getType()).getAsString();
            if(objstr.substr(0,vec_str.length())==vec_str and name.find("push_back") != string::npos){
                if(auto dc2 = clang::dyn_cast<clang::DeclRefExpr>(obj)){
                    auto objdecl = clang::dyn_cast<clang::VarDecl>(dc2->getDecl());
                    //interp_->buffer_link(objdecl);
                    //interp_->mkNode("APPEND_LIST_R1",cxxMemberCallExpr_,false);
                    std::string param_type = objstr.substr(vec_str.length(), objstr.length()-vec_str.length()-1);
                    if(false){}                

                    else if(param_type == "operatorgeometry_msgs::PoseWithCovarianceStamped" or param_type =="geometry_msgs::PoseWithCovarianceStamped" or param_type == "const geometry_msgs::PoseWithCovarianceStamped" or param_type == "class geometry_msgs::PoseWithCovarianceStamped" or param_type == "const class geometry_msgs::PoseWithCovarianceStamped" or param_type ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSGeometryPoseWithCovarianceStamped argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4X4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf2::Stamped<tf2::Transform>" or param_type =="tf2::Stamped<tf2::Transform>" or param_type == "const tf2::Stamped<tf2::Transform>" or param_type == "class tf2::Stamped<tf2::Transform>" or param_type == "const class tf2::Stamped<tf2::Transform>" or param_type ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTF2TransformStamped argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4X4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorgeometry_msgs::Quaternion" or param_type =="geometry_msgs::Quaternion" or param_type == "const geometry_msgs::Quaternion" or param_type == "class geometry_msgs::Quaternion" or param_type == "const class geometry_msgs::Quaternion" or param_type ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSGeomQuaternion argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf2::Quaternion" or param_type =="tf2::Quaternion" or param_type == "const tf2::Quaternion" or param_type == "class tf2::Quaternion" or param_type == "const class tf2::Quaternion" or param_type ==  "::tf2::Quaternion_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTF2Quaternion argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf::Quaternion" or param_type =="tf::Quaternion" or param_type == "const tf::Quaternion" or param_type == "class tf::Quaternion" or param_type == "const class tf::Quaternion" or param_type ==  "::tf::Quaternion_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTFQuaternion argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf2::Transform" or param_type =="tf2::Transform" or param_type == "const tf2::Transform" or param_type == "class tf2::Transform" or param_type == "const class tf2::Transform" or param_type ==  "::tf2::Transform_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTF2Transform argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_R4X4",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorros::Duration" or param_type =="ros::Duration" or param_type == "const ros::Duration" or param_type == "class ros::Duration" or param_type == "const class ros::Duration" or param_type ==  "::ros::Duration_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSDurationMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf2::Duration" or param_type =="tf2::Duration" or param_type == "const tf2::Duration" or param_type == "class tf2::Duration" or param_type == "const class tf2::Duration" or param_type ==  "::tf2::Duration_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTF2DurationMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf::Transform" or param_type =="tf::Transform" or param_type == "const tf::Transform" or param_type == "class tf::Transform" or param_type == "const class tf::Transform" or param_type ==  "::tf::Transform_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTFTransformMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL4X4_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf2::Vector3" or param_type =="tf2::Vector3" or param_type == "const tf2::Vector3" or param_type == "class tf2::Vector3" or param_type == "const class tf2::Vector3" or param_type ==  "::tf2::Vector3_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTF2Vector3Matcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL3_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortf::Vector3" or param_type =="tf::Vector3" or param_type == "const tf::Vector3" or param_type == "class tf::Vector3" or param_type == "const class tf::Vector3" or param_type ==  "::tf::Vector3_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTFVector3Matcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL3_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorros::Time" or param_type =="ros::Time" or param_type == "const ros::Time" or param_type == "class ros::Time" or param_type == "const class ros::Time" or param_type ==  "::ros::Time_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTFTimeMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatortfScalar" or param_type =="tfScalar" or param_type == "const tfScalar" or param_type == "class tfScalar" or param_type == "const class tfScalar" or param_type ==  "::tfScalar_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSTFScalarMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatordouble" or param_type =="double" or param_type == "const double" or param_type == "class double" or param_type == "const class double" or param_type ==  "::double_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        DoubleMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorfloat" or param_type =="float" or param_type == "const float" or param_type == "class float" or param_type == "const class float" or param_type ==  "::float_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        FloatMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_REAL1_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorbool" or param_type =="bool" or param_type == "const bool" or param_type == "class bool" or param_type == "const class bool" or param_type ==  "::bool_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        ROSBooleanMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_BOOL_EXPR",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                    else if(param_type == "operatorvoid" or param_type =="void" or param_type == "const void" or param_type == "class void" or param_type == "const class void" or param_type ==  "::void_<allocator<void> >"){
                        
                        auto arg_=cxxMemberCallExpr_->getArg(0);
                        VoidMatcher argm{this->context_,this->interp_};
                        argm.setup();
                        argm.visit(*arg_);
                        auto argstmt = argm.getChildExprStore();
                        interp_->buffer_link(objdecl);
                        interp_->buffer_operand(argstmt);
                        interp_->mkNode("APPEND_LIST_Void",cxxMemberCallExpr_, false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
                    
                }
                else {
                    std::cout<<"Warning : Not a DeclRefExpr";
                }
            }
        }
    }
    else if (exprStmt)
    {
        auto typestr = ((clang::QualType)exprStmt->getType()).getAsString();
        
        if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
            ROSGeometryPoseWithCovarianceStamped m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
            ROSTF2TransformStamped m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
            ROSGeomQuaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
            ROSTF2Quaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
            ROSTFQuaternion m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
            ROSTF2Transform m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
            ROSDurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
            ROSTF2DurationMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
            ROSTFTransformMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
            ROSTF2Vector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
            ROSTFVector3Matcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
            ROSTFTimeMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
            ROSTFScalarMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
            DoubleMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
            FloatMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
            ROSBooleanMatcher m{ this->context_, this->interp_};
            m.setup();
            m.visit(*exprStmt);
            if (m.getChildExprStore()){
                this->childExprStore_ = const_cast<clang::Stmt*>(m.getChildExprStore());
                return;
            }
                
        }
        if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
            VoidMatcher m{ this->context_, this->interp_};
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
            interp_->buffer_operand(innerMatcher.getChildExprStore());
            interp_->mkNode("TRY_STMT",tryStmt_);//,innerMatcher.getChildExprStore());
            return;
        }
    }
    else
    {
        //log error
    }

};

