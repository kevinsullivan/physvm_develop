
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "../Interpretation.h"

#include "ROSStatementMatcher.h"
#include "FloatMatcher.h"
#include "DoubleMatcher.h"
#include "ROSTFTimeMatcher.h"
#include "ROSTFDurationMatcher.h"

#include <string>


#include <iostream>

#include <memory>

//#include "../maps/ASTToCoords.h"
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

    /*
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
    */
    /*
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
    */
    /*
    if(returnStmt_){
        auto _expr = returnStmt_->getRetValue();
        auto typestr = ((clang::QualType)_expr->getType()).getAsString();
        if(false){}
        
        else if (typestr == "ros::Duration" or typestr == "const ros::Duration"  or typestr == "class ros::Duration" /*typestr.find("ros::Duration") != string::npos) != string::npos){
            ROSTFDurationMatcher m{ this->context_, this->interp_};
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
        //this->interp_->mkCOMPOUND_STMT(cmpdStmt_, stmts);
        this->interp_->buffer_operands(stmts);
        this->interp_->mkNode("COMPOUND_STMT",cmpdStmt_,false);
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

                else if (typestr == "ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration"/*typestr.find("ros::Duration") != string::npos*/){
                    //interp_->mkREAL1_VAR_IDENT(vd);
                    interp_->mkNode("IDENT_R1",vd,true);
                    if (vd->hasInit())
                    {
                        ROSTFDurationMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            //(*vd->getInit()).dump();
                            //m.getChildExprStore()->dump();
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                        //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time"/*typestr.find("ros::Time") != string::npos*/){
                    //interp_->mkREAL1_VAR_IDENT(vd);
                    interp_->mkNode("IDENT_R1",vd,true);
                    if (vd->hasInit())
                    {
                        ROSTFTimeMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                            //(*vd->getInit()).dump();
                            //m.getChildExprStore()->dump();
                        if (m.getChildExprStore())
                        {
                            //interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "double" or typestr == "const double" or typestr == "class double"/*typestr.find("double") != string::npos*/){
                    //interp_->mkREAL1_VAR_IDENT(vd);
                    interp_->mkNode("IDENT_R1",vd,true);
                    if (vd->hasInit())
                    {
                        DoubleMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
                else if (typestr == "float" or typestr == "const float" or typestr == "class float"/*typestr.find("float") != string::npos*/){
                    //interp_->mkREAL1_VAR_IDENT(vd);
                    interp_->mkNode("IDENT_R1",vd,true);
                    if (vd->hasInit())
                    {
                        FloatMatcher m{ this->context_, this->interp_};
                        m.setup();
                        m.visit((*vd->getInit()));
                        if (m.getChildExprStore())
                        {
                            //interp_->mkDECL_REAL1_VAR_REAL1_EXPR(declStmt, vd, m.getChildExprStore());
                            interp_->buffer_operand(vd);
                            interp_->buffer_operand(m.getChildExprStore());
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                        else
                        {
                            //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                            interp_->buffer_operand(vd);
                            interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                            this->childExprStore_ =  (clang::Stmt*)declStmt;
                            return;
                        }
                    }
                    else
                    {
                        //interp_->mkDECL_REAL1_VAR(declStmt, vd);
                        interp_->buffer_operand(vd);
                        interp_->mkNode("DECL_VAR_R1_EXPR_R1",declStmt,false);
                        this->childExprStore_ = (clang::Stmt*)declStmt;
                        return;
                    }
                }
            
            }
        }
    }
    else if (assignStmt)
    {
        //not implemented!!
    }
    /*
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
    */
    if (exprWithCleanupsDiscard)
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

