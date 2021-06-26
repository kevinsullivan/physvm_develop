
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFScalarMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFScalarMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSTFScalarMatcher::setup(){
		StatementMatcher cxxConstructExpr_=cxxConstructExpr().bind("CXXConstructExpr");
		localFinder_.addMatcher(cxxConstructExpr_,this);
	
		StatementMatcher memberExpr_=memberExpr().bind("MemberExpr");
		localFinder_.addMatcher(memberExpr_,this);
	
		StatementMatcher implicitCastExpr_=implicitCastExpr().bind("ImplicitCastExpr");
		localFinder_.addMatcher(implicitCastExpr_,this);
	
		StatementMatcher cxxBindTemporaryExpr_=cxxBindTemporaryExpr().bind("CXXBindTemporaryExpr");
		localFinder_.addMatcher(cxxBindTemporaryExpr_,this);
	
		StatementMatcher materializeTemporaryExpr_=materializeTemporaryExpr().bind("MaterializeTemporaryExpr");
		localFinder_.addMatcher(materializeTemporaryExpr_,this);
	
		StatementMatcher parenExpr_=parenExpr().bind("ParenExpr");
		localFinder_.addMatcher(parenExpr_,this);
	
		StatementMatcher exprWithCleanups_=exprWithCleanups().bind("ExprWithCleanups");
		localFinder_.addMatcher(exprWithCleanups_,this);
	
		StatementMatcher cxxFunctionalCastExpr_=cxxFunctionalCastExpr().bind("CXXFunctionalCastExpr");
		localFinder_.addMatcher(cxxFunctionalCastExpr_,this);
	
		StatementMatcher declRefExpr_=declRefExpr().bind("DeclRefExpr");
		localFinder_.addMatcher(declRefExpr_,this);
	
		StatementMatcher binaryOperator_=binaryOperator().bind("BinaryOperator");
		localFinder_.addMatcher(binaryOperator_,this);
    this->childExprStore_ = nullptr;
};

void ROSTFScalarMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
	
	auto binaryOperator_ = Result.Nodes.getNodeAs<clang::BinaryOperator>("BinaryOperator");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFScalarMatcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){return;}
    
            else{
                this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
                interp_->mkNode("LIT_R1",(clang::Stmt*)cxxBindTemporaryExpr_,true);
                return;
            }
        }
    }

	
	arg_decay_exist_predicates["memberExpr_tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="tfScalar" or typestr == "const tfScalar" or typestr == "const tfScalar" or typestr == "const class tfScalar"){
            ROSTFScalarMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar"){
            ROSTFScalarMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            interp_->mkNode("LIT_R1",(clang::Stmt*)implicitCastExpr_,true);
            return;
        }
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_tfScalar"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSTFScalarMatcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){return;}
    
        else{
            this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
            interp_->mkNode("LIT_R1",(clang::Stmt*)cxxBindTemporaryExpr_,true);
            return;
        }
    }

	
	arg_decay_exist_predicates["materializeTemporaryExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)materializeTemporaryExpr_;
                interp_->mkNode("LIT_R1",(clang::Stmt*)materializeTemporaryExpr_,true);
                return;
            }
        }

	
	arg_decay_exist_predicates["parenExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSTFScalarMatcher inner{ context_, interp_};
        inner.setup();
        inner.visit(*parenExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)inner.getChildExprStore();
        if(this->childExprStore_){return;}
        else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                parenExpr_->dump();
           
            }
        return;
    }
	
    if (exprWithCleanups_)
        {
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)exprWithCleanups_;
                interp_->mkNode("LIT_R1",(clang::Stmt*)exprWithCleanups_,true);
                return;
            }
        }
    
	
    if (cxxFunctionalCastExpr_)
        {
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{

                this->childExprStore_ = (clang::Stmt*)cxxFunctionalCastExpr_;
                interp_->mkNode("LIT_R1",(clang::Stmt*)cxxFunctionalCastExpr_,true);
                return;
            }
        }
    
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->buffer_link(dc);
            interp_->mkNode("REF_R1",declRefExpr_);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
    if(cxxConstructExpr_ and cxxConstructExpr_->getNumArgs() == 1){
        if(true ){
            
            if(true ){
                //interp_->mk(cxxConstructExpr_);
                
                auto consDecl_ = cxxConstructExpr_->getConstructor();
                if(this->interp_->existsConstructor(consDecl_))
                {

                }
                else
                {
                    std::vector<const clang::ParmVarDecl*> valid_params_;
                    auto params_ = consDecl_->parameters();
                    if(params_.size() > 0){

                        
                        
                        
                        /*for(auto a:consDecl_->parameters())
                        {
                            if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(a)){
                                interp_->mkNode("CONSTRUCTOR_PARAM", a,false);
                                params_.push_back(const_cast<clang::ParmVarDecl*>(a));
                             }
                            else
                            {
                                std::cout << "Warning : Param is not a ParmVarDecl\n";
                                a->dump();
                            }
                        }*/
                        if(valid_params_.size()>0)
                            interp_->buffer_operands(valid_params_);
                    }
                    interp_->mkConstructor(consDecl_);
                }

                interp_->buffer_constructor(consDecl_);
                interp_->mkNode("LIT_R1",cxxConstructExpr_,true);
                this->childExprStore_ = (clang::Stmt*)cxxConstructExpr_;
                return;
            }
        }
    }
	
	arg_decay_exist_predicates["BinaryOperator(tfScalar?FORCE,tfScalar?FORCE)@+@tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
    else { return false; }
    };
	arg_decay_exist_predicates["BinaryOperator(tfScalar?FORCE,tfScalar?FORCE)@+@tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
    else { return false; }
    };
    if(binaryOperator_){
        auto bostr = binaryOperator_->getOpcodeStr().str();
        //auto lhs = binaryOperator_->getLHS();
        //auto rhs = binaryOperator_->getRHS();
        //clang::Stmt* lhsstmt;
        //clang::Stmt* rhsstmt;
            

        if(bostr=="+" or bostr == "const +" or bostr == "class +"){
            auto lhs = binaryOperator_->getLHS();
            auto lhsstr = ((clang::QualType)lhs->getType()).getAsString();
            auto rhs = binaryOperator_->getRHS();
            auto rhsstr = ((clang::QualType)rhs->getType()).getAsString();
            clang::Stmt* lhsresult = nullptr;
            clang::Stmt* rhsresult = nullptr;
            if(false){}
            
            else if(true){
                ROSTFScalarMatcher lhsm{this->context_,this->interp_};
                lhsm.setup();
                lhsm.visit(*lhs);
                lhsresult = lhsm.getChildExprStore();
            }

            if(false){}
            
            else if(true){
                ROSTFScalarMatcher rhsm{this->context_,this->interp_};
                rhsm.setup();
                rhsm.visit(*rhs);
                rhsresult = rhsm.getChildExprStore();
            }

            if(lhsresult and rhsresult){
                //interp_->mk(binaryOperator_,lhsresult, rhsresult);
                interp_->buffer_operand(lhsresult);
                interp_->buffer_operand(rhsresult);
                interp_->mkNode("ADD_R1_R1",binaryOperator_,true);
                this->childExprStore_ = (clang::Stmt*)binaryOperator_;
                return;
            }
        }
    }

	
	arg_decay_exist_predicates["BinaryOperator(tfScalar?FORCE,tfScalar?FORCE)@*@tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
    else { return false; }
    };
	arg_decay_exist_predicates["BinaryOperator(tfScalar?FORCE,tfScalar?FORCE)@*@tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ return true; }
    else { return false; }
    };
    if(binaryOperator_){
        auto bostr = binaryOperator_->getOpcodeStr().str();
        //auto lhs = binaryOperator_->getLHS();
        //auto rhs = binaryOperator_->getRHS();
        //clang::Stmt* lhsstmt;
        //clang::Stmt* rhsstmt;
            

        if(bostr=="*" or bostr == "const *" or bostr == "class *"){
            auto lhs = binaryOperator_->getLHS();
            auto lhsstr = ((clang::QualType)lhs->getType()).getAsString();
            auto rhs = binaryOperator_->getRHS();
            auto rhsstr = ((clang::QualType)rhs->getType()).getAsString();
            clang::Stmt* lhsresult = nullptr;
            clang::Stmt* rhsresult = nullptr;
            if(false){}
            
            else if(true){
                ROSTFScalarMatcher lhsm{this->context_,this->interp_};
                lhsm.setup();
                lhsm.visit(*lhs);
                lhsresult = lhsm.getChildExprStore();
            }

            if(false){}
            
            else if(true){
                ROSTFScalarMatcher rhsm{this->context_,this->interp_};
                rhsm.setup();
                rhsm.visit(*rhs);
                rhsresult = rhsm.getChildExprStore();
            }

            if(lhsresult and rhsresult){
                //interp_->mk(binaryOperator_,lhsresult, rhsresult);
                interp_->buffer_operand(lhsresult);
                interp_->buffer_operand(rhsresult);
                interp_->mkNode("MUL_R1_R1",binaryOperator_,true);
                this->childExprStore_ = (clang::Stmt*)binaryOperator_;
                return;
            }
        }
    }



};

