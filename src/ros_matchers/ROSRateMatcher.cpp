
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSRateMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSRateMatcher::setup(){
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
};

void ROSRateMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;
    this->childExprStore_ = nullptr;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSRateMatcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){}
    
            else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                cxxConstructExpr_->dump();
           
            }
            return;
        }
    }

	
	arg_decay_exist_predicates["memberExpr_ros::Rate"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="ros::Rate" or typenm == "const ros::Rate" or typenm == "class ros::Rate"/*typenm.find("ros::Rate") != string::npos*/){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="ros::Rate" or typestr == "const ros::Rate" or typestr == "const ros::Rate"/*typestr.find("ros::Rate") != string::npos*/){
            ROSRateMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_ros::Rate"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="ros::Rate" or typenm == "const ros::Rate" or typenm == "class ros::Rate"/*typenm.find("ros::Rate") != string::npos*/){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="ros::Rate" or typestr == "const ros::Rate" or typestr == "class ros::Rate"/*typestr.find("ros::Rate") != string::npos*/){
            ROSRateMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                implicitCastExpr_->dump();
           
            }
            return;

    }
	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_ros::Rate"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="ros::Rate" or typenm == "const ros::Rate" or typenm == "class ros::Rate"/*typenm.find("ros::Rate") != string::npos*/){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSRateMatcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){}
    
        else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                cxxBindTemporaryExpr_->dump();
           
            }
            return;

    }
	
	arg_decay_exist_predicates["materializeTemporaryExpr_ros::Rate"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="ros::Rate" or typenm == "const ros::Rate" or typenm == "class ros::Rate"/*typenm.find("ros::Rate") != string::npos*/){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSRateMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                materializeTemporaryExpr_->dump();
           
            }
            return;

    }
	
	arg_decay_exist_predicates["parenExpr_ros::Rate"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="ros::Rate" or typenm == "const ros::Rate" or typenm == "class ros::Rate"/*typenm.find("ros::Rate") != string::npos*/){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSRateMatcher inner{ context_, interp_};
        inner.setup();
        inner.visit(*parenExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)inner.getChildExprStore();
        if(this->childExprStore_){}
        else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                parenExpr_->dump();
           
            }
        return;
    }
	
    if (exprWithCleanups_)
        {
            ROSRateMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                exprWithCleanups_->dump();
           
            }

    }
	
    if (cxxFunctionalCastExpr_)
        {
            ROSRateMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                cxxFunctionalCastExpr_->dump();
           
            }

    }
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL1_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
    if(cxxConstructExpr_ and cxxConstructExpr_->getNumArgs() == 1){
        if(true ){
            
            if(true ){
                interp_->mkREAL1_LIT(cxxConstructExpr_);
                this->childExprStore_ = (clang::Stmt*)cxxConstructExpr_;
                return;
            }
        }
    }


};

