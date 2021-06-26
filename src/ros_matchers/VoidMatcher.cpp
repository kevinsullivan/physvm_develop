
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "VoidMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFTransformMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void VoidMatcher::setup(){
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
	
		StatementMatcher cxxMemberCallExpr_=cxxMemberCallExpr().bind("CXXMemberCallExpr");
		localFinder_.addMatcher(cxxMemberCallExpr_,this);
    this->childExprStore_ = nullptr;
};

void VoidMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
	
	auto cxxMemberCallExpr_ = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            VoidMatcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){return;}
    
            else{
                
                return;
            }
        }
    }

	
	arg_decay_exist_predicates["memberExpr_void"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="void" or typestr == "const void" or typestr == "const void" or typestr == "const class void"){
            VoidMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_void"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void"){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void"){
            VoidMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            
            return;
        }
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_void"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void"){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        VoidMatcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){return;}
    
        else{
            
            return;
        }
    }

	
	arg_decay_exist_predicates["materializeTemporaryExpr_void"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void"){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            VoidMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                
                return;
            }
        }

	
	arg_decay_exist_predicates["parenExpr_void"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void"){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        VoidMatcher inner{ context_, interp_};
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
            VoidMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                
                return;
            }
        }
    
	
    if (cxxFunctionalCastExpr_)
        {
            VoidMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{

                
                return;
            }
        }
    
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->buffer_link(dc);
            interp_->mkNode("REF_VOID",declRefExpr_);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform"){ return true; }
        else {return false;}
    };
    if(cxxMemberCallExpr_){
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name=="mult" or name == "const mult" or name == "class mult" or name == "const class mult")){
                auto arg0 = cxxMemberCallExpr_->getImplicitObjectArgument();
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();
                
                auto arg1=cxxMemberCallExpr_->getArg(1-1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                auto arg2=cxxMemberCallExpr_->getArg(2-1);
                auto arg2str = ((clang::QualType)arg2->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;

                clang::Stmt* arg2stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg1str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg2str)){
                    if(false){}
                    else if(arg0str=="tf::Transform" or arg0str == "const tf::Transform" or arg0str == "class tf::Transform" or arg0str == "const class tf::Transform"){
                        ROSTFTransformMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="tf::Transform" or arg1str == "const tf::Transform" or arg1str == "class tf::Transform" or arg1str == "const class tf::Transform"){
                        ROSTFTransformMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg2str=="tf::Transform" or arg2str == "const tf::Transform" or arg2str == "class tf::Transform" or arg2str == "const class tf::Transform"){
                        ROSTFTransformMatcher arg2m{this->context_,this->interp_};
                        arg2m.setup();
                        arg2m.visit(*arg2);
                        arg2stmt = arg2m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt and 
                        arg2stmt){
                        //interp_->mk(cxxMemberCallExpr_,arg0stmt,arg1stmt,arg2stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->buffer_operand(arg2stmt);
                        interp_->mkNode("ASSIGN_MUL_R4X4_R4X4", cxxMemberCallExpr_,false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

