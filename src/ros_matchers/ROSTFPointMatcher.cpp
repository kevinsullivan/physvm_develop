
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFPointMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "DoubleMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSTFPointMatcher::setup(){
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
	
		StatementMatcher declRefExpr_=declRefExpr().bind("DeclRefExpr");
		localFinder_.addMatcher(declRefExpr_,this);
	
		StatementMatcher cxxFunctionalCastExpr_=cxxFunctionalCastExpr().bind("CXXFunctionalCastExpr");
		localFinder_.addMatcher(cxxFunctionalCastExpr_,this);
	
		StatementMatcher cxxOperatorCallExpr_=cxxOperatorCallExpr().bind("CXXOperatorCallExpr");
		localFinder_.addMatcher(cxxOperatorCallExpr_,this);
};

void ROSTFPointMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto cxxOperatorCallExpr_ = Result.Nodes.getNodeAs<clang::CXXOperatorCallExpr>("CXXOperatorCallExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;
    this->childExprStore_ = nullptr;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFPointMatcher pm{context_, interp_};
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

	
	arg_decay_exist_predicates["memberExpr_tf::Point"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm.find("tf::Point") != string::npos){ return true; }
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr.find("tf::Point") != string::npos){
            ROSTFPointMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr.find("tf::Vector3") != string::npos){
            ROSTFVector3Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tf::Point"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr.find("tf::Point") != string::npos){
            ROSTFPointMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr.find("tf::Vector3") != string::npos){
            ROSTFVector3Matcher innerm{this->context_,this->interp_};
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
	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_tf::Point"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSTFPointMatcher exprMatcher{ context_, interp_};
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
	
	arg_decay_exist_predicates["materializeTemporaryExpr_tf::Point"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm.find("tf::Point") != string::npos){ return true; }
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSTFPointMatcher exprMatcher{ context_, interp_};
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
	
	arg_decay_exist_predicates["parenExpr_tf::Point"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm.find("tf::Point") != string::npos){ return true; }
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
    };
    if (parenExpr_)
    {
        ROSTFPointMatcher inner{ context_, interp_};
        inner.setup();
        inner.visit(*parenExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)inner.getChildExprStore();
        if(this->childExprStore_){}
        else{
            std::cout<<"WARNING: Capture Escaping! Dump :\n";
            parenExpr_->dump();
        }
        return;
    }
	
    if (exprWithCleanups_)
        {
            ROSTFPointMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                exprWithCleanups_->dump();
            }

    }
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL3_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
    if (cxxFunctionalCastExpr_)
        {
            ROSTFPointMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                std::cout<<"WARNING: Capture Escaping! Dump : \n";
                cxxFunctionalCastExpr_->dump();
            }

    }
	
    if(cxxConstructExpr_ and cxxConstructExpr_->getNumArgs() == 3){
        if(true ){
            
            if(true ){
                interp_->mkREAL3_EMPTY(cxxConstructExpr_);
                this->childExprStore_ = (clang::Stmt*)cxxConstructExpr_;
                return;
            }
        }
    }
	
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name.find("+") != string::npos){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt;

                clang::Stmt* arg1stmt;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"](arg1str)){
                    if(false){0;}
                    else if(arg0str.find("tf::Vector3") != string::npos){
            
                        ROSTFVector3Matcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str.find("tf::Point") != string::npos){
            
                        ROSTFPointMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){1;}
                    else if(arg1str.find("tf::Vector3") != string::npos){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str.find("tf::Point") != string::npos){
            
                        ROSTFPointMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(arg0stmt and arg1stmt){
                        interp_->mkADD_REAL3_EXPR_REAL3_EXPR(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULdouble"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("double") != string::npos){ return true; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name.find("*") != string::npos){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt;

                clang::Stmt* arg1stmt;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULtf::Vector3"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULdouble"](arg1str)){
                    if(false){0;}
                    else if(arg0str.find("tf::Vector3") != string::npos){
            
                        ROSTFVector3Matcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str.find("tf::Point") != string::npos){
            
                        ROSTFPointMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){1;}
                    else if(arg1str.find("double") != string::npos){
            
                        DoubleMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(arg0stmt and arg1stmt){
                        interp_->mkRMUL_REAL3_EXPR_REAL1_EXPR(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULdouble"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("double") != string::npos){ return true; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm.find("tf::Vector3") != string::npos){ return true; }
		else if(typenm.find("tf::Point") != string::npos){ return true; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name.find("*") != string::npos){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt;

                clang::Stmt* arg1stmt;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULdouble"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULtf::Vector3"](arg1str)){
                    if(false){0;}
                    else if(arg0str.find("double") != string::npos){
            
                        DoubleMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){1;}
                    else if(arg1str.find("tf::Vector3") != string::npos){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str.find("tf::Point") != string::npos){
            
                        ROSTFPointMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(arg0stmt and arg1stmt){
                        interp_->mkLMUL_REAL1_EXPR_REAL3_EXPR(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

