
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFPointMatcher.h"
#include "ROSTFStampedPoint.h"
#include "ROSTFVector3Matcher.h"
#include "DoubleMatcher.h"
#include "ROSTFStampedTransform.h"
#include "ROSTFTransformMatcher.h"


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
	
		StatementMatcher cxxFunctionalCastExpr_=cxxFunctionalCastExpr().bind("CXXFunctionalCastExpr");
		localFinder_.addMatcher(cxxFunctionalCastExpr_,this);
	
		StatementMatcher declRefExpr_=declRefExpr().bind("DeclRefExpr");
		localFinder_.addMatcher(declRefExpr_,this);
	
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
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
	
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
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="tf::Point" or typestr == "const tf::Point" or typestr == "const tf::Point"/*typestr.find("tf::Point") != string::npos*/){
            ROSTFPointMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr=="tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>"/*typestr.find("tf::Stamped<tf::Point>") != string::npos*/){
            ROSTFStampedPoint innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr=="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "const tf::Vector3"/*typestr.find("tf::Vector3") != string::npos*/){
            ROSTFVector3Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tf::Point"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="tf::Point" or typestr == "const tf::Point" or typestr == "class tf::Point"/*typestr.find("tf::Point") != string::npos*/){
            ROSTFPointMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr=="tf::Stamped<tf::Point>" or typestr == "const tf::Stamped<tf::Point>" or typestr == "class tf::Stamped<tf::Point>"/*typestr.find("tf::Stamped<tf::Point>") != string::npos*/){
            ROSTFStampedPoint innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
		else if(typestr=="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3"/*typestr.find("tf::Vector3") != string::npos*/){
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
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else { return false; }
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
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else { return false; }
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
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSTFPointMatcher inner{ context_, interp_};
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
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL3_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

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
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name=="+" or name=="const +" or name=="class +"/*name.find("+") != string::npos*/){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,tf::Vector3).+@$.ADDtf::Vector3"](arg1str)){
                    if(false){}
                    else if(arg0str=="tf::Stamped<tf::Point>" or arg0str=="const tf::Stamped<tf::Point>" or arg0str=="class tf::Stamped<tf::Point>"/*arg0str.find("tf::Stamped<tf::Point>") != string::npos*/){
            
                        ROSTFStampedPoint arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Vector3" or arg0str=="const tf::Vector3" or arg0str=="class tf::Vector3"/*arg0str.find("tf::Vector3") != string::npos*/){
            
                        ROSTFVector3Matcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Point" or arg0str=="const tf::Point" or arg0str=="class tf::Point"/*arg0str.find("tf::Point") != string::npos*/){
            
                        ROSTFPointMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="tf::Stamped<tf::Point>" or arg1str=="const tf::Stamped<tf::Point>" or arg1str=="class tf::Stamped<tf::Point>"/*arg1str.find("tf::Stamped<tf::Point>") != string::npos*/){
            
                        ROSTFStampedPoint arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Vector3" or arg1str=="const tf::Vector3" or arg1str=="class tf::Vector3"/*arg1str.find("tf::Vector3") != string::npos*/){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Point" or arg1str=="const tf::Point" or arg1str=="class tf::Point"/*arg1str.find("tf::Point") != string::npos*/){
            
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
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULdouble"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm=="double" or typenm == "const double" or typenm == "class double"/*typenm.find("double") != string::npos*/){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name=="*" or name=="const *" or name=="class *"/*name.find("*") != string::npos*/){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULtf::Vector3"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3,double).*@$.RMULdouble"](arg1str)){
                    if(false){}
                    else if(arg0str=="tf::Stamped<tf::Point>" or arg0str=="const tf::Stamped<tf::Point>" or arg0str=="class tf::Stamped<tf::Point>"/*arg0str.find("tf::Stamped<tf::Point>") != string::npos*/){
            
                        ROSTFStampedPoint arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Vector3" or arg0str=="const tf::Vector3" or arg0str=="class tf::Vector3"/*arg0str.find("tf::Vector3") != string::npos*/){
            
                        ROSTFVector3Matcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Point" or arg0str=="const tf::Point" or arg0str=="class tf::Point"/*arg0str.find("tf::Point") != string::npos*/){
            
                        ROSTFPointMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="double" or arg1str=="const double" or arg1str=="class double"/*arg1str.find("double") != string::npos*/){
            
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
		else if(typenm=="double" or typenm == "const double" or typenm == "class double"/*typenm.find("double") != string::npos*/){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name=="*" or name=="const *" or name=="class *"/*name.find("*") != string::npos*/){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULdouble"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(double,tf::Vector3).*@$.LMULtf::Vector3"](arg1str)){
                    if(false){}
                    else if(arg0str=="double" or arg0str=="const double" or arg0str=="class double"/*arg0str.find("double") != string::npos*/){
            
                        DoubleMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="tf::Stamped<tf::Point>" or arg1str=="const tf::Stamped<tf::Point>" or arg1str=="class tf::Stamped<tf::Point>"/*arg1str.find("tf::Stamped<tf::Point>") != string::npos*/){
            
                        ROSTFStampedPoint arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Vector3" or arg1str=="const tf::Vector3" or arg1str=="class tf::Vector3"/*arg1str.find("tf::Vector3") != string::npos*/){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Point" or arg1str=="const tf::Point" or arg1str=="class tf::Point"/*arg1str.find("tf::Point") != string::npos*/){
            
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

	
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3).*@$.TMULtf::Transform"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm=="tf::StampedTransform" or typenm == "const tf::StampedTransform" or typenm == "class tf::StampedTransform"/*typenm.find("tf::StampedTransform") != string::npos*/){ return true; }
		else if(typenm=="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform"/*typenm.find("tf::Transform") != string::npos*/){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3).*@$.TMULtf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm=="tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
		else if(typenm=="tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name=="*" or name=="const *" or name=="class *"/*name.find("*") != string::npos*/){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3).*@$.TMULtf::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3).*@$.TMULtf::Vector3"](arg1str)){
                    if(false){}
                    else if(arg0str=="tf::StampedTransform" or arg0str=="const tf::StampedTransform" or arg0str=="class tf::StampedTransform"/*arg0str.find("tf::StampedTransform") != string::npos*/){
            
                        ROSTFStampedTransform arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Transform" or arg0str=="const tf::Transform" or arg0str=="class tf::Transform"/*arg0str.find("tf::Transform") != string::npos*/){
            
                        ROSTFTransformMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="tf::Stamped<tf::Point>" or arg1str=="const tf::Stamped<tf::Point>" or arg1str=="class tf::Stamped<tf::Point>"/*arg1str.find("tf::Stamped<tf::Point>") != string::npos*/){
            
                        ROSTFStampedPoint arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Vector3" or arg1str=="const tf::Vector3" or arg1str=="class tf::Vector3"/*arg1str.find("tf::Vector3") != string::npos*/){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Point" or arg1str=="const tf::Point" or arg1str=="class tf::Point"/*arg1str.find("tf::Point") != string::npos*/){
            
                        ROSTFPointMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(arg0stmt and arg1stmt){
                        interp_->mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

