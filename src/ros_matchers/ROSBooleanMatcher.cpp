
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSBooleanMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSBooleanMatcher::setup(){
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
	
		StatementMatcher cxxBoolLiteralExpr_=cxxBoolLiteral().bind("CXXBoolLiteralExpr");
		localFinder_.addMatcher(cxxBoolLiteralExpr_,this);
    this->childExprStore_ = nullptr;
};

void ROSBooleanMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto declRefExpr_ = Result.Nodes.getNodeAs<clang::DeclRefExpr>("DeclRefExpr");
	
	auto cxxBoolLiteralExpr_ = Result.Nodes.getNodeAs<clang::CXXBoolLiteralExpr>("CXXBoolLiteralExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSBooleanMatcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){return;}
    
            else{
                this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
                //interp_->mkBOOL((clang::Stmt*)cxxBindTemporaryExpr_);
                interp_->mkNode("LIT_BOOL",(clang::Stmt*)cxxBindTemporaryExpr_,true);
            }
        }
    }

	
	arg_decay_exist_predicates["memberExpr_bool"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="bool" or typestr == "const bool" or typestr == "const bool" or typestr == "const class bool"){
            ROSBooleanMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_bool"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool"){
            ROSBooleanMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            //interp_->mkBOOL((clang::Stmt*)implicitCastExpr_);
            interp_->mkNode("LIT_BOOL",(clang::Stmt*)implicitCastExpr_,true);
            return;
        }
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_bool"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSBooleanMatcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){return;}
    
        else{
            this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
            //interp_->mkBOOL((clang::Stmt*)cxxBindTemporaryExpr_);
            interp_->mkNode("LIT_BOOL",(clang::Stmt*)cxxBindTemporaryExpr_,true);
            return;
        }
    }

	
	arg_decay_exist_predicates["materializeTemporaryExpr_bool"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSBooleanMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)materializeTemporaryExpr_;
                //interp_->mkBOOL((clang::Stmt*)materializeTemporaryExpr_);
                interp_->mkNode("LIT_BOOL",(clang::Stmt*)materializeTemporaryExpr_,true);
                return;
            }
        }

	
	arg_decay_exist_predicates["parenExpr_bool"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSBooleanMatcher inner{ context_, interp_};
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
            ROSBooleanMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)exprWithCleanups_;
                //interp_->mkBOOL((clang::Stmt*)exprWithCleanups_);
                return;
            }
        }
    
	
    if (cxxFunctionalCastExpr_)
        {
            ROSBooleanMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{

                this->childExprStore_ = (clang::Stmt*)cxxFunctionalCastExpr_;
               // interp_->mkBOOL((clang::Stmt*)cxxFunctionalCastExpr_);
                return;
            }
        }
    
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->buffer_link(dc);
            interp_->mkNode("REF_BOOL",declRefExpr_);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
	arg_decay_exist_predicates["cxxBoolLiteralExpr__bool"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ return true; }
        else { return false; }
    };
    if (cxxBoolLiteralExpr_)
    {
        interp_->mkNode("BOOL_LIT",cxxBoolLiteralExpr_);
        this->childExprStore_ = (clang::Stmt*)cxxBoolLiteralExpr_;
        return;
    }


};

