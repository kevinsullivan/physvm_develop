
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

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
    this->childExprStore_ = nullptr;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFScalarMatcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){}
    
            else{
                this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
                interp_->mkREAL1_LIT((clang::Stmt*)cxxBindTemporaryExpr_);
            }
        }
    }

	
	arg_decay_exist_predicates["memberExpr_tfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="tfScalar" or typestr == "const tfScalar" or typestr == "const tfScalar"/*typestr.find("tfScalar") != string::npos*/){
            ROSTFScalarMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar"/*typestr.find("tfScalar") != string::npos*/){
            ROSTFScalarMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            interp_->mkREAL1_LIT((clang::Stmt*)implicitCastExpr_);
            return;
        }
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_tfScalar"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSTFScalarMatcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){}
    
        else{
            this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
            interp_->mkREAL1_LIT((clang::Stmt*)cxxBindTemporaryExpr_);
            return;
        }
    }

	
	arg_decay_exist_predicates["materializeTemporaryExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                this->childExprStore_ = (clang::Stmt*)materializeTemporaryExpr_;
                interp_->mkREAL1_LIT((clang::Stmt*)materializeTemporaryExpr_);
                return;
            }
        }

	
	arg_decay_exist_predicates["parenExpr_tfScalar"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSTFScalarMatcher inner{ context_, interp_};
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
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                this->childExprStore_ = (clang::Stmt*)exprWithCleanups_;
                interp_->mkREAL1_LIT((clang::Stmt*)exprWithCleanups_);
                return;
            }
        }
    
	
    if (cxxFunctionalCastExpr_)
        {
            ROSTFScalarMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                this->childExprStore_ = (clang::Stmt*)cxxFunctionalCastExpr_;
                interp_->mkREAL1_LIT((clang::Stmt*)cxxFunctionalCastExpr_);
                return;
            }
        }
    
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->mkREF_REAL1_VAR(declRefExpr_, dc);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
	arg_decay_exist_predicates["BinaryOperator(tfScalar,tfScalar).+@$.ADDtfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
    else { return false; }
    };
	arg_decay_exist_predicates["BinaryOperator(tfScalar,tfScalar).+@$.ADDtfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
    else { return false; }
    };
    if(binaryOperator_){
        auto bostr = binaryOperator_->getOpcodeStr().str();
        auto lhs = binaryOperator_->getLHS();
        auto rhs = binaryOperator_->getRHS();
        clang::Stmt* lhsstmt;
        clang::Stmt* rhsstmt;
            

        if(bostr=="+" or bostr == "const +" or bostr == "class +"/*bostr.find("+") != string::npos*/){
            auto lhs = binaryOperator_->getLHS();
            auto lhsstr = ((clang::QualType)lhs->getType()).getAsString();
            auto rhs = binaryOperator_->getRHS();
            auto rhsstr = ((clang::QualType)rhs->getType()).getAsString();
            clang::Stmt* lhsresult = nullptr;
            clang::Stmt* rhsresult = nullptr;
            if(false){}
            else if(lhsstr=="tfScalar" or lhsstr=="const tfScalar" or lhsstr=="class tfScalar"/*lhsstr.find("tfScalar") != string::npos*/){
                ROSTFScalarMatcher lhsm{this->context_,this->interp_};
                lhsm.setup();
                lhsm.visit(*lhs);
                lhsresult = lhsm.getChildExprStore();
                            
            }
            if(false){}
            
            else if(rhsstr=="tfScalar" or rhsstr=="const tfScalar" or rhsstr=="class tfScalar"/*rhsstr.find("tfScalar") != string::npos*/){
                ROSTFScalarMatcher rhsm{this->context_,this->interp_};
                rhsm.setup();
                rhsm.visit(*rhs);
                rhsresult = rhsm.getChildExprStore();
                            
            }
            if(lhsresult and rhsresult){
                interp_->mkADD_REAL1_EXPR_REAL1_EXPR(binaryOperator_,lhsresult, rhsresult);
                this->childExprStore_ = (clang::Stmt*)binaryOperator_;
                return;
            }
        }
    }

	
	arg_decay_exist_predicates["BinaryOperator(tfScalar,tfScalar).*@$.MULtfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
    else { return false; }
    };
	arg_decay_exist_predicates["BinaryOperator(tfScalar,tfScalar).*@$.MULtfScalar"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar"/*typenm.find("tfScalar") != string::npos*/){ return true; }
    else { return false; }
    };
    if(binaryOperator_){
        auto bostr = binaryOperator_->getOpcodeStr().str();
        auto lhs = binaryOperator_->getLHS();
        auto rhs = binaryOperator_->getRHS();
        clang::Stmt* lhsstmt;
        clang::Stmt* rhsstmt;
            

        if(bostr=="*" or bostr == "const *" or bostr == "class *"/*bostr.find("*") != string::npos*/){
            auto lhs = binaryOperator_->getLHS();
            auto lhsstr = ((clang::QualType)lhs->getType()).getAsString();
            auto rhs = binaryOperator_->getRHS();
            auto rhsstr = ((clang::QualType)rhs->getType()).getAsString();
            clang::Stmt* lhsresult = nullptr;
            clang::Stmt* rhsresult = nullptr;
            if(false){}
            else if(lhsstr=="tfScalar" or lhsstr=="const tfScalar" or lhsstr=="class tfScalar"/*lhsstr.find("tfScalar") != string::npos*/){
                ROSTFScalarMatcher lhsm{this->context_,this->interp_};
                lhsm.setup();
                lhsm.visit(*lhs);
                lhsresult = lhsm.getChildExprStore();
                            
            }
            if(false){}
            
            else if(rhsstr=="tfScalar" or rhsstr=="const tfScalar" or rhsstr=="class tfScalar"/*rhsstr.find("tfScalar") != string::npos*/){
                ROSTFScalarMatcher rhsm{this->context_,this->interp_};
                rhsm.setup();
                rhsm.visit(*rhs);
                rhsresult = rhsm.getChildExprStore();
                            
            }
            if(lhsresult and rhsresult){
                interp_->mkMUL_REAL1_EXPR_REAL1_EXPR(binaryOperator_,lhsresult, rhsresult);
                this->childExprStore_ = (clang::Stmt*)binaryOperator_;
                return;
            }
        }
    }



};

