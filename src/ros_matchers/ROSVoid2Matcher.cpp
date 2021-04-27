
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSVoid2Matcher.h"
#include "ROSGeometryMsgsPointStampedMatcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSVoid2Matcher::setup(){
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
	
		StatementMatcher cxxMemberCallExpr_=cxxMemberCallExpr().bind("CXXMemberCallExpr");
		localFinder_.addMatcher(cxxMemberCallExpr_,this);
};

void ROSVoid2Matcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto cxxMemberCallExpr_ = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;
    this->childExprStore_ = nullptr;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSVoid2Matcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){}
    
            else{
                
            }
            return;
        }
    }

	
	arg_decay_exist_predicates["memberExpr_void"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void"/*typenm.find("void") != string::npos*/){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = ((clang::QualType)inner->getType()).getAsString();
        if(false){}
        else if(typestr=="void" or typestr == "const void" or typestr == "const void"/*typestr.find("void") != string::npos*/){
            ROSVoid2Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_void"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm=="void" or typenm == "const void" or typenm == "class void"/*typenm.find("void") != string::npos*/){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = inner->getType().getAsString();

        if(false){}
        else if(typestr=="void" or typestr == "const void" or typestr == "class void"/*typestr.find("void") != string::npos*/){
            ROSVoid2Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
                
            }
            return;

    }
	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_void"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm=="void" or typenm == "const void" or typenm == "class void"/*typenm.find("void") != string::npos*/){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSVoid2Matcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){}
    
        else{
                
            }
            return;

    }
	
	arg_decay_exist_predicates["materializeTemporaryExpr_void"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void"/*typenm.find("void") != string::npos*/){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSVoid2Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
            }
            return;

    }
	
	arg_decay_exist_predicates["parenExpr_void"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm=="void" or typenm == "const void" or typenm == "class void"/*typenm.find("void") != string::npos*/){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSVoid2Matcher inner{ context_, interp_};
        inner.setup();
        inner.visit(*parenExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)inner.getChildExprStore();
        if(this->childExprStore_){}
        else{
                
            }
        return;
    }
	
    if (exprWithCleanups_)
        {
            ROSVoid2Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
            }

    }
	
    if (cxxFunctionalCastExpr_)
        {
            ROSVoid2Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
            }

    }
	
	arg_decay_exist_predicates["CXXMemberCallExpr(IGNORE,IGNORE,geometry_msgs::PointStamped,geometry_msgs::PointStamped).transformPoint@ASSIGN.ASNR3geometry_msgs::PointStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "geometry_msgs::PointStamped" or typenm == "const geometry_msgs::PointStamped" or typenm == "class geometry_msgs::PointStamped"/*typenm.find("geometry_msgs::PointStamped") != string::npos*/){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(IGNORE,IGNORE,geometry_msgs::PointStamped,geometry_msgs::PointStamped).transformPoint@ASSIGN.ASNR3geometry_msgs::PointStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "geometry_msgs::PointStamped" or typenm == "const geometry_msgs::PointStamped" or typenm == "class geometry_msgs::PointStamped"/*typenm.find("geometry_msgs::PointStamped") != string::npos*/){ return true; }
        else {return false;}
    };
    if(cxxMemberCallExpr_){
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name=="transformPoint" or name == "const transformPoint" or name == "class transformPoint")/*name.find("transformPoint") != string::npos*/){
                auto arg0 = cxxMemberCallExpr_->getArg(0 + 1);
        auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

        auto arg1 = clang::dyn_cast<clang::VarDecl>(clang::dyn_cast<clang::DeclRefExpr>(cxxMemberCallExpr_->getArg(1 + 1))->getFoundDecl());

        clang::Stmt* arg0stmt = nullptr;
                if (true and arg_decay_exist_predicates["CXXMemberCallExpr(IGNORE,IGNORE,geometry_msgs::PointStamped,geometry_msgs::PointStamped).transformPoint@ASSIGN.ASNR3geometry_msgs::PointStamped"](arg0str)){
                    if(false){}
                    else if(arg0str=="geometry_msgs::PointStamped" or arg0str == "const geometry_msgs::PointStamped" or arg0str == "class geometry_msgs::PointStamped"/*arg0str.find("geometry_msgs::PointStamped")!=string::npos*/){
                        ROSGeometryMsgsPointStampedMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(true and arg0stmt){
                        clang::CXXUnresolvedConstructExpr 
                            *inject_trans = clang::CXXUnresolvedConstructExpr::CreateEmpty(*this->context_, 0),
                            *inject_mul = clang::CXXUnresolvedConstructExpr::CreateEmpty(*this->context_,2);
                        clang::SourceRange sr = cxxMemberCallExpr_->getSourceRange();
                        inject_trans->setLParenLoc(sr.getBegin());
                        inject_mul->setLParenLoc(sr.getBegin());
                        inject_trans->setRParenLoc(sr.getEnd());
                        inject_mul->setRParenLoc(sr.getEnd());

                        interp_->mkREALMATRIX4_EMPTY(inject_trans);
                        interp_->mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(inject_mul, inject_trans, arg0stmt);

                        interp_->mkASNR3_REAL3_VAR_REAL3_EXPR(cxxMemberCallExpr_,arg1,inject_mul);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

