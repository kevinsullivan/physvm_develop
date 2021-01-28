
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSVoidMatcher.h"
#include "ROSGeometryMsgsPointStampedMatcher.h"
#include "ROSTFPointMatcher.h"
#include "ROSTFStampedPoint.h"
#include "ROSTFVector3Matcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSVoidMatcher::setup(){
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
	
		StatementMatcher callExpr_=callExpr().bind("CallExpr");
		localFinder_.addMatcher(callExpr_,this);
};

void ROSVoidMatcher::run(const MatchFinder::MatchResult &Result){
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto memberExpr_ = Result.Nodes.getNodeAs<clang::MemberExpr>("MemberExpr");
	
	auto implicitCastExpr_ = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExpr");
	
	auto cxxBindTemporaryExpr_ = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExpr");
	
	auto materializeTemporaryExpr_ = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExpr");
	
	auto parenExpr_ = Result.Nodes.getNodeAs<clang::ParenExpr>("ParenExpr");
	
	auto exprWithCleanups_ = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanups");
	
	auto cxxFunctionalCastExpr_ = Result.Nodes.getNodeAs<clang::CXXFunctionalCastExpr>("CXXFunctionalCastExpr");
	
	auto cxxMemberCallExpr_ = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
	
	auto callExpr_ = Result.Nodes.getNodeAs<clang::CallExpr>("CallExpr");
    std::unordered_map<std::string,std::function<bool(std::string)>> arg_decay_exist_predicates;
    std::unordered_map<std::string,std::function<std::string(std::string)>> arg_decay_match_predicates;
    this->childExprStore_ = nullptr;

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSVoidMatcher pm{context_, interp_};
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
            ROSVoidMatcher innerm{this->context_,this->interp_};
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
            ROSVoidMatcher innerm{this->context_,this->interp_};
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
        ROSVoidMatcher exprMatcher{ context_, interp_};
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
            ROSVoidMatcher exprMatcher{ context_, interp_};
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
        ROSVoidMatcher inner{ context_, interp_};
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
            ROSVoidMatcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){}
        
            else{
                
            }

    }
	
    if (cxxFunctionalCastExpr_)
        {
            ROSVoidMatcher exprMatcher{ context_, interp_};
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

	
	arg_decay_exist_predicates["CallExpr(geometry_msgs::PointStamped,tf::Stamped<tf::Point>).pointStampedMsgToTF@ASSIGN.ASNR3geometry_msgs::PointStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "geometry_msgs::PointStamped" or typenm == "const geometry_msgs::PointStamped" or typenm == "class geometry_msgs::PointStamped"/*typenm.find("geometry_msgs::PointStamped") != string::npos*/){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CallExpr(geometry_msgs::PointStamped,tf::Stamped<tf::Point>).pointStampedMsgToTF@ASSIGN.ASNR3tf::Stamped<tf::Point>"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm == "tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm == "tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else {return false;}
    };
    if(callExpr_){
        auto decl_ = callExpr_->getDirectCallee();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name.find("pointStampedMsgToTF") != string::npos)/*name.find("pointStampedMsgToTF") != string::npos*/){
                auto arg0=callExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=callExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CallExpr(geometry_msgs::PointStamped,tf::Stamped<tf::Point>).pointStampedMsgToTF@ASSIGN.ASNR3geometry_msgs::PointStamped"](arg0str) and 
                    arg_decay_exist_predicates["CallExpr(geometry_msgs::PointStamped,tf::Stamped<tf::Point>).pointStampedMsgToTF@ASSIGN.ASNR3tf::Stamped<tf::Point>"](arg1str)){
                    if(false){}
                    else if(arg0str=="geometry_msgs::PointStamped" or arg0str == "const geometry_msgs::PointStamped" or arg0str == "class geometry_msgs::PointStamped"/*arg0str.find("geometry_msgs::PointStamped")!=string::npos*/){
                        ROSGeometryMsgsPointStampedMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="tf::Point" or arg1str == "const tf::Point" or arg1str == "class tf::Point"/*arg1str.find("tf::Point")!=string::npos*/){
                        ROSTFPointMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Stamped<tf::Point>" or arg1str == "const tf::Stamped<tf::Point>" or arg1str == "class tf::Stamped<tf::Point>"/*arg1str.find("tf::Stamped<tf::Point>")!=string::npos*/){
                        ROSTFStampedPoint arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    else if(arg1str=="tf::Vector3" or arg1str == "const tf::Vector3" or arg1str == "class tf::Vector3"/*arg1str.find("tf::Vector3")!=string::npos*/){
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt){
                        auto arg1decl = clang::dyn_cast<clang::VarDecl>(clang::dyn_cast<clang::DeclRefExpr>(arg1stmt)->getFoundDecl());    
                        interp_->mkASNR3_REAL3_VAR_REAL3_EXPR(callExpr_, arg1decl,arg0stmt);
                        //interp_->mkASNR3_REAL3_VAR_REAL3_EXPR(callExpr_,arg0stmt,arg1stmt);
                        this->childExprStore_ = (clang::Stmt*)callExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CallExpr(tf::Stamped<tf::Point>,geometry_msgs::PointStamped).pointStampedTFToMsg@ASSIGN.ASNR3tf::Stamped<tf::Point>"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "tf::Point" or typenm == "const tf::Point" or typenm == "class tf::Point"/*typenm.find("tf::Point") != string::npos*/){ return true; }
		else if(typenm == "tf::Stamped<tf::Point>" or typenm == "const tf::Stamped<tf::Point>" or typenm == "class tf::Stamped<tf::Point>"/*typenm.find("tf::Stamped<tf::Point>") != string::npos*/){ return true; }
		else if(typenm == "tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3"/*typenm.find("tf::Vector3") != string::npos*/){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CallExpr(tf::Stamped<tf::Point>,geometry_msgs::PointStamped).pointStampedTFToMsg@ASSIGN.ASNR3geometry_msgs::PointStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "geometry_msgs::PointStamped" or typenm == "const geometry_msgs::PointStamped" or typenm == "class geometry_msgs::PointStamped"/*typenm.find("geometry_msgs::PointStamped") != string::npos*/){ return true; }
        else {return false;}
    };
    if(callExpr_){
        auto decl_ = callExpr_->getDirectCallee();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name.find("pointStampedTFToMsg") != string::npos)/*name.find("pointStampedTFToMsg") != string::npos*/){
                auto arg0=callExpr_->getArg(0);
                auto arg0str = ((clang::QualType)arg0->getType()).getAsString();

                auto arg1=callExpr_->getArg(1);
                auto arg1str = ((clang::QualType)arg1->getType()).getAsString();

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CallExpr(tf::Stamped<tf::Point>,geometry_msgs::PointStamped).pointStampedTFToMsg@ASSIGN.ASNR3tf::Stamped<tf::Point>"](arg0str) and 
                    arg_decay_exist_predicates["CallExpr(tf::Stamped<tf::Point>,geometry_msgs::PointStamped).pointStampedTFToMsg@ASSIGN.ASNR3geometry_msgs::PointStamped"](arg1str)){
                    if(false){}
                    else if(arg0str=="tf::Point" or arg0str == "const tf::Point" or arg0str == "class tf::Point"/*arg0str.find("tf::Point")!=string::npos*/){
                        ROSTFPointMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Stamped<tf::Point>" or arg0str == "const tf::Stamped<tf::Point>" or arg0str == "class tf::Stamped<tf::Point>"/*arg0str.find("tf::Stamped<tf::Point>")!=string::npos*/){
                        ROSTFStampedPoint arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str=="tf::Vector3" or arg0str == "const tf::Vector3" or arg0str == "class tf::Vector3"/*arg0str.find("tf::Vector3")!=string::npos*/){
                        ROSTFVector3Matcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str=="geometry_msgs::PointStamped" or arg1str == "const geometry_msgs::PointStamped" or arg1str == "class geometry_msgs::PointStamped"/*arg1str.find("geometry_msgs::PointStamped")!=string::npos*/){
                        ROSGeometryMsgsPointStampedMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt){
                        auto arg1decl = clang::dyn_cast<clang::VarDecl>(clang::dyn_cast<clang::DeclRefExpr>(arg1stmt)->getFoundDecl());    
                        interp_->mkASNR3_REAL3_VAR_REAL3_EXPR(callExpr_, arg1decl,arg0stmt);
                        //interp_->mkASNR3_REAL3_VAR_REAL3_EXPR(callExpr_,arg0stmt,arg1stmt);
                        this->childExprStore_ = (clang::Stmt*)callExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

