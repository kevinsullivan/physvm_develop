
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSTFVector3Matcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTFVector3Matcher.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSTFVector3Matcher::setup(){
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
    this->childExprStore_ = nullptr;
};

void ROSTFVector3Matcher::run(const MatchFinder::MatchResult &Result){
    if(this->childExprStore_ != nullptr){
        return;
    }
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

	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3?FORCE,tf::Vector3?FORCE)@+@tf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Vector3?FORCE,tf::Vector3?FORCE)@+@tf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name == "operator+" or name =="+" or name == "const +" or name == "class +" or name == "const class +" or name ==  "::+_<allocator<void> >"){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = this->getTypeAsString(arg0,true);

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (true and 
                    true){
                    if(false){}
                    
                    else if(true){
                    ROSTFVector3Matcher arg0m{ this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    
                    if(false){}
                    
                    else if(true){
                    ROSTFVector3Matcher arg1m{ this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    
                    if(arg0stmt and arg1stmt){
                        //interp_->mk(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("ADD_R3_R3",cxxOperatorCallExpr_,true);
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CXXOperatorCallExpr(tfScalar,tf::Vector3?FORCE)@*@tfScalar"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortfScalar" or typenm =="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar" or typenm ==  "::tfScalar_<allocator<void> >"){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tfScalar,tf::Vector3?FORCE)@*@tf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name == "operator*" or name =="*" or name == "const *" or name == "class *" or name == "const class *" or name ==  "::*_<allocator<void> >"){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = this->getTypeAsString(arg0,true);

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tfScalar,tf::Vector3?FORCE)@*@tfScalar"](arg0str) and 
                    true){
                    if(false){}
                    else if(arg0str == "operatortfScalar" or arg0str =="tfScalar" or arg0str == "const tfScalar" or arg0str == "class tfScalar" or arg0str == "const class tfScalar" or arg0str ==  "::tfScalar_<allocator<void> >"){
            
                        ROSTFScalarMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    
                    else if(true){
                    ROSTFVector3Matcher arg1m{ this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    
                    if(arg0stmt and arg1stmt){
                        //interp_->mk(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("MUL_R1_R3",cxxOperatorCallExpr_,true);
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTFVector3Matcher pm{context_, interp_};
            pm.setup();
            pm.visit(**cxxConstructExpr_->getArgs());
            this->childExprStore_ = pm.getChildExprStore();
            if(this->childExprStore_){return;}
    
            else{
                this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
                interp_->mkNode("LIT_R3",(clang::Stmt*)cxxBindTemporaryExpr_,true);
                return;
            }
        }
    }

	
	arg_decay_exist_predicates["memberExpr_tf::Vector3"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = this->getTypeAsString(inner,true);
        if(false){}
        else if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
            ROSTFVector3Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tf::Vector3"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; } 
    };

    if (implicitCastExpr_)
    {
        auto inner = implicitCastExpr_->getSubExpr();
        auto typestr = this->getTypeAsString(inner,true);
        auto hasmemb = clang::dyn_cast<clang::MemberExpr>(inner);
        if(false){}
        else if(hasmemb){
            while(auto memb = clang::dyn_cast<clang::MemberExpr>(inner))
                {
                    inner = memb->getBase();                
                }

                auto typestr = this->getTypeAsString(inner,true);
                if(auto asRef = clang::dyn_cast<clang::DeclRefExpr>(inner))
                {
            
                    if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::TransformStamped" or typestr =="geometry_msgs::TransformStamped" or typestr == "const geometry_msgs::TransformStamped" or typestr == "class geometry_msgs::TransformStamped" or typestr == "const class geometry_msgs::TransformStamped" or typestr ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::PoseStamped" or typestr =="geometry_msgs::PoseStamped" or typestr == "const geometry_msgs::PoseStamped" or typestr == "class geometry_msgs::PoseStamped" or typestr == "const class geometry_msgs::PoseStamped" or typestr ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::DurationBase" or typestr =="ros::DurationBase" or typestr == "const ros::DurationBase" or typestr == "class ros::DurationBase" or typestr == "const class ros::DurationBase" or typestr ==  "::ros::DurationBase_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::TimeBase" or typestr =="ros::TimeBase" or typestr == "const ros::TimeBase" or typestr == "class ros::TimeBase" or typestr == "const class ros::TimeBase" or typestr ==  "::ros::TimeBase_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operator_Bool" or typestr =="_Bool" or typestr == "const _Bool" or typestr == "class _Bool" or typestr == "const class _Bool" or typestr ==  "::_Bool_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
     
            }
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            interp_->mkNode("LIT_R3",(clang::Stmt*)implicitCastExpr_,true);
            return;

        }
        else if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
            ROSTFVector3Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            interp_->mkNode("LIT_R3",(clang::Stmt*)implicitCastExpr_,true);
            return;
        }
        /*else{
            
            if(auto hasmemb = clang::dyn_cast<clang::MemberExpr>(inner)){
                while(auto memb = clang::dyn_cast<clang::MemberExpr>(inner))
                {
                    inner = memb->getBase();                
                }

                auto typestr = this->getTypeAsString(inner,true);
                if(auto asRef = clang::dyn_cast<clang::DeclRefExpr>(inner))
                {
            
                    if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::TransformStamped" or typestr =="geometry_msgs::TransformStamped" or typestr == "const geometry_msgs::TransformStamped" or typestr == "class geometry_msgs::TransformStamped" or typestr == "const class geometry_msgs::TransformStamped" or typestr ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::PoseStamped" or typestr =="geometry_msgs::PoseStamped" or typestr == "const geometry_msgs::PoseStamped" or typestr == "class geometry_msgs::PoseStamped" or typestr == "const class geometry_msgs::PoseStamped" or typestr ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::DurationBase" or typestr =="ros::DurationBase" or typestr == "const ros::DurationBase" or typestr == "class ros::DurationBase" or typestr == "const class ros::DurationBase" or typestr ==  "::ros::DurationBase_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::TimeBase" or typestr =="ros::TimeBase" or typestr == "const ros::TimeBase" or typestr == "class ros::TimeBase" or typestr == "const class ros::TimeBase" or typestr ==  "::ros::TimeBase_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operator_Bool" or typestr =="_Bool" or typestr == "const _Bool" or typestr == "class _Bool" or typestr == "const class _Bool" or typestr ==  "::_Bool_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
    
                    if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                        if(auto vardecl_ = clang::dyn_cast<clang::VarDecl>(asRef->getDecl())){
                            interp_->buffer_container(vardecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_R3",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
     
                }
            }
            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
            interp_->mkNode("LIT_R3",(clang::Stmt*)implicitCastExpr_,true);
            return;
        }*/
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_tf::Vector3"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSTFVector3Matcher exprMatcher{ context_, interp_};
        exprMatcher.setup();
        exprMatcher.visit(*cxxBindTemporaryExpr_->getSubExpr());
        this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        if(this->childExprStore_){return;}
    
        else{
            this->childExprStore_ = (clang::Stmt*)cxxBindTemporaryExpr_;
            interp_->mkNode("LIT_R3",(clang::Stmt*)cxxBindTemporaryExpr_,true);
            return;
        }
    }

	
	arg_decay_exist_predicates["materializeTemporaryExpr_tf::Vector3"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSTFVector3Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*materializeTemporaryExpr_->GetTemporaryExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)materializeTemporaryExpr_;
                interp_->mkNode("LIT_R3",(clang::Stmt*)materializeTemporaryExpr_,true);
                return;
            }
        }

	
	arg_decay_exist_predicates["parenExpr_tf::Vector3"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSTFVector3Matcher inner{ context_, interp_};
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
            ROSTFVector3Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*exprWithCleanups_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{
                this->childExprStore_ = (clang::Stmt*)exprWithCleanups_;
                interp_->mkNode("LIT_R3",(clang::Stmt*)exprWithCleanups_,true);
                return;
            }
        }
    
	
    if (cxxFunctionalCastExpr_)
        {
            ROSTFVector3Matcher exprMatcher{ context_, interp_};
            exprMatcher.setup();
            exprMatcher.visit(*cxxFunctionalCastExpr_->getSubExpr());
            this->childExprStore_ = (clang::Stmt*)exprMatcher.getChildExprStore();
        
            if(this->childExprStore_){return;}
        
            else{

                this->childExprStore_ = (clang::Stmt*)cxxFunctionalCastExpr_;
                interp_->mkNode("LIT_R3",(clang::Stmt*)cxxFunctionalCastExpr_,true);
                return;
            }
        }
    
	
    if(declRefExpr_){
        if(auto dc = clang::dyn_cast<clang::VarDecl>(declRefExpr_->getDecl())){
            interp_->buffer_link(dc);
            interp_->mkNode("REF_R3",declRefExpr_);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3)@*@tf::Transform"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortf::Transform" or typenm =="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform" or typenm ==  "::tf::Transform_<allocator<void> >"){ return true; }
        else { return false; }
    };
	arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3)@*@tf::Vector3"] = [=](std::string typenm){
        if(false){ return false;}
		else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if(cxxOperatorCallExpr_){
        auto decl_ = cxxOperatorCallExpr_->getCalleeDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();

            if(name == "operator*" or name =="*" or name == "const *" or name == "class *" or name == "const class *" or name ==  "::*_<allocator<void> >"){
                auto arg0=cxxOperatorCallExpr_->getArg(0);
                auto arg0str = this->getTypeAsString(arg0,true);

                auto arg1=cxxOperatorCallExpr_->getArg(1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
              
                if (arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3)@*@tf::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXOperatorCallExpr(tf::Transform,tf::Vector3)@*@tf::Vector3"](arg1str)){
                    if(false){}
                    else if(arg0str == "operatortf::Transform" or arg0str =="tf::Transform" or arg0str == "const tf::Transform" or arg0str == "class tf::Transform" or arg0str == "const class tf::Transform" or arg0str ==  "::tf::Transform_<allocator<void> >"){
            
                        ROSTFTransformMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatortf::Vector3" or arg1str =="tf::Vector3" or arg1str == "const tf::Vector3" or arg1str == "class tf::Vector3" or arg1str == "const class tf::Vector3" or arg1str ==  "::tf::Vector3_<allocator<void> >"){
            
                        ROSTFVector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(arg0stmt and arg1stmt){
                        //interp_->mk(cxxOperatorCallExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("MUL_R4X4_R3",cxxOperatorCallExpr_,true);
                        this->childExprStore_ = (clang::Stmt*)cxxOperatorCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
    if(cxxConstructExpr_ and cxxConstructExpr_->getNumArgs() == 3){
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

                        int param_i = 0;
                        
                        
                        
                        param_i++;
                        param_i++;
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
                interp_->mkNode("LIT_R3",cxxConstructExpr_,true);
                this->childExprStore_ = (clang::Stmt*)cxxConstructExpr_;
                return;
            }
        }
    }


};

