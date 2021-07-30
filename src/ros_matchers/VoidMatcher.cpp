
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "VoidMatcher.h"
#include "ROSTF2TransformStamped.h"
#include "ROSTF2Transform.h"
#include "ROSTF2Vector3Matcher.h"
#include "ROSTF2TransformStamped.h"
#include "ROSTF2Transform.h"
#include "ROSTF2Quaternion.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "ROSGeomPoseStamped.h"
#include "ROSGeomPoseStamped.h"
#include "ROSGeomTransformStamped.h"
#include "ROSGeomQuaternion.h"
#include "ROSTF2Quaternion.h"


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
	
		StatementMatcher callExpr_=callExpr().bind("CallExpr");
		localFinder_.addMatcher(callExpr_,this);
    this->childExprStore_ = nullptr;
};

void VoidMatcher::run(const MatchFinder::MatchResult &Result){
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
	
	auto cxxMemberCallExpr_ = Result.Nodes.getNodeAs<clang::CXXMemberCallExpr>("CXXMemberCallExpr");
	
	auto callExpr_ = Result.Nodes.getNodeAs<clang::CallExpr>("CallExpr");
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
		else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = this->getTypeAsString(inner,true);
        if(false){}
        else if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
            VoidMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_void"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ return true; }
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
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
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else if(auto paramdecl_ = clang::dyn_cast<clang::ParmVarDecl>(asRef->getDecl())){
                            interp_->buffer_container(paramdecl_);
                            this->childExprStore_ = (clang::Stmt*)implicitCastExpr_;
                            interp_->mkNode("REF_Void",(clang::Stmt*)implicitCastExpr_);
                            return;
                        }
                        else {
                            std::cout<<"Can't find declaration\n";
                            asRef->getDecl()->dump();
                        }
                    }
     
            }
            
            return;

        }
        else if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
            VoidMatcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }
        else{
            
            return;
        }
        /*else{
            
            return;
        }*/
    }

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_void"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ return true; }
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
		else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ return true; }
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
		else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ return true; }
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
            interp_->mkNode("REF_Void",declRefExpr_);
            this->childExprStore_ = (clang::Stmt*)declRefExpr_;
            return;

        }
    }

	
	arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Vector3)@setOrigin@Capture=falsetf2::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Stamped<tf2::Transform>" or typenm =="tf2::Stamped<tf2::Transform>" or typenm == "const tf2::Stamped<tf2::Transform>" or typenm == "class tf2::Stamped<tf2::Transform>" or typenm == "const class tf2::Stamped<tf2::Transform>" or typenm ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){ return true; }
		else if(typenm == "operatortf2::Transform" or typenm =="tf2::Transform" or typenm == "const tf2::Transform" or typenm == "class tf2::Transform" or typenm == "const class tf2::Transform" or typenm ==  "::tf2::Transform_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Vector3)@setOrigin@Capture=falsetf2::Vector3"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
        else {return false;}
    };
    if(cxxMemberCallExpr_){
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name == "operatorsetOrigin" or name =="setOrigin" or name == "const setOrigin" or name == "class setOrigin" or name == "const class setOrigin" or name ==  "::setOrigin_<allocator<void> >")){
                auto arg0 = cxxMemberCallExpr_->getImplicitObjectArgument();
                auto arg0str = this->getTypeAsString(arg0,true);
                
                auto arg1=cxxMemberCallExpr_->getArg(1-1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Vector3)@setOrigin@Capture=falsetf2::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Vector3)@setOrigin@Capture=falsetf2::Vector3"](arg1str)){
                    if(false){}
                    else if(arg0str == "operatortf2::Stamped<tf2::Transform>" or arg0str =="tf2::Stamped<tf2::Transform>" or arg0str == "const tf2::Stamped<tf2::Transform>" or arg0str == "class tf2::Stamped<tf2::Transform>" or arg0str == "const class tf2::Stamped<tf2::Transform>" or arg0str ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        ROSTF2TransformStamped arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str == "operatortf2::Transform" or arg0str =="tf2::Transform" or arg0str == "const tf2::Transform" or arg0str == "class tf2::Transform" or arg0str == "const class tf2::Transform" or arg0str ==  "::tf2::Transform_<allocator<void> >"){
                        ROSTF2Transform arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatortf2::Vector3" or arg1str =="tf2::Vector3" or arg1str == "const tf2::Vector3" or arg1str == "class tf2::Vector3" or arg1str == "const class tf2::Vector3" or arg1str ==  "::tf2::Vector3_<allocator<void> >"){
                        ROSTF2Vector3Matcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt){
                        //interp_->mk(cxxMemberCallExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("ASSIGN_R4X4_AT_R3", cxxMemberCallExpr_,false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Quaternion)@setRotation@Capture=falsetf2::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Stamped<tf2::Transform>" or typenm =="tf2::Stamped<tf2::Transform>" or typenm == "const tf2::Stamped<tf2::Transform>" or typenm == "class tf2::Stamped<tf2::Transform>" or typenm == "const class tf2::Stamped<tf2::Transform>" or typenm ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){ return true; }
		else if(typenm == "operatortf2::Transform" or typenm =="tf2::Transform" or typenm == "const tf2::Transform" or typenm == "class tf2::Transform" or typenm == "const class tf2::Transform" or typenm ==  "::tf2::Transform_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Quaternion)@setRotation@Capture=falsetf2::Quaternion"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Quaternion" or typenm =="tf2::Quaternion" or typenm == "const tf2::Quaternion" or typenm == "class tf2::Quaternion" or typenm == "const class tf2::Quaternion" or typenm ==  "::tf2::Quaternion_<allocator<void> >"){ return true; }
        else {return false;}
    };
    if(cxxMemberCallExpr_){
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name == "operatorsetRotation" or name =="setRotation" or name == "const setRotation" or name == "class setRotation" or name == "const class setRotation" or name ==  "::setRotation_<allocator<void> >")){
                auto arg0 = cxxMemberCallExpr_->getImplicitObjectArgument();
                auto arg0str = this->getTypeAsString(arg0,true);
                
                auto arg1=cxxMemberCallExpr_->getArg(1-1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Quaternion)@setRotation@Capture=falsetf2::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf2::Transform,tf2::Quaternion)@setRotation@Capture=falsetf2::Quaternion"](arg1str)){
                    if(false){}
                    else if(arg0str == "operatortf2::Stamped<tf2::Transform>" or arg0str =="tf2::Stamped<tf2::Transform>" or arg0str == "const tf2::Stamped<tf2::Transform>" or arg0str == "class tf2::Stamped<tf2::Transform>" or arg0str == "const class tf2::Stamped<tf2::Transform>" or arg0str ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                        ROSTF2TransformStamped arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    else if(arg0str == "operatortf2::Transform" or arg0str =="tf2::Transform" or arg0str == "const tf2::Transform" or arg0str == "class tf2::Transform" or arg0str == "const class tf2::Transform" or arg0str ==  "::tf2::Transform_<allocator<void> >"){
                        ROSTF2Transform arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatortf2::Quaternion" or arg1str =="tf2::Quaternion" or arg1str == "const tf2::Quaternion" or arg1str == "class tf2::Quaternion" or arg1str == "const class tf2::Quaternion" or arg1str ==  "::tf2::Quaternion_<allocator<void> >"){
                        ROSTF2Quaternion arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt){
                        //interp_->mk(cxxMemberCallExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("ASSIGN_R4X4_AT_R4", cxxMemberCallExpr_,false);
                        this->childExprStore_ = (clang::Stmt*)cxxMemberCallExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf::Transform" or typenm =="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform" or typenm ==  "::tf::Transform_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf::Transform" or typenm =="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform" or typenm ==  "::tf::Transform_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf::Transform" or typenm =="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform" or typenm ==  "::tf::Transform_<allocator<void> >"){ return true; }
        else {return false;}
    };
    if(cxxMemberCallExpr_){
        auto decl_ = cxxMemberCallExpr_->getMethodDecl();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name == "operatormult" or name =="mult" or name == "const mult" or name == "class mult" or name == "const class mult" or name ==  "::mult_<allocator<void> >")){
                auto arg0 = cxxMemberCallExpr_->getImplicitObjectArgument();
                auto arg0str = this->getTypeAsString(arg0,true);
                
                auto arg1=cxxMemberCallExpr_->getArg(1-1);
                auto arg1str = this->getTypeAsString(arg1,true);

                auto arg2=cxxMemberCallExpr_->getArg(2-1);
                auto arg2str = this->getTypeAsString(arg2,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;

                clang::Stmt* arg2stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg0str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg1str) and 
                    arg_decay_exist_predicates["CXXMemberCallExpr(tf::Transform,tf::Transform,tf::Transform)@mult@Capture=falsetf::Transform"](arg2str)){
                    if(false){}
                    else if(arg0str == "operatortf::Transform" or arg0str =="tf::Transform" or arg0str == "const tf::Transform" or arg0str == "class tf::Transform" or arg0str == "const class tf::Transform" or arg0str ==  "::tf::Transform_<allocator<void> >"){
                        ROSTFTransformMatcher arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatortf::Transform" or arg1str =="tf::Transform" or arg1str == "const tf::Transform" or arg1str == "class tf::Transform" or arg1str == "const class tf::Transform" or arg1str ==  "::tf::Transform_<allocator<void> >"){
                        ROSTFTransformMatcher arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg2str == "operatortf::Transform" or arg2str =="tf::Transform" or arg2str == "const tf::Transform" or arg2str == "class tf::Transform" or arg2str == "const class tf::Transform" or arg2str ==  "::tf::Transform_<allocator<void> >"){
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

	
	arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::PoseStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatorgeometry_msgs::PoseStamped" or typenm =="geometry_msgs::PoseStamped" or typenm == "const geometry_msgs::PoseStamped" or typenm == "class geometry_msgs::PoseStamped" or typenm == "const class geometry_msgs::PoseStamped" or typenm ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::PoseStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatorgeometry_msgs::PoseStamped" or typenm =="geometry_msgs::PoseStamped" or typenm == "const geometry_msgs::PoseStamped" or typenm == "class geometry_msgs::PoseStamped" or typenm == "const class geometry_msgs::PoseStamped" or typenm ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::TransformStamped"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatorgeometry_msgs::TransformStamped" or typenm =="geometry_msgs::TransformStamped" or typenm == "const geometry_msgs::TransformStamped" or typenm == "class geometry_msgs::TransformStamped" or typenm == "const class geometry_msgs::TransformStamped" or typenm ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){ return true; }
        else {return false;}
    };
    if(callExpr_){
        auto decl_ = callExpr_->getDirectCallee();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name == "operatordoTransform" or name =="doTransform" or name == "const doTransform" or name == "class doTransform" or name == "const class doTransform" or name ==  "::doTransform_<allocator<void> >")){
                auto arg0=callExpr_->getArg(0);
                auto arg0str = this->getTypeAsString(arg0,true);

                auto arg1=callExpr_->getArg(1);
                auto arg1str = this->getTypeAsString(arg1,true);

                auto arg2=callExpr_->getArg(2);
                auto arg2str = this->getTypeAsString(arg2,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;

                clang::Stmt* arg2stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::PoseStamped"](arg0str) and 
                    arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::PoseStamped"](arg1str) and 
                    arg_decay_exist_predicates["CallExpr(geometry_msgs::PoseStamped,geometry_msgs::PoseStamped,geometry_msgs::TransformStamped)@doTransform@Capture=falsegeometry_msgs::TransformStamped"](arg2str)){
                    if(false){}
                    else if(arg0str == "operatorgeometry_msgs::PoseStamped" or arg0str =="geometry_msgs::PoseStamped" or arg0str == "const geometry_msgs::PoseStamped" or arg0str == "class geometry_msgs::PoseStamped" or arg0str == "const class geometry_msgs::PoseStamped" or arg0str ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                        ROSGeomPoseStamped arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatorgeometry_msgs::PoseStamped" or arg1str =="geometry_msgs::PoseStamped" or arg1str == "const geometry_msgs::PoseStamped" or arg1str == "class geometry_msgs::PoseStamped" or arg1str == "const class geometry_msgs::PoseStamped" or arg1str ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                        ROSGeomPoseStamped arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg2str == "operatorgeometry_msgs::TransformStamped" or arg2str =="geometry_msgs::TransformStamped" or arg2str == "const geometry_msgs::TransformStamped" or arg2str == "class geometry_msgs::TransformStamped" or arg2str == "const class geometry_msgs::TransformStamped" or arg2str ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){
                        ROSGeomTransformStamped arg2m{this->context_,this->interp_};
                        arg2m.setup();
                        arg2m.visit(*arg2);
                        arg2stmt = arg2m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt and 
                        arg2stmt){
                        //interp_->mk(callExpr_,arg0stmt,arg1stmt,arg2stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->buffer_operand(arg2stmt);
                        interp_->mkNode("ASSIGN_MUL_R4X4_R4X4_2",callExpr_,false);
                        this->childExprStore_ = (clang::Stmt*)callExpr_;
                        return;
                    }
            
                }
            }
        }
    }

	
	arg_decay_exist_predicates["CallExpr(geometry_msgs::Quaternion,tf2::Quaternion)@fromMsg@Capture=falsegeometry_msgs::Quaternion"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatorgeometry_msgs::Quaternion" or typenm =="geometry_msgs::Quaternion" or typenm == "const geometry_msgs::Quaternion" or typenm == "class geometry_msgs::Quaternion" or typenm == "const class geometry_msgs::Quaternion" or typenm ==  "::geometry_msgs::Quaternion_<allocator<void> >"){ return true; }
        else {return false;}
    };
	arg_decay_exist_predicates["CallExpr(geometry_msgs::Quaternion,tf2::Quaternion)@fromMsg@Capture=falsetf2::Quaternion"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Quaternion" or typenm =="tf2::Quaternion" or typenm == "const tf2::Quaternion" or typenm == "class tf2::Quaternion" or typenm == "const class tf2::Quaternion" or typenm ==  "::tf2::Quaternion_<allocator<void> >"){ return true; }
        else {return false;}
    };
    if(callExpr_){
        auto decl_ = callExpr_->getDirectCallee();
        if(auto dc = clang::dyn_cast<clang::NamedDecl>(decl_)){
            auto name = dc->getNameAsString();
            

            if((name == "operatorfromMsg" or name =="fromMsg" or name == "const fromMsg" or name == "class fromMsg" or name == "const class fromMsg" or name ==  "::fromMsg_<allocator<void> >")){
                auto arg0=callExpr_->getArg(0);
                auto arg0str = this->getTypeAsString(arg0,true);

                auto arg1=callExpr_->getArg(1);
                auto arg1str = this->getTypeAsString(arg1,true);

                clang::Stmt* arg0stmt = nullptr;

                clang::Stmt* arg1stmt = nullptr;
            
                if (true and arg_decay_exist_predicates["CallExpr(geometry_msgs::Quaternion,tf2::Quaternion)@fromMsg@Capture=falsegeometry_msgs::Quaternion"](arg0str) and 
                    arg_decay_exist_predicates["CallExpr(geometry_msgs::Quaternion,tf2::Quaternion)@fromMsg@Capture=falsetf2::Quaternion"](arg1str)){
                    if(false){}
                    else if(arg0str == "operatorgeometry_msgs::Quaternion" or arg0str =="geometry_msgs::Quaternion" or arg0str == "const geometry_msgs::Quaternion" or arg0str == "class geometry_msgs::Quaternion" or arg0str == "const class geometry_msgs::Quaternion" or arg0str ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                        ROSGeomQuaternion arg0m{this->context_,this->interp_};
                        arg0m.setup();
                        arg0m.visit(*arg0);
                        arg0stmt = arg0m.getChildExprStore();
                    }
                    if(false){}
                    else if(arg1str == "operatortf2::Quaternion" or arg1str =="tf2::Quaternion" or arg1str == "const tf2::Quaternion" or arg1str == "class tf2::Quaternion" or arg1str == "const class tf2::Quaternion" or arg1str ==  "::tf2::Quaternion_<allocator<void> >"){
                        ROSTF2Quaternion arg1m{this->context_,this->interp_};
                        arg1m.setup();
                        arg1m.visit(*arg1);
                        arg1stmt = arg1m.getChildExprStore();
                    }
                    if(true and arg0stmt and 
                        arg1stmt){
                        //interp_->mk(callExpr_,arg0stmt,arg1stmt);
                        
                        interp_->buffer_operand(arg0stmt);
                        interp_->buffer_operand(arg1stmt);
                        interp_->mkNode("ASSIGN_R4_SWAP",callExpr_,false);
                        this->childExprStore_ = (clang::Stmt*)callExpr_;
                        return;
                    }
            
                }
            }
        }
    }



};

