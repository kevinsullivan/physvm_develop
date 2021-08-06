
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

#include "ROSBooleanMatcher.h"
#include "ROSBoolMatcher.h"
#include "FloatMatcher.h"
#include "DoubleMatcher.h"
#include "ROSTFScalarMatcher.h"
#include "ROSTimeMatcher.h"
#include "ROSTimeBaseMatcher.h"
#include "ROSDurationMatcher.h"
#include "ROSDurationBaseMatcher.h"
#include "ROSTFVector3Matcher.h"
#include "ROSTF2DurationMatcher.h"
#include "ROSTFTransformMatcher.h"
#include "VoidMatcher.h"
#include "ROSGeometryPoseWithCovarianceStamped.h"
#include "ROSGeomQuaternion.h"
#include "ROSTFQuaternion.h"
#include "ROSTF2Quaternion.h"
#include "ROSTF2Vector3Matcher.h"
#include "ROSTF2TransformStamped.h"
#include "ROSTF2Transform.h"
#include "ROSGeomPoseStamped.h"
#include "ROSGeomTransformStamped.h"


#include <string>
#include <unordered_map>
#include <functional>


void ROSTF2Vector3Matcher::setup(){
		StatementMatcher cxxConstructExpr_=cxxConstructExpr().bind("CXXConstructExpr");
		localFinder_.addMatcher(cxxConstructExpr_,this);
	
		StatementMatcher callExpr_=callExpr().bind("CallExpr");
		localFinder_.addMatcher(callExpr_,this);
	
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
    this->childExprStore_ = nullptr;
};

void ROSTF2Vector3Matcher::run(const MatchFinder::MatchResult &Result){
    if(this->childExprStore_ != nullptr){
        return;
    }
	auto cxxConstructExpr_ = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExpr");
	
	auto callExpr_ = Result.Nodes.getNodeAs<clang::CallExpr>("CallExpr");
	
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

    if(cxxConstructExpr_){
        auto decl_ = cxxConstructExpr_->getConstructor();
        if(decl_->isCopyOrMoveConstructor())
        {
            ROSTF2Vector3Matcher pm{context_, interp_};
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

	
	arg_decay_exist_predicates["callExpr_tf2::Vector3"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
    else { return false; }
    };
    if(callExpr_){
        auto func_ = callExpr_->getDirectCallee();
        if(interp_->checkFuncExists(func_)){
            std::vector<const clang::Stmt*> operands_;
            for(auto arg : callExpr_->arguments()){
                std::string typestr = "";
                if(false){}
    
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                    ROSGeometryPoseWithCovarianceStamped m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorgeometry_msgs::TransformStamped" or typestr =="geometry_msgs::TransformStamped" or typestr == "const geometry_msgs::TransformStamped" or typestr == "class geometry_msgs::TransformStamped" or typestr == "const class geometry_msgs::TransformStamped" or typestr ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){
                    ROSGeomTransformStamped m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,false);
                if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                    ROSTF2TransformStamped m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorgeometry_msgs::PoseStamped" or typestr =="geometry_msgs::PoseStamped" or typestr == "const geometry_msgs::PoseStamped" or typestr == "class geometry_msgs::PoseStamped" or typestr == "const class geometry_msgs::PoseStamped" or typestr ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                    ROSGeomPoseStamped m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                    ROSGeomQuaternion m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorros::DurationBase" or typestr =="ros::DurationBase" or typestr == "const ros::DurationBase" or typestr == "class ros::DurationBase" or typestr == "const class ros::DurationBase" or typestr ==  "::ros::DurationBase_<allocator<void> >"){
                    ROSDurationBaseMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                    ROSTF2Quaternion m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                    ROSTFQuaternion m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                    ROSTF2Transform m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorros::TimeBase" or typestr =="ros::TimeBase" or typestr == "const ros::TimeBase" or typestr == "class ros::TimeBase" or typestr == "const class ros::TimeBase" or typestr ==  "::ros::TimeBase_<allocator<void> >"){
                    ROSTimeBaseMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                    ROSDurationMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                    ROSTF2DurationMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                    ROSTFTransformMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                    ROSTF2Vector3Matcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                    ROSTFVector3Matcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                    ROSTimeMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                    ROSTFScalarMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                    DoubleMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operator_Bool" or typestr =="_Bool" or typestr == "const _Bool" or typestr == "class _Bool" or typestr == "const class _Bool" or typestr ==  "::_Bool_<allocator<void> >"){
                    ROSBoolMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                    FloatMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                    ROSBooleanMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
                typestr = this->getTypeAsString(arg,true);
                if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                    VoidMatcher m{ this->context_, this->interp_};
                    m.setup();
                    m.visit(*arg);
                    if (m.getChildExprStore())
                        operands_.push_back(m.getChildExprStore());
                    continue;
                }
            }
            interp_->buffer_link(func_);
            interp_->buffer_operands(operands_);
            interp_->mkNode("CALL_R3",callExpr_,true);
            this->childExprStore_ = (clang::Stmt*)callExpr_;
            return;
        }
    }

	
	arg_decay_exist_predicates["memberExpr_tf2::Vector3"] = [=](std::string typenm){
    if(false){return false;}
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
    else { return false; }
    };
    if(memberExpr_){
        auto inner = memberExpr_->getBase();
        auto typestr = this->getTypeAsString(inner,true);
        if(false){}
        else if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
            ROSTF2Vector3Matcher innerm{this->context_,this->interp_};
            innerm.setup();
            innerm.visit(*inner);
            this->childExprStore_ = (clang::Stmt*)innerm.getChildExprStore();
            return;
        }

    }

	
	arg_decay_exist_predicates["implicitCastExpr_tf2::Vector3"] = [=](std::string typenm){
        if(false){return false; }
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
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
        else if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
            ROSTF2Vector3Matcher innerm{this->context_,this->interp_};
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

	
	arg_decay_exist_predicates["cxxBindTemporaryExpr_tf2::Vector3"] = [=](std::string typenm){
        if(false){ return false; }
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if (cxxBindTemporaryExpr_)
    {
        ROSTF2Vector3Matcher exprMatcher{ context_, interp_};
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

	
	arg_decay_exist_predicates["materializeTemporaryExpr_tf2::Vector3"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
        else { return false; }
    };
    if (materializeTemporaryExpr_)
        {
            ROSTF2Vector3Matcher exprMatcher{ context_, interp_};
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

	
	arg_decay_exist_predicates["parenExpr_tf2::Vector3"] = [=](std::string typenm){
        if(false){return false;}
		else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ return true; }
        else { return false; } 
    };
    if (parenExpr_)
    {
        ROSTF2Vector3Matcher inner{ context_, interp_};
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
            ROSTF2Vector3Matcher exprMatcher{ context_, interp_};
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
            ROSTF2Vector3Matcher exprMatcher{ context_, interp_};
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

