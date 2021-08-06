

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/AST/Decl.h"
#include <vector>
#include <iostream>

#include "ROS1ProgramMatcher.h"
#include "ROSStatementMatcher.h"

//#include "../ASTToCoords.h"

int TUDCount;

using namespace clang::ast_matchers;

void ROS1ProgramMatcher::setup()
    {
        //valid without pointers!
        /*  DeclarationMatcher root =//isMain() <-- certain __important__ matchers like this are missing. find them.
              functionDecl(has(compoundStmt().bind("MainCompoundStatement")
              )).bind("MainCandidate");
      */
        DeclarationMatcher roott =
            translationUnitDecl().bind("MainProg");

        //localFinder_.addMatcher(root, this);
        localFinder_.addMatcher(roott, this);
    };

    /*
    This is a callback method that gets called when Clang matches on a pattern set up in the search method above.
    */
    void ROS1ProgramMatcher::run(const MatchFinder::MatchResult &Result)
    {
        //auto mainCompoundStatement = Result.Nodes.getNodeAs<clang::CompoundStmt>("MainCompoundStatement");
        //auto mainCandidate = Result.Nodes.getNodeAs<clang::FunctionDecl>("MainCandidate");

        auto tud = Result.Nodes.getNodeAs<clang::TranslationUnitDecl>("MainProg");

        auto srcs = this->interp_->getSources();
        /*
            std::cout<<"Sources:\n";
            for(auto src:srcs)
            {
                std::cout<<src<<"\n";
            }*/

        if (tud)
        {
            std::cout << "TranslationUnitDeclCounter:" << std::to_string(TUDCount++) << "\n";
            if (TUDCount > 1)
            {
                std::cout << "WARNING : UPDATE  LOGIC TO HANDLE MULTIPLE TRANSLATION UNITS.";
                throw "Bad Code!";
            }
        }
        std::vector <const clang::FunctionDecl*> globals;
        if (tud)
        {
            //auto tud = clang::TranslationUnitDecl::castFromDeclContext(mainCandidate->getParent());
            auto & srcm = this->context_->getSourceManager();
            for (auto d : tud->decls())
            {

                if (auto fn = clang::dyn_cast<clang::FunctionDecl>(d))
            {
                auto loc = fn->getLocation();

                auto srcloc = srcm.getFileLoc(loc);
                auto locstr = srcloc.printToString(srcm);

                for (auto & src: srcs)
                {
                    if (locstr.find(src) != string::npos)
                    {
                        std::vector <const clang::Stmt*> stmts;
                        if (fn->isMain())
                        {
                            if (auto cmpd = clang::dyn_cast<clang::CompoundStmt>(fn->getBody())){

                                for (auto it = cmpd->body_begin(); it != cmpd->body_end(); it++)
                                {
                                    ROSStatementMatcher rootMatcher{ this->context_, this->interp_};
                                    rootMatcher.setup();
                                    //std::cout<<"dumping\n";
                                    //(*it)->dump();
                                    //std::cout<<"dumped\n";
                                    rootMatcher.visit(**it);
                                    if (rootMatcher.getChildExprStore())
                                    {
                                        //std::cout<<"child!!!\n";
                                        //rootMatcher.getChildExprStore()->dump();
                                        stmts.push_back(rootMatcher.getChildExprStore());
                                    }
                                }
                                this->interp_->buffer_body(stmts);
                                this->interp_->mkNode("COMPOUND_STMT", cmpd, false);
                                this->interp_->buffer_body(cmpd);
                                this->interp_->mkNode("FUNCTION_MAIN", fn, false);
                                globals.push_back(fn);

                            }
                            else
                            {
                                std::cout << "Warning : Unable to parse main function? \n";
                                fn->getBody()->dump();
                            }
                        }
                        else{
                            auto retType = (clang::QualType)fn->getReturnType();
        
                            auto fbody = fn->getBody();

                            ROSStatementMatcher bodym{ this->context_, this->interp_};
                            bodym.setup();
                            bodym.visit(*fbody);

                            if(!bodym.getChildExprStore()){
                                std::cout<<"No detected nodes in body of function\n";
                            }

                            std::vector<const clang::ParmVarDecl*> valid_params_;
                            auto params_ = fn->parameters();
                            if(params_.size() > 0){
                                for(auto param_ : params_){
                                    auto typestr = param_->getType().getAsString();
                                    if(false){}
                                 
                                    else if(typestr == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typestr =="geometry_msgs::PoseWithCovarianceStamped" or typestr == "const geometry_msgs::PoseWithCovarianceStamped" or typestr == "class geometry_msgs::PoseWithCovarianceStamped" or typestr == "const class geometry_msgs::PoseWithCovarianceStamped" or typestr ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorgeometry_msgs::TransformStamped" or typestr =="geometry_msgs::TransformStamped" or typestr == "const geometry_msgs::TransformStamped" or typestr == "class geometry_msgs::TransformStamped" or typestr == "const class geometry_msgs::TransformStamped" or typestr ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf2::Stamped<tf2::Transform>" or typestr =="tf2::Stamped<tf2::Transform>" or typestr == "const tf2::Stamped<tf2::Transform>" or typestr == "class tf2::Stamped<tf2::Transform>" or typestr == "const class tf2::Stamped<tf2::Transform>" or typestr ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorgeometry_msgs::PoseStamped" or typestr =="geometry_msgs::PoseStamped" or typestr == "const geometry_msgs::PoseStamped" or typestr == "class geometry_msgs::PoseStamped" or typestr == "const class geometry_msgs::PoseStamped" or typestr ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorgeometry_msgs::Quaternion" or typestr =="geometry_msgs::Quaternion" or typestr == "const geometry_msgs::Quaternion" or typestr == "class geometry_msgs::Quaternion" or typestr == "const class geometry_msgs::Quaternion" or typestr ==  "::geometry_msgs::Quaternion_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorros::DurationBase" or typestr =="ros::DurationBase" or typestr == "const ros::DurationBase" or typestr == "class ros::DurationBase" or typestr == "const class ros::DurationBase" or typestr ==  "::ros::DurationBase_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf2::Quaternion" or typestr =="tf2::Quaternion" or typestr == "const tf2::Quaternion" or typestr == "class tf2::Quaternion" or typestr == "const class tf2::Quaternion" or typestr ==  "::tf2::Quaternion_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf::Quaternion" or typestr =="tf::Quaternion" or typestr == "const tf::Quaternion" or typestr == "class tf::Quaternion" or typestr == "const class tf::Quaternion" or typestr ==  "::tf::Quaternion_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf2::Transform" or typestr =="tf2::Transform" or typestr == "const tf2::Transform" or typestr == "class tf2::Transform" or typestr == "const class tf2::Transform" or typestr ==  "::tf2::Transform_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorros::TimeBase" or typestr =="ros::TimeBase" or typestr == "const ros::TimeBase" or typestr == "class ros::TimeBase" or typestr == "const class ros::TimeBase" or typestr ==  "::ros::TimeBase_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorros::Duration" or typestr =="ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration" or typestr ==  "::ros::Duration_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf2::Duration" or typestr =="tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration" or typestr ==  "::tf2::Duration_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf::Transform" or typestr =="tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform" or typestr ==  "::tf::Transform_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R4X4", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf2::Vector3" or typestr =="tf2::Vector3" or typestr == "const tf2::Vector3" or typestr == "class tf2::Vector3" or typestr == "const class tf2::Vector3" or typestr ==  "::tf2::Vector3_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R3", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortf::Vector3" or typestr =="tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3" or typestr ==  "::tf::Vector3_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R3", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorros::Time" or typestr =="ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time" or typestr ==  "::ros::Time_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatortfScalar" or typestr =="tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar" or typestr ==  "::tfScalar_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatordouble" or typestr =="double" or typestr == "const double" or typestr == "class double" or typestr == "const class double" or typestr ==  "::double_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operator_Bool" or typestr =="_Bool" or typestr == "const _Bool" or typestr == "class _Bool" or typestr == "const class _Bool" or typestr ==  "::_Bool_<allocator<void> >"){
                                        //interp_->mkFunctionParam("BOOL", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorfloat" or typestr =="float" or typestr == "const float" or typestr == "class float" or typestr == "const class float" or typestr ==  "::float_<allocator<void> >"){
                                        //interp_->mkFunctionParam("R1", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorbool" or typestr =="bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool" or typestr ==  "::bool_<allocator<void> >"){
                                        //interp_->mkFunctionParam("BOOL", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "operatorvoid" or typestr =="void" or typestr == "const void" or typestr == "class void" or typestr == "const class void" or typestr ==  "::void_<allocator<void> >"){
                                        //interp_->mkFunctionParam("Void", param_);

                                        if(auto dc = clang::dyn_cast<clang::ParmVarDecl>(param_)){
                                            interp_->mkNode("FUNCTION_PARAM", param_,false);
                                            valid_params_.push_back(const_cast<clang::ParmVarDecl*>(param_));
                                        }
                                        else
                                        {
                                            std::cout << "Warning : Param is not a ParmVarDecl\n";
                                            param_->dump();
                                        }
                                        //valid_params_.push_back(param_);
                                    }
                                }
                            }
                            bool hasReturn = false;
                            auto nodePrefix = std::string("");
                            auto typenm = retType.getAsString();
                            if(false){}
                        
							else if(typenm == "operatorgeometry_msgs::PoseWithCovarianceStamped" or typenm =="geometry_msgs::PoseWithCovarianceStamped" or typenm == "const geometry_msgs::PoseWithCovarianceStamped" or typenm == "class geometry_msgs::PoseWithCovarianceStamped" or typenm == "const class geometry_msgs::PoseWithCovarianceStamped" or typenm ==  "::geometry_msgs::PoseWithCovarianceStamped_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatorgeometry_msgs::TransformStamped" or typenm =="geometry_msgs::TransformStamped" or typenm == "const geometry_msgs::TransformStamped" or typenm == "class geometry_msgs::TransformStamped" or typenm == "const class geometry_msgs::TransformStamped" or typenm ==  "::geometry_msgs::TransformStamped_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatortf2::Stamped<tf2::Transform>" or typenm =="tf2::Stamped<tf2::Transform>" or typenm == "const tf2::Stamped<tf2::Transform>" or typenm == "class tf2::Stamped<tf2::Transform>" or typenm == "const class tf2::Stamped<tf2::Transform>" or typenm ==  "::tf2::Stamped<tf2::Transform>_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatorgeometry_msgs::PoseStamped" or typenm =="geometry_msgs::PoseStamped" or typenm == "const geometry_msgs::PoseStamped" or typenm == "class geometry_msgs::PoseStamped" or typenm == "const class geometry_msgs::PoseStamped" or typenm ==  "::geometry_msgs::PoseStamped_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatorgeometry_msgs::Quaternion" or typenm =="geometry_msgs::Quaternion" or typenm == "const geometry_msgs::Quaternion" or typenm == "class geometry_msgs::Quaternion" or typenm == "const class geometry_msgs::Quaternion" or typenm ==  "::geometry_msgs::Quaternion_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4"; }
							else if(typenm == "operatorros::DurationBase" or typenm =="ros::DurationBase" or typenm == "const ros::DurationBase" or typenm == "class ros::DurationBase" or typenm == "const class ros::DurationBase" or typenm ==  "::ros::DurationBase_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatortf2::Quaternion" or typenm =="tf2::Quaternion" or typenm == "const tf2::Quaternion" or typenm == "class tf2::Quaternion" or typenm == "const class tf2::Quaternion" or typenm ==  "::tf2::Quaternion_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4"; }
							else if(typenm == "operatortf::Quaternion" or typenm =="tf::Quaternion" or typenm == "const tf::Quaternion" or typenm == "class tf::Quaternion" or typenm == "const class tf::Quaternion" or typenm ==  "::tf::Quaternion_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4"; }
							else if(typenm == "operatortf2::Transform" or typenm =="tf2::Transform" or typenm == "const tf2::Transform" or typenm == "class tf2::Transform" or typenm == "const class tf2::Transform" or typenm ==  "::tf2::Transform_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatorros::TimeBase" or typenm =="ros::TimeBase" or typenm == "const ros::TimeBase" or typenm == "class ros::TimeBase" or typenm == "const class ros::TimeBase" or typenm ==  "::ros::TimeBase_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatorros::Duration" or typenm =="ros::Duration" or typenm == "const ros::Duration" or typenm == "class ros::Duration" or typenm == "const class ros::Duration" or typenm ==  "::ros::Duration_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatortf2::Duration" or typenm =="tf2::Duration" or typenm == "const tf2::Duration" or typenm == "class tf2::Duration" or typenm == "const class tf2::Duration" or typenm ==  "::tf2::Duration_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatortf::Transform" or typenm =="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform" or typenm ==  "::tf::Transform_<allocator<void> >"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm == "operatortf2::Vector3" or typenm =="tf2::Vector3" or typenm == "const tf2::Vector3" or typenm == "class tf2::Vector3" or typenm == "const class tf2::Vector3" or typenm ==  "::tf2::Vector3_<allocator<void> >"){ hasReturn = true; nodePrefix = "R3"; }
							else if(typenm == "operatortf::Vector3" or typenm =="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3" or typenm ==  "::tf::Vector3_<allocator<void> >"){ hasReturn = true; nodePrefix = "R3"; }
							else if(typenm == "operatorros::Time" or typenm =="ros::Time" or typenm == "const ros::Time" or typenm == "class ros::Time" or typenm == "const class ros::Time" or typenm ==  "::ros::Time_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatortfScalar" or typenm =="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar" or typenm ==  "::tfScalar_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatordouble" or typenm =="double" or typenm == "const double" or typenm == "class double" or typenm == "const class double" or typenm ==  "::double_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operator_Bool" or typenm =="_Bool" or typenm == "const _Bool" or typenm == "class _Bool" or typenm == "const class _Bool" or typenm ==  "::_Bool_<allocator<void> >"){ hasReturn = true; nodePrefix = "BOOL"; }
							else if(typenm == "operatorfloat" or typenm =="float" or typenm == "const float" or typenm == "class float" or typenm == "const class float" or typenm ==  "::float_<allocator<void> >"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm == "operatorbool" or typenm =="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool" or typenm ==  "::bool_<allocator<void> >"){ hasReturn = true; nodePrefix = "BOOL"; }
							else if(typenm == "operatorvoid" or typenm =="void" or typenm == "const void" or typenm == "class void" or typenm == "const class void" or typenm ==  "::void_<allocator<void> >"){ hasReturn = true; nodePrefix = "Void"; }
                            else {}
        

                            if(valid_params_.size()>0){
                                interp_->buffer_operands(valid_params_);
            
                            }
                            if(bodym.getChildExprStore())
                                interp_->buffer_body(bodym.getChildExprStore());
                            if(hasReturn){
                                interp_->mkFunctionWithReturn(nodePrefix, fn);
                            }
                            else{
                                interp_->mkFunction(fn);
                            }
                            globals.push_back(fn);
                                    
                        }
                    }
                }
            }
        }

        //this->interp_->mkSEQ_GLOBALSTMT(tud, globals);
        this->interp_->buffer_body(globals);
        this->interp_->mkNode("COMPOUND_GLOBAL", tud, false, true);
    }
};
