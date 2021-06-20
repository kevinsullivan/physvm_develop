

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
                            /*
                            auto typeDetector = [=](std::string typenm){
                                if(false){return false;}
                        
			else if(typenm=="ros::Duration" or typenm == "const ros::Duration" or typenm == "class ros::Duration" or typestr == "const class ros::Duration"){ return true; }
			else if(typenm=="tf2::Duration" or typenm == "const tf2::Duration" or typenm == "class tf2::Duration" or typestr == "const class tf2::Duration"){ return true; }
			else if(typenm=="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typestr == "const class tf::Transform"){ return true; }
			else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typestr == "const class tf::Vector3"){ return true; }
			else if(typenm=="ros::Time" or typenm == "const ros::Time" or typenm == "class ros::Time" or typestr == "const class ros::Time"){ return true; }
			else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typestr == "const class tfScalar"){ return true; }
			else if(typenm=="double" or typenm == "const double" or typenm == "class double" or typestr == "const class double"){ return true; }
			else if(typenm=="float" or typenm == "const float" or typenm == "class float" or typestr == "const class float"){ return true; }
			else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typestr == "const class bool"){ return true; }
                                else { return false;}
                            };*/

                            ROSStatementMatcher bodym{ this->context_, this->interp_};
                            bodym.setup();
                            bodym.visit(*fbody);

                            if(!bodym.getChildExprStore()){
                                std::cout<<"No detected nodes in body of function\n";
                                return;
                            }

                            std::vector<const clang::ParmVarDecl*> valid_params_;
                            auto params_ = fn->parameters();
                            if(params_.size() > 0){
                                for(auto param_ : params_){
                                    auto typestr = param_->getType().getAsString();
                                    if(false){}
                                 
                                    else if(typestr == "ros::Duration" or typestr == "const ros::Duration" or typestr == "class ros::Duration" or typestr == "const class ros::Duration"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "tf2::Duration" or typestr == "const tf2::Duration" or typestr == "class tf2::Duration" or typestr == "const class tf2::Duration"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "tf::Transform" or typestr == "const tf::Transform" or typestr == "class tf::Transform" or typestr == "const class tf::Transform"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "tf::Vector3" or typestr == "const tf::Vector3" or typestr == "class tf::Vector3" or typestr == "const class tf::Vector3"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "ros::Time" or typestr == "const ros::Time" or typestr == "class ros::Time" or typestr == "const class ros::Time"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "tfScalar" or typestr == "const tfScalar" or typestr == "class tfScalar" or typestr == "const class tfScalar"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "double" or typestr == "const double" or typestr == "class double" or typestr == "const class double"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "float" or typestr == "const float" or typestr == "class float" or typestr == "const class float"){
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
                                        valid_params_.push_back(param_);
                                    }
                                    else if(typestr == "bool" or typestr == "const bool" or typestr == "class bool" or typestr == "const class bool"){
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
                                        valid_params_.push_back(param_);
                                    }
                                }
                            }
                            bool hasReturn = false;
                            auto nodePrefix = std::string("");
                            auto typenm = retType.getAsString();
                            if(false){}
                        
							else if(typenm=="ros::Duration" or typenm == "const ros::Duration" or typenm == "class ros::Duration" or typenm == "const class ros::Duration"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="tf2::Duration" or typenm == "const tf2::Duration" or typenm == "class tf2::Duration" or typenm == "const class tf2::Duration"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="tf::Transform" or typenm == "const tf::Transform" or typenm == "class tf::Transform" or typenm == "const class tf::Transform"){ hasReturn = true; nodePrefix = "R4X4"; }
							else if(typenm=="tf::Vector3" or typenm == "const tf::Vector3" or typenm == "class tf::Vector3" or typenm == "const class tf::Vector3"){ hasReturn = true; nodePrefix = "R3"; }
							else if(typenm=="ros::Time" or typenm == "const ros::Time" or typenm == "class ros::Time" or typenm == "const class ros::Time"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="tfScalar" or typenm == "const tfScalar" or typenm == "class tfScalar" or typenm == "const class tfScalar"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="double" or typenm == "const double" or typenm == "class double" or typenm == "const class double"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="float" or typenm == "const float" or typenm == "class float" or typenm == "const class float"){ hasReturn = true; nodePrefix = "R1"; }
							else if(typenm=="bool" or typenm == "const bool" or typenm == "class bool" or typenm == "const class bool"){ hasReturn = true; nodePrefix = "BOOL"; }
                            else {}
        

                            if(valid_params_.size()>0){
                                interp_->buffer_operands(valid_params_);
            
                            }
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
