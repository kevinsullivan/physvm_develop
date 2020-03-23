#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include <vector>

#include "Interpretation.h"


#include "StatementProductionMatcher.h"
#include "VectorExprMatcher.h"
#include "ScalarExprMatcher.h"

#include <iostream>

/*
    virtual void Traverse() = 0;
    virtual void BuildRepresentation() = 0;
    virtual StatementMatcher GetStatementMatcher() = 0;
    virtual void run(const MatchFinder::MatchResult &Result) = 0;

    
STMT := VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | VEC_EXPR | SCALAR_EXPR | DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR
*/


void StatementProductionMatcher::search(){
    StatementMatcher scalarDecl =
        declStmt(has(varDecl(
            allOf(hasType(asString("float")),anyOf(has(expr().bind("ScalarDeclRV")), has(binaryOperator().bind("ScalarDeclRV")))))
                .bind("ScalarVarDecl")))
                .bind("ScalarDeclStatement");
    StatementMatcher vectorDecl =
       declStmt(has(varDecl(has(
           expr().bind("VectorDeclRV"))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
           //cxxConstructExpr(allOf(hasType(asString("class Vec")),has(expr().bind("VectorDeclRV")))))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
    StatementMatcher floatExpr = 
        expr(hasType(asString("float"))).bind("ScalarExprStatement");
    StatementMatcher vectorExpr = 
        expr(hasType(asString("Vec"))).bind("VectorExprStatement");
    StatementMatcher scalarAssign =
        binaryOperator(allOf(
            hasOperatorName("="),
            has(declRefExpr(hasType(asString("float"))).bind("ScalarAssignLV")), 
            hasRHS(expr().bind("ScalarAssignRV"))
        )).bind("ScalarAssignStatement");
    StatementMatcher vectorAssign = 
        cxxOperatorCallExpr(allOf(hasOverloadedOperatorName("="),
            has(declRefExpr(hasType(asString("class Vec"))).bind("VectorAssignLV")), has(expr().bind("VectorAssignRV")))).bind("VectorAssignmentStatement");

    localFinder_.addMatcher(scalarDecl, this);
    localFinder_.addMatcher(vectorDecl, this);
    localFinder_.addMatcher(floatExpr, this);
    localFinder_.addMatcher(vectorExpr, this);
    localFinder_.addMatcher(scalarAssign, this);
    localFinder_.addMatcher(vectorAssign, this);
};

void StatementProductionMatcher::run(const MatchFinder::MatchResult &Result){
    
    auto scalarDecl = Result.Nodes.getNodeAs<clang::DeclStmt>("ScalarDeclStatement");
    auto scalarVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("ScalarVarStatement");
    auto scalarDeclRV = Result.Nodes.getNodeAs<clang::Expr>("ScalarDeclRV");
    auto vectorDecl = Result.Nodes.getNodeAs<clang::DeclStmt>("VectorDeclStatement");
    auto vectorVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("VectorVarDecl");
    auto vectorDeclRV = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("VectorDeclRV");
    auto floatExpr = Result.Nodes.getNodeAs<clang::Expr>("ScalarExprStatement");
    auto vecExpr = Result.Nodes.getNodeAs<clang::Expr>("VectorExprStatement");
    auto scalarAssign = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignStatement");
    auto scalarAssignLV = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignLV");
    auto scalarAssignRV = Result.Nodes.getNodeAs<clang::Expr>("ScalarAssignRV");
    auto vectorAssign = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignmentStatement");
    auto vectorAssignLV = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignLV");
    auto vectorAssignRV = Result.Nodes.getNodeAs<clang::Expr>("VectorAssignRV");

    vectorDecl->dump();

    if(scalarDecl or scalarVarDecl or scalarDeclRV){
        if(scalarDecl and scalarVarDecl and scalarDeclRV){
            this->interp_->mkVecIdent(scalarVarDecl);
            this->interp_->mkVector_Def(scalarDecl, scalarVarDecl, scalarDeclRV);
            ScalarExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*scalarDeclRV);
        }
        else{
            //log error
        }
    }
    else if(vectorDecl or vectorVarDecl or vectorDeclRV){
        if(vectorDecl and vectorVarDecl and vectorDeclRV){
            //vectorVarDecl->dump();
            vectorDeclRV->dump();
            //vectorDeclRV->getConstructor()->dump();
            //vectorDeclRV->getConstructor()->getDefinition()->dump();

            //std::cout<<

            std::cout<<"tmp"<<vectorDeclRV->getConstructor()->getDefinition()->getNameInfo().getAsString()<<std::endl;

            std::cout<<"tmp"<<vectorDeclRV->getConstructor()->getDefinition()->getName().str()<<std::endl;

            this->interp_->mkVecIdent(vectorVarDecl);
            this->interp_->mkVector_Def(vectorDecl, vectorVarDecl, vectorDeclRV);
            VectorExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*vectorDeclRV);

        }
        else{
            //log error
        }
    }
    else if(floatExpr){
            ScalarExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*floatExpr);

    }
    else if(vecExpr){
            VectorExprMatcher exprMatcher{this->context_};
            exprMatcher.search();
            exprMatcher.visit(*vecExpr);


    }
    else if(scalarAssign or scalarAssignLV or scalarAssignRV){
        if(scalarAssign and scalarAssignLV and scalarAssignRV){
            //NOT IMPLEMENTED IN BACKEND
        }
        else{
            //log error
        }
    }
    else if(vectorAssign or vectorAssignLV or vectorAssignRV){
        if(vectorAssign and vectorAssignLV and vectorAssignRV){
            //NOT IMPLEMENTED IN BACKEND
        }
        else{
            //log error
        }
    }

};