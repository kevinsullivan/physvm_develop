#include "AST.h"
#include <memory>
#include <iostream>

namespace ast{

std::shared_ptr<NodeContainer> mkContainer (UnitDecl* unitDecl){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::UnitDecl__;
    nc->ASTNode_.UnitDecl_ = unitDecl;
    return nc;
};

std::shared_ptr<NodeContainer> mkContainer (FuncDecl* funcDecl){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::FuncDecl__;
    nc->ASTNode_.FuncDecl_ = funcDecl;
    return nc;
};

std::shared_ptr<NodeContainer> mkContainer (Stmt* stmt){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::Stmt__;
    nc->ASTNode_.Stmt_ = stmt;
    return nc;
};

std::shared_ptr<NodeContainer> mkContainer (VarDecl* varDecl){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::VarDecl__;
    nc->ASTNode_.VarDecl_ = varDecl;
    return nc;
};

std::shared_ptr<NodeContainer> mkContainer (ConsDecl* consDecl){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::ConsDecl__;
    nc->ASTNode_.ConsDecl_ = consDecl;
    return nc;
};

std::shared_ptr<NodeContainer> mkContainer (ParamDecl* paramDecl){
    auto nc = std::make_shared<NodeContainer>(NodeContainer());
    nc->ASTTag_ = ASTTag::ParamDecl__;
    nc->ASTNode_.ParamDecl_ = paramDecl;
    return nc;
};

}//end ast