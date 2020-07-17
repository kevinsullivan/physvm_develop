
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"


#include "TempROSMatcher.h"

void TempROSMatcher::search(){
    StatementMatcher exprWithCleanupsDiscard = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher implicitCastExprDiscard = 
        implicitCastExpr().bind("ImplicitCastExprDiscard"); //could also potentially use ignoringImplicit(expr().bind).bind...but need to modify EVERY matcher to handle this, then
    StatementMatcher cxxBindTemporaryExprDiscard =
        cxxBindTemporaryExpr(has(expr().bind("CXXBindTemporaryExprChild"))).bind("CXXBindTemporaryExprDiscard");
    StatementMatcher materializeTemporaryExprDiscard =
        materializeTemporaryExpr(has(expr().bind("MaterializeTemporaryExprChild"))).bind("MaterializeTemporaryExprDiscard");
    
  /*  StatementMatcher transformExprWithCleanups = 
        exprWithCleanups(has(expr().bind("UsefulExpr"))).bind("ExprWithCleanupsDiscard");
    StatementMatcher transformImplicitCastExpr = 
        implicitCastExpr().bind("ImplicitCastExprDiscard"); //could also potentially use ignoringImplicit(expr().bind).bind...but need to modify EVERY matcher to handle this, then
    StatementMatcher transformCXXConstructExpr = //could also use isMoveConstructor / isCopyConstructor
        cxxConstructExpr(allOf(unless(argumentCountIs(3)),has(expr().bind("CXXConstructExprChild")))).bind("CXXConstructExprDiscard");
    StatementMatcher transformCXXBindTemporaryExpr =
        cxxBindTemporaryExpr(has(expr().bind("CXXBindTemporaryExprChild"))).bind("CXXBindTemporaryExprDiscard");
    StatementMatcher transformMaterializeTemporaryExpr =
        materializeTemporaryExpr(has(expr().bind("MaterializeTemporaryExprChild"))).bind("MaterializeTemporaryExprDiscard");
    
    StatementMatcher transformParenExpr =
        parenExpr(allOf(hasType(asString("class Transform")),has(expr().bind("TransformInnerExpr")))).bind("TransformParenExpr");
    StatementMatcher transformVarExpr = 
        declRefExpr(hasType(asString("class Transform"))).bind("TransformDeclRefExpr");
    StatementMatcher transformLiteral = 
        //anyOf(
        //    cxxConstructExpr(allOf(hasType(asString("class Transform")),hasDeclaration(namedDecl(hasName("void (float, float, float)"))))).bind("TransformLiteralExpr"),
            cxxConstructExpr(allOf(
                hasType(asString("class Transform")),
                hasArgument(0, expr(hasType(asString("class Vec"))).bind("VecArg1")),
                hasArgument(1, expr(hasType(asString("class Vec"))).bind("VecArg2")),
                hasArgument(2, expr(hasType(asString("class Vec"))).bind("VecArg3"))
            )).bind("TransformLiteralExpr");

        //);
    StatementMatcher transformComposeExpr =
        cxxMemberCallExpr(allOf(
            hasType(asString("class Transform")),
            has(memberExpr(allOf(has(expr().bind("TransformComposeMember")), member(hasName("compose"))))), 
            hasArgument(0,expr().bind("TransformComposeArgument")))).bind("TransformComposeExpr");
*/
/*

DeclStmt 0x558e2b418dd0 <line:104:5, line:106:45>
    | |-VarDecl 0x558e2b4188d8 <line:104:5, line:105:46> col:9 used tf_start_point 'tf::Point':'tf::Vector3' cinit
    | | `-ExprWithCleanups 0x558e2b418b10 <col:26, col:46> 'tf::Point':'tf::Vector3'
    | |   `-CXXConstructExpr 0x558e2b418ad8 <col:26, col:46> 'tf::Point':'tf::Vector3' 'void (tf::Vector3 &&) noexcept' elidable
    | |     `-MaterializeTemporaryExpr 0x558e2b418ac0 <col:26, col:46> 'tf::Point':'tf::Vector3' xvalue
    | |       `-CXXTemporaryObjectExpr 0x558e2b418a70 <col:26, col:46> 'tf::Point':'tf::Vector3' 'void (const tfScalar &, const tfScalar &, const tfScalar &)'
    | |         |-MaterializeTemporaryExpr 0x558e2b4189f8 <col:36> 'const tfScalar':'const double' lvalue
    | |         | `-ImplicitCastExpr 0x558e2b4189e0 <col:36> 'const tfScalar':'const double' <IntegralToFloating>
    | |         |   `-IntegerLiteral 0x558e2b418980 <col:36> 'int' 10
    | |         |-MaterializeTemporaryExpr 0x558e2b418a28 <col:40> 'const tfScalar':'const double' lvalue
    | |         | `-ImplicitCastExpr 0x558e2b418a10 <col:40> 'const tfScalar':'const double' <IntegralToFloating>
    | |         |   `-IntegerLiteral 0x558e2b4189a0 <col:40> 'int' 10
    | |         `-MaterializeTemporaryExpr 0x558e2b418a58 <col:44> 'const tfScalar':'const double' lvalue
    | |           `-ImplicitCastExpr 0x558e2b418a40 <col:44> 'const tfScalar':'const double' <IntegralToFloating>
    | |             `-IntegerLiteral 0x558e2b4189c0 <col:44> 'int' 10
    | `-VarDecl 0x558e2b418b48 <line:104:5, line:106:44> col:9 used tf_end_point 'tf::Point':'tf::Vector3' cinit
    |   `-ExprWithCleanups 0x558e2b418da0 <col:24, col:44> 'tf::Point':'tf::Vector3'
    |     `-CXXConstructExpr 0x558e2b418d68 <col:24, col:44> 'tf::Point':'tf::Vector3' 'void (tf::Vector3 &&) noexcept' elidable
    |       `-MaterializeTemporaryExpr 0x558e2b418d50 <col:24, col:44> 'tf::Point':'tf::Vector3' xvalue
    |         `-CXXTemporaryObjectExpr 0x558e2b418d00 <col:24, col:44> 'tf::Point':'tf::Vector3' 'void (const tfScalar &, const tfScalar &, const tfScalar &)'
    |           |-MaterializeTemporaryExpr 0x558e2b418c88 <col:34> 'const tfScalar':'const double' lvalue
    |           | `-ImplicitCastExpr 0x558e2b418c70 <col:34> 'const tfScalar':'const double' <IntegralToFloating>
    |           |   `-IntegerLiteral 0x558e2b418bf0 <col:34> 'int' 20
    |           |-MaterializeTemporaryExpr 0x558e2b418cb8 <col:38, col:39> 'const tfScalar':'const double' lvalue
    |           | `-ImplicitCastExpr 0x558e2b418ca0 <col:38, col:39> 'const tfScalar':'const double' <IntegralToFloating>
    |           |   `-UnaryOperator 0x558e2b418c30 <col:38, col:39> 'int' prefix '-'
    |           |     `-IntegerLiteral 0x558e2b418c10 <col:39> 'int' 2
    |           `-MaterializeTemporaryExpr 0x558e2b418ce8 <col:42> 'const tfScalar':'const double' lvalue
    |             `-ImplicitCastExpr 0x558e2b418cd0 <col:42> 'const tfScalar':'const double' <IntegralToFloating>
    |               `-IntegerLiteral 0x558e2b418c50 <col:42> 'int' 12
    `-DeclStmt 0x558e2b419080 <line:108:5, col:64>
      `-VarDecl 0x558e2b418e30 <col:5, col:50> col:17 tf_displacement 'tf::Vector3':'tf::Vector3' cinit
        `-ExprWithCleanups 0x558e2b419068 <col:35, col:50> 'tf::Vector3':'tf::Vector3'
          `-CXXConstructExpr 0x558e2b419030 <col:35, col:50> 'tf::Vector3':'tf::Vector3' 'void (tf::Vector3 &&) noexcept' elidable
            `-MaterializeTemporaryExpr 0x558e2b419018 <col:35, col:50> 'tf::Vector3' xvalue
              `-CXXOperatorCallExpr 0x558e2b418fd0 <col:35, col:50> 'tf::Vector3'
                |-ImplicitCastExpr 0x558e2b418fb8 <col:48> 'tf::Vector3 (*)(const tf::Vector3 &, const tf::Vector3 &)' <FunctionToPointerDecay>
                | `-DeclRefExpr 0x558e2b418f90 <col:48> 'tf::Vector3 (const tf::Vector3 &, const tf::Vector3 &)' lvalue Function 0x558e2b12c080 'operator-' 'tf::Vector3 (const tf::Vector3 &, const tf::Vector3 &)'
                |-ImplicitCastExpr 0x558e2b418f60 <col:35> 'const tf::Point':'const tf::Vector3' lvalue <NoOp>
                | `-DeclRefExpr 0x558e2b418e90 <col:35> 'tf::Point':'tf::Vector3' lvalue Var 0x558e2b418b48 'tf_end_point' 'tf::Point':'tf::Vector3'
                `-ImplicitCastExpr 0x558e2b418f78 <col:50> 'const tf::Point':'const tf::Vector3' lvalue <NoOp>
                  `-DeclRefExpr 0x558e2b418eb8 <col:50> 'tf::Point':'tf::Vector3' lvalue Var 0x558e2b4188d8 'tf_start_point' 'tf::Point':'tf::Vector3'

*/
/*
StatementMatcher vectorDecl =
       declStmt(has(varDecl(allOf(hasType(asString("class Vec")),anyOf(
           has(expr().bind("VectorDeclRV")),
           has(exprWithCleanups().bind("VectorDeclRV"))
           ))).bind("VectorVarDecl"))).bind("VectorDeclStatement");
*/

    StatementMatcher pointDecl = 
        declStmt(
            has(varDecl(allOf(hasType(asString("tf::Point")),
                has(materializeTemporaryExpr(has(cxxTemporaryObjectExpr(
                    allOf(
                        hasArgument(0, expr().bind("PointArg1")),
                        hasArgument(1, expr().bind("PointArg2")),
                        hasArgument(2, expr().bind("PointArg3"))
                    )
                ))))
           )).bind("PointVarDecl"))).bind("PointDeclStatement");
    StatementMatcher pointDecl2 = 
        declStmt(
            has(varDecl(allOf(hasType(asString("tf::Point")),
                has(expr().bind("PointVarRV"))
           )).bind("PointVarDecl"))).bind("PointDeclStatement");
/*
`-ExprWithCleanups 0x558e2b418da0 <col:24, col:44> 'tf::Point':'tf::Vector3'
    |     `-CXXConstructExpr 0x558e2b418d68 <col:24, col:44> 'tf::Point':'tf::Vector3' 'void (tf::Vector3 &&) noexcept' elidable
    |       `-MaterializeTemporaryExpr 0x558e2b418d50 <col:24, col:44> 'tf::Point':'tf::Vector3' xvalue
    |         `-CXXTemporaryObjectExpr 0x558e2b418d00 <col:24, col:44> 'tf::Point':'tf::Vector3' 'void (const tfScalar &, const tfScalar &, const tfScalar &)'
    |           |-MaterializeTemporaryExpr 0x558e2b418c88 <col:34> 'const tfScalar':'const double' lvalue
    |           | `-ImplicitCastExpr 0x558e2b418c70 <col:34> 'const tfScalar':'const double' <IntegralToFloating>
    |           |   `-IntegerLiteral 0x558e2b418bf0 <col:34> 'int' 20
    |           |-MaterializeTemporaryExpr 0x558e2b418cb8 <col:38, col:39> 'const tfScalar':'const double' lvalue
    |           | `-ImplicitCastExpr 0x558e2b418ca0 <col:38, col:39> 'const tfScalar':'const double' <IntegralToFloating>
    |           |   `-UnaryOperator 0x558e2b418c30 <col:38, col:39> 'int' prefix '-'
    |           |     `-IntegerLiteral 0x558e2b418c10 <col:39> 'int' 2
    |           `-MaterializeTemporaryExpr 0x558e2b418ce8 <col:42> 'const tfScalar':'const double' lvalue
    |             `-ImplicitCastExpr 0x558e2b418cd0 <col:42> 'const tfScalar':'const double' <IntegralToFloating>
    |               `-IntegerLiteral 0x558e2b418c50 <col:42> 'int' 12

*/


    StatementMatcher vectorDecl = 
        declStmt(
            has(varDecl(allOf(hasType(asString("tf::Vector3")),
                has(expr().bind("VectorDeclRV"))
           )).bind("VectorVarDecl"))).bind("VectorDeclStatement");

    StatementMatcher vd = 
        declStmt(has(varDecl(hasType(asString("tf::Vector3"))))).bind("myvecdecl");

    StatementMatcher pd = 
        declStmt(has(varDecl(hasType(asString("tf::Point"))))).bind("myptdecl");
    //localFinder_.addMatcher(transformParenExpr, this);

    localFinder_.addMatcher(pointDecl, this);
    localFinder_.addMatcher(vectorDecl, this);
    //localFinder_.addMatcher(vd, this);
    //localFinder_.addMatcher(pd, this);
};

void TempROSMatcher::run(const MatchFinder::MatchResult &Result){
    auto pointDeclStmt = Result.Nodes.getNodeAs<clang::Stmt>("PointDeclStatement");
    auto pointVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("PointVarDecl");
    auto pointRV = Result.Nodes.getNodeAs<clang::Expr>("PointDeclRV");
    auto p1 = Result.Nodes.getNodeAs<clang::Expr>("PointArg1");
    auto p2 = Result.Nodes.getNodeAs<clang::Expr>("PointArg2");
    auto p3 = Result.Nodes.getNodeAs<clang::Expr>("PointArg3");

    auto p4 = Result.Nodes.getNodeAs<clang::Stmt>("myvecdecl");
    auto p5 = Result.Nodes.getNodeAs<clang::Stmt>("myptdecl");

    auto vectorDeclStmt = Result.Nodes.getNodeAs<clang::Stmt>("VectorDeclStatement");
    auto vectorVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("VectorVarDecl");
    auto vectorDeclRV = Result.Nodes.getNodeAs<clang::Expr>("VectorDeclRV");



    if(pointDeclStmt)
        pointDeclStmt->dump();
    if(pointVarDecl)
        pointVarDecl->dump();
    if(pointRV)
        pointRV->dump();
    if(p1)
        p1->dump();
    if(p2)
        p2->dump();
    if(p3)
        p3->dump();
    if(vectorDeclStmt)
        vectorDeclStmt->dump();
    if(vectorVarDecl)
        vectorVarDecl->dump();
    if(vectorDeclRV)
        vectorDeclRV->dump();
    

    //if(p4)
    //    p4->dump();
    //if(p5)
    //    p5->dump();

    if(pointDeclStmt and pointVarDecl and pointRV)
    {
        //TempROSMatcher exprMatcher{this->context_, this->interp_};
        //exprMatcher.search();
        //exprMatcher.visit(*pointDeclRV);
        // this->interp_->mkVector_Def(vectorDecl, vectorVarDecl, exprMatcher.getChildExprStore());
        this->interp_->mkDECL_REAL3_VAR_REAL3_EXPR(pointDeclStmt, pointVarDecl, pointRV);
        this->interp_->mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(pointRV, p1, p2, p3);
    }


    //auto vectorDeclStmt = Result.Nodes.getNodeAs<clang::Stmt>("CXXConstructExprDiscard");
   // auto vectorVarDecl = Result.Nodes.getNodeAs<clang::VarDecl>("CXXConstructExprDiscard");
    //auto vectorDeclRV = Result.Nodes.getNodeAs<clang::DeclRefExpr>("CXXConstructExprDiscard");

    if(vectorDeclStmt and vectorVarDecl and vectorDeclRV)
    {
        this->interp_->mkDECL_REAL3_VAR_REAL3_EXPR(vectorDeclStmt, vectorVarDecl, vectorDeclRV);

        auto ref_expr = clang::dyn_cast<clang::DeclRefExpr>(vectorDeclRV);
        this->interp_->mkREF_REAL3_VAR(vectorDeclRV, clang::dyn_cast<clang::VarDecl>(ref_expr->getDecl()));
    }


    auto constructExpr = Result.Nodes.getNodeAs<clang::CXXConstructExpr>("CXXConstructExprDiscard");
    auto constructExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXConstructExprChild");

    auto transformExprWithCleanups = Result.Nodes.getNodeAs<clang::ExprWithCleanups>("ExprWithCleanupsDiscard");

    auto implicitCastExpr = Result.Nodes.getNodeAs<clang::ImplicitCastExpr>("ImplicitCastExprDiscard");

    auto bindTemporaryExpr = Result.Nodes.getNodeAs<clang::CXXBindTemporaryExpr>("CXXBindTemporaryExprDiscard");
    auto bindTemporaryExprChild = Result.Nodes.getNodeAs<clang::Expr>("CXXBindTemporaryExprChild");

    auto materializeTemporaryExpr = Result.Nodes.getNodeAs<clang::MaterializeTemporaryExpr>("MaterializeTemporaryExprDiscard");
    auto materializeTemporaryChild = Result.Nodes.getNodeAs<clang::Expr>("MaterializeTemporaryExprChild");


    if(implicitCastExpr){
        TempROSMatcher exprMatcher{this->context_, this->interp_};
        exprMatcher.search();
        exprMatcher.visit(*implicitCastExpr->getSubExpr());
        this->childExprStore_ = exprMatcher.getChildExprStore();

        //interp_->mkVecWrapperExpr(transformImplicitCastExpr, transformImplicitCastExpr->getSubExpr());
    }
    else if(constructExpr or constructExprChild){
        if(constructExpr and constructExprChild){
            TempROSMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*constructExprChild);
            
            this->childExprStore_ = (clang::Expr*)exprMatcher.getChildExprStore();

          //  interp_->mkTransform_Expr(transformConstructExpr, exprMatcher.getChildExprStore());
            //interp_->mkVecWrapperExpr(transformConstructExpr, transformConstructExprChild);
        }
        else{
            //log error
        }
    }
    else if(bindTemporaryExpr or bindTemporaryExprChild){
        if(bindTemporaryExpr and bindTemporaryExprChild){
            TempROSMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*bindTemporaryExprChild);

            this->childExprStore_ = exprMatcher.getChildExprStore();
            //no longer doing this!
            //interp_->mkVecWrapperExpr(transformBindTemporaryExpr, transformBindTemporaryExprChild);

        }
        else{
            //log error
        }
    }
    else if(materializeTemporaryExpr and materializeTemporaryChild){
        if(materializeTemporaryExpr and materializeTemporaryChild){
            TempROSMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*materializeTemporaryChild);

            this->childExprStore_ = exprMatcher.getChildExprStore();
            //interp_->mkVecWrapperExpr(transformMaterializeTemporaryExpr, transformMaterializeTemporaryChild);

        }
        else{
            //log error
        }
    }
    //const auto parenExpr = Result.Nodes.getNodeAs<clang::ParenExpr>("TransformParenExpr");

    /*if(parenExpr or innerExpr){
        if(parenExpr and innerExpr){

            TempROSMatcher exprMatcher{this->context_, this->interp_};
            exprMatcher.search();
            exprMatcher.visit(*innerExpr);
           // interp_->mkTransformParenExpr(parenExpr, exprMatcher.getChildExprStore());
            this->childExprStore_ = (clang::Expr*)parenExpr;
            
        }
        else{
            //log error
        }
    }*/
};