/*
 Vector class
*/
class VectorTypeDeclHandler : public MatchFinder::MatchCallback {
public:
  virtual void run(const MatchFinder::MatchResult &Result){
    const CXXRecordDecl *typeVector = 
      Result.Nodes.getNodeAs<clang::CXXRecordDecl>("VectorTypeDecl");
    if(typeVector != NULL) {
      // NO ACTION
      //cerr << "Found Vec class declaration\n";
    }
  }
};


/*
 Vector.add method
*/
class VectorAddMethodDeclHandler: public  MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    // kevin's question is why would this ever be null? -- see clang details
    const CXXMethodDecl *vecAdd = 
      Result.Nodes.getNodeAs<clang::CXXMethodDecl>("VectorAddMethodDecl");
    if(vecAdd != NULL) {
      // NO ACTION
      //cerr << "Found Vec::add method declaration\n";
    }
  }
};


==============

  /*

    // declstmt->dump();

    // get identifier node 
    const VarDecl* identifier_VarDecl = dyn_cast<VarDecl>(declstmt->getSingleDecl());
    // get expression node 
    const clang::Expr *ptr_expression = identifier_VarDecl->getInit();

    // separately the cases of initialization and the assignment
    const clang::CXXConstructExpr *CCE_expression = static_cast<const clang::CXXConstructExpr *>(ptr_expression);

    // TODO design the matchers to do case analysis instead of hacking
    // This is not robust code
    const unsigned numArg = CCE_expression->getNumArgs();
    
    if (numArg > 1) 
      // initialization case
    {
      cout<<"initialization!"<<endl;
      // convert the identifier to Domain identifier

      // Get file location information
      ASTContext *context = Result.Context;
      FullSourceLoc FullLocation = 
        context->getFullLoc(identifier_VarDecl->getBeginLoc());
      SourceManager& sm = context->getSourceManager();
      string where = FullLocation.printToString(sm);

      // HERE'S THE REAL ACTION
      Space& s = oracle->getSpaceForVector(where); // fix: need filename

      // Create code coordinate object to use in interp
      VectorASTNode& n = 
        *new VectorASTNode(declstmt, Result);

      // Create corresponding abstract vector in domain 
      const clang::Stmt* vecInstStmt = static_cast<const clang::Stmt*>(declstmt);
      VecVarExpr& abst_v = domain->addVecVarExpr(s,vecInstStmt);

      // Connect them through the interpretation
      interp->putVectorInterp(n, abst_v);

      // Construct Expression
      // iterate over the children of this node to get the literal values
      VecLitExpr& vle = domain-> addVecLitExpr(s);

      for(clang::Stmt::const_child_iterator it = CCE_expression->child_begin();
                      it!= CCE_expression->child_end(); ++ it)
      {
        double value = static_cast<const clang::FloatingLiteral*>(it->IgnoreImplicit())->getValueAsApproximateDouble();
        vle.addFloatLit(value);
      }
      // Add the binding
      domain->addLitExprBinding(abst_v,vle);
    }
    else
     // vec_add application
    {
      cout<<"vec_add application" <<endl; 
    }
    // recursively find the DeclRefExprs
    // bool VisitDeclRefExpr(DeclRefExpr* DRE) {
    //   const Decl* D = DRE->getDecl();
    //   cout<<"Found leave node!\n";
    //   return true; // returning false will abort the in-depth traversal.
    // } 
    // *add expression to the domain
    // constructExpression(ptr_expression);

    // *add identifier to domain
    

    // *create the binding 


  }
// private:
  // a class for visiting calls recursively 
  */


=============

    /**************
    Define MATCHERS
    ***************/

    // Vector class declaration
    // DeclarationMatcher match_Vector_decl = cxxRecordDecl(hasName("Vec"))
    //   .bind("VectorTypeDecl");

    // Vector::add method declaration
    // DeclarationMatcher match_Vector_add_decl = 
    //   cxxMethodDecl(hasName("vec_add"))
    //     .bind("VectorAddMethodDecl");

    // OLD HANDLERS THAT HANDLES THE VECTOR CASES SEPARATELY
    // Vector instance declaration
    // DeclarationMatcher match_Vector_instance_decl = 
    //  varDecl(hasInitializer(cxxConstructExpr(hasType(cxxRecordDecl(hasName("Vec")))))).bind("VectorInstanceDecl");

    // Vector::add call
    // StatementMatcher match_Vector_add_call =
    //   cxxMemberCallExpr(hasDeclaration(namedDecl(hasName("vec_add"))))
    //     .bind("VecAddCall");

    // Add the new matcher that matches the Vector cases in general - instance and vec_ad application



================

    /************
    Bind Handlers
    ************/

    // Matcher.addMatcher(match_Vector_decl, &HandlerForVecDef);
    // Matcher.addMatcher(match_Vector_add_decl, &HandlerForVecAddDef);
    
    // comment out those handlers that handles vectors cases separately 
    // Matcher.addMatcher(match_Vector_instance_decl, &HandlerForVecInstanceInit);
    // Matcher.addMatcher(match_Vector_add_call, &HandlerForVecAdd);

===============


  // VectorTypeDeclHandler HandlerForVecDef;
  // VectorAddMethodDeclHandler HandlerForVecAddDef;
  // VectorInstanceDeclHandler HandlerForVecInstanceInit;
  // VectorAddCallHandler HandlerForVecAdd;

===============

