|-UsingDirectiveDecl 0x5597b9cfd3c0 <main.cpp:4:1, col:17> col:17 Namespace 0x5597b97053f0 'std'
`-FunctionDecl 0x5597b9cfd570 <line:6:1, line:15:1> line:6:5 main 'int (int, char **)'
  |-ParmVarDecl 0x5597b9cfd420 <col:10, col:14> col:14 argc 'int'
  |-ParmVarDecl 0x5597b9cfd498 <col:20, col:27> col:27 argv 'char **'
  `-CompoundStmt 0x5597b9cfe150 <col:32, line:15:1>
    |-DeclStmt 0x5597b9cfd998 <line:8:3, col:22>
    | `-VarDecl 0x5597b9cfd638 <col:3, col:21> col:7 used v1 'class Vec' callinit
    |   `-CXXConstructExpr 0x5597b9cfd950 <col:7, col:21> 'class Vec' 'void (float, float, float)'
    |     |-ImplicitCastExpr 0x5597b9cfd908 <col:10> 'float' <FloatingCast>
    |     | `-FloatingLiteral 0x5597b9cfd698 <col:10> 'double' 1.000000e+00
    |     |-ImplicitCastExpr 0x5597b9cfd920 <col:14> 'float' <FloatingCast>
    |     | `-FloatingLiteral 0x5597b9cfd6b8 <col:14> 'double' 1.000000e+00
    |     `-ImplicitCastExpr 0x5597b9cfd938 <col:18> 'float' <FloatingCast>
    |       `-FloatingLiteral 0x5597b9cfd6d8 <col:18> 'double' 1.000000e+00
    |-DeclStmt 0x5597b9cfdb50 <line:9:3, col:22>
    | `-VarDecl 0x5597b9cfd9c0 <col:3, col:21> col:7 used v2 'class Vec' callinit
    |   `-CXXConstructExpr 0x5597b9cfdb08 <col:7, col:21> 'class Vec' 'void (float, float, float)'
    |     |-ImplicitCastExpr 0x5597b9cfdac0 <col:10> 'float' <FloatingCast>
    |     | `-FloatingLiteral 0x5597b9cfda20 <col:10> 'double' 2.000000e+00
    |     |-ImplicitCastExpr 0x5597b9cfdad8 <col:14> 'float' <FloatingCast>
    |     | `-FloatingLiteral 0x5597b9cfda40 <col:14> 'double' 2.000000e+00
    |     `-ImplicitCastExpr 0x5597b9cfdaf0 <col:18> 'float' <FloatingCast>
    |       `-FloatingLiteral 0x5597b9cfda60 <col:18> 'double' 2.000000e+00
    |-DeclStmt 0x5597b9cfdf70 <line:11:3, col:26>
    | `-VarDecl 0x5597b9cfdb78 <col:3, col:25> col:7 v3 'class Vec' cinit
    |   `-CXXConstructExpr 0x5597b9cfdf38 <col:12, col:25> 'class Vec' 'void (const class Vec &) throw()'
    |     `-ImplicitCastExpr 0x5597b9cfdc90 <col:12, col:25> 'const class Vec' lvalue <NoOp>
    |       `-CXXMemberCallExpr 0x5597b9cfdc60 <col:12, col:25> 'class Vec' lvalue
    |         |-MemberExpr 0x5597b9cfdc00 <col:12, col:15> '<bound member function type>' .vec_add 0x5597b9cfc570
    |         | `-DeclRefExpr 0x5597b9cfdbd8 <col:12> 'class Vec' lvalue Var 0x5597b9cfd638 'v1' 'class Vec'
    |         `-DeclRefExpr 0x5597b9cfdc38 <col:23> 'class Vec' lvalue Var 0x5597b9cfd638 'v1' 'class Vec'
    |-DeclStmt 0x5597b9cfe100 <line:12:3, col:26>
    | `-VarDecl 0x5597b9cfdf98 <col:3, col:25> col:7 v4 'class Vec' cinit
    |   `-CXXConstructExpr 0x5597b9cfe0c8 <col:12, col:25> 'class Vec' 'void (const class Vec &) throw()'
    |     `-ImplicitCastExpr 0x5597b9cfe0b0 <col:12, col:25> 'const class Vec' lvalue <NoOp>
    |       `-CXXMemberCallExpr 0x5597b9cfe080 <col:12, col:25> 'class Vec' lvalue
    |         |-MemberExpr 0x5597b9cfe020 <col:12, col:15> '<bound member function type>' .vec_add 0x5597b9cfc570
    |         | `-DeclRefExpr 0x5597b9cfdff8 <col:12> 'class Vec' lvalue Var 0x5597b9cfd638 'v1' 'class Vec'
    |         `-DeclRefExpr 0x5597b9cfe058 <col:23> 'class Vec' lvalue Var 0x5597b9cfd9c0 'v2' 'class Vec'
    `-ReturnStmt 0x5597b9cfe138 <line:14:3, col:10>
      `-IntegerLiteral 0x5597b9cfe118 <col:10> 'int' 0

Matcher solution
declStmt(hasDescendant(varDecl(hasInitializer(cxxConstructExpr(argumentCountIs(3)))))
declStmt(hasDescendant(varDecl(hasDescendant(cxxMemberCallExpr(hasDescendant(memberExpr(hasDescendant(declRefExpr()),hasDeclaration(namedDecl(hasName("vec_add"))))),hasDescendant(declRefExpr()))))))


// refine the matcher to find every elements in the declStmt and annotat them
declStmt(hasDescendant(varDecl(hasInitializer(cxxConstructExpr(argumentCountIs(3)))).bind("VecInstantiation")).bind("VecInstantiation")


declStmt(hasDescendant(
    varDecl(hasDescendant(
        cxxMemberCallExpr(
            hasDescendant(memberExpr(hasDescendant(declRefExpr().bind("VecAddParam2")),
                            hasDeclaration(namedDecl(hasName("vec_add")))).bind("VecAddCall"),
            hasDescendant(declRefExpr().bind("VecAddParam2")))))).bind("AssignedValue")))


Found the following declstmt:-----
DeclStmt 0x55e24da0f728
`-VarDecl 0x55e24da0f550  v5 'class Vec' cinit
  `-CXXConstructExpr 0x55e24da0f6f8 'class Vec' 'void (const class Vec &) noexcept'
    `-ImplicitCastExpr 0x55e24da0f6e0 'const class Vec' lvalue <NoOp>
      `-CXXMemberCallExpr 0x55e24da0f6b8 'class Vec' lvalue
        |-MemberExpr 0x55e24da0f668 '<bound member function type>' .vec_add 0x55e24d9ded78
        | `-ParenExpr 0x55e24da0f648 'class Vec' lvalue
        |   `-CXXMemberCallExpr 0x55e24da0f620 'class Vec' lvalue
        |     |-MemberExpr 0x55e24da0f5d0 '<bound member function type>' .vec_add 0x55e24d9ded78
        |     | `-DeclRefExpr 0x55e24da0f5b0 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'
        |     `-DeclRefExpr 0x55e24da0f600 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'
        `-DeclRefExpr 0x55e24da0f698 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'

Found the following declstmt:-----
DeclStmt 0x55e24da0f9a0
`-VarDecl 0x55e24da0f750  v6 'class Vec' cinit
  `-CXXConstructExpr 0x55e24da0f970 'class Vec' 'void (const class Vec &) noexcept'
    `-ImplicitCastExpr 0x55e24da0f958 'const class Vec' lvalue <NoOp>
      `-CXXMemberCallExpr 0x55e24da0f930 'class Vec' lvalue
        |-MemberExpr 0x55e24da0f868 '<bound member function type>' .vec_add 0x55e24d9ded78
        | `-ParenExpr 0x55e24da0f848 'class Vec' lvalue
        |   `-CXXMemberCallExpr 0x55e24da0f820 'class Vec' lvalue
        |     |-MemberExpr 0x55e24da0f7d0 '<bound member function type>' .vec_add 0x55e24d9ded78
        |     | `-DeclRefExpr 0x55e24da0f7b0 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'
        |     `-DeclRefExpr 0x55e24da0f800 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'
        `-CXXMemberCallExpr 0x55e24da0f908 'class Vec' lvalue
          |-MemberExpr 0x55e24da0f8b8 '<bound member function type>' .vec_add 0x55e24d9ded78
          | `-DeclRefExpr 0x55e24da0f898 'class Vec' lvalue Var 0x55e24da0e008 'v1' 'class Vec'
          `-DeclRefExpr 0x55e24da0f8e8 'class Vec' lvalue Var 0x55e24da0e350 'v2' 'class Vec'












