

#ifndef rosstatement
#define rosstatement
#include "../BaseMatcher.h"
#include "../Interpretation.h"

/*
See BaseMatcher.h for method details
Searches for relevant statements including physical calculations, generally inside a "compound" statement in a code block
*/
/*
STMT := 
    VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | TRANSFORM_EXPR
    VEC_EXPR | SCALAR_EXPR | TRANSFORM_EXPR
    DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR | DECL TRANSFORM_VAR = TRANSFORM_EXPR
*/
class ROSStatementMatcher : public BaseMatcher {
public:
    ROSStatementMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif