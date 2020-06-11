/*
See BaseMatcher.h for method details
matches all "Scalar Expressions"
*/
/*
SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL
*/

#ifndef scalarm
#define scalarm
#include "BaseMatcher.h"
#include "ScalarExprMatcher.h"
#include "Interpretation.h"

class ScalarExprMatcher : public BaseMatcher {
public:
    ScalarExprMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif