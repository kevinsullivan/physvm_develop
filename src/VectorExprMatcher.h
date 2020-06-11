

#ifndef vectorm
#define vectorm
#include "BaseMatcher.h"
#include "Interpretation.h"

/*
See BaseMatcher.h for method details
matches all "Vector Expressions"
*/
/*
    VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL
*/
class VectorExprMatcher : public BaseMatcher {
public:
    VectorExprMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif