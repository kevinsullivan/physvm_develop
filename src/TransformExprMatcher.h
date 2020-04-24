#ifndef vectorm
#define vectorm
#include "BaseMatcher.h"
#include "Interpretation.h"

/*
See BaseMatcher.h for method details
matches all "Vector Expressions"
*/
/*
    TRANSFORM_EXPR := (TRANSFORM_EXPR) | COMPOSE TRANSFORM_EXPR TRANSFORM_EXPR | TRANSFORM_VAR | VEC_LITERAL
*/
class TransformExprMatcher : public BaseMatcher {
public:
    TransformExprMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif