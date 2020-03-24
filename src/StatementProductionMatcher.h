

#ifndef statem
#define statem
#include "BaseMatcher.h"
#include "Interpretation.h"

class StatementProductionMatcher : public BaseMatcher {
public:
    StatementProductionMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif