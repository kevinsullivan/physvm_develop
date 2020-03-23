#include "BaseMatcher.h"

#ifndef statem
#define statem

class StatementProductionMatcher : public BaseMatcher {
public:
    StatementProductionMatcher(clang::ASTContext* context) : BaseMatcher(context) {}
    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};

#endif