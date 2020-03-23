#include "BaseMatcher.h"

class MainMatcher : public BaseMatcher {
public:
    MainMatcher(clang::ASTContext* context) : BaseMatcher(context) {}

    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};