#include "../BaseMatcher.h"
#include "../Interpretation.h"
/*
See BaseMatcher.h for method details
Starting point entry for matching Clang AST. Searches for main method
*/
class ROS1ProgramMatcher : public BaseMatcher {
public:
    ROS1ProgramMatcher(
        clang::ASTContext* context, 
        interp::Interpretation* interp) 
        : BaseMatcher(context, interp) {}

    virtual void setup();
    virtual void run(const MatchFinder::MatchResult &Result);
protected:
    
};