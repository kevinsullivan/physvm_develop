
/*
Establish interpretations for AST nodes:

-  get any required information from oracle 
-  create coordinates for object
-  update ast-coord bijections
-  create corresponding domain object
-  update coord-domain bijection
-  create element-wise inter object
-  update maps: coords-interp, interp-domain
*/

// TODO: These two can be integrated
#include "Coords.h"
#include "Interpretation.h"
#include "Interp.h"
#include "maps/CoordsToInterp.h"
#include "maps/CoordsToDomain.h"
#include "maps/InterpToDomain.h"
#include "maps/ASTToCoords.h"
#include "oracles/Oracle_AskAll.h"    // default oracle
#include "oracles/Oracle_LeanInference.h"
//#include "Space.h"
#include "Checker.h"

//#include <g3log/g3log.hpp>
#include <unordered_map>
#include <memory>
#include <vector>
using namespace interp;


std::vector<string> *choice_buffer;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    //REPLACE WITH A MULTI-ORACLE
    oracle_ = new oracle::Oracle_AskAll(domain_); 
    oracle_infer_ = new oracle::Oracle_LeanInference(domain_);
    //choice_buffer = new std::vector<string>();
    //oracle_->choice_buffer = choice_buffer;
    /* 
    context_ can only be set later, once Clang starts parse
    */
    ast2coords_ = new ast2coords::ASTToCoords(); 
    coords2dom_ = new coords2domain::CoordsToDomain();
    coords2interp_ = new coords2interp::CoordsToInterp();
    interp2domain_ = new interp2domain::InterpToDomain();
    checker_ = new Checker(this);
}

std::string Interpretation::toString_AST(){
    //this should technically be in Interp but OKAY this second
    //4/13 - nope move this 
    std::string math = "";

    math += "import .new.lang.expressions.time_expr_current\n\n";
    math += "open lang.time\nabbreviation F := lang.time.K\n\n";
    //math += "noncomputable theory\n\n";
    //math += "def " + interp::getEnvName() + " := environment.init_env";
    //math += interp->toString_Spaces();
    //math += interp->toString_PROGRAMs();
    //math += this->toString_COMPOUND_STMTs();
    //math += this->
    auto astInterp = coords2interp_->getInterp(this->AST);
    math+= astInterp->toStringLinked(domain_->getSpaces());
    return math;
};

/*
Simple implementation for all nodes - configuration can handle how to differentiate between add and mul nodes, etc.
*/
int global_index = 0; //auto increment for each AST Coords
void Interpretation::mkNode(std::string nodeType, std::shared_ptr<ast::NodeContainer> astNode, bool capture, bool isAST){
    std::vector<coords::Coords*> operand_coords;
    std::vector<domain::DomainContainer*> operand_domains;
    std::vector<interp::Interp*> operand_interps;
    int i = 0;
    for(auto child:this->astBuffer){
        operand_coords.push_back(this->ast2coords_->getCoords(child));
    }
    for(auto operand_coord : operand_coords){
        operand_domains.push_back(this->coords2dom_->getDomain(operand_coord));
        operand_interps.push_back(this->coords2interp_->getInterp(operand_coord));
    }

    coords::Coords* coords_ = new coords::Coords(nodeType, operand_coords);
    coords_->setIndex(global_index++);
    this->ast2coords_->put(astNode, coords_);
    this->ast2coords_->setASTState(coords_,astNode,context_);
    domain::DomainContainer* domain__ = this->domain_->mkDefaultDomainContainer(operand_domains);
    interp::Interp* interp_ = new interp::Interp(coords_, domain__, operand_interps);

    this->coords2dom_->put(coords_, domain__);
    this->coords2interp_->put(coords_,interp_);
    this->interp2domain_->put(interp_,domain__);
    
    if(this->link){
        auto link_coords = this->ast2coords_->getCoords(this->link);
        link_coords->addLink(coords_);
        coords_->setLinked(link_coords);
    }
    else if(capture){
        this->captureCache.push_back(coords_);
    }
    if(isAST){
        this->AST = coords_;
    }
    this->clear_buffer();
}


void Interpretation::printChoices(){
    aFile* f = new aFile;
    std::string name = "/peirce/annotations.txt";
    char * name_cstr = new char [name.length()+1];
    strcpy (name_cstr, name.c_str());
    f->name = name_cstr;
    f->file = fopen(f->name, "w");
    for(auto choice: this->oracle_->getChoices()){
        fputs((choice + "\n").c_str(), f->file);
    }

    fclose(f->file);
    delete f->name;
    delete f;
};

int optionSize = 5;
void Interpretation::printVarTable(){
    int i = optionSize+1;//move to "menu offset" global variable
    for(auto coords_ : this->captureCache)
    {
        auto dom_ = this->coords2dom_->getDomain(coords_);
        std::cout<<"Index: "<<i++<<", Node Type : "<<coords_->getNodeType()<<", Annotation State : "<<dom_->getAnnotationStateStr()<<",\n\tSnippet: "<<coords_->state_->code_<<", \n\t"<<coords_->getSourceLoc()
            <<"\n\tExisting Interpretation: "<<dom_->toString()<<std::endl<<std::endl;
    }
};

void Interpretation::printErrors(){
    int i = optionSize+1;//move to "menu offset" global variable
    for(auto coords_ : this->captureCache)
    {
        auto dom_ = this->coords2dom_->getDomain(coords_);

        std::string error_str_ = "No Error Detected";
        if(dom_->hasValue()){
            if(auto dc = dynamic_cast<domain::ErrorObject*>(dom_->getValue())){
                error_str_ = dc->toErrorString();
            }
        }

        std::cout<<"Index: "<<i++<<",Node Type : "<<coords_->getNodeType()<<",\n\tSnippet: "<<coords_->state_->code_<<", \n\t"<<coords_->getSourceLoc()
            <<"\n\tError Message: "<<error_str_<<std::endl;
    }
};


void Interpretation::interpretProgram(){
    bool continue_ = true;
    std::vector<interp::Interp*> ordered_nodes;
    for(auto coords_ : this->captureCache) 
        ordered_nodes.push_back(this->coords2interp_->getInterp(coords_));

    oracle_infer_->setNodes(ordered_nodes);
    while(continue_)
    {
        checker_->CheckPoll();

        this->printChoices();
        std::cout << "********************************************\n";
        std::cout << "See type-checking output in "<<"/peirce/PeirceOutput.lean"<<"\n";
        std::cout << "Annotations stored in " <<"/peirce/annotations.txt"<<"\n";
        std::cout << "********************************************\n";

        int menuSize = optionSize+this->captureCache.size();
        std::string menu = std::string("Options:\n")
            +"0 - Print Variable Table\n"
            +"1 - Print Available Coordinate Spaces\n"
            +"2 - Create Coordinate Space\n"
            +"3 - Exit and Finish Type Checking\n"
            +"4 - Perform Lean Inference\n"
            +"5 - Print Detected Lean Errors\n";
        if(this->captureCache.size()>0){
            menu = menu+(std::to_string(optionSize+1))+"-"+std::to_string(menuSize)+" - Annotate Node\n";
        }
        int choice = oracle_->getValidChoice(0, menuSize+1, menu);
        switch(choice)
        {
            case 0:{
                printVarTable();
            } break;
            case 1:{
                auto spaces = domain_->getSpaces();
                for(auto sp : spaces)
                    std::cout<<sp->toString()<<"\n"; 
            } break;
            case 2:{
                oracle_->getSpace();
            } break;
            case 3:{
                continue_ = false;
            } break;
            case 4:{
                
                /*
                move this somewhere maybe
                Organize loop better
                */
                oracle_infer_->buildInterpretations("PeirceOutput");//move to configuration or method
                for(auto coords_ : this->captureCache){
                    /*
                    What is the update logic? Very difficult question to answer.
                    */
                    auto dom_cont = this->coords2dom_->getDomain(coords_);
                    auto infer_dom = oracle_infer_->getInterpretation(coords_);

                    switch(dom_cont->getAnnotationState()){
                        case domain::AnnotationState::Manual : {
                            //dont overwrite manual annotations
                        } break;
                        default : {
                            if(infer_dom){
                                dom_cont->setValue(infer_dom);

                                if(auto dc = dynamic_cast<domain::ErrorObject*>(infer_dom))
                                    dom_cont->setAnnotationState(domain::AnnotationState::Error);
                                else 
                                    dom_cont->setAnnotationState(domain::AnnotationState::Inferred);

                            }
                        }
                    }
                }
            } break;
            case 5: {
                this->printErrors();
            } break;
            default:{
                auto coords_ = this->captureCache[choice-optionSize-1];
                domain::DomainContainer* dom_cont = this->coords2dom_->getDomain(coords_);
                auto new_dom = this->oracle_->getInterpretation(coords_);
                
                if(new_dom){

                    dom_cont->setValue(new_dom);
                    dom_cont->setAnnotationState(domain::AnnotationState::Manual);
                    for(auto link_ : coords_->getLinks()){
                        domain::DomainContainer* link_cont = this->coords2dom_->getDomain(link_);
                        link_cont->setValue(new_dom);
                        link_cont->setAnnotationState(domain::AnnotationState::Inferred);
                    }
                }
            };
        }
    }
};

void remap(coords::Coords* c, domain::DomainObject* newinterp){
    return;
};

