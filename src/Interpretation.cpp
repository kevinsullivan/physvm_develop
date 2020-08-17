
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
#include "CoordsToInterp.h"
#include "CoordsToDomain.h"
#include "InterpToDomain.h"
#include "ASTToCoords.h"
#include "Oracle_AskAll.h"    // default oracle
//#include "Space.h"
#include "Checker.h"

//#include <g3log/g3log.hpp>
#include <unordered_map>
#include <memory>
using namespace interp;

Interpretation::Interpretation() { 
    domain_ = new domain::Domain();
    oracle_ = new oracle::Oracle_AskAll(domain_); 
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
    std::string math = "";

    math += "import .lang.imperative_DSL.physlang\n\n";
    math += "noncomputable theory\n\n";
            math += "def " + interp::getEnvName() + " := init_env";
            //math += interp->toString_Spaces();
            //math += interp->toString_PROGRAMs();
            math += this->toString_COMPOUND_STMTs();

            return math;
        };




void Interpretation::mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT * ast , std::vector <ast::GLOBALSTMT*> operands) {
//const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands 
	//coords::GLOBALSTMT* operand1_coords = static_cast<coords::GLOBALSTMT*>(ast2coords_->getDeclCoords(operands));

    vector<coords::GLOBALSTMT*> operand_coords;

    for(auto op : operands)
    {
        
        if(ast2coords_->existsDeclCoords(op)){
            operand_coords.push_back(static_cast<coords::GLOBALSTMT*>(ast2coords_->getDeclCoords(op)));
        } 
    }

    coords::SEQ_GLOBALSTMT* coords = ast2coords_->mkSEQ_GLOBALSTMT(ast, context_ ,operand_coords);

	//domain::DomainObject* operand1_dom = coords2dom_->getGLOBALSTMT(operand_coords);

    vector<domain::DomainObject*> operand_domain;

    for(auto op : operand_coords)
    {
        operand_domain.push_back(coords2dom_->getGLOBALSTMT(op));
    }

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer(operand_domain);
    coords2dom_->putSEQ_GLOBALSTMT(coords, dom);

	//interp::GLOBALSTMT* operand1_interp = coords2interp_->getGLOBALSTMT(operand1_coords);

    vector<interp::GLOBALSTMT*> operand_interp;

    for(auto op : operand_coords)
    {
        auto p = coords2interp_->getGLOBALSTMT(op);
        operand_interp.push_back(coords2interp_->getGLOBALSTMT(op));
    }

    interp::SEQ_GLOBALSTMT* interp = new interp::SEQ_GLOBALSTMT(coords, dom, operand_interp);
    coords2interp_->putSEQ_GLOBALSTMT(coords, interp);
    interp2domain_->putSEQ_GLOBALSTMT(interp, dom); 
	this->PROGRAM_vec.push_back(coords);
	this->SEQ_GLOBALSTMT_vec.push_back(coords);
};


 std::string Interpretation::toString_SEQ_GLOBALSTMTs(){ 
    std::vector<interp::SEQ_GLOBALSTMT*> interps;
    for(auto coord : this->SEQ_GLOBALSTMT_vec){
        interps.push_back((interp::SEQ_GLOBALSTMT*)this->coords2interp_->getPROGRAM(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toStringLinked(this->getSpaceInterps(), this->getSpaceNames(), this->getFrameInterps(), this->getFrameNames(), true) + "\n";

    }
    return retval;
}

 std::string Interpretation::toString_PROGRAMs(){ 
    std::vector<interp::PROGRAM*> interps;
    for(auto coord : this->PROGRAM_vec){
        interps.push_back(this->coords2interp_->getPROGRAM(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_GLOBALSTMTs(){ 
    std::vector<interp::GLOBALSTMT*> interps;
    for(auto coord : this->GLOBALSTMT_vec){
        interps.push_back(this->coords2interp_->getGLOBALSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}


void Interpretation::mkCOMPOUND_STMT(const ast::COMPOUND_STMT * ast , std::vector <ast::STMT*> operands) {
//const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands 
	//coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operands));

    vector<coords::STMT*> operand_coords;

    for(auto op : operands)
    {
        
        if(ast2coords_->existsStmtCoords(op)){
            operand_coords.push_back(static_cast<coords::STMT*>(ast2coords_->getStmtCoords(op)));
        } 
    }

    coords::COMPOUND_STMT* coords = ast2coords_->mkCOMPOUND_STMT(ast, context_ ,operand_coords);

	//domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand_coords);

    vector<domain::DomainObject*> operand_domain;

    for(auto op : operand_coords)
    {
        operand_domain.push_back(coords2dom_->getSTMT(op));
    }

    domain::DomainObject* dom = domain_->mkDefaultDomainContainer(operand_domain);
    coords2dom_->putCOMPOUND_STMT(coords, dom);

	//interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    vector<interp::STMT*> operand_interp;

    for(auto op : operand_coords)
    {
        auto p = coords2interp_->getSTMT(op);
        operand_interp.push_back(coords2interp_->getSTMT(op));
    }

    interp::COMPOUND_STMT* interp = new interp::COMPOUND_STMT(coords, dom, operand_interp);
    coords2interp_->putCOMPOUND_STMT(coords, interp);
    interp2domain_->putCOMPOUND_STMT(interp, dom); 
	this->STMT_vec.push_back(coords);
	this->COMPOUND_STMT_vec.push_back(coords);
};


 std::string Interpretation::toString_COMPOUND_STMTs(){ 
    std::vector<interp::COMPOUND_STMT*> interps;
    for(auto coord : this->COMPOUND_STMT_vec){
        interps.push_back((interp::COMPOUND_STMT*)this->coords2interp_->getSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toStringLinked(this->getSpaceInterps(), this->getSpaceNames(), this->getFrameInterps(), this->getFrameNames(), true) + "\n";

    }
    return retval;
}

 std::string Interpretation::toString_STMTs(){ 
    std::vector<interp::STMT*> interps;
    for(auto coord : this->STMT_vec){
        interps.push_back(this->coords2interp_->getSTMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}

 std::string Interpretation::toString_FUNC_DECLs(){ 
    std::vector<interp::FUNC_DECL*> interps;
    for(auto coord : this->FUNC_DECL_vec){
        interps.push_back(this->coords2interp_->getFUNC_DECL(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkVOID_FUNC_DECL_STMT(const ast::VOID_FUNC_DECL_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::VOID_FUNC_DECL_STMT* coords = ast2coords_->mkVOID_FUNC_DECL_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putVOID_FUNC_DECL_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::VOID_FUNC_DECL_STMT* interp = new interp::VOID_FUNC_DECL_STMT(coords, dom, operand1_interp);
    coords2interp_->putVOID_FUNC_DECL_STMT(coords, interp);
    interp2domain_->putVOID_FUNC_DECL_STMT(interp, dom); 
	this->VOID_FUNC_DECL_STMT_vec.push_back(coords);

} 


 std::string Interpretation::toString_VOID_FUNC_DECL_STMTs(){ 
    std::vector<interp::VOID_FUNC_DECL_STMT*> interps;
    for(auto coord : this->VOID_FUNC_DECL_STMT_vec){
        interps.push_back(this->coords2interp_->getVOID_FUNC_DECL_STMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}
void Interpretation::mkMAIN_FUNC_DECL_STMT(const ast::MAIN_FUNC_DECL_STMT * ast ,ast::STMT* operand1) {

	coords::STMT* operand1_coords = static_cast<coords::STMT*>(ast2coords_->getStmtCoords(operand1));

    coords::MAIN_FUNC_DECL_STMT* coords = ast2coords_->mkMAIN_FUNC_DECL_STMT(ast, context_ ,operand1_coords);

	domain::DomainObject* operand1_dom = coords2dom_->getSTMT(operand1_coords);
    domain::DomainObject* dom = domain_->mkDefaultDomainContainer({operand1_dom});
    coords2dom_->putMAIN_FUNC_DECL_STMT(coords, dom);

	interp::STMT* operand1_interp = coords2interp_->getSTMT(operand1_coords);

    interp::MAIN_FUNC_DECL_STMT* interp = new interp::MAIN_FUNC_DECL_STMT(coords, dom, operand1_interp);
    coords2interp_->putMAIN_FUNC_DECL_STMT(coords, interp);
    interp2domain_->putMAIN_FUNC_DECL_STMT(interp, dom); 
	this->MAIN_FUNC_DECL_STMT_vec.push_back(coords);

} 


 std::string Interpretation::toString_MAIN_FUNC_DECL_STMTs(){ 
    std::vector<interp::MAIN_FUNC_DECL_STMT*> interps;
    for(auto coord : this->MAIN_FUNC_DECL_STMT_vec){
        interps.push_back(this->coords2interp_->getMAIN_FUNC_DECL_STMT(coord));
    }
    std::string retval = "";
    for(auto interp_ : interps){
        retval += "\n" + interp_->toString() + "\n";
    }
    return retval;
}


std::string Interpretation::toString_Spaces() {
        int index = 0;
    std::string retval = "";
    //std::vector<domain::Space*> & s = domain_->getSpaces();
    //for (std::vector<domain::Space*>::iterator it = s.begin(); it != s.end(); ++it)
     //   retval = retval.append("def ")
     //                   .append((*it)->toString())
     //                   .append(" : peirce.vector_space := peirce.vector_space.mk ")
     //                   .append(std::to_string(index++))
     //                   .append("\n");
     //auto spaces = domain_->getSpaces();
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        retval.append("\n" + (sp->toString()) + "\n");
    }
            

    return retval;
}   

std::vector<interp::Space*> Interpretation::getSpaceInterps() {
    std::vector<interp::Space*> interps;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        interps.push_back(sp);
    }
            

    return interps;
}   

std::vector<std::string> Interpretation::getSpaceNames() {
    std::vector<std::string> names;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto sp = interp2domain_->getSpace(*it);
        names.push_back((*it)->getName());
    }
            

    return names;
}

std::vector<interp::Frame*> Interpretation::getFrameInterps() {
    std::vector<interp::Frame*> interps;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            auto intfr = interp2domain_->getFrame(fr);
            interps.push_back(intfr);
        }
    }
            

    return interps;
}   

std::vector<std::string> Interpretation::getFrameNames() {
    std::vector<std::string> names;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        auto frs = (*it)->getFrames();

        for(auto fr : frs){
            //auto intfr = interp2domain_->getFrame(fr);
            names.push_back((*it)->getName()+"."+fr->getName());
        }
    }
            

    return names;
}




    
void Interpretation::buildDefaultSpaces(){
    


}

void Interpretation::buildSpace(){
    int index = 0;
    int choice = 0;
    int size = 3;
    if (size == 0){
        std::cout<<"Warning: No Available Spaces to Build";
        return;
    }
    while((choice <= 0 or choice > size)){ 
        std::cout<<"Available types of Spaces to build:\n";
        std::cout <<"("<<std::to_string(++index)<<")"<<"EuclideanGeometry\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalTime\n";
		std::cout <<"("<<std::to_string(++index)<<")"<<"ClassicalVelocity\n";
        std::cin>>choice;
    }
    index = 0;
    
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
            
            int dimension;
            std::cout<<"Enter Dimension (integer):\n";
            std::cin>>dimension;
            auto sp = this->domain_->mkEuclideanGeometry(name, name, dimension);
    
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
	
        if(choice==++index){
            std::string name;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
            
            auto sp = this->domain_->mkClassicalTime(name, name);
            auto isp = new interp::Space(sp);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

    
	
        if(choice==++index){
            std::string name;
            domain::Space *base1,*base2;
            std::cout<<"Enter Name (string):\n";
            std::cin>>name;
            int index = 0;
            std::unordered_map<int, domain::Space*> index_to_sp;
        
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
            for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
            for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
            for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
            {
                std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
                index_to_sp[index] = *it;
            }

            if(index==0){
                std::cout<<"Unable to Proceed - No Existing Spaces\n";
                return;
            }
            int choice;
            label1st:
            std::cout<<"Select First Base Space : "<<"\n";
            std::cin>>choice;
            if(choice >0 and choice <=index){
                base1 = index_to_sp[choice];
            }
            else
                goto label1st;
            
            label2nd:
            std::cout<<"Select Second Base Space : "<<"\n";
            std::cin>>choice;
            if(choice >0 and choice <=index){
                base2 = index_to_sp[choice];
            }
            else
                goto label2nd;
            auto sp = this->domain_->mkClassicalVelocity(name, name, base1, base2);
            auto ib1 = this->interp2domain_->getSpace(base1);
            auto ib2 = this->interp2domain_->getSpace(base2);

            auto isp = new interp::DerivedSpace(sp, ib1, ib2);
            interp2domain_->putSpace(isp, sp);
            auto standard_framesp = sp->getFrames()[0];
            auto interp_framesp = new interp::Frame(standard_framesp);
            interp2domain_->putFrame(interp_framesp, sp->getFrames()[0]);
        }

}

void Interpretation::buildFrame(){
    while(true){
        std::cout<<"Select Space : "<<"\n";
        int index = 0;
        std::unordered_map<int, domain::Space*> index_to_sp;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
        for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
        for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
        for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
        {
            std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
            index_to_sp[index] = *it;
        }
        int choice;
        std::cin>>choice;
        if(choice >0 and choice <=index){
            auto chosen = index_to_sp[choice];
            std::cout<<"Building Frame For : "<<chosen->toString()<<"\n";
            auto frames = chosen->getFrames();
            std::cout<<"Select Parent Frame : "<<"\n";
            index = 0;
            std::unordered_map<int, domain::Frame*> index_to_fr;
        
            auto frs = chosen->getFrames();
            for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<(fr)->toString()<<"\n";
            index_to_fr[index] = fr;
            }
            choice = 0;
            std::cin>>choice;
            if(choice > 0 and choice<= index){
                auto parent = index_to_fr[index];
                std::cout<<"Enter Name of Frame:\n";
                std::string name;
                std::cin>>name;
                auto child = domain_->mkFrame(name, chosen, parent);
                interp::Frame* interp = new interp::Frame(child);
                interp2domain_->putFrame(interp, child);
                return;
            }
            
        }

    }
}

void Interpretation::printSpaces(){
    int index = 0;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        std::cout<<"("<<std::to_string(++index)<<")"<<(*it)->toString() + "\n";
    }
}

void Interpretation::printFrames(){
    int index = 0;
    
	auto EuclideanGeometrys = domain_->getEuclideanGeometrySpaces();
    for (auto it = EuclideanGeometrys.begin(); it != EuclideanGeometrys.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto ClassicalTimes = domain_->getClassicalTimeSpaces();
    for (auto it = ClassicalTimes.begin(); it != ClassicalTimes.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }
	auto ClassicalVelocitys = domain_->getClassicalVelocitySpaces();
    for (auto it = ClassicalVelocitys.begin(); it != ClassicalVelocitys.end(); it++)
    {
        std::cout<<"Printing Frames For : " + (*it)->toString() + "\n";
        auto frs = (*it)->getFrames();
        index = 0;
        for(auto fr : frs){
            std::cout<<"("<<std::to_string(++index)<<")"<<fr->toString() + "\n";
        }
    }

}

void Interpretation::mkVarTable(){
    int idx = 0;
  


}

//print the indexed variable table for the user
void Interpretation::printVarTable(){
  int sz = this->index2coords_.size();

  for(int i = 1; i<=sz;i++)
  {
    coords::Coords* coords = this->index2coords_[i];
    if(false){}

    
  }

}//make a printable, indexed table of variables that can have their types assigned by a user or oracle

//void Interpretation::printVarTable(){}//print the indexed variable table for the user
//while loop where user can select a variable by index and provide a physical type for that variable
void Interpretation::updateVarTable(){
  auto sz = (int)this->index2coords_.size()+1;
  int choice;
  try{
        checker_->CheckPoll();
        //std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout << "See type-checking output in /peirce/phys/deps/orig/PeirceOutput.lean\n";
        std::cout << "********************************************\n";
        //std::cout << "********************************************\n";
        std::cout << "********************************************\n";
        std::cout<<"Enter -1 to print Available Spaces\n";
        std::cout<<"Enter -2 to create a New Space\n";
        std::cout<<"Enter -3 to print Available Frames\n";
        std::cout<<"Enter -4 to create a New Frame\n";
        std::cout<<"Enter 0 to print the Variable Table again.\n";
        std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
        std::cin >> choice;
        std::cout << std::to_string(choice) << "\n";


        while ((choice == -3 || choice == -2 || choice == -1 || choice == 0 || this->index2coords_.find(choice) != this->index2coords_.end()) && choice != sz)
        {
            if (choice == -4)
            {
                this->buildFrame();
            }
            else if(choice == -3)
            {
                this->printFrames();
            }
            else if(choice == -2)
            {
                this->buildSpace();
            }
            else if (choice == -1)
            {
                this->printSpaces();
            }
            else if (choice == 0)
            {
                this->printVarTable();
            }
            else
            {
                if(false){}

            }
            checker_->CheckPoll();
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout << "See type-checking output in /peirce/phys/deps/orig/PeirceOutput.lean\n";
            std::cout << "********************************************\n";
            std::cout << "********************************************\n";
            //std::cout << "********************************************\n";
            std::cout<<"Enter -1 to print Available Spaces\n";
            std::cout<<"Enter -2 to create a New Space\n";
            std::cout<<"Enter -3 to print Available Frames\n";
            std::cout<<"Enter -4 to create a New Frame\n";
            std::cout<<"Enter 0 to print the Variable Table again.\n";
            std::cout << "Enter the index of a Variable to update its physical type. Enter " << sz << " to exit and check." << std::endl;
            std::cin >> choice;
            std::cout << std::to_string(choice) << "\n";
        }
    }
    catch(std::exception ex){
        std::cout<<ex.what()<<"\n";
    }
};

void remap(coords::Coords c, domain::DomainObject newinterp){
    return;
};

