
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
# include <g3log/g3log.hpp>
# include <vector>

//using namespace std;
using namespace oracle;



domain::Frame* Oracle_AskAll::getFrame(domain::Space* space){

    auto frames = space->getFrames();
    auto sz = frames.size();
            
    while(true){
        int i = 0;
        std::cout<<"Available Frames For : " << space->toString() << "\n";
        for(auto fr : frames){
            std::cout<<"("+std::to_string((i + 1))+") "<<frames[i++]->toString()<<"\n";
        }
        int choice = 0;
        std::cin>>choice;
        if(choice > 0 and choice <= sz){
            return frames[choice-1];
        }
    }
}

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords, domain::DomainObject* dom){

	if(false){}
    else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL1_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL3_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL4_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL4_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REALMATRIX_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREALMATRIX_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL1_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_EXPR*>(coords)){
    
        return this->getInterpretationForREAL1_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL3_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_EXPR*>(coords)){
    
        return this->getInterpretationForREAL3_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL4_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL4_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL4_EXPR*>(coords)){
    
        return this->getInterpretationForREAL4_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REALMATRIX_LITERAL*>(coords)){
    
        return this->getInterpretationForREALMATRIX_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REALMATRIX_EXPR*>(coords)){
    
        return this->getInterpretationForREALMATRIX_EXPR(dc, dom);
    }
}

domain::DomainObject* Oracle_AskAll::getInterpretationForIFCOND(coords::IFCOND * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"None available!\n";
    return this->domain_->mkDefaultDomainContainer();
}


domain::DomainObject* Oracle_AskAll::getInterpretationForSTMT(coords::STMT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"None available!\n";
    return this->domain_->mkDefaultDomainContainer();
}


domain::DomainObject* Oracle_AskAll::getInterpretationForEXPR(coords::EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"None available!\n";
    return this->domain_->mkDefaultDomainContainer();
}


domain::DomainObject* Oracle_AskAll::getInterpretationForASSIGNMENT(coords::ASSIGNMENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"None available!\n";
    return this->domain_->mkDefaultDomainContainer();
}


domain::DomainObject* Oracle_AskAll::getInterpretationForDECLARE(coords::DECLARE * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"None available!\n";
    return this->domain_->mkDefaultDomainContainer();
}


domain::DomainObject* Oracle_AskAll::getInterpretationForREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle()\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Angle(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Scalar(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeScalar(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Scalar(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Vector(sp);
                        auto frame = (domain::ClassicalVelocity3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeVector(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Vector(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimePoint(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Point(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeHomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3HomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling()\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear()\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear()\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear()\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange()\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange()\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeScaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeShear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 8 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeBasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 9 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 10 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeFrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 11 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3FrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL1_LITERAL(coords::REAL1_LITERAL * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle()\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Angle(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Scalar(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeScalar(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Scalar(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL1_EXPR(coords::REAL1_EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle()\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Angle(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Scalar(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeScalar(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Scalar(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL3_LITERAL(coords::REAL3_LITERAL * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Vector(sp);
                        auto frame = (domain::ClassicalVelocity3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeVector(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Vector(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimePoint(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Point(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL3_EXPR(coords::REAL3_EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalVelocity3Vector(sp);
                        auto frame = (domain::ClassicalVelocity3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeVector(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Vector(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimePoint(sp);
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Point(sp);
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrame(sp); 
                        ret->setFrame(frame);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL4_LITERAL(coords::REAL4_LITERAL * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeHomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3HomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL4_EXPR(coords::REAL4_EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Orientation(sp);
                        return ret;
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkClassicalTimeHomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3HomogenousPoint(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX_LITERAL(coords::REALMATRIX_LITERAL * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling()\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear()\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear()\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear()\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange()\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange()\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeScaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeShear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 8 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeBasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 9 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 10 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeFrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 11 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3FrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX_EXPR(coords::REALMATRIX_EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling()\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear()\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear()\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear()\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange()\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange()\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeScaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Scaling(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeShear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 6 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3Shear(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 7 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalVelocity*> index_to_sp;

                    std::cout<<"Choose ClassicalVelocity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalVelocity3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 8 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeBasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 9 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3BasisChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 10 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalTime*> index_to_sp;

                    std::cout<<"Choose ClassicalTime Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkClassicalTimeFrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 11 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                index_to_dom[++dom_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>dom_choice;

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::Frame*> index_to_cod;
                            for(auto fr: frs){
                                index_to_cod[++cod_index] = fr;
                                std::cout<<"("<<std::to_string(index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_index]);
                                auto ret = this->domain_->mkEuclideanGeometry3FrameChange(mapsp);
                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
            }
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(true){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        auto ret = this->domain_->mkEuclideanGeometry3Rotation(sp);
                        return ret;
            
                    }
                }
            }

        }
    }
  

}