
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
# include <g3log/g3log.hpp>
# include <vector>
#include <memory>

//using namespace std;
using namespace oracle;



domain::Frame* Oracle_AskAll::getFrameForInterpretation(domain::Space* space){

    auto frames = space->getFrames();
    auto sz = (int)frames.size();
            
    while(true){
        int i = 0;
        std::cout<<"Available Frames For : " << space->toString() << "\n";
        for(auto fr : frames){
            std::cout<<"("+std::to_string((i++))+") "<<fr->toString()<<"\n";
        }
        int choice = 0;
        std::cin>>choice;
        if(choice > 0 and choice <= sz){
            return frames[choice-1];
        }
    }
    return nullptr;
}

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords, domain::DomainObject* dom){

	if(false){}
    else if(auto dc = dynamic_cast<coords::REAL3_EXPR*>(coords)){
    
        return this->getInterpretationForREAL3_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_EXPR*>(coords)){
    
        return this->getInterpretationForREAL1_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL1_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL3_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL3_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL1_LITERAL(dc, dom);
    }
	return nullptr;
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

}

domain::DomainObject* Oracle_AskAll::getInterpretationForREAL3_LEXPR(coords::REAL3_LEXPR * coords, domain::DomainObject * dom){
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(5)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cin>>choice;
    if(choice < 1 or choice > 5) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
                std::vector<domain::ClassicalVelocity*> spaces = this->domain_->getClassicalVelocitySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalVelocityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalVelocityFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalVelocity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 4 : 
            {
                std::vector<domain::ClassicalTime*> spaces = this->domain_->getClassicalTimeSpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalTimeCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalTimeFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::EuclideanGeometry*> spaces = this->domain_->getEuclideanGeometrySpaces();
                while(spaces.size()>0){
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
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometryCoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometryFrame*)this->getFrameForInterpretation(sp); 
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                        }
                        catch(std::exception ex){
                            return ret;
                        }
/*
    while (true){
                            std::cout<<"Provide Values For Interpretation? (1) Yes (2) No\n";
                            int vchoice = 0;
                            std::cin>>vchoice;
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else if(vchoice == 0){
                                break;
                            }
                            else if(vchoice != 0)
                                continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

}