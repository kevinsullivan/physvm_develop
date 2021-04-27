
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
//# include <g3log/g3log.hpp>
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
            if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
            std::cout<<"("+std::to_string((++i))+") "<<fr->toString()<<"\n";
        }
        if(i == 0){
            std::cout<<"No available interpreted frames";
            return nullptr;
        }
        int choice = 0;
        std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
        if(choice >= 0 and choice < sz){
            return frames[choice];
        }
    }
    return nullptr;
}

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords, domain::DomainObject* dom){

	if(false){}
    else if(auto dc = dynamic_cast<coords::REALMATRIX4_EXPR*>(coords)){
    
        return this->getInterpretationForREALMATRIX4_EXPR(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL4_EXPR*>(coords)){
    
        return this->getInterpretationForREAL4_EXPR(dc, dom);
    }
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
    else if(auto dc = dynamic_cast<coords::REAL4_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREAL4_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REALMATRIX4_VAR_IDENT*>(coords)){
    
        return this->getInterpretationForREALMATRIX4_VAR_IDENT(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL4_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL4_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL3_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL3_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REAL1_LITERAL*>(coords)){
    
        return this->getInterpretationForREAL1_LITERAL(dc, dom);
    }
    else if(auto dc = dynamic_cast<coords::REALMATRIX4_LITERAL*>(coords)){
    
        return this->getInterpretationForREALMATRIX4_LITERAL(dc, dom);
    }
	return nullptr;
}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX4_EXPR(coords::REALMATRIX4_EXPR * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalTimeTransform()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometryTransform()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Transform()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 3) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkClassicalTimeTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometryTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometry3Transform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometryRotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryOrientation()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryRotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Rotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryOrientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Orientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 15) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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

                    
    if(false){choice = 1; goto choose;}
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
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cout<<"(16)"<<"@@ClassicalVelocityScalar()\n";
    std::cout<<"(17)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(18)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(19)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(20)"<<"@@ClassicalHertzScalar()\n";
    std::cout<<"(21)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(22)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(23)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(24)"<<"@@ClassicalLuminousIntensityScalar()\n";
    std::cout<<"(25)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(26)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(27)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(28)"<<"@@ClassicalVelocityQuantity()\n";
    std::cout<<"(29)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(30)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(31)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(32)"<<"@@ClassicalHertzQuantity()\n";
    std::cout<<"(33)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(34)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(35)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(36)"<<"@@ClassicalLuminousIntensityQuantity()\n";
    std::cout<<"(37)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(38)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(39)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 39) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 16 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 17 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 18 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 19 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 20 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 21 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 22 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 23 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 24 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 25 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 26 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 27 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 28 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 29 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 30 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 31 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 32 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 33 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 34 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 35 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 36 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 37 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 38 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 39 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

domain::DomainObject* Oracle_AskAll::getInterpretationForBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    if(false){choice = 1; goto choose;}
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocityCoordinateVector()\n";
    std::cout<<"(2)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cout<<"(16)"<<"@@ClassicalVelocityScalar()\n";
    std::cout<<"(17)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(18)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(19)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(20)"<<"@@ClassicalHertzScalar()\n";
    std::cout<<"(21)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(22)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(23)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(24)"<<"@@ClassicalLuminousIntensityScalar()\n";
    std::cout<<"(25)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(26)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(27)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(28)"<<"@@ClassicalVelocityQuantity()\n";
    std::cout<<"(29)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(30)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(31)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(32)"<<"@@ClassicalHertzQuantity()\n";
    std::cout<<"(33)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(34)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(35)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(36)"<<"@@ClassicalLuminousIntensityQuantity()\n";
    std::cout<<"(37)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(38)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(39)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 39) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 16 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 17 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 18 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 19 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 20 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 21 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 22 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 23 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 24 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 25 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 26 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 27 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 28 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 29 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 30 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 31 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 32 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 33 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 34 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 35 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 36 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 37 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 38 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 39 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 15) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometryRotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryOrientation()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryRotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Rotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryOrientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Orientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalTimeTransform()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometryTransform()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Transform()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 3) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkClassicalTimeTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometryTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometry3Transform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometryRotation()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Rotation()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometryOrientation()\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Orientation()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryRotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 2 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Rotation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryOrientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[4];
                                auto vals = ((coords::ValueCoords<float,4>*)coords)->getValues();
                                for(int idx = 0;idx < 4;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Orientation<float,4>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 4; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<4;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 4; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 15) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[3];
                                auto vals = ((coords::ValueCoords<float,3>*)coords)->getValues();
                                for(int idx = 0;idx < 3;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,3>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 3; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<3;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 3; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

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
    std::cout<<"(4)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(5)"<<"@@ClassicalHertzCoordinateVector()\n";
    std::cout<<"(6)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(7)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(8)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(9)"<<"@@ClassicalLuminousIntensityCoordinateVector()\n";
    std::cout<<"(10)"<<"@@ClassicalTimeCoordinateVector()\n";
    std::cout<<"(11)"<<"@@EuclideanGeometryCoordinateVector()\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3CoordinateVector()\n";
    std::cout<<"(13)"<<"@@ClassicalTimeCoordinatePoint()\n";
    std::cout<<"(14)"<<"@@EuclideanGeometryCoordinatePoint()\n";
    std::cout<<"(15)"<<"@@EuclideanGeometry3CoordinatePoint()\n";
    std::cout<<"(16)"<<"@@ClassicalVelocityScalar()\n";
    std::cout<<"(17)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(18)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(19)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(20)"<<"@@ClassicalHertzScalar()\n";
    std::cout<<"(21)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(22)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(23)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(24)"<<"@@ClassicalLuminousIntensityScalar()\n";
    std::cout<<"(25)"<<"@@ClassicalTimeScalar()\n";
    std::cout<<"(26)"<<"@@EuclideanGeometryScalar()\n";
    std::cout<<"(27)"<<"@@EuclideanGeometry3Scalar()\n";
    std::cout<<"(28)"<<"@@ClassicalVelocityQuantity()\n";
    std::cout<<"(29)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(30)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(31)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(32)"<<"@@ClassicalHertzQuantity()\n";
    std::cout<<"(33)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(34)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(35)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cout<<"(36)"<<"@@ClassicalLuminousIntensityQuantity()\n";
    std::cout<<"(37)"<<"@@ClassicalTimeQuantity()\n";
    std::cout<<"(38)"<<"@@EuclideanGeometryQuantity()\n";
    std::cout<<"(39)"<<"@@EuclideanGeometry3Quantity()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 39) {
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 5 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalHertzCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalHertzFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 6 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 7 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 8 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 9 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkClassicalLuminousIntensityCoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::ClassicalLuminousIntensityFrame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 10 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 11 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 12 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinateVector<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 13 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 14 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
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
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 15 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }
                    

                        auto ret = this->domain_->mkEuclideanGeometry3CoordinatePoint<float,1>(sp,cp);
                        //delete[] cp;
                        auto frame = (domain::EuclideanGeometry3Frame*)this->getFrameForInterpretation(sp); 
                        if(!frame) {
                            std::cout<<"Missing frame : failed to build interpretation\n";
                            return nullptr;
                        }
                        ret->setFrame(frame);
                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 16 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 17 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 18 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 19 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 20 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 21 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 22 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 23 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 24 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 25 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 26 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryScalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 27 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Scalar<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 28 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalVelocityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 29 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 30 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 31 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 32 : 
            {
                std::vector<domain::ClassicalHertz*> spaces = this->domain_->getClassicalHertzSpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalHertz*> index_to_sp;

                    std::cout<<"Choose ClassicalHertz Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalHertzQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalHertz Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 33 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 34 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 35 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 36 : 
            {
                std::vector<domain::ClassicalLuminousIntensity*> spaces = this->domain_->getClassicalLuminousIntensitySpaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::ClassicalLuminousIntensity*> index_to_sp;

                    std::cout<<"Choose ClassicalLuminousIntensity Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalLuminousIntensityQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalLuminousIntensity Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 37 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkClassicalTimeQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 38 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometryQuantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
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
            case 39 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        std::shared_ptr<float> cp[1];
                                auto vals = ((coords::ValueCoords<float,1>*)coords)->getValues();
                                for(int idx = 0;idx < 1;idx++){
                                    cp[idx] = vals[idx] ? std::make_shared<float>(*vals[idx]) : nullptr;
                                }

                        auto ret = this->domain_->mkEuclideanGeometry3Quantity<float,1>(sp,cp); 
                        //delete[] cp;

                        std::cout<<"Provide Values For Interpretation? (1) Yes(2) No\n";
                        try{
                            int vchoice = 0;
                            std::cin >> vchoice;
        choice_buffer->push_back(std::to_string(vchoice));
                            if (vchoice == 1)
                            {
                                for (int i = 0; i < 1; i++)
                                {
                                    std::cout << "Enter Value " << i << ":\n";
                                    float val = 4;
                                    std::cin >> val;
        choice_buffer->push_back(std::to_string(val));
                                    //float* vc = new float(valvc);
                                    ret->setValue(val, i);
                                    //delete vc;
                                }
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
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
        choice_buffer->push_back(std::to_string(vchoice));
                            if(vchoice == 1){
                                for(int i = 0; i<1;i++){
                                    std::cout<<"Enter Value "<<i<<":\n";
                                    float valvc;
                                    std::cin>>valvc;
        choice_buffer->push_back(std::to_string(valvc));
                                    float* vc;
                                    ret->setValue(vc, i);
                                    delete vc;
                                }
                                break;
                            }
                            else{
                                for (int i = 0; i < 1; i++)
                                {
                                    //float* vc = new float(0);
                                    ret->setValue(0, i);
                                    //delete vc;
                                }
                                break;
                            }
                            //else if(vchoice != 0)
                            //    continue;
                        }*/
                        
                        
                        return ret;
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}

domain::DomainObject* Oracle_AskAll::getInterpretationForREALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL * coords, domain::DomainObject * dom){
    std::cout << "Provide new interpretation for : " << "";
    std::cout << "\nExisting interpretation:   ";
    std::cout << dom->toString();
    std::cout << "\nAt location:  ";
    std::cout << coords->getSourceLoc();
    int choice;
    choose:
    std::cout<<"\nAvailable Interpretations (Enter numeral choice) : \n";
    
    //return getInterpretation(coords);

                    
    std::cout<<"(1)"<<"@@ClassicalTimeTransform()\n";
    std::cout<<"(2)"<<"@@EuclideanGeometryTransform()\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Transform()\n";
    std::cin>>choice;
        choice_buffer->push_back(std::to_string(choice));
    if(choice < 1 or choice > 3) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::ClassicalTimeFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::ClassicalTimeFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkClassicalTimeTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available ClassicalTime Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 2 : 
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
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometryFrame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometryFrame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometryTransform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }
            case 3 : 
            {
                std::vector<domain::EuclideanGeometry3*> spaces = this->domain_->getEuclideanGeometry3Spaces();
                while(spaces.size()>0){
                    int sp_choice = 0;
                    int index = 0;

                    std::unordered_map<int,domain::EuclideanGeometry3*> index_to_sp;

                    std::cout<<"Choose EuclideanGeometry3 Space to Attach to This Annotation : \n";

                    for(auto sp : spaces){
                        index_to_sp[++index] = sp;
                        std::cout<<"("<<std::to_string(index)<<") "<<sp->toString()<<"\n";
                
                    }
                    std::cin>>sp_choice;
        choice_buffer->push_back(std::to_string(sp_choice));
                    if(sp_choice >0 and sp_choice <= index){
                        auto sp = index_to_sp[sp_choice];
                        while(true){
                            auto frs = sp->getFrames();
                            std::cout<<"Enter Frame of Transform Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_dom;
                            int dom_index = 0,
                                cod_index = 0;
                            int dom_choice = 0, 
                                cod_choice = 0;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_dom[++dom_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(dom_index)<<") "<<fr->toString()<<"\n";
                            }
                            if(dom_index == 0) {
                                std::cout<<"No available interpreted frames\n";
                                return nullptr;
                            }
                            std::cin>>dom_choice;
                            choice_buffer->push_back(std::to_string(dom_choice));

                        
                            std::cout<<"Enter Frame of Transform Co-Domain : \n";
                            std::unordered_map<int, domain::EuclideanGeometry3Frame*> index_to_cod;
                            for(auto fr: frs){
                                if(auto dc = dynamic_cast<domain::StandardFrame*>(fr)) continue;
                                index_to_cod[++cod_index] = (domain::EuclideanGeometry3Frame*)fr;
                                std::cout<<"("<<std::to_string(cod_index)<<") "<<fr->toString()<<"\n";
                            }
                            std::cin>>cod_choice;
        choice_buffer->push_back(std::to_string(cod_choice));

                            if(dom_choice >0 and dom_choice <= dom_index and cod_choice >0 and cod_choice <= cod_index){
                                //auto mapsp = this->domain_->mkMapSpace(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                                

                                auto ret = this->domain_->mkEuclideanGeometry3Transform<float,1>(sp, index_to_dom[dom_choice], index_to_cod[cod_choice]);
                               // delete[] cp;

                                return ret;

                            }
                        
                        }
                        
            
                    }
                }
                if(spaces.size() == 0){
                    std::cout<<"Invalid Annotation: No Available EuclideanGeometry3 Spaces!\n";
                    return nullptr;

                    std::cout<<"Provide Another Intepretation\n";
                    goto choose;
                }
            }

        }
    }
  

 return nullptr;}