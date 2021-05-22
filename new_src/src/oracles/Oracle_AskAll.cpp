
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
# include <vector>
#include <memory>

//using namespace std;
using namespace oracle;

/*
    std::string getName();
    template<int Dimension>
    float* getValueVector();
    domain::CoordinateSpace* selectSpace(std::vector<domain::CoordinateSpace*>);
*/

std::string Oracle_AskAll::getName(){
    std::cout<<"Choose a name for interpretation : \n";    
    //char* str_ = new char[255];
    //std::cout<<"hey...";
    //std::gets(str_);
    //std::cout<<"hmmm";
    std::string name;
    std::cin>>name;
    this->choices.push_back(name);
    //std::getline(std::cin, name);
    return name;//std::string(str_);
};

template<int Dimension>
float* Oracle_AskAll::getValueVector(){
    float* values = new float[Dimension];
    float value = 0;
    for(auto i = 0; i<Dimension;i++){
        redo:
        std::cout<<"Enter value at index : "<<i<<"\n";
        try{
            std::cin.clear();
            std::cin>>value;
        }
        catch(std::exception ex){
            goto redo;
        }
        values[i] = value;
    }
    for(auto i = 0; i< Dimension;i++)
        this->choices.push_back(std::to_string(values[i]));
    return values;
};
template<int Dimension>
float** Oracle_AskAll::getValueMatrix(){
    float** values = new float*[Dimension];
    for(auto i = 0;i<Dimension;i++)
        values[i] = new float[Dimension];
    float value = 0;
    for(auto i = 0; i<Dimension;i++){
        for(auto j = 0;j<Dimension;j++){
            redo:
            std::cout<<"Enter value at index : "<<i<<","<<j<<"\n";
            try{
                std::cin.clear();
                std::cin>>value;
            }
            catch(std::exception ex){
                goto redo;
            }
            values[i][j] = value;
        }
    }
    for(auto i = 0; i<Dimension;i++)
        for(auto j = 0;j<Dimension;j++)
            this->choices.push_back(std::to_string(values[i][j]));
    return values;
};

template<typename SpaceType>
domain::CoordinateSpace* Oracle_AskAll::selectSpace(std::vector<SpaceType*> options){
    if(options.size() == 0){
        std::cout<<"No available spaces\n";
        return nullptr;
    }
    redo:
    std::cout<<"Select Space : \n";
    for(auto i = 0;i<options.size();i++){

        std::cout<<(i+1)<<" - "<<options[i]->toString()<<"\n";//yay templates?
    }
    int choice = 0;
    try{
        std::cin.clear();
        std::cin>>choice;
    }
    catch(std::exception ex){
        goto redo;
    }
    if(choice >= 1 and choice <= options.size()){
        this->choices.push_back(std::to_string(choice));
        return options[choice-1];
    }
    else goto redo;
};

domain::CoordinateSpace* Oracle_AskAll::getSpace(){
    /*
    To be improved substantially..
    move to configuration and/or type reflection as opposed to hard-coding in possible interpretations
    */
    int choice;
    redo:
    std::string menu = std::string("Choose Space:\n")+
        "1 - Classical Time Coordinate Space\n";
    choice = this->getValidChoice(1,2, menu);
    if(choice==1)
    {
        menu = "1 - Time Space with Standard Frame\n2 - Time Space Derived from Existing Coordinate Space\n";
        menu += "3 - Geom1D Space with Standard Frame\n4 - Geom1D Space Derived from Existing Coordinate Space\n";
        choice = this->getValidChoice(1,5, menu);
        //std::cin>>choice;
        switch(choice){
            case 1:{
                auto name = this->getName();
                return static_cast<domain::TimeCoordinateSpace*>(this->domain_->mkStandardTimeCoordinateSpace(name));
            } break;
            case 2:{
                auto name = this->getName();
                std::cout<<"Choose Parent Coordinate Space : \n";
                auto parent = dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
                std::cout<<"Choose Origin Coordinates : \n";
                auto originData = this->getValueVector<1>();
                std::cout<<"Choose Basis Coordinates : \n";
                auto basisData = this->getValueMatrix<1>();
            
                return static_cast<domain::TimeCoordinateSpace*>(this->domain_->mkDerivedTimeCoordinateSpace(name, parent, originData, basisData));
                
                //probably bad code, not really clear where to delete these...
            } break;
            case 3:{
                auto name = this->getName();
                return static_cast<domain::Geom1DCoordinateSpace*>(this->domain_->mkStandardGeom1DCoordinateSpace(name));
            } break;
            case 4:{
                auto name = this->getName();
                std::cout<<"Choose Parent Coordinate Space : \n";
                auto parent = dynamic_cast<domain::Geom1DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom1DSpaces()));
                std::cout<<"Choose Origin Coordinates : \n";
                auto originData = this->getValueVector<1>();
                std::cout<<"Choose Basis Coordinates : \n";
                auto basisData = this->getValueMatrix<1>();
            
                return static_cast<domain::Geom1DCoordinateSpace*>(this->domain_->mkDerivedGeom1DCoordinateSpace(name, parent, originData, basisData));
                
                //probably bad code, not really clear where to delete these...
            } break;
            default: goto redo;
        }
    }
};

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords){
    /*
    To be improved substantially..
    move to configuration and/or type reflection as opposed to hard-coding in possible interpretations
    */
    std::string menu = std::string("Choose Interpretation:\n")+
        "1 - Select Existing Interpretation\n"+
        "2 - Duration\n"+
        "3 - Time\n"+
        "4 - Scalar\n"+
        "5 - Time Transform\n"+
        "6 - Displacement\n"+
        "7 - Position\n"+
        "8 - Geom1D Transform\n";
    redo:
    int choice = this->getValidChoice(1,9,menu);

    //std::cin>>choice;
    switch(choice)
    {
        case 1:{
            auto existing_ = selectExisting();//std::cout<<"Choose Existing Interpretation:\n";
            if(!existing_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            else
                return existing_;
        }
        case 2:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            //std::cout<<sp->getName();
            auto interpretation_ = this->domain_->mkDuration(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 3:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkTime(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 4:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkScalar(name, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 5:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkTimeTransform(name, tdom_, tcod_);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 6:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom1DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom1DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            //std::cout<<sp->getName();
            auto interpretation_ = this->domain_->mkDisplacement(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 7:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom1DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom1DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkPosition(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 8:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::Geom1DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom1DSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::Geom1DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom1DSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkGeom1DTransform(name, tdom_, tcod_);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        default: goto redo;
    }
};

int Oracle_AskAll::getValidChoice(int lower, int upperExclusive, std::string selectionMenu)
{
    if(lower >= upperExclusive)
        throw "Lower Bound on Choices must be less than Upper";
    
    int choice = 0;
    redo:
    std::cout<<selectionMenu<<"\n";
    try{
        std::cin.clear();
        std::cin>>choice;
    }
    catch(std::exception ex){
        goto redo;
    }
    if(choice >= lower and choice < upperExclusive){
        this->choices.push_back(std::to_string(choice));
        return choice;
    }
    else goto redo;
}

domain::DomainObject* Oracle_AskAll::selectExisting(){
    if(this->existing_interpretations.size() == 0){
        std::cout<<"No Existing Interpretations to choose from\n";
        return nullptr;
    }
    int i = 1;
    std::string menu("Choose From Existing Interpretations:\n");
    for(auto interp_ : this->existing_interpretations){
        if(auto dc = dynamic_cast<domain::Time*>(interp_))
            menu += std::to_string(i++) + " - " + dc->toString() + "\n";
        else if(auto dc = dynamic_cast<domain::Duration*>(interp_))
            menu += std::to_string(i++) + " - " + dc->toString() + "\n";
        else if(auto dc = dynamic_cast<domain::Scalar*>(interp_))
            menu += std::to_string(i++) + " - " + dc->toString() + "\n";
        else if(auto dc = dynamic_cast<domain::TimeTransform*>(interp_))
            menu += std::to_string(i++) + " - " + dc->toString() + "\n";
    }
    int choice = getValidChoice(1, this->existing_interpretations.size()+1,menu)-1;
    return this->existing_interpretations[choice];
}