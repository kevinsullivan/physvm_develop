
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
    std::string name;
    std::cin>>name;
    this->choices.push_back(name);
    return name;//std::string(str_);
};

template<int Dimension>
float* Oracle_AskAll::getValueVector(){
    float* values = new float[Dimension];
    redo:
    try{
        float value = 0;
        for(auto i = 0; i<Dimension;i++){
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
    }
    catch(std::exception ex){
        goto redo;
    }
    return nullptr;
};
template<int Dimension>
float** Oracle_AskAll::getValueMatrix(){
    float** values = new float*[Dimension];
    redo:
    try{
        for(auto i = 0;i<Dimension;i++)
            values[i] = new float[Dimension];
        float value = 0;
        for(auto i = 0; i<Dimension;i++){
            for(auto j = 0;j<Dimension;j++){
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
    }
    catch(std::exception ex){
        goto redo;
    }
    return nullptr;
};

template<typename SpaceType>
domain::CoordinateSpace* Oracle_AskAll::selectSpace(std::vector<SpaceType*> options){
    if(options.size() == 0){
        std::cout<<"No available spaces\n";
        return nullptr;
    }
    redo:
    std::cout<<"Select Space : \n";
    for(auto i = 0;i<((int)options.size());i++){

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
    if(choice >= 1 and choice <= ((int)options.size())){
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
        "1 - Classical Time Coordinate Space\n"+
        "2 - Euclidean Geometry 1D Space\n"+
        "3 - Euclidean Geometry 3D Space\n";
        
    choice = this->getValidChoice(1,4, menu);
    switch(choice)
    {
        case 1: {
            menu = "1 - Time Space with Standard Frame\n2 - Time Space Derived from Existing Coordinate Space\n";
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
                default: goto redo;
            }
        } break;
        case 2: {
            menu = "1 - Geom1D Space with Standard Frame\n2 - Geom1D Space Derived from Existing Coordinate Space\n";
            choice = this->getValidChoice(1,3, menu);
            //std::cin>>choice;
            switch(choice){
                case 1:{
                    auto name = this->getName();
                    return static_cast<domain::Geom1DCoordinateSpace*>(this->domain_->mkStandardGeom1DCoordinateSpace(name));
                } break;
                case 2:{
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
        } break;
        case 3: {
            menu = "1 - Geom3D Space with Standard Frame\n2 - Geom3D Space Derived from Existing Coordinate Space\n";
            choice = this->getValidChoice(1,3, menu);
            //std::cin>>choice;
            switch(choice){
                case 1:{
                    auto name = this->getName();
                    return static_cast<domain::Geom3DCoordinateSpace*>(this->domain_->mkStandardGeom3DCoordinateSpace(name));
                } break;
                case 2:{
                    auto name = this->getName();
                    std::cout<<"Choose Parent Coordinate Space : \n";
                    auto parent = dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
                    std::cout<<"Choose Origin Coordinates : \n";
                    auto originData = this->getValueVector<3>();
                    std::cout<<"Choose Basis Coordinates : \n";
                    auto basisData = this->getValueMatrix<3>();
                
                    return static_cast<domain::Geom3DCoordinateSpace*>(this->domain_->mkDerivedGeom3DCoordinateSpace(name, parent, originData, basisData));
                    
                    //probably bad code, not really clear where to delete these...
                } break;
                default: goto redo;
            }
        } break;
        default: goto redo;
    }

    return nullptr;
    
};

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords){
    /*
    To be improved substantially..
    move to configuration and/or type reflection as opposed to hard-coding in possible interpretations
    */
    int choice = -1;
    redo_ident:
    std::string menu = std::string("Choose Interpretation:\n")+
        "1 - Select Existing Interpretation\n"+
        "2 - Duration\n"+
        "3 - Time\n"+
        "4 - Scalar\n"+
        "5 - Time Transform\n"+
        "6 - Displacement1D\n"+
        "7 - Position1D\n"+
        "8 - Geom1D Transform\n"+
        "9 - Displacement3D\n"+
        "10 - Position3D\n"+
        "11 - Orientation3D\n" + 
        "12 - Rotation3D\n" + 
        "13 - Pose3D\n" + 
        "14 - Geom3D Transform\n" +
        "15 - TimeStamped Pose3D\n" + 
        "16 - TimeStamped Geom3D Transform\n" + 
        "17 - TimeSeries Value\n";
    int menuSize = 18;
    
    if(coords->getNodeType().find("IDENT") != string::npos){
        menu+=
            std::to_string(menuSize++)+" - Create a Time Series\n";    
           // std::to_string(menuSize++)+" - Pose3D Time Series\n" +
           // std::to_string(menuSize++)+" - Geom3D Transform Time Series";
        menuSize +=1;
    }

    choice = this->getValidChoice(1,menuSize,menu);
    

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
            auto interpretation_ = this->domain_->mkDisplacement1D(name, sp, value);
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
            auto interpretation_ = this->domain_->mkPosition1D(name, sp, value);
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
        case 9:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<3>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            //std::cout<<sp->getName();
            auto interpretation_ = this->domain_->mkDisplacement3D(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 10:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<3>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkPosition3D(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 11:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            float* value = nullptr;
            if(coords->getNodeType().find("R4") != string::npos)
                value = this->getValueVector<4>();
            else
                value = this->getValueVector<9>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkOrientation3D(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 12:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            float* value = nullptr;
            if(coords->getNodeType().find("R4") != string::npos)
                value = this->getValueVector<4>();
            else
                value = this->getValueVector<9>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkRotation3D(name, sp, value);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 13:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            auto sp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!sp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Enter Orientation Coordinates\n";
            auto value = this->getValueVector<9>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto ort = this->domain_->mkOrientation3D(name, sp, value);
            std::cout<<"Enter Position Coordinates\n";
            value = this->getValueVector<3>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto pos = this->domain_->mkPosition3D(name, sp, value);
            auto interpretation_ = this->domain_->mkPose3D(name, sp, ort, pos);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 14:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto interpretation_ = this->domain_->mkGeom3DTransform(name, tdom_, tcod_);
            this->existing_interpretations.push_back(interpretation_);
            return interpretation_;
        } break;
        case 15: {
            //this is the timestamped pose
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Building Timestamp\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto time_ = this->domain_->mkTime("", tsp, value);
            std::cout<<"Building Pose\n";
            auto gsp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!gsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Enter Orientation Coordinates\n";
            value = this->getValueVector<9>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto ort = this->domain_->mkOrientation3D("", gsp, value);
            std::cout<<"Enter Position Coordinates\n";
            value = this->getValueVector<3>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto pos = this->domain_->mkPosition3D("", gsp, value);


            auto pose_ = this->domain_->mkPose3D("", gsp, ort, pos);
            
            auto ts_ = this->domain_->mkTimeStampedPose3D(name, time_, pose_);
            this->existing_interpretations.push_back(ts_);
            return ts_;

        } break;
        case 16: {
            //this is the timestamped transform
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Building Timestamp\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto value = this->getValueVector<1>();
            if(!value){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto time_ = this->domain_->mkTime("", tsp, value);
            std::cout<<"Building Transform\n";
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }

            auto tr = this->domain_->mkGeom3DTransform(name, tdom_, tcod_);

            auto ttr_ = this->domain_->mkTimeStampedGeom3DTransform(name, time_, tr);
            this->existing_interpretations.push_back(ttr_);
            return ttr_;
        } break;
        case 17: {
            auto ts_ = selectTimeSeries();
            if(!ts_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto sp = ts_->getTimeSpace();

            std::cout<<"Choose Type of Index into Time Series : \n";
            menu = std::string("1 - Get Latest Value from Time Series\n2 - Provide Specific Time\n");
            choice = this->getValidChoice(1,3,menu);
            if(choice == 1)
            {
                auto si = new domain::SeriesIndex(ts_, nullptr);
                this->existing_interpretations.push_back(si);
                return si;
            }
            else
            {
                std::cout<<"Provide Time Index : \n";
                auto value = this->getValueVector<1>();
                if(!value){
                    std::cout<<"Interpretation building failed\n";
                    return nullptr;
                }
                auto time_ = this->domain_->mkTime("", sp, value);
                auto si = new domain::SeriesIndex(ts_, time_);
                this->existing_interpretations.push_back(si);
                return si;
            }
            return nullptr;

        } break;
        case 18:{
            return this->buildTimeSeries(coords);
        }
        /*case 18: {
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Choose Timestamp Space\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Choose Pose3D Space\n";
            auto gsp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!gsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto tpose_ = this->domain_->mkPose3DSeries(name, tsp, gsp);
            this->existing_interpretations.push_back(tpose_);
            return tpose_;
        } break;
        case 19:{
            auto name = coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Choose Timestamp Space\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            std::cout<<"Choose Geom3D Transform Space\n";
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            auto ttr_ = this->domain_->mkGeom3DTransformSeries(name, tsp, tdom_, tcod_);
            this->existing_interpretations.push_back(ttr_);
            return ttr_;
        } break;*/
        default: goto redo_ident;
    }
};

domain::DomainObject* Oracle_AskAll::getBooleanInterpretation(){
    
    redo:

    std::string menu("1 - True\n2- False");
    
    int choice = this->getValidChoice(1,3, menu);

    switch(choice)
    {
        case 1: {
            return new domain::BoolTrue();
        } break;
        case 2: {
            return new domain::BoolFalse();
        } break;
        default: {
            goto redo;
        }
    }
}

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
    for(auto domain_ : this->existing_interpretations){
        menu += std::to_string(i++) + " - " + domain_->toString() + "\n";
    }
    int choice = getValidChoice(1, this->existing_interpretations.size()+1,menu)-1;
    return this->existing_interpretations[choice];
}


domain::TimeSeries* Oracle_AskAll::selectTimeSeries(){
    std::vector<domain::TimeSeries*> ts_;
    //std::copy_if no
    for(auto dom_ : this->existing_interpretations){
        if(auto dc=dynamic_cast<domain::TimeSeries*>(dom_)){
            ts_.push_back(dc);
        }
    }
    if(ts_.size()==0){
        std::cout<<"No available Time Series to sample from";
        return nullptr;
    }
    std::string menu("");
    int i = 0;
    for(auto domain_ : ts_){
        menu += std::to_string(++i) + " - " + domain_->toString() + "\n";
    }
    int choice = getValidChoice(1, ts_.size()+1,menu)-1;
    return ts_[choice];
}

domain::TimeSeries* Oracle_AskAll::buildTimeSeries(coords::Coords* coords){

    std::string menu =     
            std::string("1 - Pose3D Time Series\n") +
            "2 - Geom3D Transform Time Series";
    int choice = this->getValidChoice(1,3,menu);
    switch(choice)
    {
        case 1:{
            auto name = coords && coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Choose Timestamp Space\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            if(!tsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Choose Pose3D Space\n";
            auto gsp =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!gsp){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }

            domain::Pose3DSeries* tpose_;
            if(coords)//hairy issue of 
                tpose_ = new domain::Pose3DSeries(name, tsp, gsp);
            else
                tpose_ = this->domain_->mkPose3DSeries(name, tsp, gsp);
            
            this->existing_interpretations.push_back(tpose_);
            return tpose_;

        }
        case 2:{
            auto name = coords && coords->hasName() ? coords->getName() : this->getName();
            std::cout<<"Choose Timestamp Space\n";
            auto tsp =  dynamic_cast<domain::TimeCoordinateSpace*>(this->selectSpace(this->domain_->getTimeSpaces()));
            std::cout<<"Choose Geom3D Transform Space\n";
            std::cout<<"Annotate Domain:\n";
            auto tdom_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tdom_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            std::cout<<"Annotate Codomain:\n";
            auto tcod_ =  dynamic_cast<domain::Geom3DCoordinateSpace*>(this->selectSpace(this->domain_->getGeom3DSpaces()));
            if(!tcod_){
                std::cout<<"Interpretation building failed\n";
                return nullptr;
            }
            domain::Geom3DTransformSeries* ttr_;
            if(coords)//hairy issue of 
                ttr_ = new domain::Geom3DTransformSeries(name, tsp, tdom_, tcod_);
            else
                ttr_ = this->domain_->mkGeom3DTransformSeries(name, tsp, tdom_, tcod_);
            this->existing_interpretations.push_back(ttr_);
            return ttr_;

        }
    }
    return nullptr;
}

void Oracle_AskAll::addTimeStampedToTimeSeries(){
    auto ts_ = this->selectTimeSeries();

    if(!ts_){
        std::cout<<"Invalid Time Series - Ending Add Time Stamped Procedure\n";
        return;
    }

    if(auto dc = dynamic_cast<domain::Pose3DSeries*>(ts_)){

        //auto name = coords->hasName() ? coords->getName() : this->getName();
        std::cout<<"Building Timestamp\n";
        auto tsp = dc->getTimeSpace();//
        if(!tsp){
            std::cout<<"Interpretation building failed\n";
            return; //nullptr;
        }
        auto value = this->getValueVector<1>();
        if(!value){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        auto time_ = this->domain_->mkTime("", tsp, value);
        std::cout<<"Building Pose\n";
        auto gsp = dc->getSpace();
        if(!gsp){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        std::cout<<"Enter Orientation Coordinates\n";
        value = this->getValueVector<9>();
        if(!value){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        auto ort = this->domain_->mkOrientation3D("", gsp, value);
        std::cout<<"Enter Position Coordinates\n";
        value = this->getValueVector<3>();
        if(!value){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        auto pos = this->domain_->mkPosition3D("", gsp, value);

        auto pose_ = this->domain_->mkPose3D("", gsp, ort, pos);

        auto tspose_ = this->domain_->mkTimeStampedPose3D("", time_, pose_);
        
        dc->insertValue(tspose_);

    }
    else if(auto dc = dynamic_cast<domain::Geom3DTransformSeries*>(ts_)){
        //this is the timestamped transform
        //auto name = coords->hasName() ? coords->getName() : this->getName();
        std::cout<<"Building Timestamp\n";
        auto tsp = dc->getTimeSpace();
        if(!tsp){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        auto value = this->getValueVector<1>();
        if(!value){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        auto time_ = this->domain_->mkTime("", tsp, value);
        std::cout<<"Building Transform\n";
        std::cout<<"Annotate Domain:\n";
        auto tdom_ = dc->getDomain();
        if(!tdom_){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }
        std::cout<<"Annotate Codomain:\n";
        auto tcod_ = dc->getCodomain();
        if(!tcod_){
            std::cout<<"Interpretation building failed\n";
            return;// nullptr;
        }

        auto tr = this->domain_->mkGeom3DTransform("", tdom_, tcod_);

        auto tstr = this->domain_->mkTimeStampedGeom3DTransform("", time_, tr);
        
        dc->insertValue(tstr);
    } 
    else{
        std::cout<<"Did not recognize series type.\n";
        return;
    }
}