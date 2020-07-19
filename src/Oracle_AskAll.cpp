
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
# include <g3log/g3log.hpp>
# include <vector>

//using namespace std;
using namespace oracle;



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

                    
    std::cout<<"(1)"<<"@@Geometric3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@Velocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@TimeScalar(time)\n";
    std::cout<<"(4)"<<"@@Geometric3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@Velocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@TimeVector(time)\n";
    std::cout<<"(5)"<<"@@Geometric3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@TimePoint(time)\n";
    std::cout<<"(7)"<<"@@Geometric3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@TimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@Geometric3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Velocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@TimeScaling(time)\n";
    std::cout<<"(3)"<<"@@Geometric3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@Velocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@TimeShear(time)\n";
    std::cout<<"(6)"<<"@@Geometric3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@Velocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@TimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@Geometric3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@TimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@Geometric3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@Velocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@TimeScalar(time)\n";
    std::cout<<"(4)"<<"@@Geometric3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@Velocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@TimeScalar(time)\n";
    std::cout<<"(4)"<<"@@Geometric3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@Velocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@TimeVector(time)\n";
    std::cout<<"(5)"<<"@@Geometric3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@TimePoint(time)\n";
    std::cout<<"(7)"<<"@@Geometric3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@Velocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@TimeVector(time)\n";
    std::cout<<"(5)"<<"@@Geometric3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@TimePoint(time)\n";
    std::cout<<"(7)"<<"@@Geometric3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@TimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@Geometric3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@Geometric3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@TimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@Geometric3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Velocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@TimeScaling(time)\n";
    std::cout<<"(3)"<<"@@Geometric3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@Velocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@TimeShear(time)\n";
    std::cout<<"(6)"<<"@@Geometric3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@Velocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@TimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@Geometric3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@TimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@Geometric3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
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

                    
    std::cout<<"(1)"<<"@@Velocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@TimeScaling(time)\n";
    std::cout<<"(3)"<<"@@Geometric3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@Velocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@TimeShear(time)\n";
    std::cout<<"(6)"<<"@@Geometric3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@Velocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@TimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@Geometric3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@TimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@Geometric3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@Geometric3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkGeometric3Rotation(geom3d);
            }

        }
    }
  

}