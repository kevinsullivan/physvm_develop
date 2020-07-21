
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

domain::DomainObject* Oracle_AskAll::getInterpretationForPROGRAM(coords::PROGRAM * coords, domain::DomainObject * dom){
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


domain::DomainObject* Oracle_AskAll::getInterpretationForGLOBALSTMT(coords::GLOBALSTMT * coords, domain::DomainObject * dom){
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector(time)\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint(time)\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling(time)\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear(time)\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Angle(geom3d)\n";
    std::cout<<"(2)"<<"@@ClassicalVelocity3Scalar(vel)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeScalar(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3Scalar(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Angle(geom3d);
            }
            case 2 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scalar(vel);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScalar(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scalar(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector(time)\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint(time)\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalVelocity3Vector(vel)\n";
    std::cout<<"(4)"<<"@@ClassicalTimeVector(time)\n";
    std::cout<<"(5)"<<"@@EuclideanGeometry3Vector(geom3d)\n";
    std::cout<<"(6)"<<"@@ClassicalTimePoint(time)\n";
    std::cout<<"(7)"<<"@@EuclideanGeometry3Point(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 7) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Vector(vel);
            }
            case 4 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeVector(time);
            }
            case 5 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Vector(geom3d);
            }
            case 6 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimePoint(time);
            }
            case 7 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Point(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cout<<"(2)"<<"@@EuclideanGeometry3Orientation(geom3d)\n";
    std::cout<<"(3)"<<"@@ClassicalTimeHomogenousPoint(time)\n";
    std::cout<<"(4)"<<"@@EuclideanGeometry3HomogenousPoint(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 4) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }
            case 2 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Orientation(geom3d);
            }
            case 3 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeHomogenousPoint(time);
            }
            case 4 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3HomogenousPoint(geom3d);
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling(time)\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear(time)\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
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

                    
    std::cout<<"(1)"<<"@@ClassicalVelocity3Scaling(vel)\n";
    std::cout<<"(2)"<<"@@ClassicalTimeScaling(time)\n";
    std::cout<<"(3)"<<"@@EuclideanGeometry3Scaling(geom3d)\n";
    std::cout<<"(4)"<<"@@ClassicalVelocity3Shear(vel)\n";
    std::cout<<"(5)"<<"@@ClassicalTimeShear(time)\n";
    std::cout<<"(6)"<<"@@EuclideanGeometry3Shear(geom3d)\n";
    std::cout<<"(7)"<<"@@ClassicalVelocity3BasisChange(vel)\n";
    std::cout<<"(8)"<<"@@ClassicalTimeBasisChange(time)\n";
    std::cout<<"(9)"<<"@@EuclideanGeometry3BasisChange(geom3d)\n";
    std::cout<<"(10)"<<"@@ClassicalTimeFrameChange(time)\n";
    std::cout<<"(11)"<<"@@EuclideanGeometry3FrameChange(geom3d)\n";
    std::cout<<"(12)"<<"@@EuclideanGeometry3Rotation(geom3d)\n";
    std::cin>>choice;
    if(choice < 1 or choice > 12) {
        goto choose;
    } else {
        switch(choice){

            case 1 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Scaling(vel);
            }
            case 2 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeScaling(time);
            }
            case 3 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Scaling(geom3d);
            }
            case 4 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3Shear(vel);
            }
            case 5 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeShear(time);
            }
            case 6 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Shear(geom3d);
            }
            case 7 : 
            {
            domain::ClassicalVelocity* vel = (domain::ClassicalVelocity*)this->domain_->getSpace("vel");
            return this->domain_->mkClassicalVelocity3BasisChange(vel);
            }
            case 8 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeBasisChange(time);
            }
            case 9 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3BasisChange(geom3d);
            }
            case 10 : 
            {
            domain::ClassicalTime* time = (domain::ClassicalTime*)this->domain_->getSpace("time");
            return this->domain_->mkClassicalTimeFrameChange(time);
            }
            case 11 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3FrameChange(geom3d);
            }
            case 12 : 
            {
            domain::EuclideanGeometry* geom3d = (domain::EuclideanGeometry*)this->domain_->getSpace("geom3d");
            return this->domain_->mkEuclideanGeometry3Rotation(geom3d);
            }

        }
    }
  

}