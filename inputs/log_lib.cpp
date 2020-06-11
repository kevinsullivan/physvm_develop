//#include <g3log/g3log.hpp>
//#include <g3log/logworker.hpp>
#include <iostream>
#include "vec.h"
/*
void initializeLogger()
{
    using namespace g3;
    auto worker = g3::LogWorker::createLogWorker();
    std::string logFile = "Peirce.log";
    std::string logDir = ".";
    auto defaultHandler = worker->addDefaultLogger(logFile, logDir);
    g3::initializeLogging(worker.get());
}
*/
float logScalar(float val, std::string name)
{
    std::cout << "Value : " + std::to_string(val) + " found for scalar : " + name <<std::endl;

}

Vec logVector(Vec val, std::string name)
{
    std::cout << "Value : " + std::to_string(val.get_x()) + "," + std::to_string(val.get_y()) + "," + std::to_string(val.get_z()) + " found for vector : " + name <<std::endl;

    return val;
}