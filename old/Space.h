/*#include <string>
#include <vector>
#include <unordered_map>
#include <functional>

//wait on Lean concept of units and dimensions

class EuclideanGeometry;
class ClassicalTime;
class ClassicalVelocity;

namespace domain{

//this should hook into objects more concretely . for example, tagging relevant objects
class Space {
public:
	Space() : name_("") {};
	Space(std::string name) : name_(name) {};
	Space(std::string name, int dimension) : name_(name), dimension_(dimension) {}
	std::string getName() const;
	int getDimension() const;
	std::string toString() const {
		return "@@" + getName() + "(" + std::to_string(getDimension()) + ")"; 
	}
    

    static std::unordered_map<std::string, std::function<Space(std::string,int)>> getRegistry();

  private:
	std::string name_;
	int dimension_;
};

class ClassicalVelocity : Space{

}

class 

class MapSpace {
public:
	MapSpace() {}
	MapSpace(std::string domain_name, std::string codomain_name) : domain_{Space(domain_name)}, codomain_{Space(codomain_name)} {}
	MapSpace(domain::Space domain, domain::Space codomain) : domain_{domain}, codomain_{codomain} {}
	std::string getName() const;
	std::string toString() const {
		return getName(); 
	}
	domain::Space domain_;
	domain::Space codomain_;
};

union SpaceContainer{
	SpaceContainer() { setDefault(); }//this->inferenceSymbol = leanInferenceWildcard; }
	~SpaceContainer(){
		delete space;
		delete inferenceSymbol;
	}
    domain::Space* space;
    std::string* inferenceSymbol;

	void setDefault(){
		//this->space = nullptr;
		this->inferenceSymbol = new std::string("_");
	}

	void setSpace(Space* space){
		if(space){
			this->space = space;
		}
		else{
			this->inferenceSymbol = new std::string("_");
		}
	}

	std::string toString(){
		if (*this->inferenceSymbol == "_"){
			return *this->inferenceSymbol;
		}
		else{
			return this->space->toString();
		}
	}
};

union MapSpaceContainer
{
	MapSpaceContainer() { setDefault(); }
	~MapSpaceContainer(){
		delete space;
		//delete inferenceSymbol;
	}

	domain::MapSpace* space;
	std::string* inferenceSymbol;

	void setDefault(){
		this->inferenceSymbol = new std::string(this->getDefault());
	};

	void setSpace(domain::MapSpace space){
		if(true){
			this->space = new MapSpace(space.domain_, space.codomain_);
		}
		else{
			setDefault();
		}
	};

	std::string getDefault(){
		return domain::MapSpace(Space("_"),Space("_")).toString();
	}

	std::string toString(){
		if(*(this->inferenceSymbol) == this->getDefault()){
			return *(this->inferenceSymbol);
		}
		else{
			return this->space->toString();
		}
	};
};

}
*/