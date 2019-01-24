// test the oracle.h

#include <iostream>
#include <string>
#include "oracle.h"

using namespace std;

int main(){
	
	string vecCC;
	string vecCCspace;

	GroundTruth gt = GroundTruth();

	cout<<"Please indicate the entity you want to annotate"<<endl;
	cin>> vecCC;
	gt.setVecKey(vecCC);

	cout<<"Please indicate the space for that entity"<<endl;
	cin>>vecCCspace;
	gt.setVecValue(vecCCspace);

	cout<<"The space for "<<gt.GetVecKey()<<" is "<<gt.GetVecValue()<<endl;

	return 0;
}