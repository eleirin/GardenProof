#include <iostream>
#include "oracle.h"

using namespace std;
int main(void)
{
	Oracle ora("/home/epiphanie/.opam/down/bin/");	
	std::string hyp;

	while(hyp != "quit")	
	{	
		cout <<	ora.showLemma() << std::endl;
		cin >> hyp;
		ora.click(hyp);
		
	}
	

	return 0;
}
