#ifndef HEAD_ORACLE
#define HEAD_ORACLE
#define EOT_GOOD "EOT_COQ"
#define EOT_ERROR "Error: "

#include <string>

class Oracle
{
	public:
		
		Oracle(std::string path); 
		~Oracle(void);
		std::string showLemma(void);
		void click(std::string hyp); 
	
	private:
		void ask(std::string query); 
		std::string listen(void); 
	
		int m_Question;
		int m_Answer;
};

#endif //HEAD_ORACLE
