#include <unistd.h>
#include <sys/wait.h>
#include <cstdio>
#include <string>
#include <iostream>
#include "oracle.h"

Oracle::Oracle(std::string path)
{
	char *const arguments[] = {(char*) "coqtop", (char*)"-quiet", (char*)"-l", (char*)"Tactic.v", nullptr};
	const int write = 1;
	const int read = 0;


	int pipes [4];
	int *ext_to_oracle = &pipes[0];
	int *oracle_to_ext =&pipes[2];

	//TODO: Rewrite this to handle errors
	pipe (ext_to_oracle);
	pipe (oracle_to_ext);

	pid_t id = fork();

	if(id == 0)
	{
		close(ext_to_oracle[write]);
		close(oracle_to_ext[read]);
		
		m_Question = ext_to_oracle[read];
		m_Answer = oracle_to_ext[write];

		dup2(m_Question, STDIN_FILENO);
		dup2(m_Answer, STDOUT_FILENO);
		dup2(m_Answer, STDERR_FILENO);


		execv((path + arguments[0]).c_str(), arguments);

		perror((std::string(arguments[0]) + " died: ").c_str());
		/*Program stopped: error*/
		_exit(0);			
	}
	else
	{
		close(ext_to_oracle[read]);
		close(oracle_to_ext[write]);

		m_Question = ext_to_oracle[write];
		m_Answer = oracle_to_ext[read];
		ask("Lemma oiashd A B C (H : A -> B -> C) (H1: A -> B) (H2: A) : C");
	}

}

Oracle::~Oracle(void)
{
	close(m_Question);
	close(m_Answer);
	wait(nullptr);
}

std::string Oracle::showLemma(void)
{
	ask("show_lemma");

	return listen();
}

void Oracle::click(std::string hyp)
{
	ask("click " + hyp);
}

void Oracle::ask(std::string query)
{
	query += ".\n";
	write(m_Question, query.c_str(), query.length());
	fsync(m_Question);	
}

std::string Oracle::listen(void)
{
	#define SIZE_BUFFER_ORACLE 1000
	const std::string Eot_good = "EOT_COQ";
	const std::string Eot_error = "Error: ";
	fsync(m_Answer);

	char Buffer[SIZE_BUFFER_ORACLE];
	std::string result;
	bool cond = true;
	while(cond)
	{
		int nb_read = read(m_Answer, Buffer, SIZE_BUFFER_ORACLE);
		if(nb_read > 0)
		{
			Buffer[nb_read] = '\0';
			result += Buffer;
			cond = (result.rfind(Eot_good) == std::string::npos) && 
			       (result.rfind(Eot_error) == std::string::npos);
		}
		else
		{
			cond = false;
		}
	}
	return result;
}
