
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "smt-parser.h"

#include "Solver.h"

using namespace std;

string read_file(const char* filename)
{
  string cur;
  ifstream myfile;
  myfile.open(filename);
  if(!myfile.is_open()) {
    std::ostringstream ss;
    ss << "failed to open file '" << filename << "'";
    throw invalid_argument(ss.str());
  }
  while(!myfile.eof())
  {
          string t;
          std::getline(myfile, t);
          cur+=t+"\n";
  }
  myfile.close();
  return cur;
}

void print_error(string s)
{
  cout << "(error \"" << s << "\")" << endl;
}


int main(int argc, char** argv)
{
  if (argc > 1) {
    try {
      string constraint = read_file(argv[1]);

      SmtResult res = smtlib_parse_constraint(constraint, &print_error);

      //cout << "Constraint: " << res.constraint->to_string() << endl;

      if(res.smt_command == CheckSat) {
        Solver s(res.constraint, UNSAT_SIMPLIFY);
        CNode* res = s.get_result();
        if(res->get_type() == FALSE_NODE) cout << "unsat";
        else cout << "sat";
        cout << endl;
      }
      else if (res.smt_command == GetAbduct) {
        //cout << "Conclusion: " << res.conclusion->to_string() << endl;
        Constraint premises(res.constraint);
        Constraint conclusion(res.conclusion);
        Constraint explanation = conclusion.abduce(premises);
        cout << "; " << explanation << endl;
        auto cnodes = explanation.get_cnodes ();
        cout << "(define-fun " <<  res.abduct_name->to_string()
             << " () Bool " << cnodes.first->to_prefix_notation() << ")" << endl;
      }
    }
    catch ( std::exception& e ) {
      print_error(e.what());
      return 2;
    }

    return 0;
  }
  else {
    cout << "Usage: " << argv[0] << " <problem.smt2>" << endl;
    return 1;
  } 
}


