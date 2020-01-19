 
 #include <iostream>
 #include "CNode.h"
 #include "Constraint.h"
 #include "term.h"

 
 /*
 * Compile as: g++ -I.. -I../cnode -I../solver -I../numeric-lib -I../term/ -std=c++0x -lgmp example.cpp ../build/libmistral.a ../build/parser/libparser.a -o my_project
 * The, run ./my_project
 */
 
 using namespace std;
 #include <string>
 #include <map>
 int main(int c, char** argv)
 {
   
   Term* t1 = VariableTerm::make("a");
   Term* t2 = VariableTerm::make("b");
   map<Term*, long int> elems;
   elems[t1] = 3;
   elems[t2] = 7;
   Term* t4 = ArithmeticTerm::make(elems, 0);
   cout << "Term t4 is: " << t4->to_string() << endl;
   
   
   Term* t3 = VariableTerm::make("x");
   
   
   Constraint c1(t4, t3, ATOM_GT);
   cout << "c1: " << c1 << endl;
   
   Constraint c2(t1, ConstantTerm::make(5), ATOM_EQ);
   cout << "c2: " << c2 << endl;
   
   c2 &=c1;
   
   cout << "c2: " << c2 << endl;
   
   assert(t1->get_term_type() == VARIABLE_TERM);
   VariableTerm* vt = static_cast<VariableTerm*>(t1);
   c2.eliminate_evar(vt);
   
   cout << "c2 after eliminating a: " << c2 << endl;
   
   
   //replace b by 88;
   c2.replace_term(t2, ConstantTerm::make(88));
   
   cout << "c2 after replacing b with 88: " << c2 << endl;
   
   
   //Some satifiability queries
   Constraint c3(t3, ConstantTerm::make(7), ATOM_EQ);
   
   cout << "c3:: " << c3 << endl;
   Constraint new_c = c3 & c2;
   cout << "new_c: " << new_c << endl;
   
   cout << "Is this constraint SAT? (use sat_discard() to check this.)" << (new_c.sat_discard() ? " yes " : " no " ) << endl;
   cout << "~~~~~~~~~~~~~~~~~~~~~ " << endl;
   cout << "Alternatively, use sat() to check satisfiability & bring constraint to simplified form " << endl;
   cout << "(See paper http://www.stanford.edu/~isil/sas2010.pdf). Use this if you reuse the constraint or want it simplified." << endl;
   cout << "~~~~~~~~~~~~~~~~~~~~~ " << endl;
   cout << "Result of sat(): " << (new_c.sat() ? " yes " : " no " ) << endl;
   cout << "Simplified Constraint: " << new_c << endl;
   
   
   
 }