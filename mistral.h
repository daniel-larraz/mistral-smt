/*
 * mistral.h
 *
 *  Created on: Dec 4, 2012
 *      Author: isil
 */


/**
 * \mainpage MISTRAL
 * \image html mistral.png
 *
 *
 * \section intro_sec Introduction
 * Mistral is an <a href = "http://en.wikipedia.org/wiki/Satisfiability_Modulo_Theories">
 * SMT solver </a> which decides satisfiability of formulas in the
 * <a href="http://en.wikipedia.org/wiki/Presburger_arithmetic"> theory
 * of linear arithmetic over integers </a> and theory of equality with
 * uninterpreted functions. Mistral is written in C++
 * and can be used both through a graphical user interface as well as a C++ library.
 * In addition to deciding satisfiability, Mistral
 * consists of the following modules:
 * - \ref explain which can be used for performing
 * <a href="http://en.wikipedia.org/wiki/Abductive_reasoning"> abductive inference </a>
 * - \ref simplify which can be used for simplifying formulas
 * - \ref cooper which performs quantifier elimination
 * - \ref msa which can be used to compute minimum satisfying assignments
 *
 * \section req_section Requirements and Installation
 * You can obtain the source code of Mistral from http://www.cs.wm.edu/~tdillig/mistral-1.1.tar.gz
 *
 *
 * Mistral has been tested to compile on Ubuntu 12.04.
* First, to compile Mistral, you need to have cmake installed on your system as
* well as a set of other required libraries. On a recent Ubuntu/Kubuntu system, the
* following command will install everything you need:
\verbatim
sudo apt-get install libc6-dev-i386 gettext gawk flex libmpfr-dev cmake  \
kdelibs5-dev libgtkmm-2.4-dev libboost-thread-dev libboost-serialization-dev \
libglademm-2.4-dev graphviz doxygen g++ libgmp-dev build-essential flex bison  \
binutils-gold
\endverbatim


* Once you have cmake installed, go to the mistral folder and type the following commands
\verbatim
mkdir build
cd build
cmake ..
make
\endverbatim

* Once you type these commands, you can use Mistral either through
* a graphical user interface or as a library.
* For using Mistral from the GUI, type the following commands:

\verbatim
cd ui
../build/ui/mistral_ui
\endverbatim

* You can only start the Mistral GUI from  the /mistral/ui folder

* If you want to use Mistral as a library, see the Section \ref start.

* \section start Getting Started
* Logical formulas are represented in Mistral using the Constraint type.
* For example, you can construct boolean constants true and false in the following way:
* \verbatim
Constraint t(true);
Constraint f(false);
\endverbatim
Here "t" represents the boolean constant "true" and "f" represents the boolean constant false.
More complicated formulas are constructed using Term. Terms  can be ConstantTerm
(such as 0), VariableTerm (such as x), ArithmeticTerm (such as 3x + 2y), or
FunctionTerm (such as f(g(x, 0), a)). Here is an example illustrating creation of
 various kinds of terms.
\verbatim
   Term* t1 = VariableTerm::make("a");
   Term* t2 = VariableTerm::make("b");

   map<Term*, long int> elems;
   elems[t1] = 3;
   elems[t2] = 7;
   Term* t3 = ArithmeticTerm::make(elems, 2);

   vector<Term*> args;
   args.push_back(t1);
   Term* t4 = FunctionTerm::make("f", args);

\endverbatim
Here, term t3 represents the arithmetic term 3a + 7b + 2,
and term t4 represents the function term f(a).

Now, using these terms, we can create more interesting constraints. For example,
the following code snippet shows how to create the constraint f(a) <= b & 3a + 7b + 2 = 4:

\verbatim
Constraint c1(t4, t2, ATOM_LEQ);
Constraint c2(t3, ConstantTerm::make(4), ATOM_EQ);
Constraint c3 = c1 & c2;
\endverbatim

In this example, c1 corresponds to the formula f(a) <= b, c2 represents the formula
3a + 7b + 2 =4, and c3 represents the conjunction of c1 and c2. Mistral overloads the C++
operators &, |, ! for performing conjunction, disjunction, and negation of formulas
respectively. For example, in the following code snippet:

\verbatim
Constraint c4 = !c1;
Constraint c5 = c4 | c2;
\endverbatim

c4 represents the formula f(a) > b and c5 represents the disjunction of f(a) > b
and 3a + 7b + 2 = 4.

\section sat Checking Satisfiability and Validity

Now that we can construct constraints, we can use Mistral to decide their satisfiability
and  validity:

\verbatim
bool res1 = c5.sat_discard();
bool res2 = c3.valid_discard();
bool res3 = c5.equivalent(c3);
\endverbatim

Here res1 is true if and only if the formula represented by c5 is satisfiable,
and res2 is true if and only if the formula represented by c3 is valid. The
equivalent method of Constraint is used to check equivalence. Therefore, res3 is true
if and only if c2 and c5 are equivalent.

There is also another way to check satisfiability and validity in Mistral using
the sat() and valid() methods rather than sat_discard() and valid_discard().
The difference between these is that sat() and valid() also simplify the formula,
as described in this
<a href="http://www.cs.wm.edu/~idillig/sas2010.pdf"> publication </a>. Therefore,
the methods sat and valid are more expensive than sat_discard and valid_discard and should
only be used if you want the formula to get simplified after performing a satisfiability or
validity query. The section \ref simplify describes this in more detail.

Given a satisfiable constraint, Mistral also provides a way for obtaining satisfying
assignments as follows:

\verbatim
map<Term*, SatValue> assignment;
bool res = c5.get_assignment(assignment);
for(auto it = assignment.begin(); it!= assignment.end(); it++)
{
    Term* t = it->first;
    SatValue sv = it->second;
    cout << " Term: " << t->to_string() << " satisfying assignment: " << sv.to_string() << endl;
}
\endverbatim

The code snippet above shows how to obtain and print the satisfying assignment for
formula represented by c5. In this code snippet, res indicates whether c5 is satisfiable,
and, if res is true, "assignment" is a full satisfying assignment from each term
in the formula to a satisfying value.


* \section further Other Functionalities
*
In addition to checking satisfiability and validity, Mistral can be used for
performing abductive inference, simplifying constraints, performing quantifier elimination,
and computing minimum satisfying assignments. For tutorials on using these functionalities,
please refer to the \ref explain, \ref simplify, \ref cooper, and \ref msa pages.

* \section people People
Mistral is developed and maintained by:
 - <a href = "http://www.cs.wm.edu/~tdillig/">Thomas Dillig </a>
 - <a href = "http://www.cs.wm.edu/~idillig/">Isil Dillig </a>


 Other people who
 have contributed to some of the ideas implemented in Mistral include:
 - <a href = "http://www.kenmcmil.com/"> Ken McMillan </a>
 - <a href = "http://theory.stanford.edu/~aiken/"> Alex Aiken </a>

* \section publications Publications
* The techniques described in the following publications are incorporated in Mistral:
* - <a href = "http://www.cs.wm.edu/~idillig/cav2009.pdf"> Cuts-from-Proofs: A Complete and Practical Technique for
* Solving Linear Inequalities over Integers </a>,
* Isil Dillig, Thomas Dillig, and Alex Aiken, CAV 2009
* - <a href = "http://www.cs.wm.edu/~idillig/sas2010.pdf">
* Small Formulas for Large Programs: Constraint Simplification for
* Scalable Static Analysis </a>, Isil Dillig, Thomas Dillig, Alex Aiken, SAS 2010
* - <a href = "http://www.cs.wm.edu/~idillig/cav2012.pdf">
* Minimum Satisfying Assignments for SMT </a>, Isil Dillig, Thomas Dillig, Ken McMillan,
* Alex Aiken, CAV 2012
* \section ack Acknowledgments
We are grateful to the developers of the <a href="http://minisat.se/"> MiniSAT </a> SAT solver, which forms the
SAT solving engine of Mistral. We also thank the developers of the <a href="http://gmplib.org/">
GNU MP Bignum Library </a>.
\section license License and Support
Mistral is freely available for research purposes under the
<a href="http://www.gnu.org/licenses/gpl.html"> GPL license </a>.


* \page explain Explain
*   \image html explain4.png
*   \section abduction What is Abductive Inference?
Explain is the component of Mistral that performs abductive inference (or abduction).
Given a formula \f$ \phi_1 \f$ and another formula \f$ \phi_2 \f$, abduction is
the problem of finding an explanatory hypothesis  \f$ \psi \f$ such that:
  \f$
\phi_1 \land \psi \models \phi_2
  \f$ and
  \f$
\phi_1 \land \psi
  \f$ is satisfiable. In contrast to logical deduction which
  reaches valid conclusions from a set of premises, abduction is used to infer
  likely premises for a given conclusion. In general, there are many solutions to
  an abductive inference problem, but typically, concise and  general solutions are
  more desirable than others. The abductive solutions computed by Explain are guaranteed
   to contain a minimum number of variables among all other abductive solutions. Furthermore,
   among other solutions that contain the same set of variables, the solutions computed by
   Explain are as logically weak as possible.

   \section use Using Explain
   To perform abductive inference, use the abduce functions in Constraint.h.
   Here is an example
   illustrating a typical usage of abduction:

   \verbatim
  Term* x = VariableTerm::make("x");
  Term* y = VariableTerm::make("y");
  Term* z = VariableTerm::make("z");

  Constraint c1(x, ConstantTerm::make(0), ATOM_LEQ);
  Constraint c2(y, ConstantTerm::make(1), ATOM_GT);
  Constraint premises = c1 & c2;

  map<Term*, long int> elems;
  elems[x] = 2;
  elems[y] = -1;
  elems[z] = 3;
  Term* t = ArithmeticTerm::make(elems);
  Constraint conclusion(t, ConstantTerm::make(10), ATOM_LEQ);

  Constraint explanation = conclusion.abduce(premises);
  cout << "Explanation: " << explanation << endl;
   \endverbatim

 Here, constraint c1 represents the formula x<=0, and c2 represents the formula
 y > 1. Hence, the constraint premises represents x<=0 & y > 1. The constraint conclusion
stands for the formula 2x - y +3z  <=10. Here, we use the abduce function to find a formula
called "explanation" such that premises and explanation together imply the conclusion
and the premises and explanation are consistent with each other. For this example,
the solution that is computed by Explain (and printed out at the last line) is x<=4.

Explain also supports computing abductive solutions that must be consistent with a set
of given formulas. For example, suppose that we want the abductive solution to be
consistent with z > 1 as well as x < 2. In this case, we can create a set of
consistency requirements and pass it as an argument to abduce. The following code
snippet illustrates this functionality:

\verbatim
Constraint c3(z, ConstantTerm::make(1), ATOM_GT);
Constraint c4(x, ConstantTerm::make(2), ATOM_LT);
set<Constraint> reqs;
reqs.insert(c3);
reqs.insert(c4);
explanation = conclusion.abduce(premises, reqs);
\endverbatim

In this case, Explain will ensure that the computed abductive solution is consistent
with every formula in the set reqs.

Finally, in some cases, we might prefer abductive solutions that contain
certain variables over others. For instance, in our earlier example, we might want
abductive solutions containing variables z,y over solutions that contain x. For this reason,
Explain allows specifying costs for each variable. Here is an example illustrating this
functionality:

\verbatim
map<Term*, int> costs;
costs[x] = 5;
costs[y] = 1;
costs[z] = 1;
explanation = conclusion.abduce(premises, reqs, costs);
\endverbatim

In this case, since the cost of x is higher than the sum of the costs of y,z
Explain will return solutions that contain both y and z rather than solutions
that contain only x.


* \page simplify Simplify
*    \image html simplify2.png
*    \section simplify-intro What is Simplify?
*    Simplify is the constraint simplification engine of Mistral, which
*    implements the algorithm described in
*    <a href="http://www.cs.wm.edu/~idillig/sas2010.pdf"> this paper</a>.
*    It brings formulas to a so-called "simplified form" which has the guarantee
*    that no subpart of the formula is redundant. Simplification can be useful either
*    to make the constraint more readable by humans or in contexts where it is
*    desirable or beneficial to keep formulas as concise and as non-redundant as possible.
*
*    \section use-simplify How to Use Simplify
*    Using the simplification functionality of constraint is very simple: It simplifies
*     formulas every time you make a satsfiability or validity query using
*     sat() or valid(). The following example illustrates how simplification works:
*
     \verbatim
     Term* x = VariableTerm::make("x");
     Term* y = VariableTerm::make("y");

     Constraint c1(x, ConstantTerm::make(0), ATOM_GT);
     Constraint c2(y, ConstantTerm::make(1), ATOM_EQ);
     Constraint c3 = (c1 | (!c1 & c2));

     cout << "Redundant constraint: " << c3 << endl;
     c3.sat();
     cout << "Simplified constraint: " << c3 << endl;
    \endverbatim

    Here, we construct a constraint c3, which represents the formula x>0 | (x<=0 & y=1).
    However, as a result of the satisfiability query c3.sat(), c3 gets simplified, and the
    formula that is printed at the last line is the simpler constraint x>0| y=1.
    Simplify guarantees that any formula that is valid gets simplified to true, and any
    unsatisfiable formula simplifies to false. If simplification is not desired or needed,
    use the sat_discard() and valid_discard() methods.

    Another functionality that Simplify provides is to simplify a formula with
    respect to another one. This is achieved using the assume function provided
    in Constraint.h. Here is an example illustrating the use of assume:

    \verbatim
     Term* x = VariableTerm::make("x");
     Term* y = VariableTerm::make("y");

     Constraint c1(x, ConstantTerm::make(1), ATOM_GT);
     Constraint c2(y, ConstantTerm::make(2), ATOM_EQ );
     Constraint c3 = c1 | c2;

     cout << "Original constraint: " << c3 << endl;
     c3.assume(!c1);
     cout << "After assuming !c1: " << c3 << endl;

    \endverbatim

Here, we first construct a constraint c3, which represents (x > 1 | y = 2).
After the assume operation at the last line, the new constraint c3 now becomes y=2,
since we are assuming that x <=1.

*
*
*
*
*
* \page cooper Cooper
* \image html cooper2.png

\section cooper-intro What is Cooper?
Cooper is the component of Mistral for performing quantifier elimination.
It implements <a href="http://www.cs.wm.edu/~idillig/cs780-02/Cooper.pdf">
Cooper's method </a> for eliminating quantifiers in Presburger arithmetic (i.e., linear
arithmetic over integers).

\section cooper-use How to Use Cooper
To perform existential quantifier elimination, one can use the eliminate_evar methods provided
in Constraint.h. Here is a simple example illustrating existential quantifier elimination:

\verbatim
VariableTerm* x = VariableTerm::make("x");
VariableTerm* y = VariableTerm::make("y");

map<Term*, long int> elems;
elems[x] = 1;
elems[y] = 1;
Term* t = ArithmeticTerm::make(elems, 0);

Constraint c1(x, ConstantTerm::make(0), ATOM_LT);
Constraint c2(t, ConstantTerm::make(0), ATOM_GEQ);
Constraint c3 = c1 & c2;

cout << "Before elimination: " << c3 << endl;
c3.eliminate_evar(x);
cout << "After elimination: " << c3 << endl;
\endverbatim

Here, we first construct a constraint c3 which represents the formula x<0 & x+y >=0.
We then call the eliminate_evar method to eliminate variable x as an existentially quantified
variable. The constraint that is printed at the last line is y>0, which is the result
of performing quantifier elimination.

There is also an interface that allows eliminating multiple variables at the same time.
For instance, in the previous example, here is how we would eliminate both x and y
from constraint c3:

\verbatim
set<VariableTerm*> vars;
vars.insert(x);
vars.insert(y);
c3. eliminate(vars);
cout << "Result of quantifier elimination: " << c3 << endl;
\endverbatim

In addition, Cooper provides an interface for eliminating universally quantified variables.
For this purpose, one can use the eliminate_uvar method as follows:
\verbatim
VariableTerm* x = VariableTerm::make("x");
VariableTerm* y = VariableTerm::make("y");

map<Term*, long int> elems;
elems[x] = 1;
elems[y] = 1;
Term* t = ArithmeticTerm::make(elems, 0);

Constraint c1(x, ConstantTerm::make(0), ATOM_GEQ);
Constraint c2(t, ConstantTerm::make(0), ATOM_LT);
Constraint c3 = c1 & c2;

cout << "Before elimination: " << c3 << endl;
c3.eliminate_uvar(x);
cout << "After elimination: " << c3 << endl;
\endverbatim

Here, the original constraint c3 is (x>=0 | x+y<0). After eliminating x as a
universally quantified variable, we obtain y <= 0.



*
* \page msa MSAFinder
* \image html msa.png

\section msa-intro What is MSAFinder?
MSAFinder is the component of Mistral that can be used to compute
minimum satisfying assignments (MSA) of Presburger arithmetic formulas.
An MSA of a formula F is a partial satisfying assignment of F that contains as few variables
as possible, but is still sufficient to imply the validity of the formula. A precise definition of MSAs as well as the algorithm MSAFinder uses
to compute MSAs is described <a href="http://www.cs.wm.edu/~idillig/cav2012.pdf">
in this paper</a>.

\section use-msa Using MSAFinder

To compute minimum satisfying assignments of Presburger arithmetic formulas,
use the msa method provided in Constraint.h. Here is an example code snippet
that illustrates how to compute MSAs:

\verbatim
Term* x = VariableTerm::make("x");
Term* y = VariableTerm::make("y");
Term* z = VariableTerm::make("z");

map<Term*, long int> elems1;
elems1[x] = 1;
elems1[y] = 1;
Term* t1 = ArithmeticTerm::make(elems1, 0);

map<Term*, ling int> elems2;
elems2[x] = 1;
elems2[y] = 1;
elems2[z] = 1;
Term* t2 = ArithmeticTerm::make(elems2, 0);

Constraint c1(t1, ConstantTerm::make(0), ATOM_GT);
Constraint c2(t2, ConstantTerm::make(5), ATOM_LT);
Constraint c3 = (c1 | c2);

map<Term*, SatValue> min_assign;
int min_vars = c3.msa(min_assign);
for(auto it = min_assign.begin(); it!= min_assign.end(); it++) {
	Term* t = it->first;
	SatValue sv = it->second;
	cout << t->to_string() << ":" << sv.to_string() << "\t";

}
\endverbatim

Here, c3 corresponds to the formula x+y>0 | x+y+z <=5. The return value, min_vars, of the msa
method tells us how many variables the MSA of c3 contains, and the map min_assign gives
the actual minimum satisfying assignment.  The for loop in the above code snippet prints
a satisfying assignment for each variable in the msa. In this particular example,
the minimum satisfying assignment of c3 contains only one variable, namely z,
and an MSA of c3 is z=0.

When computing minimum satisfying assignments, one can also assign a cost to each variable.
In this case, the msa method yields a partial satisfying assignment that minimizes the sum of
the costs of each variable used in the assignment. For instance, consider the cost
function C such that C(x) = 1, C(y) = 1, C(z) = 5. Under this cost function, z= 0 is no longer
an MSA of (x+y > 0 | x+y+z <=5 ) because the cost of the assignment z=0 is 5, and there exists
a satisfying assignment with smaller cost, such as y= 0 and x=1. The following code
snippet shows how to obtain an MSA for c3 subject to a cost function C(x) = 1, C(y) = 1,
C(z) =5.

\verbatim
map<VariableTerm*, int> costs;
costs[x] = 1;
costs[y] = 1;
costs[z] = 5;


map<Term*, SatValue> min_assign;
int msa_cost = c3.msa(min_assign, costs);
for(auto it = min_assign.begin(); it!= min_assign.end(); it++) {
	Term* t = it->first;
	SatValue sv = it->second;
	cout << t->to_string() << ":" << sv.to_string() << "\t";

}
\endverbatim

For this example, msa_cost is 2 and the MSA is printed as y:0  x:1.

*/

#include <string>
using namespace std;

#include <vector>
#include <map>
#include <set>
using namespace std;


class Leaf;
class SatValue;
class VariableTerm;
class Term;
class AccessPath;
class CNode;
/*
 * MISTRAL is the the constraint solver for Compass.
 */



void register_output_callback(void (*write_fn)(string));

void display(string s);

