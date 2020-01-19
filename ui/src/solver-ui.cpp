/*
 * The GTK solver UI front-end for interactive constraint solving and
 * regression testing with Mistral.
 */

#include <iostream>
#include <pwd.h>
#include <gtkmm.h>
#include <libglademm.h>
#include <assert.h>
#include <fstream>
#include <vector>
#include <map>
#include <sys/types.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <gtk/gtk.h>
#include "ExistentialEliminator.h"
#include "VariableEliminator.h"
#include <string.h>

#include <string.h>

#include "ConstantTerm.h"
#include "ArithmeticTerm.h"
#include "Constraint.h"
#include "MSAFinder.h"
#include "mistral-parser.h"
#include "Optimizer.h"
#include "../util.h"
#include "smt-parser.h"


#define LAST_FILE ".mistral.mcf"

void (*_display)(string s) = NULL;

void register_output_callback(void(*write_fn)(string)) {
	_display = write_fn;
}

void display(string s) {
	_display(s);
}





#include <dirent.h>
#include <errno.h>

#include "Solver.h"
#include "cnode.h"


using namespace std;

#define TIMEOUT_EXIT_STATUS 14
#define CANCEL_EXIT_STATUS 9

/*
 * Spurious Mistral dependencies -- fixme
 *
 */

Term* _make_ap(long int c)
{
	ConstantTerm* ct;
	ct = new ConstantTerm(c);
	return ct;
}

Term*_make_ap(const string & name)
{
	VariableTerm* vt = new VariableTerm(CNode::get_varmap().get_id(name));
	return vt;
}

Term* _make_ap(const map<Term*, long int>& elems,long int constant)
{
	ArithmeticTerm* at;
	at = new ArithmeticTerm(elems, constant);
	return at;
}

Term* _make_ap(const string & name, vector<Term*>& args, bool invertible)
{
	FunctionTerm* fv;
	fv = new FunctionTerm(CNode::get_varmap().get_id(name), args, invertible);
	return fv;
}


class AccessPath;
class IndexVarManager;
class Term;
class Variable;
AccessPath* constraint_to_ap(CNode* c,
		IndexVarManager& ivm)
{
	assert(false);
}

CNode* ap_to_constraint(AccessPath *ap)
{
	assert(false);
}

void replace_access_path(AccessPath* ap_old, AccessPath* ap_new)
{
	assert(false);
}

Term* make_term(AccessPath* ap_old)
{
	assert(false);
}

AccessPath* make_ap_from_term(Term* t, IndexVarManager& ivm,
		set<AccessPath*>& to_add, map<Term*, Variable*>& replacement_map)
{
	assert(false);
}

namespace sail {
class Variable
{
	Variable* clone();
};

Variable* Variable::clone()
{
	assert(false);
}
}

/*
 * Dependencies end
 */

enum sat_query_status
{
	SAT,
	UNSAT,
	TIMEOUT,
	CANCEL,
	VERIFY_ERROR,
	NOT_SAT_BY_ASSIGNMENT_ERROR,
	CRASH,
	PARSE_ERROR
};

int rgfd[2];


/*
 * Global variables
 */
string levels [] = {
		"Solve only",
		"Solve only (DNF)",
		"Boolean Simplify",
		"Hybrid Simplify",
		"Theory Simplify"
		};

/*
 * Solving Tab
 */
Gtk::Button* solve_button = NULL;
Gtk::Button* cancel_button = NULL;
Gtk::Button* add_regression_button = NULL;
Glib::RefPtr<Gtk::TextBuffer> input_buffer;
Glib::RefPtr<Gtk::TextBuffer> output_buffer;

Glib::RefPtr<Gtk::TextBuffer> input_elim_buffer;
Glib::RefPtr<Gtk::TextBuffer> output_elim_buffer;

Gtk::SpinButton* timeout_button = NULL;
Gtk::SpinButton* select_regression_button = NULL;
int timeout = 0;
Gtk::CheckButton* assign_button = NULL;
Gtk::CheckButton* single_process_button = NULL;
Gtk::CheckButton* no_verify_button = NULL;
Gtk::CheckButton* print_stats_button = NULL;

Gtk::ComboBox* level_combobox = NULL;
Glib::RefPtr<Gtk::ListStore> f_refTreeModel;

Gtk::Entry* path = NULL;


/*
 * Regression Tab
 */
Gtk::ProgressBar* regression_progressbar = NULL;
Gtk::Label* success_label = NULL;
Gtk::Label* failed_label = NULL;
Gtk::Label* time_label = NULL;
Gtk::Image* status_image = NULL;
Gtk::Button* run_regressions_button = NULL;
Gtk::Button* cancel_regressions_button= NULL;
Gtk::Label* regression_status = NULL;
Gtk::TreeView * regression_treeview = NULL;
Gtk::CheckButton* only_failed = NULL;
Gtk::CheckButton* show_all = NULL;
Gtk::Entry* regression_filter = NULL;

/*
 * MSA Tab
 */
Gtk::Button* msa_button = NULL;
Glib::RefPtr<Gtk::TextBuffer> msa_input_buffer;
Glib::RefPtr<Gtk::TextBuffer> msa_high_cost_buffer;
Glib::RefPtr<Gtk::TextBuffer> msa_output_buffer;
Glib::RefPtr<Gtk::TextBuffer> msa_invariants_buffer;

/*
 * Optimization Tab
 */

Glib::RefPtr<Gtk::TextBuffer> opt_constraint_buffer;
Glib::RefPtr<Gtk::TextBuffer> opt_cost_buffer;
Gtk::Entry* opt_bound;

Gtk::CheckButton* opt_check_max = NULL;
Gtk::Button* opt_button = NULL;

Gtk::Entry* opt_value;
Glib::RefPtr<Gtk::TextBuffer> opt_assignment_buffer;


class OptionColumns : public Gtk::TreeModel::ColumnRecord
{
public:
	OptionColumns()
  {
	  add(col_id);

  }
  Gtk::TreeModelColumn<string> col_id;


};
OptionColumns option_columns;

simplification_level cur_level;
bool use_dnf;



bool check_command_line(int argc, char** argv);
void init_solve_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml);
void init_regression_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml);
void init_msa_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml);
void init_opt_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml);
void solve_button_clicked();
void add_regresssion_button_clicked();
void timeout_changed();
void select_regression_changed();
void level_changed();
bool is_sat(CNode* constraint);
bool constraint_equivalent(CNode* c1, CNode* c2);
sat_query_status run_mistral(string node, int & ticks, bool new_process,
		bool regress, int & size);
string assignment_to_string(map<Term*, SatValue>* assignments);
double ticks_to_seconds(int ticks);
sat_query_status invoke_mistral(CNode* node, int & ticks, int & size,
		string* info = NULL);



/*
 * Regression related functions, data types & globals
 */

#define REGRESSION_FILE_SUFFIX ".mcf"
#define REGRESSION_FOLDER "regressions"

struct solve_regression
{
	bool status;
	string constraint;
};

struct eliminate_regression
{
	string constraint;
	string elimination_result;
};

struct solve_regression_result
{
	string id;
	bool passed;
	sat_query_status actual_status;
	int ticks;
	int size;
};

map<string, solve_regression> solve_regressions;
map<string, solve_regression_result> solve_regressions_results;

map<string, eliminate_regression> eliminate_regressions;
set<string> solve_constraints;

string current_directory = "";


class RegressionModelColumns : public Gtk::TreeModel::ColumnRecord
{
public:
  RegressionModelColumns()
  {
	  add(col_id);
	  add(col_status);
	  add(col_res);
	  add(col_time);
	  add(col_size);

  }
  Gtk::TreeModelColumn<string> col_id;
  Gtk::TreeModelColumn<string> col_status;
  Gtk::TreeModelColumn<string> col_res;
  Gtk::TreeModelColumn<string> col_time;
  Gtk::TreeModelColumn<string> col_size;

};
RegressionModelColumns regression_columns;
Glib::RefPtr<Gtk::ListStore> regression_model_ref;




void load_solve_regressions();
void get_all_files(string dir, set<string> & files, string suffix);
void add_solve_regression(string file, string regression);
void fill_solve_regressions(set<string> & files);
void refresh_solve_regression_info();
void update_regress_treeview();
string strip(string s);

void path_changed()
{
	string tt = strip(path->get_text());
	if(tt == "") current_directory = "";
	else current_directory = "/" + tt;

	//cout << "dir: " << current_directory << endl;
}

string current_filter = "";

Glib::Mutex* m;
Glib::Dispatcher* solve_regression_info_changed;

Glib::Mutex* dm;
Glib::Dispatcher* display_changed;
Glib::Dispatcher* solve_status;

void regression_filter_changed()
{
	Glib::Mutex::Lock l(*m);
	string tt = strip(regression_filter->get_text());
	current_filter = tt;
	update_regress_treeview();

	//cout << "dir: " << current_directory << endl;
}

string strip(string s)
{
	string res;
	for(unsigned int i=0; i < s.size(); i++)
	{
		if(s[i] == ' ' || s[i] == '\n' || s[i] == '\t') continue;
		res+=s[i];
	}
	return res;
}




void load_solve_regressions()
{
	set<string> files;
	get_all_files(REGRESSION_FOLDER, files, REGRESSION_FILE_SUFFIX);
	set<string>::iterator it = files.begin();
	/*
	for(; it != files.end(); it++)
	{
		cout << "File: " << *it << endl;
	}*/
	fill_solve_regressions(files);
	update_regress_treeview();
	select_regression_button->set_range(0, solve_regressions.size() - 1);
	//cout << "num regressions: " << solve_regressions.size() << endl;
}

string get_line(string s, int line, bool include_later_lines = false)
{
	string first_line;
	unsigned int i = 0;

	while(i<s.size() && (s[i] == ' ' || s[i] == '\n' || s[i] == '\t')) i++;
	while(line >= 0 && i < s.size())
	{
		first_line = "";

		while(i<s.size() &&
				((line == 0 && include_later_lines) ||
						s[i]!='\n')){
			first_line +=s[i++];
		}
		i++;
		line--;
	}

	return first_line;
}

bool is_solve_regression(string s)
{
	string first_line = get_line(s, 0);
	//cout << "first line: " << first_line << endl;
	if(first_line.find("solve")!=string::npos) return true;
	return false;
}

string read_file(string file)
{
	ifstream myfile;
	myfile.open(file.c_str());
	if(!myfile.is_open()) return "";
	string cur;
	while(!myfile.eof())
	{
		string t;
		std::getline(myfile, t);
		cur+=t+"\n";
	}
	myfile.close();
	return cur;
}

void add_solve_regression(string file, string regression)
{
	string status_line = get_line(regression, 1);
	//cout <<"status line: " << status_line << endl;

	bool sat;
	if(status_line.find("UNSAT")!=string::npos) sat = false;
	else if(status_line.find("SAT")!=string::npos) sat = true;
	else {
		//cout << "Error:  " << status_line << endl;
		return; //
	}

	string constraint = get_line(regression, 2, true);
	solve_regression sr;
	sr.status = sat;
	sr.constraint = constraint;
	solve_regressions[file] = sr;
	solve_constraints.insert(strip(constraint));

}

void fill_solve_regressions(set<string> & files)
{
	solve_regressions.clear();
	solve_constraints.clear();
	set<string>::iterator it = files.begin();
	for(; it!= files.end(); it++)
	{
		string regression = read_file(*it);
		if(!is_solve_regression(regression)) continue;
		add_solve_regression(*it, regression);
	}
}

void create_folder(string path)
{
	string cur = "";
	for(unsigned int i=0; i < path.size(); i++)
	{
		cur+=path[i];
		if(path[i]=='/' || i == path.size()-1) {
			string dir = cur;
			mkdir(dir.c_str(), S_IRWXU);
		}

	}

}

int last_status = -1;
string last_solve_input = "";

void add_regresssion_button_clicked()
{
	load_solve_regressions();

	string input_str = input_buffer->get_text();
	string strip_input_str = strip(input_str);
	if(strip_input_str == "") return;
	//cout << "input string: " << input_str << "  " << last_solve_input << endl;
	if(strip_input_str != last_solve_input)
	{
		output_buffer->set_text("This regression has not yet been solved. "
						"It has not been added.");
		return;
	}

	//save_input_buffer();


	if(solve_constraints.count(strip_input_str) >0)
	{
		output_buffer->set_text("This regression already exists. "
				"It has not been added.");
		return;
	}


	if(last_status == -1)
	{
		output_buffer->set_text("This constraint cannot be solved. "
					"It has not been added.");
		return;
	}

	sat_query_status status = (last_status == 0 ? UNSAT: SAT);

	string dir = string(REGRESSION_FOLDER) + current_directory;
	string id;
	while(true)
	{
		int name = rand();
		if(name < 0) name *=-1;
		id = dir + "/" + int_to_string(name) + REGRESSION_FILE_SUFFIX;
		if(solve_regressions.count(id) == 0) break;
	}
	string file;
	file = "Type: solve\n";
	file+= string("Status: ") + (status == SAT ? "SAT" : "UNSAT") + "\n";
	file+=input_str + "\n";


	ofstream myfile;
	myfile.open(id.c_str());
	if(!myfile.is_open())
	{
		Gtk::MessageDialog dialog("Regression folder \"" + dir +
				"\" does not exist. Create?",
				         false, Gtk::MESSAGE_QUESTION,
				         Gtk::BUTTONS_OK_CANCEL);

		int result = dialog.run();
		//Handle the response:
		switch(result)
		{
			case(Gtk::RESPONSE_CANCEL):
			{
				return;
			}
			default:
			{
				break;
			}
		}
		create_folder(dir);
		myfile.open(id.c_str());
	}
	myfile << file;
	myfile.close();

	output_buffer->set_text(output_buffer->get_text() + "\nAdded Regression " +
			id);

	sync();
	load_solve_regressions();


}

string out_buffer;

void refresh_display()
{
	Glib::Mutex::Lock l(*dm);
	string current_text = output_buffer->get_text();
	current_text += out_buffer;
	out_buffer = "";
	output_buffer->set_text(current_text);

}

void display_out(string s)
{
	Glib::Mutex::Lock l(*dm);
	out_buffer +=s;
	display_changed->emit();

}

void display_line(string s)
{
	s += "\n";
	output_buffer->insert(output_buffer->end(), s);


}

/*
 * All the date here is protected by mutex m
 */
volatile bool regressions_canceled = false;
volatile bool regressions_finished = true;
volatile int num_success = 0;
volatile int num_failed = 0;
volatile double regression_time = 0.0;

volatile bool assign = false;//assign_button->get_active();
volatile bool print_stats = false;//print_stats_button->get_active();
volatile bool verify_simplification = true;//!no_verify_button->get_active();

volatile bool solve_active = false;

string last;




void solve_completed();


void print_error(string s)
{
	cout << "Error: " << s << endl;

}





int main(int argc, char** argv)
{
/*
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
    cout << "c1:" << c1 << endl;
    cout << "c2:" << c2 << endl;
    cout << "c3:" << conclusion << endl;

    Constraint explanation = conclusion.abduce(premises);
    cout << "Explanation: " << explanation << endl;
*/



	if(argc >=2 && strcmp(argv[1], "--regress") == 0)
	{
		verify_simplification = false;
		cur_level =  HYBRID_SIMPLIFY;
		set<string> files;
		get_all_files(REGRESSION_FOLDER, files, REGRESSION_FILE_SUFFIX);
		fill_solve_regressions(files);
		int total_ticks = 0;
		map<string, solve_regression>::iterator it = solve_regressions.begin();
		int start = clock();

		for(; it!= solve_regressions.end(); it++)
		{
			string id = it->first;
			//if(id.find("real") == string::npos) continue;
			string input = it->second.constraint;
			int ticks = 0;
			int size = 0;
			sat_query_status status = run_mistral(input, ticks, false, true, size);
			if((status == SAT && it->second.status) || (status == UNSAT &&
					it->second.status == false)){
				//success
			}

			else {
				cout << "Regression failed: " << id << endl;
			}

			total_ticks += ticks;
		}
		int end = clock();
		int abs_time = end-start;
		cout << "Total regression time: " << ticks_to_seconds(total_ticks) << endl;
		cout << "Total time including parsing & construction: " <<
		ticks_to_seconds(abs_time) << endl;
		return 0;
	}
	if(argc >=3 && strcmp(argv[1], "--file") == 0)
	{
		cur_level = THEORY_SIMPLIFY;
		verify_simplification = false;
		string file_name = argv[2];
		string constraint = read_file(file_name);
		int ticks = 0;
		for(int i=0; i < 1; i++)
		{
			int size;
			sat_query_status status = run_mistral(constraint, ticks, false, true,
					size);
			cout << "Solve time: " << ticks_to_seconds(ticks) << endl;
		}
		return 0;

	}

	if(argc >=3 && strcmp(argv[1], "--smtlibfile") == 0)
	{
		cur_level = UNSAT_SIMPLIFY;
		verify_simplification = false;
		string file_name = argv[2];
		string constraint = read_file(file_name);
		CNode* res = smtlib_parse_constraint(constraint, &print_error);
		if(res != NULL) {

			cout << "Constraint: " << res->to_string() << endl;
			Solver s(res, UNSAT_SIMPLIFY);
			CNode* res = s.get_result();
			if(res->get_type() == FALSE_NODE) cout << "UNSAT";
			else cout << "SAT";
			cout << endl;
		}

		return 0;

	}

	if(argc >=3 && strcmp(argv[1], "--smtlibfolder") == 0)
		{
			cur_level = UNSAT_SIMPLIFY;
			verify_simplification = false;
			string folder_name = argv[2];
			set<string> files;
			get_all_files(folder_name, files, ".smt2");
			cout  << "num files: " << files.size() << endl;
			for(set<string>::iterator it = files.begin(); it != files.end(); it++) {
				//cout << "File: " << *it << endl;
				int p_id = fork();
				if(p_id == 0)
				{
					alarm(10);
					cout << "$$$$$$$$$$$ BEGIN $$$$$$$$$ " << endl;
					string constraint = read_file(*it);
					string file = *it;
					if(file.find("bofill-scheduling")!= string::npos)
						exit(0);
					CNode* c = smtlib_parse_constraint(constraint, &print_error);
					cout << "^^^^^^^^^^^ PARSIING COMPLETED ^^^^^^^^^ " << endl;
					if(c == NULL) {
						cout << "File: " << *it << " PARSE ERROR "  << endl;
						exit(0);
					}

					/*if(c->get_type() == AND) {
						bool has_or = false;
						Connective* conn = static_cast<Connective*>(c);
						for(auto it2 = conn->get_operands().begin();
								it2 != conn->get_operands().end(); it2++)
						{
							CNode* n = *it2;
							if(n->get_type() == OR) {
								has_or = true;
								break;
							}
						}
						if(!has_or) {
							cout << "File: " << *it << " NO DISJUNCT "  << endl;
							exit(0);
						}
					}*/
					cout << "GETTING NUM VARS " << endl;
					set<Term*> vars;
					c->get_vars(vars);
					int num_vars = vars.size();
					cout << "NUM VARS: " << num_vars << endl;


					int ticks = clock();
					Solver s(c, UNSAT_SIMPLIFY);
					int end =  clock()-ticks;
					CNode* res = s.get_result();
					if(res->get_type() == FALSE_NODE) {
						cout << "*****File: " << *it << " UNSAT " << ticks_to_seconds(end)
								<< endl;
						exit(0);
					}
					cout << "*****File: " << *it << " SAT " <<
												ticks_to_seconds(end) << endl;

					set<CNode*> inv_set;
					map<VariableTerm*, int> costs;
					int msa_start = clock();
					MSAFinder msa_f(res, inv_set, costs);
					int msa_time = clock() - msa_start;
					int msa_size = msa_f.get_vars_in_msa().size();
					cout << "#File: " << *it << " Solve time: " <<
							ticks_to_seconds(end)
							<< " MSA time: " << ticks_to_seconds(msa_time)
							<< " #vars: " << num_vars <<
							" MSA size: " << msa_size << endl;




					exit(0);
				}
				int childExitStatus;
				pid_t ws = waitpid( p_id, &childExitStatus, 0);
				if(childExitStatus != 0) {
					cout << "File: " << *it << " TIMEOUT" << endl;
				}
				//cout << "process returned" << endl;




			}





			exit(0);
		}


	srand(time(NULL));
	if(check_command_line(argc, argv)) return 0;


	Glib::thread_init();
	m = new Glib::Mutex();
	solve_regression_info_changed = new Glib::Dispatcher();

	dm = new Glib::Mutex();
	display_changed = new Glib::Dispatcher();


	solve_regression_info_changed->connect(
			sigc::ptr_fun(refresh_solve_regression_info) );

	display_changed->connect(
				sigc::ptr_fun(refresh_display) );

	solve_status = new Glib::Dispatcher();
	solve_status->connect(
				sigc::ptr_fun(solve_completed) );

	display_changed->connect(
				sigc::ptr_fun(refresh_display) );

	register_output_callback(display_line);

	Gtk::Main kit(argc, argv);
	Gtk::Window* ui_window = NULL;
	Glib::RefPtr<Gnome::Glade::Xml> refXml =
				Gnome::Glade::Xml::create("solver.glade", "solverui");
	refXml->get_widget("solverui", ui_window);

	init_solve_elements(refXml);
	init_regression_elements(refXml);
	init_msa_elements(refXml);
	init_opt_elements(refXml);
	load_solve_regressions();

	/*
	 * load last run
	 */
	passwd *pw = getpwuid(getuid());
	assert(pw != NULL);
	string home_dir = pw->pw_dir;
	last = home_dir + "/" + LAST_FILE;
	ifstream in_file(last.c_str());
	string cc;
	if(in_file.is_open())
	{
		while(!in_file.eof())
		{
			string temp;
			std::getline(in_file, temp);
			cc+=temp;
			cc+="\n";
		}
		in_file.close();
	}
	input_buffer->set_text(cc);

	kit.run(*ui_window);
	delete m;
	delete dm;
	delete display_changed;
	delete solve_regression_info_changed;
	delete solve_status;
	return 0;

}





void solve_started()
{
	solve_active = true;
	solve_button->set_sensitive(false);
	add_regression_button->set_sensitive(false);
	cancel_button->set_sensitive(true);
}

string __node;
int* __ticks;
int* __size;
volatile bool __new_process;
volatile bool __regress;
volatile sat_query_status __res;


string solve_output = "";

void solve_completed()
{
	Glib::Mutex::Lock l(*m);
	if(__res == SAT) last_status = 1;
	else if(__res == UNSAT) last_status = 0;
	else last_status = -1;
	solve_active = false;
	solve_button->set_sensitive(true);
	if(last_status == 0 || last_status == 1)
		add_regression_button->set_sensitive(true);
	cancel_button->set_sensitive(false);
}

volatile int cur_process_id = -1;

void cancel_button_clicked()
{
	Glib::Mutex::Lock l(*m);
	if(cur_process_id == -1)
		return;
	kill(cur_process_id, CANCEL_EXIT_STATUS);
}


/*
 * Protection end
 */

void assign_changed()
{
	assign = assign_button->get_active();
}

void no_verify_changed()
{
	verify_simplification = !no_verify_button->get_active();
}

void print_stats_changed()
{
	print_stats = print_stats_button->get_active();
}

void input_buffer_changed()
{
	//CAN SWITCH BACK
	//string content = strip(input_buffer->get_text());
	string content = strip(input_buffer->get_text());
	if(last_status == -1) return;
	if(content == last_solve_input)
		add_regression_button->set_sensitive(true);
	else add_regression_button->set_sensitive(false);
}

void elim_button_clicked()
{

	string input_str = input_elim_buffer->get_text();
	if(input_str == "") return;


	output_elim_buffer->set_text("");

	CNode* node = parse_constraint(input_str, display_out);
	if(node == NULL) {
		output_elim_buffer->set_text("Parse error.");
		return;
	}
	set<Term*> vars;
	node->get_vars(vars);
	vector<VariableTerm*> to_eliminate;
	set<Term*>::iterator it = vars.begin();
	for(; it != vars.end(); it++)
	{
		Term* t = *it;
		if(t->get_term_type() != VARIABLE_TERM) continue;
		VariableTerm* vt = (VariableTerm*)t;
		if(vt->to_string()[0] == 't')
			to_eliminate.push_back(vt);
	}
	CNode* nc = node;
	CNode* sc = node;
	int t1, t2;
	{
		int start = clock();
		for(vector<VariableTerm*>::iterator it = to_eliminate.begin();
				it != to_eliminate.end(); it++)
		{
			VariableTerm* cur = *it;
			ExistentialEliminator ve(nc, cur, true);
			//VariableEliminator ve(nc, cur, THEORY_SIMPLIFY, true);
			nc = ve.get_result();
		}

		t1 = clock() - start;
	}
	{
		int start = clock();
		for(vector<VariableTerm*>::iterator it = to_eliminate.begin();
						it != to_eliminate.end(); it++)
		{
			VariableTerm* cur = *it;
			ExistentialEliminator ve(sc, cur, false);
			//VariableEliminator ve(sc, cur, THEORY_SIMPLIFY,false);
			sc = ve.get_result();
		}
		t2 = clock() - start;
	}
	string res;
	res = "NC (time: " + float_to_string(ticks_to_seconds(t1)) + ") :" +
			nc->to_string() + "\n";
	res += "SC (time: " + float_to_string(ticks_to_seconds(t2)) + ") :" +
				sc->to_string() + "\n";
	//cout << "RESULT: " << res << endl;

	output_elim_buffer->set_text(res);


}

void init_solve_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml)
{

	refXml->get_widget("solve", solve_button);
	assert(solve_button != NULL);
	solve_button->signal_clicked().connect(
			sigc::ptr_fun(solve_button_clicked) );

	refXml->get_widget("cancel", cancel_button);
	assert(cancel_button != NULL);
	cancel_button->signal_clicked().connect(
			sigc::ptr_fun(cancel_button_clicked) );


	refXml->get_widget("add_regression", add_regression_button);
	assert(add_regression_button != NULL);
	add_regression_button->signal_clicked().connect(
			sigc::ptr_fun(add_regresssion_button_clicked) );

	Gtk::TextView* input = NULL;
	refXml->get_widget("input", input);
	assert(input!=NULL);
	input_buffer = Gtk::TextBuffer::create();
	input->set_buffer(input_buffer);

	input_buffer->signal_changed().connect(
			sigc::ptr_fun(input_buffer_changed) );




	Gtk::TextView* elim_input = NULL;
	refXml->get_widget("elim_input", elim_input);
	assert(elim_input!=NULL);
	input_elim_buffer = Gtk::TextBuffer::create();
	elim_input->set_buffer(input_elim_buffer);


	Gtk::TextView* elim_output = NULL;
	refXml->get_widget("elim_output", elim_output);
	assert(elim_output!=NULL);
	output_elim_buffer = Gtk::TextBuffer::create();
	elim_output->set_buffer(output_elim_buffer);


	Gtk::Button* elim_button;
	refXml->get_widget("eliminate", elim_button);
	assert(elim_button != NULL);
	elim_button->signal_clicked().connect(
			sigc::ptr_fun(elim_button_clicked) );





	Gtk::TextView* output = NULL;
	refXml->get_widget("output", output);
	assert(output!=NULL);
	output_buffer = Gtk::TextBuffer::create();
	output->set_buffer(output_buffer);

	timeout_button = NULL;
	refXml->get_widget("timeout_spinbutton", timeout_button);
	assert(timeout_button != NULL);
	timeout_button->signal_value_changed().connect
		( sigc::ptr_fun(timeout_changed) );
	timeout_changed();

	select_regression_button = NULL;
	refXml->get_widget("select_regression", select_regression_button);
	assert(select_regression_button != NULL);
	select_regression_button->signal_value_changed().connect
			( sigc::ptr_fun(select_regression_changed) );

	refXml->get_widget("single_process_checkbutton", single_process_button);
	assert(single_process_button != NULL);

	refXml->get_widget("assignment_checkbutton", assign_button);
	assert(assign_button != NULL);
	assign_button->signal_clicked().connect
			( sigc::ptr_fun(assign_changed) );
	assign_changed();


	refXml->get_widget("no_verify_checkbutton", no_verify_button);
	assert(no_verify_button != NULL);
	no_verify_button->signal_clicked().connect
		( sigc::ptr_fun(no_verify_changed) );
	no_verify_changed();



	refXml->get_widget("print_stats_checkbutton", print_stats_button);
	assert(print_stats_button != NULL);
	print_stats_button->signal_clicked().connect
		( sigc::ptr_fun(print_stats_changed) );
	print_stats_changed();


	refXml->get_widget("level_combobox", level_combobox);
	assert(level_combobox != NULL);
	f_refTreeModel = Gtk::ListStore::create(option_columns);
	f_refTreeModel->clear();
	level_combobox->set_model(f_refTreeModel);
	level_combobox->pack_start(option_columns.col_id);

	for(int i=0; i < (int)(sizeof(levels)/sizeof(string*)); i++) {
		Gtk::TreeModel::Row row = *(f_refTreeModel->append());
		row[option_columns.col_id] = levels[i];
	}
	level_combobox->set_active(0);
	level_combobox->signal_changed().connect
		( sigc::ptr_fun(level_changed) );
	level_changed();



	refXml->get_widget("path", path);
	assert(path != NULL);
	path->signal_changed().connect( sigc::ptr_fun(path_changed) );




}




bool regression_in_filter(string id)
{
	string display_id = id.substr(string(REGRESSION_FOLDER).size() + 1);
	return display_id.find(current_filter) != string::npos;
}

void update_regress_treeview()
{
	regression_model_ref->clear();
	map<string, solve_regression>::iterator it = solve_regressions.begin();
	int folder_length = string(REGRESSION_FOLDER).size();
	bool failed = only_failed->get_active();
	for(; it != solve_regressions.end(); it++)
	{
		bool show = false;
		if(!failed) show = true;
		string id = it->first;
		string expected = it->second.status ? "sat" : "unsat";
		string time = "";
		string status = "";
		string size = "";
		if(solve_regressions_results.count(id) > 0)
		{
			solve_regression_result & res = solve_regressions_results[id];
			if(res.passed) status = "passed";
			else {
				status = "failed (";
				if(res.actual_status == SAT || res.actual_status == UNSAT)
					status += "wrong)";
				else if(res.actual_status == CRASH)
					status += "crash)";
				else if(res.actual_status == PARSE_ERROR)
					status += "parse error)";
				else if(res.actual_status == CANCEL)
					status += "canceled)";
				else status += "timeout)";
				show = true;
			}
			size = int_to_string(res.size);
			time = float_to_string(ticks_to_seconds(res.ticks)) + "s";
		}
		if(!show) continue;
		string display_id = id.substr(folder_length+1);

		if(!show_all->get_active() && !regression_in_filter(id))
			continue;
		Gtk::TreeModel::Row row = *(regression_model_ref->append());


		row[regression_columns.col_id] = display_id;
		row[regression_columns.col_status] = expected;
		row[regression_columns.col_res] = status;
		row[regression_columns.col_time] = time;
		row[regression_columns.col_size] = size;

	}
}


void refresh_solve_regression_info()
{

	Glib::Mutex::Lock l(*m);
	success_label->set_text(int_to_string(num_success));
	failed_label->set_text(int_to_string(num_failed));
	time_label->set_text(float_to_string(regression_time));
	double fraction = ((double)num_success+num_failed)/
		((double)solve_regressions.size());
	regression_progressbar->set_fraction(fraction);
	if(num_failed > 0)
	{
		Gtk::IconSize s(4);
		status_image->set_from_icon_name(GTK_STOCK_NO, s);
	}

	/*
	 * Update the tree-view
	 */
	update_regress_treeview();

	if(regressions_finished)
	{
		if(regressions_canceled)
			regression_status->set_text("Status: Canceled");
		else regression_status->set_text("Status: Completed");
		run_regressions_button->set_sensitive(true);
		cancel_regressions_button->set_sensitive(false);
		regressions_finished = true;

	}

}

void cancel_regressions()
{
	Glib::Mutex::Lock l(*m);
	regressions_canceled = true;
	if(cur_process_id == -1)
		return;
	kill(cur_process_id, CANCEL_EXIT_STATUS);
}


CNode* replace_funs_with_vars(CNode* n)
{
	map<Term*, Term*> fun_to_vars;
	set<Term*> terms;
	n->get_nested_terms(terms, false, false);
	set<Term*>::iterator it = terms.begin();
	int counter = 1;
	for(; it != terms.end(); it++) {
		Term* t = *it;
		if(t->get_term_type() != FUNCTION_TERM) continue;
		if(fun_to_vars.count(t) > 0) continue;
		fun_to_vars[t] = VariableTerm::make("var_" + int_to_string(counter++));
	}
	return n->substitute(fun_to_vars);

}

void run_regressions_internal()
{
	int num_regressions = solve_regressions.size();
	if(num_regressions == 0) return;
	map<string, solve_regression>::iterator it = solve_regressions.begin();
	int i = 1;
	{
		Glib::Mutex::Lock l(*m);
		num_success = 0;
		num_failed = 0;
	}
	usleep(50000);
	int total_ticks = 0;
	for(; it!= solve_regressions.end(); it++, i++)
	{
		{
			string id = it->first;
			Glib::Mutex::Lock l(*m);
			if(!regression_in_filter(id)) continue;


			if(regressions_canceled)
			{
				regressions_finished = true;
				solve_regression_info_changed->emit();
				return;

			}
		}
		string input = it->second.constraint;
		int ticks = 0;
		int size;
		sat_query_status status = run_mistral(input, ticks, true, true, size);
		bool success = true;
		if((status == SAT && it->second.status) || (status == UNSAT &&
				it->second.status == false))
		{
			Glib::Mutex::Lock l(*m);
			num_success++;
		}
		else {
			Glib::Mutex::Lock l(*m);
			num_failed++;
			success = false;
		}

		total_ticks += ticks;
		double time = ticks_to_seconds(total_ticks);
		{
			Glib::Mutex::Lock l(*m);
			regression_time = time;

			/*
			 * Add info to regression map
			 */
			string id = it->first;
			solve_regression_result & res = solve_regressions_results[id];
			res.actual_status = status;
			res.passed = success;
			res.id = id;
			res.ticks = ticks;
			res.size = size;

		}
		solve_regression_info_changed->emit();
		Glib::Thread::yield();
		//cout << i << endl;
		if(i%3==0) usleep(50000);

	}
	Glib::Mutex::Lock l(*m);
	regressions_finished = true;
	solve_regression_info_changed->emit();
}



void run_regressions()
{
	run_regressions_button->set_sensitive(false);
	cancel_regressions_button->set_sensitive(true);
	regression_status->set_text("Status: Running...");
	{
		Glib::Mutex::Lock l(*m);

		if(!regressions_finished) return;
		solve_regressions_results.clear();
		regressions_canceled = false;
		regressions_finished = false;
		num_success = 0;
		num_failed = 0;
		regression_time = 0.0;
	}
	regression_progressbar->set_fraction(0.0);
	Gtk::IconSize s(4);
	status_image->set_from_icon_name(GTK_STOCK_YES, s);
	solve_regression_info_changed->emit();
	//run_regressions_internal();
	Glib::Thread::create(sigc::ptr_fun(run_regressions_internal), false);
}

void extract_costs(CNode* c, map<VariableTerm*, int> & costs)
{
	if(c->get_type() == EQ) {
		EqLeaf* eq = static_cast<EqLeaf*>(c);
		Term* rhs = eq->get_rhs();
		Term* lhs = eq->get_lhs();
		if(rhs->get_term_type() == VARIABLE_TERM)
		{
			Term* t = rhs;
			rhs = lhs;
			lhs = t;
		}
		if(lhs->get_term_type() == VARIABLE_TERM) {
			VariableTerm* vt = static_cast<VariableTerm*>(lhs);
			if(rhs->get_term_type() == CONSTANT_TERM) {
				ConstantTerm * ct = static_cast<ConstantTerm*>(rhs);
				costs[vt] = ct->get_constant();
			}

		}
		return;
	}
	if(c->get_type() != AND) return;
	Connective* and_c = static_cast<Connective*>(c);
	const set<CNode*>& ops = and_c->get_operands();

	set<CNode*>::const_iterator it = ops.begin();
	for(; it!= ops.end(); it++)
	{
		CNode* cur = *it;
		extract_costs(cur, costs);
	}


}

bool is_empty_string(string  s)
{
	for(unsigned int i = 0; i <s.size(); i++)
	{
		if(s[i] != ' ' && s[i] != '\t' && s[i] != '\n') return false;
	}
	return true;
}

void split_invariants(string s, set<string> & split)
{
   string cur;
   for(unsigned int i=0; i < s.size(); i++) {
       if(s[i] == '\n')
       {

          if(!is_empty_string(cur)) {
        	  split.insert(cur);
          }
          cur = "";
       }
       cur +=s[i];

   }
   if(!is_empty_string(cur)){
	   split.insert(cur);
   }



}

void run_msa()
{
   string input_str = msa_input_buffer->get_text();
   string high_cost = msa_high_cost_buffer->get_text();

   string invariants = msa_invariants_buffer->get_text();

   cout << "INPUT STRING: " << input_str << endl;

   msa_output_buffer->set_text("");

   if(input_str == "") return;


   CNode* node = parse_constraint(input_str, display_out);
   if(node == NULL) {
       msa_output_buffer->set_text("Parse error.");
       return;
   }


   set<string> invs;
   split_invariants(invariants, invs);
   cout << "INVARIANTS:::::::::::" << endl;
   set<CNode*> bg;
   for(auto it = invs.begin(); it != invs.end(); it++) {

       CNode* inv = parse_constraint(*it, display_out);
       if(inv == NULL) {
           cout << "No invariant parsed" << endl;
           break;
       }
       bg.insert(inv);
       cout << "Invariant: " << inv->to_string() << endl;
       //cout << *it << " ********* "<< endl;

   }


/*
   CNode* inv = parse_constraint(invariants, display_out);
   if(inv == NULL) {
       cout << "No invariant parsed" << endl;
       inv = True::make();
   }*/

   map<VariableTerm*, int> costs;
   CNode* cost = parse_constraint(high_cost, display_out);
   if(cost != NULL){
       cout << "non-null costs " << endl;
       extract_costs(cost, costs);

       cout << "===========Costs==============" << endl;
       map<VariableTerm*, int>::iterator it = costs.begin();
       for(; it!= costs.end(); it++)
       {
           VariableTerm* vt = it->first;
           int cost = it->second;
           cout << "Cost of : " << vt->to_string() << ": " <<  cost << endl;
       }
       cout << "===========+++++==============" << endl;
   }


//    set<CNode*> inv_set;
   //inv_set.insert(inv);
   int start = clock();
   node = replace_funs_with_vars(node);
   cout << "Finding MSA of: " << node->to_string() << endl;
   MSAFinder msa_f(node, bg, costs);
   int end = clock();
   int ticks = end-start;
   cout << "DONE!" << endl;
   string result = "{ ";
   const set<VariableTerm*> & msa = msa_f.get_vars_in_msa();
   set<VariableTerm*>::const_iterator it = msa.begin();
   for(int i = 0; it != msa.end(); it++, i++) {
       result += (*it)->to_string();
       if(i != (int) msa.size()-1) result += ", ";
   }
   result += "}\n";

   set<Term*> terms;
   node->get_vars(terms);
   Constraint c(node);
   auto it2 = terms.begin();
   for(; it2 != terms.end(); it2++) {
       Term* t = *it2;
       assert(t->get_term_type() == VARIABLE_TERM);
       VariableTerm* vt = static_cast<VariableTerm*>(t);
       if(msa.count(vt) == 0) {
           c.eliminate_uvar(vt);
       }
   }
   result += "Abductive Solution: " + c.to_string() + "\n";



   result += "Time (s): " + float_to_string(ticks_to_seconds(ticks));
   result+="\n";
   result += msa_f.get_stats();
   msa_output_buffer->set_text(result);


}

void run_opt()
{
	CNode::clear();
	string constraint_str = opt_constraint_buffer->get_text();
	string cost_str = opt_cost_buffer->get_text();
	string bound_str = opt_bound->get_text();

	long int bound = string_to_int(bound_str);

	CNode* constraint = parse_constraint(constraint_str, display_out);
	if(constraint == NULL) {
		cout << "constraint NULL " << endl;
		return;
	}

	Term* cost_fn = parse_term(cost_str, display_out);
	if(cost_fn == NULL){
		cout << "TERM null " << endl;
		return;
	}

	cout << "constraint: " << constraint->to_string() << endl;
	cout << "cost fn: " << cost_fn->to_string() << endl;
	cout << "bound: " << bound << endl;


	Optimizer o(constraint, cost_fn, !opt_check_max->get_active(),bound);
	long int op_cost = o.get_optimal_cost();
	const map<Term*, SatValue> & assignment = o.get_assignment();

	string res;
	res = "Optimal cost: " + int_to_string(op_cost)+"\n";
	res += "************************************\n";
	for(map<Term*, SatValue>::const_iterator it = assignment.begin();
			it != assignment.end(); it++)
	{
		Term* t = it->first;
		SatValue v = it->second;
		res += t->to_string() + ": " + v.to_string() + "\n";
	}

	res += o.get_stats();
	opt_assignment_buffer->set_text(res);


}

void regression_selected(GdkEventButton* const& s)
{
	if(s->type != GDK_2BUTTON_PRESS) return;
	Glib::RefPtr<Gtk::TreeView::Selection> refSelection =
		regression_treeview->get_selection();
	if(refSelection)
	{
		Gtk::TreeModel::iterator iter = refSelection->get_selected();
		if(iter)
		{
			string key = (*iter)[regression_columns.col_id];
			Gtk::MessageDialog dialog("Really load regression and overwrite "
					"current constraint?",
			false /* use_markup */, Gtk::MESSAGE_QUESTION,
			Gtk::BUTTONS_OK_CANCEL);
			if(dialog.run() != Gtk::RESPONSE_OK) return;
			string id = (*iter)[regression_columns.col_id];
			id = string(REGRESSION_FOLDER) + "/" + id;
			assert(solve_regressions.count(id) > 0);
			string constraint = solve_regressions[id].constraint;
			input_buffer->set_text(constraint);

		}
	}

}


void init_regression_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml)
{
	refXml->get_widget("run_regressions", run_regressions_button);
	assert(run_regressions_button != NULL);
	run_regressions_button->signal_clicked().connect
		( sigc::ptr_fun(run_regressions));

	refXml->get_widget("cancel_regressions", cancel_regressions_button);
	assert(cancel_regressions_button != NULL);
	cancel_regressions_button->signal_clicked().connect
		( sigc::ptr_fun(cancel_regressions));

	refXml->get_widget("regression_progressbar", regression_progressbar);
	assert(regression_progressbar != NULL);

	refXml->get_widget("success_label", success_label);
	assert(success_label != NULL);

	refXml->get_widget("failed_label", failed_label);
	assert(failed_label != NULL);

	refXml->get_widget("time_label", time_label);
	assert(time_label != NULL);

	refXml->get_widget("status_image", status_image);
	assert(status_image != NULL);
	Gtk::IconSize s(4);
	status_image->set_from_icon_name(GTK_STOCK_YES, s);

	refXml->get_widget("regression_status", regression_status);
	assert(regression_status != NULL);

	refXml->get_widget("regression_treeview", regression_treeview);
	assert(regression_treeview != NULL);
	regression_model_ref = Gtk::ListStore::create(regression_columns);
	regression_treeview->set_model(regression_model_ref);
	regression_treeview->append_column("Name", regression_columns.col_id);
	regression_treeview->append_column("Type", regression_columns.col_status);
	regression_treeview->append_column("Result", regression_columns.col_res);
	regression_treeview->append_column("Time", regression_columns.col_time);
	regression_treeview->append_column("Size", regression_columns.col_size);
	regression_treeview->signal_button_press_event().connect_notify(
			sigc::ptr_fun(regression_selected));

	refXml->get_widget("only_failed", only_failed);
	assert(only_failed != NULL);
	only_failed->signal_clicked().connect
	( sigc::ptr_fun(update_regress_treeview));

	refXml->get_widget("no_filter", show_all);
	assert(show_all != NULL);
	show_all->signal_clicked().connect
	( sigc::ptr_fun(update_regress_treeview));


	refXml->get_widget("regression_filter", regression_filter);
	assert(regression_filter != NULL);
	regression_filter->signal_changed().connect(
			sigc::ptr_fun(regression_filter_changed) );


}



void init_msa_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml)
{
	refXml->get_widget("compute_msa", msa_button);
	assert(msa_button != NULL);
	msa_button->signal_clicked().connect
		( sigc::ptr_fun(run_msa));

	Gtk::TextView* msa_input = NULL;
	refXml->get_widget("msa_input", msa_input);
	assert(msa_input!=NULL);
	msa_input_buffer = Gtk::TextBuffer::create();
	msa_input->set_buffer(msa_input_buffer);

	Gtk::TextView* msa_invariants = NULL;
	refXml->get_widget("msa_invariants", msa_invariants);
	assert(msa_invariants!=NULL);
	msa_invariants_buffer = Gtk::TextBuffer::create();
	msa_invariants->set_buffer(msa_invariants_buffer);

	Gtk::TextView* msa_high_cost = NULL;
	refXml->get_widget("msa_highcost", msa_high_cost);
	assert(msa_high_cost!=NULL);
	msa_high_cost_buffer = Gtk::TextBuffer::create();
	msa_high_cost->set_buffer(msa_high_cost_buffer);

	Gtk::TextView* msa_output = NULL;
	refXml->get_widget("msa_output", msa_output);
	assert(msa_output!=NULL);
	msa_output_buffer = Gtk::TextBuffer::create();
	msa_output->set_buffer(msa_output_buffer);





}

void init_opt_elements(Glib::RefPtr<Gnome::Glade::Xml> & refXml)
{

	Gtk::TextView* opt_constraint = NULL;
	refXml->get_widget("opt_constraint", opt_constraint);
	assert(opt_constraint!=NULL);
	opt_constraint_buffer = Gtk::TextBuffer::create();
	opt_constraint->set_buffer(opt_constraint_buffer);

	Gtk::TextView* opt_cost = NULL;
	refXml->get_widget("opt_cost", opt_cost);
	assert(opt_cost!=NULL);
	opt_cost_buffer = Gtk::TextBuffer::create();
	opt_cost->set_buffer(opt_cost_buffer);

	refXml->get_widget("opt_bound", opt_bound);
	assert(opt_bound != NULL);

	refXml->get_widget("opt_check_max", opt_check_max);
	assert(opt_check_max != NULL);

	refXml->get_widget("opt_button", opt_button);
	assert(opt_button != NULL);
	opt_button->signal_clicked().connect
		( sigc::ptr_fun(run_opt));


	refXml->get_widget("opt_value", opt_value);
	assert(opt_value != NULL);


	Gtk::TextView* opt_assignment = NULL;
	refXml->get_widget("opt_assignment", opt_assignment);
	assert(opt_assignment!=NULL);
	opt_assignment_buffer = Gtk::TextBuffer::create();
	opt_assignment->set_buffer(opt_assignment_buffer);






}


void save_input_buffer()
{

	string cur = input_buffer->get_text();
	ofstream myfile;
	myfile.open(last.c_str());
	myfile << cur;
	myfile.close();




}


void solve_button_clicked()
{
	{
		Glib::Mutex::Lock l(*m);
		if(solve_active) return;
		solve_started();
	}
	//string input_str = strip(input_buffer->get_text());
	string input_str = strip(input_buffer->get_text());
	if(input_str == "") return;
	last_solve_input = input_str;

	  save_input_buffer();

	output_buffer->set_text("");
	int ticks;
	int size;
	run_mistral(input_str, ticks,
			  !single_process_button->get_active(), false, size);
}




double ticks_to_seconds(int ticks)
{
	return ((double)ticks)/((double)CLOCKS_PER_SEC);
}

void timeout_changed()
{
	timeout = timeout_button->get_value_as_int();
}

void select_regression_changed()
{
	int num = select_regression_button->get_value_as_int();
	if(num < 0 || num >= (int)solve_regressions.size()) return;
	map<string, solve_regression>::iterator it = solve_regressions.begin();
	while(num > 0) {
		num--;
		it++;
	}
	solve_regression & reg = it->second;
	input_buffer->set_text(reg.constraint);

}

void level_changed()
{
	Gtk::TreeIter it = level_combobox->get_active();
	string key = (*it)[option_columns.col_id];

	if(levels[0] == key){
		cur_level = UNSAT_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[1] == key){
		cur_level = UNSAT_SIMPLIFY;
		use_dnf = true;
	}
	else if(levels[2] == key){
		cur_level = BOOLEAN_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[3] == key){
		cur_level = HYBRID_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[4] == key){
		cur_level = THEORY_SIMPLIFY;
		use_dnf = false;
	}
	else assert(false);

}


/*
 * Checks if any command-line arguments are given. If return value is true,
 * no GTK UI is started.
 */
bool check_command_line(int argc, char** argv)
{

	return false;
}

string get_display_string(sat_query_status status, int ticks, Solver & s,
		bool print_stats, map<Term*, SatValue>*  mm = NULL)
{
	if(status == CRASH)
		return "*** Crashed ***";
	if(status == TIMEOUT)
		return "Timeout";
	if(status == VERIFY_ERROR)
	{
		return "Error: Result constraint " +
			s.get_result()->to_string()
			+ " not equivalent to input.";
	}
	if(status == NOT_SAT_BY_ASSIGNMENT_ERROR)
	{
		return "Assignment does not satisfy formula";
	}

	string res = "Total time (s): " +
		float_to_string(ticks_to_seconds(ticks)) +"\n";
	if(print_stats) res += s.get_stats();
	if(status == UNSAT) res += "UNSAT";
	if(status == SAT)
	{
		res+=s.get_result()->to_string()+"\n";
		if(mm != NULL)
			res += "Assignment:\n" + assignment_to_string(mm);
		res+="SAT";
	}
	return res;
}


sat_query_status invoke_mistral(CNode* node, int & ticks, int & size,
		string* info)
{
	srand(time(NULL));

	//sleep(1);
	sat_query_status status;

	map<Term*, SatValue>*  mm = NULL;
	map<Term*, SatValue>  m;
	if(assign){
		mm = &m;
	}
	int start = clock();
	Solver s(node, cur_level, mm, use_dnf);
	size = s.get_result()->get_size();
	int end = clock();
	int time = end-start;


	//delete me
	/*
	CNode* temp = Connective::make_not(node);
	Solver s2(temp, UNSAT_SIMPLIFY);

	if(s2.get_result()->get_type() != FALSE_NODE) {


		int start2 = clock();

		int cost = -1;
		//for(int i=0; i<1;i++) {
			set<CNode*> bg;
			map<VariableTerm*, int> costs;
			CNode* nn = replace_funs_with_vars(node);
			MSAFinder msa_f(nn, bg, costs);
			int new_cost = msa_f.get_cost();
			if(cost==-1) cost = new_cost;
			else{
				if(new_cost != cost) {
					cout << "cost is: " << cost << "  new cost is: " << new_cost << endl;
					cout << "wrong costs: "<< replace_funs_with_vars(node)->to_string() << endl;
					assert(false);
				}
			}




		//}
		int end2 = clock();
		time = end2 - start2;



		cout << "TICKS FOR MSA:\t" << time << endl;

		set<Term*> vt;
		node->get_vars(vt);

		string r =  float_to_string(((double)time)/((double)CLOCKS_PER_SEC)) +
				"\t" + int_to_string(vt.size()) + "\t" + int_to_string(node->get_size())
				+ "\t"+int_to_string(cost) + "\t" +int_to_string(msa_f.mpi_estimate)+
				"\t" + float_to_string(((double)msa_f.mpi_time)/((double)CLOCKS_PER_SEC)) +
				"\t" + float_to_string((((double)msa_f.cost_pruned)/((double)msa_f.total))*100.0)+
				"\t" + float_to_string((((double)msa_f.e_only)/((double)msa_f.total))*100.0)+
				"\n";

		ofstream myfile;
		myfile.open("/home/isil/msa.dat", ios::app);
		assert(myfile.is_open());
		myfile << r;
		myfile.close();
	}
	*/

	//delete me end



	/*{
		CNode* res = s.get_result();
		CNode* not_res = Connective::make_not(res);
		Solver ss(not_res, cur_level, mm, use_dnf);
		if(not_res != ss.get_result())
		{
			cout << "Error: Orig: " << node->to_string() << endl;
			cout << "First simp: " << s.get_result()->to_string() << endl;
			cout << "Second simp: " << ss.get_result()->to_string() << endl;
		}
	}*/



	bool error = false;

	if(verify_simplification) {


		bool equivalent = constraint_equivalent(node, s.get_result());
		if(!equivalent){
			error = true;
			status =  VERIFY_ERROR;
		}
	}
	ticks = time;
	if(!error) {
		if(s.get_result()->get_type() == FALSE_NODE) status = UNSAT;
		else status = SAT;
	}

	if(status == SAT && assign)
	{
		CNode* new_node = node->evaluate_assignment(m);
		cout << "Evaluated assignment: " << new_node->to_string() << endl;
		if(new_node->get_type() == FALSE_NODE)
			status = NOT_SAT_BY_ASSIGNMENT_ERROR;
	}

	if(info!=NULL) *info = get_display_string(status, time, s, print_stats, mm);
	return status;

}




void run_mistral_internal()
{
	CNode::clear();
	int start = clock();
	CNode* node = parse_constraint(__node, display_out);
	int end = clock();
	int parse_ticks = end-start;
	if(node == NULL){
		__res = PARSE_ERROR;
		solve_status->emit();
		return;
	}




	//cout << "parsed constraint: " << node->to_string() << endl;
	int & ticks = *__ticks;
	int & size = *__size;
	bool new_process = __new_process;
	bool regress = __regress;

	if(!new_process)
	{
		string *res = NULL;
		string _res;
		if(!regress) res = &_res;
		sat_query_status status = invoke_mistral(node, ticks,  size, res);
		//ticks+=parse_ticks;
		if(!regress) display_out(_res);
		__res = status;
		if(!regress) solve_status->emit();
		return;
	}

	int pipe_status = pipe(rgfd);
	assert(pipe_status == 0);

	int p_id = fork();
	if(p_id == 0)
	{
		alarm(timeout);

		//nice(20);


		int v = 0;
		int time = 0;
		assert(write(rgfd[1], &v, sizeof(int))!=-1);
		assert(write(rgfd[1], &v, sizeof(int))!=-1);
		assert(write(rgfd[1], &v, sizeof(int))!=-1);
		assert(write(rgfd[1], &v, sizeof(char))!=-1);

		string *res = NULL;
		string _res;
		if(!regress) res = &_res;
		v = invoke_mistral(node, time, size, res);


		int t;
		assert(read(rgfd[0], &t, sizeof(int))!=-1);
		assert(read(rgfd[0], &t, sizeof(int))!=-1);
		assert(read(rgfd[0], &t, sizeof(int))!=-1);
		assert(read(rgfd[0], &t, sizeof(char))!=-1);


		assert(write(rgfd[1], &v, sizeof(int))!=-1);
		assert(write(rgfd[1], &time, sizeof(int))!=-1);
		assert(write(rgfd[1], &size, sizeof(int))!=-1);


		for(unsigned int i = 0; i < _res.size(); i++) {
			assert(write(rgfd[1], &_res[i], sizeof(char))!=-1);
		}
		assert(write(rgfd[1], "\0", sizeof(char))!=-1);
		exit(0);
	}
	{
		Glib::Mutex::Lock l(*m);
		cur_process_id = p_id;
	}
	int childExitStatus = 0;
	pid_t ws = waitpid( p_id, &childExitStatus, 0);
	{
		Glib::Mutex::Lock l(*m);
		cur_process_id = -1;
	}
	assert(ws != -1);
	int s;
	assert(read(rgfd[0], &s, sizeof(int))!=-1);
	int _time;
	assert(read(rgfd[0], &_time, sizeof(int))!=-1);
	ticks = _time;
	assert(read(rgfd[0], &size, sizeof(int))!=-1);
	//ticks+=parse_ticks;

	string res;
	if(!regress)
	{
		while(true) {
			char cur;
			assert(read(rgfd[0], &cur, sizeof(char))!=-1);
			if(cur == '\0') break;
			res+=cur;
		}
		display_out(res);
	}

	close(rgfd[0]);
	close(rgfd[1]);

	//cout << "exit status: "<< childExitStatus << endl;

	if(childExitStatus!=0) {
		if(childExitStatus== TIMEOUT_EXIT_STATUS)
		{


			if(!regress) display_out("Timeout");
			__res = TIMEOUT;
		}
		else if(childExitStatus== CANCEL_EXIT_STATUS)
		{
			if(!regress) display_out("Canceled");
			__res = CANCEL;
		}
		else
		{
			if(!regress) display_out("*** crash***");
			__res = CRASH;
		}
		if(!regress) solve_status->emit();
		return;
	}
	if(s == 0){
		__res = SAT;
		if(!regress) solve_status->emit();
		return;
	}
	if(s == 1){
		__res = UNSAT;
		if(!regress) solve_status->emit();
		return;
	}
	if(s == 4){
		res = VERIFY_ERROR;
		if(!regress) solve_status->emit();
		return;
	}
	if(s == 5) {
		res = NOT_SAT_BY_ASSIGNMENT_ERROR;
		if(!regress) solve_status->emit();
		return;
	}
	assert(false);

}

sat_query_status run_mistral(string node, int & ticks, bool new_process,
		bool regress, int & size)
{
	__node = node;
	__ticks = &ticks;
	__size = &size;
	__new_process = new_process;
	__regress = regress;
	if(!regress && false)
	{
		Glib::Thread::create(sigc::ptr_fun(run_mistral_internal), false);
		return SAT; //not checked in interactive mode
	}
	run_mistral_internal();
	return __res;

}

bool is_sat(CNode* constraint) {

	if(constraint->get_type() == FALSE_NODE) return false;
	if(constraint->get_type() == TRUE_NODE) return true;

	Solver s(constraint, UNSAT_SIMPLIFY, NULL);
	CNode* res = s.get_result();
	bool sat = res->get_type()!= FALSE_NODE;
	return sat;
}


bool constraint_equivalent(CNode* c1, CNode* c2)
{

	{

		CNode* c_not = Connective::make_not(c1);
		CNode* res = Connective::make(OR, c_not, c2);
		CNode* v1 = Connective::make_not(res);
		bool sat = is_sat(v1);
		if(sat){
			return false;
		}
	}
	{
		CNode* c_not = Connective::make_not(c2);
		CNode* res = Connective::make(OR, c_not, c1);
		CNode* v1 = Connective::make_not(res);
		bool sat = is_sat(v1);
		if(sat){
			return false;
		}
	}
	return true;

}

string assignment_to_string(map<Term*, SatValue>* assignments)
{
	if (assignments == NULL)
		return "";
	string res;
	map<Term*, SatValue>::iterator it = assignments->begin();
	for (; it != assignments->end(); it++) {
		Term* t = it->first;
		SatValue sv = it->second;
		res += "\t " + t->to_string() + ": " + sv.to_string();
		res += "\n";
	}
	return res;
}


void get_all_files(string cur_prefix, set<string> & files, string suffix)
{
	/*
	 * Base case 1: Prefix is file with desired extension.
	 */
	if(cur_prefix.find(suffix)!= string::npos)
	{
		files.insert(cur_prefix);
		return;
	}
	DIR *dp;

	/*
	 * Base case 2: Prefix is file with incompatible extension.
	 */
	if((dp  = opendir(cur_prefix.c_str())) == NULL) {
		return;
	}

	struct dirent *dirp;
    while ((dirp = readdir(dp)) != NULL) {
    	string name = string(dirp->d_name);
    	if(name == "." || name == "..") continue;
    	get_all_files(cur_prefix + "/" + name, files, suffix);
    }
    closedir(dp);


}



/*
#include <iostream>
#include <gtkmm.h>
#include <libglademm.h>
#include <assert.h>
#include "mistral.h"
#include <iostream>
#include <fstream>
#include <vector>
#include "VarMap.h"
#include "util.h"

#include "Solver.h"

#include "CNode.h"
#include "parser.h"
#include "UniversalInstantiator.h"
#include "VariableEliminator.h"
#include "VariableTerm.h"

#define REGRESS_FILE "mistral-regress.txt"

#define REGRESS_E_FILE "mistral-existential-regress.txt"


#define CURRENT_FILE "current.txt"

#include <sys/types.h>
#include <unistd.h>
#include <sys/wait.h>
#include "cnode.h"
#include <string.h>
#include "EqualityFinder.h"

using namespace std;

Glib::RefPtr<Gtk::TextBuffer> input_buffer;
Glib::RefPtr<Gtk::TextBuffer> output_buffer;
Glib::RefPtr<Gtk::ListStore> f_refTreeModel;
Glib::RefPtr<Gtk::TextBuffer> cinput_buffer;
Glib::RefPtr<Gtk::TextBuffer> coutput_buffer;

Glib::RefPtr<Gtk::TextBuffer>generated_buffer;


Glib::RefPtr<Gtk::TextBuffer>hnf_in_buffer;


Glib::RefPtr<Gtk::TextBuffer>hnf_out_buffer;


Gtk::CheckButton* sat_assign_button;
Gtk::CheckButton* stats_button;
Gtk::CheckButton* verify_simplification_button;

Gtk::SpinButton* spin_button;
Gtk::SpinButton* espin_button;
Gtk::SpinButton* timeout_button;


Gtk::Image *red;
Gtk::Image *green;

Gtk::Image *ered;
Gtk::Image *egreen;

Gtk::Entry* num_vars;
Gtk::Entry* max_coefficient;
Gtk::Entry* num_constraints;

Gtk::ComboBox* solve_options;



Glib::RefPtr<Gtk::TextBuffer> regress_buffer;
Glib::RefPtr<Gtk::TextBuffer> eregress_buffer;

Gtk::Label* status;


simplification_level cur_level = UNSAT_SIMPLIFY;
bool use_dnf = false;
int timeout = 10;

class AccessPath;
class IndexVarManager;
class Term;
class Variable;
AccessPath* constraint_to_ap(CNode* c,
		IndexVarManager& ivm)
{
	assert(false);
}

CNode* ap_to_constraint(AccessPath *ap)
{
	assert(false);
}

void replace_access_path(AccessPath* ap_old, AccessPath* ap_new)
{
	assert(false);
}

Term* make_term(AccessPath* ap_old)
{
	assert(false);
}

AccessPath* make_ap_from_term(Term* t, IndexVarManager& ivm,
		set<AccessPath*>& to_add, map<Term*, Variable*>& replacement_map)
{
	assert(false);
}

namespace sail {
class Variable
{
	Variable* clone();
};

Variable* Variable::clone()
{
	assert(false);
}
}

void display_out(string s)
{
	output_buffer->insert(output_buffer->end(), s);
}

void display_line(string s)
{
	s += "\n";
	output_buffer->insert(output_buffer->end(), s);


}

void display_regress(string s)
{
	regress_buffer->insert(regress_buffer->end(), s);
}

void display_eregress(string s)
{
	eregress_buffer->insert(eregress_buffer->end(), s);
}

enum sat_query_status
{
	SAT,
	UNSAT,
	TIMEOUT,
	VERIFY_ERROR
};

int rgfd[2];


void load_input_buffer()
{
	 ifstream myfile;
	 myfile.open(CURRENT_FILE);
	 if(!myfile.is_open()) return;
	 string cur;
	 while(!myfile.eof())
	 {
		 string t;
		 std::getline(myfile, t);
		 cur+=t;
	 }


	 myfile.close();
	 input_buffer->set_text(cur);

}

void save_input_buffer()
{
	string cur = input_buffer->get_text();
	ofstream myfile;
	myfile.open(CURRENT_FILE);
	myfile << cur;
	myfile.close();


}

string assignment_to_string(map<Term*, SatValue>* assignments) {
	if (assignments == NULL)
		return "";
	string res;
	map<Term*, SatValue>::iterator it = assignments->begin();
	for (; it != assignments->end(); it++) {
		Term* t = it->first;
		SatValue sv = it->second;
		res += "\t " + t->to_string() + ": " + sv.to_string();
		res += "\n";
	}
	return res;
}

bool is_satisfiable_ui(CNode* constraint, map<Term*,SatValue>* sat_assignments = NULL,
		bool verbose = false, bool ilp_only =false) {

	if(constraint->get_type() == FALSE_NODE) return false;
	if(constraint->get_type() == TRUE_NODE) return true;

	Solver s(constraint, UNSAT_SIMPLIFY, sat_assignments);
	CNode* res = s.get_result();
	bool sat = res->get_type()!= FALSE_NODE;
	return sat;
}

pair<CNode*, CNode*> eliminate_evars(CNode* c, bool regress = false)
{
	set<string> v;
	c->get_vars(v);

	vector<int> evars;
	set<string>::iterator it = v.begin();
	for(; it != v.end(); it++) {
		if((*it)[0] == 't'){
			evars.push_back(CNode::get_varmap().get_id((*it)));
		}
	}
	int start = clock();
	VariableEliminator ve_nc(c, evars, cur_level, true);
	CNode* nc = ve_nc.get_result();

	CNode* neg_c = Connective::make_not(c);

	VariableEliminator ve_sc(neg_c, evars, cur_level, true);
	CNode* sc = ve_sc.get_result();
	sc = Connective::make_not(sc);

	//CNode* sc = False::make();

	int end = clock();
	if(!regress)
	{
		int t = end-start;
		display_out("Time: " + float_to_string(((double)t)/
				  ((double)CLOCKS_PER_SEC)) + "s\n");
	}

	//temporary

	if(evars.size() != 0)
	{
		Term *t = VariableTerm::make(*evars.begin());
		EqualityFinder ef(c, t, true);
		const map<Term*, CNode*> & eqs = ef.get_disjunctive_equalities();
		display_out("EQUALITIES::\n");
		map<Term*, CNode*>::const_iterator it = eqs.begin();
		for(; it != eqs.end(); it++) {
			display_out ("Equality: " + it->first->to_string() + " under "+
					it->second->to_string());
			display_out("\n");

		}
	}








	return pair<CNode*, CNode*>(nc, sc);
}

bool constraint_equivalent(CNode* c1, CNode* c2)
{
	{

		CNode* c_not = Connective::make_not(c1);
		CNode* res = Connective::make(OR, c_not, c2);
		CNode* v1 = Connective::make_not(res);
		//cout << "11: " << v1->to_string() << endl;
		bool is_sat = is_satisfiable_ui(v1, NULL);
		if(is_sat){
			//cout << "SAT 1 "<< endl;
			return false;
		}
	}
	{
		CNode* c_not = Connective::make_not(c2);
		CNode* res = Connective::make(OR, c_not, c1);
		CNode* v1 = Connective::make_not(res);
		//cout << "22: " << v1->to_string() << endl;
		bool is_sat = is_satisfiable_ui(v1, NULL);
		if(is_sat){
			//cout << "SAT 2 "<< endl;
			return false;
		}
	}
	return true;

}

sat_query_status run_mistral(CNode* node, int & ticks, bool regress = false,
		bool new_process = true)
{
	bool assign = sat_assign_button->get_active();
	bool print_stats = stats_button->get_active();
	bool verify_simplification = verify_simplification_button->get_active();
	if(!new_process)
	{
		map<Term*, SatValue>*  mm = NULL;
		map<Term*, SatValue>  m;
		if(assign) mm = &m;
		int start = clock();
		Solver s(node, cur_level, mm, use_dnf);
		int end = clock();
		int time = end-start;


		if(verify_simplification) {
			bool equivalent = constraint_equivalent(node, s.get_result());
			if(!equivalent){
				cout << "ERROR: NOT EQUIVALENT:" << endl;
				display_out("ERROR: NOT EQUIVALENT:");
				return VERIFY_ERROR;
			}
		}
		ticks = time;
		if(s.get_result()->get_type() == FALSE_NODE) return UNSAT;
		return SAT;
	}

	pipe(rgfd);

	int p_id = fork();
	if(p_id == 0)
	{
		alarm(timeout);

		int v = 0;
		int time = 0;
		string temp;
		string stats;
		map<Term*, SatValue>*  mm = NULL;
		map<Term*, SatValue>  m;
		write(rgfd[1], &v, sizeof(int));
		write(rgfd[1], &v, sizeof(int));
		write(rgfd[1], &v, sizeof(char));


		{

			if(assign) mm = &m;
			int start = clock();
			Solver s(node, cur_level, mm, use_dnf);
			int end = clock();
			time = end-start;
			if(!regress) temp = s.get_result()->to_string();
			if(!regress && print_stats) stats = s.get_stats();
			if(s.get_result()->get_type() != FALSE_NODE){
				cout << "SAT" << endl;
				v = 1;
			}
			else cout << "UNSAT" << endl;

			if(verify_simplification) {
				bool equivalent = constraint_equivalent(node, s.get_result());
				if(!equivalent){
					v = 2;
					cout << "ERROR: NOT EQUIVALENT:" << endl;
					display_out("ERROR: NOT EQUIVALENT:");
				}
			}

		}
		int t;
		read(rgfd[0], &t, sizeof(int));
		read(rgfd[0], &t, sizeof(int));
		read(rgfd[0], &t, sizeof(char));
		write(rgfd[1], &v, sizeof(int));
		write(rgfd[1], &time, sizeof(int));

		if(!regress) {

			if(assign && v == 1) {
				temp+="\n";
				temp+=assignment_to_string(mm);
			}

			if(print_stats) {
				temp+="\n";
				temp+= stats;
			}

			for(unsigned int i = 0; i < temp.size(); i++) {
				write(rgfd[1], &temp[i], sizeof(char));
			}
			write(rgfd[1], "\0", sizeof(char));
		}


		exit(0);
	}
	int childExitStatus;
	pid_t ws = waitpid( p_id, &childExitStatus, 0);
	int s;
	read(rgfd[0], &s, sizeof(int));
	int _time;
	read(rgfd[0], &_time, sizeof(int));
	ticks = _time;

	string res;
	if(!regress)
	{
		while(true) {
			char cur;
			read(rgfd[0], &cur, sizeof(char));
			if(cur == '\0') break;
			res+=cur;
		}
		//cout << "ggg " << endl;
		display_out("Result: " + res + "\n");
	}

	close(rgfd[0]);
	close(rgfd[1]);

	if(childExitStatus!=0) {
		if(childExitStatus!= 14) {
			cerr << "******* crash ********" << endl;
			display_out("************** CRASH ************\n");
		}
		return TIMEOUT;
	}
	if(s == 0) return UNSAT;
	if(s == 1) return SAT;
	if(s == 2) return VERIFY_ERROR;
	assert(false);

}

void solve_button_clicked()
{
  string input_str = input_buffer->get_text();
  if(input_str == "") return;

  save_input_buffer();

  output_buffer->set_text("");
  CNode::clear();
  CNode* constraint = parse_constraint(input_str , display);
  int ticks;
  sat_query_status s = run_mistral(constraint, ticks);
  display_out("\nTotal time: " + float_to_string(((double)ticks)/
		  ((double)CLOCKS_PER_SEC)) + "\n");
  if(s == SAT) display_out("SAT\n");
  else if (s == UNSAT) display_out("UNSAT\n");
  else if(s == VERIFY_ERROR) display_out("*******VERIFY ERROR*******\n");
  else display_out("Timeout\n");
  CNode::clear();




}

string cnode_to_smtlib_format(CNode* node, string benchmark_name)
{

	cout << node->to_string() << endl;

	string res = "( benchmark " + benchmark_name + "\n";
	res+=  ":logic QF_LIA\n";
	res += "\t :extrafuns ( \n";

	set<string> vars;
	CNode::get_varmap().get_all_vars(vars);
	set<string>::iterator it = vars.begin();
	for(; it!= vars.end(); it++)
	{
		res += "\t \t(" + *it + " Int" + ")\n";
	}
	res += ")\n"; // end extrafuns paren

	res += "\t :formula \n";
	res += node->to_prefix_notation();

	res += ")"; // end benchmark paren
	return res;
}

void convert_button_clicked()
{
  coutput_buffer->set_text("");
  string input_str = cinput_buffer->get_text();

  CNode* res = parse_constraint(input_str, NULL);
  if(res == NULL){
	  coutput_buffer->set_text("Parse error.");
	  return;
  }
  string smtformat = cnode_to_smtlib_format(res, "test");
  coutput_buffer->set_text(smtformat);

}


string generate_ilp_constraint(int num_rows, int num_cols, int num_vars,
		int max_coefficient)
{
	string result;
	srand(time(NULL));







	for(int i=0; i < num_rows; i++)
	{
		string r;
		for(int j=0; j<num_cols; j++)
		{
			int c = rand()%max_coefficient;
			int s = rand()%2;
			int v = rand()%num_vars;
			r+=  int_to_string(c) + "x" + int_to_string(v) + " ";
			if(j<num_cols-1)
			{
				r+= (s==0?string("-"):string("+")) + string(" ");
			}
		}
		int c = rand()%max_coefficient;
		int s = rand()%2;
		if(s==0) c = -c;
		int b = rand()%2;
		if(b==0)
			r+=" <= " + int_to_string(c);
		else
		{
			r+=" <= " + int_to_string(c);
		}
		result+=r;
		if(i!= num_rows-1) result+= " & \n";
	}


	return result;

}

void generate_button_clicked()
{
	int nv = string_to_int(num_vars->get_text());
	int mc = string_to_int(max_coefficient->get_text());
	int nc = string_to_int(num_constraints->get_text());

	string res = generate_ilp_constraint(nc, nv, nv, mc);
	generated_buffer->set_text(res);

}





void eliminate_button_clicked()
{

  string input_str = input_buffer->get_text();
  save_input_buffer();

  CNode::clear();
  CNode* constraint = parse_constraint(input_str , NULL);
  output_buffer->set_text("");
  if(constraint == NULL){
	display_out("Parse Error\n");
	return;
  }

  pair<CNode*, CNode*> res = eliminate_evars(constraint);

  string out = "NC: " + res.first->to_string() + "\n";
  out+= string("SC: ") + res.second->to_string() + "\n";
  display_out(out);
  CNode::clear();

}

//-------------
class ERegression
{
public:
	string query;
	string nc;
	string sc;
};
void init_eregs(ifstream & file, vector<ERegression> & regs);
int num_eregs;

int get_num_eregs()
{
	 ifstream myfile;
	 myfile.open(REGRESS_E_FILE);
	 vector<ERegression> regs;

	 init_eregs(myfile, regs);
	 myfile.close();
	 return regs.size();
}

void load_eregressions()
{

	 ifstream myfile;
	 myfile.open(REGRESS_E_FILE);
	 vector<ERegression> regs;

	 init_eregs(myfile, regs);
	 myfile.close();
	int i = espin_button->get_value();
	if(i<0 || i >= (int)regs.size())
		return;

	input_buffer->set_text(regs[i].query);

}

void init_eregs(ifstream & file, vector<ERegression> & regs)
{
	assert(file.is_open());

	set<string> q;


	while (!file.eof() )
	{
		ERegression r;
		string line;
		while(!file.eof())
		{
			line = "";
			std::getline (file, line);
			if(line.find("NC")!=string::npos)
				break;
			r.query+=line;
		}
		if(file.eof()) break;
		std::getline(file, line);
		r.nc = line;
		std::getline(file, line);
		assert(line.find("SC")!=string::npos);
		std::getline(file, line);
		r.sc = line;
		std::getline(file, line);
		if(r.query!="")
		{
			if(q.count(r.query)==0){
				regs.push_back(r);
				q.insert(r.query);
			}
		}
	}


}

void run_eregressions()
{
	 ifstream myfile;
	 myfile.open(REGRESS_E_FILE);
	 vector<ERegression> regs;

	 init_eregs(myfile, regs);
	 myfile.close();
	 eregress_buffer->set_text("");
	 display_eregress("Running Regressions...\n");
	 bool success = true;
	 for(unsigned int i=0; i < regs.size(); i++)
	 {
		ERegression &r = regs[i];
		CNode* constraint = parse_constraint(r.query , NULL);
		if(constraint == NULL){
			display_eregress("Parse Error at " + int_to_string(i) + ":\n");
			display_eregress(r.query + "\n");
			continue;
		}

		cout << "Existential Regression #: " << i << endl;
		pair<CNode*, CNode*>  res = eliminate_evars(constraint);

		CNode* nc_node = parse_constraint(r.nc, NULL);
		if(nc_node == NULL){
			display_eregress("Parse Error at NC " + int_to_string(i) + ":\n");
			display_eregress(r.nc + "\n");
			continue;
		}
		CNode* sc_node = parse_constraint(r.sc, NULL);
		if(sc_node == NULL){
			display_eregress("Parse Error at SC " + int_to_string(i) + ":\n");
			display_eregress(r.sc + "\n");
			continue;
		}

		bool cur_succ = true;
		if(!constraint_equivalent(nc_node, res.first)){
			success = false;
			display_eregress("Regression " + int_to_string(i) + " failed: \n");
			display_eregress("NC not equivalent: Expected: " + r.nc + " Result: " +
					res.first->to_string() +"\n");
			cur_succ = false;
		}

		if(!constraint_equivalent(sc_node, res.second)){
			success = false;
			display_eregress("Regression " + int_to_string(i) + " failed: \n");
			display_eregress("SC not equivalent: Expected: " + r.sc + " Result: " +
					res.second->to_string()+"\n" );
			cur_succ = false;
		}

		if(cur_succ)
			display_eregress("passed.\n");
	 }
	 display_eregress("Completed.\n");
	 if(success){
		 egreen->show();
		 ered->hide();
	 } else
	 {
		 ered->show();
		 egreen->hide();
	 }



}

//------------------





class Regression
{
public:
	string query;
	bool sat;
};
void init_regs(ifstream & file, vector<Regression> & regs);

int num_regs;

int get_num_regs()
{
	 ifstream myfile;
	 myfile.open(REGRESS_FILE);
	 vector<Regression> regs;

	 init_regs(myfile, regs);
	 myfile.close();
	 return regs.size();
}

void load_regressions()
{

	 ifstream myfile;
	 myfile.open(REGRESS_FILE);
	 vector<Regression> regs;

	 init_regs(myfile, regs);
	 myfile.close();
	int i = spin_button->get_value();
	if(i<0 || i >= (int)regs.size())
		return;

	input_buffer->set_text(regs[i].query);

}



void init_regs(ifstream & file, vector<Regression> & regs)
{
	assert(file.is_open());

	set<string> q;


	while (!file.eof() )
	{
		Regression r;
		r.sat = false;
		string line;
		while(!file.eof())
		{
			line = "";
			std::getline (file, line);
			if(line.find("SAT")!=string::npos)
				break;
			r.query+=line;
		}
		if(line.find("UNSAT")!=string::npos)
			r.sat = false;
		else r.sat = true;
		if(r.query!="")
		{
			if(q.count(r.query)==0){
				regs.push_back(r);
				q.insert(r.query);
			}
		}
	}


}

void run_regressions()
{
	 ifstream myfile;
	 myfile.open(REGRESS_FILE);
	 vector<Regression> regs;

	 init_regs(myfile, regs);
	 myfile.close();
	 regress_buffer->set_text("");
	 display_regress("Running Regressions...\n");
	 bool total_success = true;
	 int ticks = 0;
	 for(unsigned int i=0; i < regs.size(); i++)
	 {
		bool success = true;
		Regression &r = regs[i];
		int cur_ticks = 0;;
		cerr << "Regression #: " << i << endl;
		CNode::clear();
		CNode* constraint = parse_constraint(r.query, NULL);
		if(constraint ==  NULL) {
			display_regress("Parse error in regression \n");
			success = false;
		}
		else if(constraint->has_quantifier())
		{
			success = true;
		}
		else
		{

			sat_query_status s = run_mistral(constraint, cur_ticks, true);

			if(s == TIMEOUT) {
				display_regress("Timeout in regression \n");
				success = false;
			}
			else if(s == VERIFY_ERROR) {
				display_regress("Verify Error in regression \n");
				success = false;
			}
			else
			{
				ticks+=cur_ticks;
				bool sat = s == SAT;
				if(sat != r.sat)
				{


					if(sat)
						display_regress("SAT instead of UNSAT\n");
					else display_regress("UNSAT instead of SAT\n");
					display_regress(r.query + "\n\n");
					success = false;
				}

			}
		}
		if(!success){
			display_regress("Regression " + int_to_string(i) + " failed:\n");
		}
		else {
			display_regress("Regression " + int_to_string(i) + " passed: "
				+ float_to_string((double)cur_ticks/(double)CLOCKS_PER_SEC)+
				"s \n");
		}
		if(!success)
			total_success = false;
	 }
	 double time = ((double)(ticks)/(double)CLOCKS_PER_SEC);
	 display_regress("Completed.\n");
	 display_regress(float_to_string(time) + " seconds.\n");
	 if(total_success){
		 green->show();
		 red->hide();
	 } else
	 {
		 red->show();
		 green->hide();
	 }

	 CNode::clear();

}

void add_e_regression()
{
	string res = input_buffer->get_text();

	if(res == "")
		return;

	CNode* constraint = parse_constraint(res, NULL);
	if(constraint == NULL){
		output_buffer->set_text("");
		display_out("Parse error: Cannot be added as regression");
		return;
	}
	pair<CNode*, CNode*> res1 = eliminate_evars(constraint);
	num_eregs++;
	espin_button->set_range(0, num_regs-1);
	ofstream myfile;
	myfile.open(REGRESS_E_FILE,ios::app);
	myfile<< "\n\n";
	myfile << res;
	myfile << "\n";
	myfile << "NC: ******\n";
	myfile << res1.first->to_string() << "\n";
	myfile << "SC: ******\n";
	myfile << res1.second->to_string() << "\n";
	myfile << "************" << "\n";
	myfile.close();

}


void add_regression()
{
	string res = input_buffer->get_text();

	if(res == "")
		return;

	CNode* constraint = parse_constraint(res, NULL);
	if(constraint == NULL){
		output_buffer->set_text("");
		display_out("Parse error: Cannot be added as regression");
		return;
	}
	bool sat =  is_satisfiable_ui(constraint);

	num_regs++;
	spin_button->set_range(0, num_regs-1);
	ofstream myfile;
	myfile.open(REGRESS_FILE,ios::app);
	myfile<< "\n\n";
	myfile << res;
	myfile << "\n";
	if(sat)
		myfile << "*** SAT ***\n";
	else myfile << "*** UNSAT ***\n";
	myfile.close();

}

void hnf_button_clicked()
{

}

void timeout_changed()
{
	timeout = timeout_button->get_value_as_int();
}

class OptionColumns : public Gtk::TreeModel::ColumnRecord
{
public:
	OptionColumns()
  {
	  add(col_id);

  }
  Gtk::TreeModelColumn<string> col_id;


};
OptionColumns option_columns;



int num_levels = 5;
string levels [] = {
		"Solve only",
		"Solve only (DNF)",
		"Local Simplify (Lazy)",
		"Local Simplify (Full)",
		"Semantic Simplify"
		};


void solve_options_changed()
{
	Gtk::TreeIter it = solve_options->get_active();
	string key = (*it)[option_columns.col_id];

	if(levels[0] == key){
		cur_level = UNSAT_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[1] == key){
		cur_level = UNSAT_SIMPLIFY;
		use_dnf = true;
	}
	else if(levels[2] == key){
		cur_level = LAZY_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[3] == key){
		cur_level = FULL_SIMPLIFY;
		use_dnf = false;
	}
	else if(levels[4] == key){
		cur_level = SEMANTIC_SIMPLIFY;
		use_dnf = false;
	}
	else assert(false);

}



int main(int argc, char** argv) {


	if(argc >=2) {


		simplification_level level = UNSAT_SIMPLIFY;
		if(argc>=3)
		{
			if(strcmp(argv[2], "--unsat") == 0)
			{
				level = UNSAT_SIMPLIFY;
			}
			else if(strcmp(argv[2], "--lazy") == 0)
			{
				level = LAZY_SIMPLIFY;
			}
			else if(strcmp(argv[2], "--full") == 0)
			{
				level = FULL_SIMPLIFY;
			}
			else if(strcmp(argv[2], "--semantic") == 0)
			{
				level = SEMANTIC_SIMPLIFY;
			}
			else if(strcmp(argv[2], "--guarantee") == 0)
			{
				level = GUARANTEE_SEMANTIC_SIMPLIFY;
			}
		}
		int i = level;
		if(i>0) i++;
		cout << "Level: " << levels[i] << endl;

		if(strcmp(argv[1], "--file") == 0) {
			ifstream in;
			in.open("test");
			assert(!in.fail());
			string c;
			while(!in.eof()) {
				string temp;
				std::getline(in, temp);
				c+=temp;
			}
			CNode* node =  parse_constraint(c, NULL);
			int start = clock();
			Solver s(node, level, NULL, false);
			int end = clock();
			int time = end-start;

			if(s.get_result()->get_type() != FALSE_NODE){
				cout << "SAT" << endl;
			}
			else cout << "UNSAT" << endl;
			cout << "Time: " << ((double)time)/((double)CLOCKS_PER_SEC) << endl;
		}
		else if(strcmp(argv[1], "--regress") == 0)
		{
			ifstream myfile;
			myfile.open(REGRESS_FILE);
			vector<Regression> regs;
			init_regs(myfile, regs);
			myfile.close();
			int ticks = 0;
			bool success = true;
			for(unsigned int i=0; i < regs.size(); i++)
			{
				cout << "Regression #" << i << ": ";
				Regression &r = regs[i];
				CNode::clear();
				CNode* constraint = parse_constraint(r.query, NULL);
				if(constraint ==  NULL) {
					cout << "Regression # " << i << " does not parse." << endl;
					success = false;
					continue;
				}
				int start = clock();
				Solver s(constraint, level, NULL, false);
				int end = clock();
				ticks+=(end-start);
				bool sat = s.get_result()->get_type()!=FALSE_NODE;
				if(sat!=r.sat){
					cout << "Regression #" << i << " failed." << endl;
					success = false;
				}
				else
					cout << "Success (" <<
					((double)(end-start))/((double)CLOCKS_PER_SEC) << ") seconds"
					<< endl;

			}
			if(success) cout << "Success" << endl;
			else cout << "Failure" << endl;
			cout << "Total time: " <<
			((double)ticks)/((double)CLOCKS_PER_SEC) << endl;


		}
		return 0;
	}


	pipe(rgfd);

	//delete me
	{
	Gtk::Main kit(argc, argv);
	Gtk::Window* ui_window = NULL;
	Glib::RefPtr<Gnome::Glade::Xml> refXml =
				Gnome::Glade::Xml::create("/home/tdillig/Desktop/solver.glade", "solverui");
	refXml->get_widget("solverui", ui_window);
	kit.run(*ui_window);
	return 0;
	}
	//delete me end



	Gtk::Main kit(argc, argv);
	Gtk::Window* ui_window = NULL;
	Glib::RefPtr<Gnome::Glade::Xml> refXml =
				Gnome::Glade::Xml::create("solver-ui.glade", "solverui");
	refXml->get_widget("solverui", ui_window);
	Gtk::Button* solve_button = NULL;
	refXml->get_widget("solve", solve_button);
	assert(solve_button != NULL);
	solve_button->signal_clicked().connect( sigc::ptr_fun(solve_button_clicked) );

	Gtk::TextView* input = NULL;
	refXml->get_widget("input", input);
	assert(input!=NULL);
	input_buffer = Gtk::TextBuffer::create();
	input->set_buffer(input_buffer);

	Gtk::TextView* output = NULL;
	refXml->get_widget("output", output);
	assert(output!=NULL);
	output_buffer = Gtk::TextBuffer::create();
	output->set_buffer(output_buffer);






	sat_assign_button = NULL;
	refXml->get_widget("assignment", sat_assign_button);
	assert(sat_assign_button != NULL);


	verify_simplification_button = NULL;
	refXml->get_widget("verify_simplification", verify_simplification_button);
	assert(verify_simplification_button != NULL);

	stats_button = NULL;
	refXml->get_widget("stats", stats_button);
	assert(stats_button != NULL);



	spin_button = NULL;
	refXml->get_widget("spinbutton", spin_button);
	assert(spin_button != NULL);

	espin_button = NULL;
	refXml->get_widget("espinbutton", espin_button);
	assert(espin_button != NULL);


	register_output_callback(display_line);

	Gtk::Button* add_regress_button = NULL;
	refXml->get_widget("add", add_regress_button);
	assert(add_regress_button != NULL);
	add_regress_button->signal_clicked().connect
	( sigc::ptr_fun(add_regression) );

	Gtk::Button* add_e_regress_button = NULL;
	refXml->get_widget("adde", add_e_regress_button);
	assert(add_e_regress_button != NULL);
	add_e_regress_button->signal_clicked().connect
	( sigc::ptr_fun(add_e_regression) );

	Gtk::Button* run_regress_button = NULL;
	refXml->get_widget("run", run_regress_button);
	assert(run_regress_button != NULL);
	run_regress_button->signal_clicked().connect
	( sigc::ptr_fun(run_regressions) );

	Gtk::Button* run_eregress_button = NULL;
	refXml->get_widget("rune", run_eregress_button);
	assert(run_eregress_button != NULL);
	run_eregress_button->signal_clicked().connect
	( sigc::ptr_fun(run_eregressions) );


	Gtk::Button* eliminate = NULL;
	refXml->get_widget("eliminate", eliminate);
	assert(eliminate != NULL);
	eliminate->signal_clicked().connect
	( sigc::ptr_fun(eliminate_button_clicked) );



	spin_button->signal_value_changed().connect
	( sigc::ptr_fun(load_regressions) );


	espin_button->signal_value_changed().connect
	( sigc::ptr_fun(load_eregressions) );

	red = NULL;
	refXml->get_widget("red", red);
	assert(red != NULL);

	green = NULL;
	refXml->get_widget("green", green);
	assert(green != NULL);


	ered = NULL;
	refXml->get_widget("ered", ered);
	assert(ered != NULL);

	egreen = NULL;
	refXml->get_widget("egreen", egreen);
	assert(egreen != NULL);



	Gtk::TextView* regress = NULL;
	refXml->get_widget("regress", regress);
	assert(regress!=NULL);
	regress_buffer = Gtk::TextBuffer::create();
	regress->set_buffer(regress_buffer);

	Gtk::TextView* eregress = NULL;
	refXml->get_widget("eregress", eregress);
	assert(eregress!=NULL);
	eregress_buffer = Gtk::TextBuffer::create();
	eregress->set_buffer(eregress_buffer);


	Gtk::TextView* cinput = NULL;
	refXml->get_widget("cinput", cinput);
	assert(cinput!=NULL);
	cinput_buffer = Gtk::TextBuffer::create();
	cinput->set_buffer(cinput_buffer);

	Gtk::TextView* coutput = NULL;
	refXml->get_widget("coutput", coutput);
	assert(coutput!=NULL);
	coutput_buffer = Gtk::TextBuffer::create();
	coutput->set_buffer(coutput_buffer);



	Gtk::Button* convert_button = NULL;
	refXml->get_widget("convert", convert_button);
	assert(convert_button != NULL);
	convert_button->signal_clicked().connect
	( sigc::ptr_fun(convert_button_clicked) );


	num_vars = NULL;
	refXml->get_widget("num_vars", num_vars);
	assert(num_vars != NULL);

	max_coefficient = NULL;
	refXml->get_widget("max_coefficient", max_coefficient);
	assert(max_coefficient != NULL);

	num_constraints = NULL;
	refXml->get_widget("num_constraints", num_constraints);
	assert(num_constraints != NULL);

	Gtk::TextView* generated = NULL;
	refXml->get_widget("generated", generated);
	assert(generated!=NULL);
	generated_buffer = Gtk::TextBuffer::create();
	generated->set_buffer(generated_buffer);

	Gtk::Button* generate_button = NULL;
	refXml->get_widget("generate", generate_button);
	assert(generate_button != NULL);
	generate_button->signal_clicked().connect
	( sigc::ptr_fun(generate_button_clicked) );



	Gtk::TextView* hnf_in = NULL;
	refXml->get_widget("hnf_in", hnf_in);
	assert(hnf_in!=NULL);
	hnf_in_buffer = Gtk::TextBuffer::create();
	hnf_in->set_buffer(hnf_in_buffer);

	Gtk::TextView* hnf_out = NULL;
	refXml->get_widget("hnf_out", hnf_out);
	assert(hnf_out!=NULL);
	hnf_out_buffer = Gtk::TextBuffer::create();
	hnf_out->set_buffer(hnf_out_buffer);

	Gtk::Button* hnf_button = NULL;
	refXml->get_widget("hnf_button", hnf_button);
	assert(hnf_button != NULL);
	hnf_button->signal_clicked().connect
	( sigc::ptr_fun(hnf_button_clicked) );

	timeout_button = NULL;
	refXml->get_widget("timeout", timeout_button);
	assert(timeout_button != NULL);
	timeout_button->signal_value_changed().connect
		( sigc::ptr_fun(timeout_changed) );


	solve_options = NULL;
	refXml->get_widget("solve_options", solve_options);
	f_refTreeModel = Gtk::ListStore::create(option_columns);
	f_refTreeModel->clear();
	solve_options->set_model(f_refTreeModel);
	//solve_options->pack_start(option_columns.col_id);

	for(int i=0; i < num_levels; i++) {
		Gtk::TreeModel::Row row = *(f_refTreeModel->append());
		row[option_columns.col_id] = levels[i];
	}
	solve_options->set_active(0);




	solve_options->signal_changed().connect(sigc::ptr_fun(solve_options_changed) );

	status = NULL;
	refXml->get_widget("status", status);
	assert(status!=NULL);

	num_regs = get_num_regs();
	spin_button->set_range(0, num_regs-1);

	num_eregs = get_num_eregs();
	espin_button->set_range(0, num_eregs-1);

	load_input_buffer();

	kit.run(*ui_window);
	delete solve_button;
	delete input;
	delete output;
	delete sat_assign_button;
	delete add_regress_button;
	delete run_regress_button;
	delete verify_simplification_button;
	delete stats_button;
	delete red;
	delete green;
	delete regress;
	delete status;
	delete ui_window;

	return 0;
}
*/
