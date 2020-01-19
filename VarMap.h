/*
 * VarMap.h
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#ifndef VARMAP_H_
#define VARMAP_H_

#include <map>
#include <unordered_map>
#include <string>
#include <set>
using namespace std;


#define NUM_BITS_RESERVED 5


namespace il{
	class type;
}
namespace sail{
	class Variable;
}

class Term;
class CNode;

/*
 * Since string's can take too much space, we associate every
 * variable or function with a unique identifier. VarMap is needed
 * for pretty printing.
 */
class VarMap {
private:
	unordered_map<string, int> name_to_id_map;
	unordered_map<int, string> id_to_name_map;
	int cur_id;
public:
	VarMap();
	int get_id(string name, bool invertible=false);
	int get_attrib(int id);
	string get_name(int id);
	bool contains_name(string name);
	void get_all_vars(set<string>& var_names);
	virtual ~VarMap();
	void clear();

};

#endif /* VARMAP_H_ */
