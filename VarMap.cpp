/*
 * VarMap.cpp
 *
 *  Created on: Sep 1, 2008
 *      Author: tdillig
 */

#include "VarMap.h"
#include "assert.h"
#include "cnode.h"
#include "Term.h"

#define START_ID 0



VarMap::VarMap() {
	cur_id=START_ID;

}

void VarMap::clear()
{
	cur_id=START_ID;
	name_to_id_map.clear();
	id_to_name_map.clear();
}



int VarMap::get_id(string name, bool invertible)
{
	if(name == "" || (name[0]>='0' && name[0]<='9')){
		cout << "name: " << name << endl;
		assert(false);
	}

	if(name_to_id_map.count(name) > 0){
		int res = name_to_id_map[name] << (NUM_BITS_RESERVED+1);
		if(invertible) res |= (1 << NUM_BITS_RESERVED);
		return res;
	}
	name_to_id_map[name]=cur_id;
	id_to_name_map[cur_id] = name;
	++cur_id;
	int res = (cur_id-1) << (NUM_BITS_RESERVED+1);
	if(invertible) res |= (1 << NUM_BITS_RESERVED);
	return res;
}
string VarMap::get_name(int id)
{
	id = id >> (NUM_BITS_RESERVED+1);
	assert(id_to_name_map.count(id) >0);
	return id_to_name_map[id];
}

int VarMap::get_attrib(int id)
{
	unsigned int attrib = id << (sizeof(int)*8 - NUM_BITS_RESERVED);
	attrib = attrib >> (sizeof(int)*8 - NUM_BITS_RESERVED);
	return attrib;
}


bool VarMap::contains_name(string name)
{
	return (name_to_id_map.count(name) > 0);
}

void VarMap::get_all_vars(set<string>& var_names)
{
	unordered_map<string, int>::iterator it = name_to_id_map.begin();
	for(; it!= name_to_id_map.end(); it++)
	{
		var_names.insert(it->first);
	}
}


VarMap::~VarMap() {

}
