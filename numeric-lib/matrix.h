/*
 * matrix.h
 *
 *  Created on: Dec 6, 2008
 *      Author: tdillig
 *
 *  This class allows for infinite precision matrix computations.
 *  To increase efficiency, the matrix "upgrades" entire rows at a time to
 *  GNU MP values rather than representing each indivdual element as a bignum.
 */

#ifndef MATRIX_H_
#define MATRIX_H_

#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include "bignum.h"
#include <assert.h>
#include <vector>
using namespace std;


#include <map>
#include <set>


typedef long int d_type;





typedef d_type v4si __attribute__ ((vector_size (32)));

typedef d_type v2si __attribute__ ((vector_size (16)));

/*
 * Should operations on rows use SSE vector (SIMD) instructions?
 */
#define VECTORIZE_TWO true

//#define VECTORIZE_FOUR true





#define MD(rr,cc) (((d_type*)(dmatrix+(rr*mcols)))[cc])


//#define MD(rr,cc)((dmatrix[rr*mcols+cc]).d)
#define MI(rr,cc)((dmatrix[rr*mcols+cc]).i)


/*
 * Enables bounds checking for each operation. Since most checks are
 * amortized over a row operation, the expected slow-down is ~5%.
 */
#define CHECK_BOUNDS false

//#define ENABLE_CHECKS true

#define DWORD_ALIGN(x) (((((x)+1)+3)/4)*4)


class matrix {
	friend class slack_matrix;

protected:
	data_type *dmatrix;
	const int rows;
	const int cols;
	const int mcols;
	bool *big_rows;
	vector<string> *vars;

/*
 * If checking is enabled, we compare the matrix with a matrix of
 * bignums.
 */
#ifdef ENABLE_CHECKS
	bignum* cmatrix;
#endif

public:
	/*
	 * Constructs an infinite precision matrix of size rows x num_vars+2 and
	 * initializes all values to 0.
	 */
	inline matrix(int rows, int num_vars,
			vector<string> *vars):
				rows(rows), cols(num_vars+2), mcols(DWORD_ALIGN(cols+1)),
				vars(vars)
	{
		dmatrix = new data_type[(rows+2)*mcols];
		big_rows = new bool[rows];
		memset(big_rows, 0, rows*sizeof(bool));
		memset(dmatrix, 0, rows*mcols*sizeof(data_type));


#ifdef ENABLE_CHECKS
		cmatrix = new bignum[(rows+2)*mcols];
		for(int r=0; r<rows; r++) {
			infinitize_row(r);
		}
#endif

	}

	inline matrix(int rows, int cols):
					rows(rows), cols(cols), mcols(DWORD_ALIGN(cols+1))
	{
		dmatrix = new data_type[(rows+2)*mcols];
		big_rows = new bool[rows];
		memset(big_rows, 0, rows*sizeof(bool));
		memset(dmatrix, 0, rows*mcols*sizeof(data_type));
		vars = NULL;
	}


	inline int num_rows()
	{
		return rows;
	}


	inline int num_vars()
	{
		return cols-2;
	}
	inline int num_cols()
	{
		return cols;
	}

	/*
	 * Creates a duplicate of other matrix. Takes an (optional) argument
	 * specifying how many rows should be added.
	 */
	inline matrix(const matrix& other, int new_rows=-1):
		rows(new_rows==-1 ? other.rows : other.rows+new_rows),
	cols(other.cols), mcols(other.mcols),vars(other.vars)
	{



		dmatrix = new data_type[(rows+2)*mcols];
		big_rows = new bool[rows];
		if(new_rows!=-1){
			memset(big_rows, 0, rows*sizeof(bool));
			memset(dmatrix, 0, rows*mcols*sizeof(data_type));

		}
		memcpy(big_rows, other.big_rows, rows*sizeof(bool));
		for(int r=0; r < rows; r++) {
			if(!big_rows[r]) {
				memcpy(dmatrix+r*mcols, other.dmatrix+r*mcols,
						cols*sizeof(data_type));
				continue;
			}
			int end = r*mcols+cols;
			for(int i = r*mcols; i < end; i++) {
				mpz_init_set(dmatrix[i].i, other.dmatrix[i].i);
			}

		}
#ifdef ENABLE_CHECKS
		cmatrix = new bignum[(rows+2)*mcols];
		for(int r = 0; r < rows; r++)
		{
			for(int c=0; c < cols; c++)
			{
				cmatrix[r*mcols+c] = other.cmatrix[r*mcols+c];
			}
		}
#endif
	}

	/*
	 * Simplifies all entries in the matrix.
	 */
	inline void simplify_matrix()
	{
		for(int r=0; r < rows; r++) {
			simplify_row(r);
		}
	}

	/*
	 * Sets matrix[r][c] = v.
	 */
	inline void set(int r, int c, bignum  v)
	{


		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
			assert(c>=0 && c<cols);
		}
#ifdef ENABLE_CHECKS
		cmatrix[r*mcols+c] = v;
#endif

		if(!v.infinite && !big_rows[r]){
			//dmatrix[r*mcols+c].d = v.data.d;
			MD(r, c) = v.data.d;
			return;
		}
		if(!big_rows[r]){
			infinitize_row(r);
		}
		if(v.infinite){
			//mpz_set(dmatrix[r*mcols+c].i, v.data.i);
			mpz_set(MI(r,c), v.data.i);
		}
		else {
			//mpz_set_si(dmatrix[r*mcols+c].i, v.data.d);
			mpz_set_si(MI(r, c), v.data.d);
		}
	}


	/*
	 * Sets matrix[r][c] = v.
	 */
	inline void set(int r, int c, long int i)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
			assert(c>=0 && c<cols);
		}
#ifdef ENABLE_CHECKS
		cmatrix[r*mcols+c] = bignum(i);
#endif
		if(!big_rows[r]){
			//dmatrix[r*mcols+c].d = i;
			MD(r,c) = i;
			return;
		}
		//mpz_set_si(dmatrix[r*mcols+c].i, i);
		mpz_set_si(MI(r, c), i);

	}
	/*
	 * Returns matrix[r][c].
	 */
	inline bignum get(int r, int c)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
			assert(c>=0 && c<cols);
		}
		if(!big_rows[r]){
			//bignum bg(dmatrix[r*mcols+c].d);
			bignum bg(MD(r, c));
			return bg;
		}
		//return bignum(dmatrix[r*mcols+c].i);
		return bignum(MI(r, c));

	}

	/*
	 * Multiplies row r by f.
	 */
	inline void multiply_row(int r, bignum f)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
#ifdef ENABLE_CHECKS
		for(int i=r*mcols; i<r*mcols+cols-1; i++) {
			cmatrix[i]*=f;
		}
#endif


		if(big_rows[r]){
			multiply_row_i(r, f);
			return;
		}
		if(f.infinite){
			infinitize_row(r);
			multiply_row_i(r, f);
			return;
		}



		long int max = labs(MD(r, 0));
		/*for(int i=r*mcols+1; i<end; i++) {
			if(labs(dmatrix[i].d)>max){
				max = labs(dmatrix[i].d);
			}
		}*/
		for(int i=1; i<cols-1; i++) {
			if(labs(MD(r, i))>max){
				max = labs(MD(r, i));
			}
		}
		if(bignum::m_overflow(max, f.data.d)){
			infinitize_row(r);
			multiply_row_i(r, f);
			return;
		}

		/*for(int i=r*mcols; i<end; i++) {
			dmatrix[i].d*=f.data.d;
		}*/
#ifdef VECTORIZE_TWO
		{
			v2si c = {f.data.d, f.data.d};
			d_type last = MD(r, cols-1);
			v2si* cur = (v2si*)&(MD(r, 0));
			v2si* end = (v2si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)*=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifdef VECTORIZE_FOUR
		{
			v4si c = {f.data.d, f.data.d, f.data.d, f.data.d};
			d_type last = MD(r, cols-1);
			v4si* cur = (v4si*)&(MD(r, 0));
			v4si* end = (v4si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)*=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif


#ifndef VECTORIZE_TWO
#ifndef VECTORIZE_FOUR
		else
		{
			for(int i=0; i<cols-1; i++) {
				MD(r, i)*=f.data.d;
			}
		}
#endif
#endif

	}

	/*
	 * Multiplies row r by f.
	 */
	inline void flip_row_sign(int r)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
#ifdef ENABLE_CHECKS
		for(int i=r*mcols; i<r*mcols+cols-1; i++) {
				cmatrix[i]=-cmatrix[i];
		}
#endif

		if(big_rows[r]){
			//for(int i=r*mcols; i < end; i++) {
			//	mpz_neg(dmatrix[i].i, dmatrix[i].i);
			//}
			for(int i=0; i < cols-1; i++) {
				mpz_neg(MI(r, i), MI(r, i));
			}
			return;
		}
		//for(int i=r*mcols; i < end; i++) {
		//	dmatrix[i].d=-dmatrix[i].d;
		//}

#ifdef VECTORIZE_TWO
		{
			d_type last = MD(r, cols-1);
			v2si* cur = (v2si*)&(MD(r, 0));
			v2si* end = (v2si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)=-*cur;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifdef VECTORIZE_FOUR
		{
			d_type last = MD(r, cols-1);
			v4si* cur = (v4si*)&(MD(r, 0));
			v4si* end = (v4si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)=-*cur;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif





#ifndef VECTORIZE_TWO
#ifndef VECTORIZE_FOUR

		for(int i=0; i < cols-1; i++) {
			MD(r, i)=-MD(r, i);
		}
#endif
#endif


	}


	/*
	 * Note: This function assumes that f divides every elem cleanly &
	 * that f>0.
	 */
	inline void divide_row(int r, bignum f)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
			assert(f>=0);
		}
#ifdef ENABLE_CHECKS
		for(int i=r*mcols; i<r*mcols+cols-1; i++) {
				cmatrix[i]/=f;
		}
#endif

		if(big_rows[r]){
			divide_row_i(r, f);
			return;
		}
		if(f.infinite){
			infinitize_row(r);
			divide_row_i(r, f);
			return;
		}


		//for(int i=r*mcols; i<end; i++) {
		//	dmatrix[i].d/=f.data.d;
		//}

#ifdef VECTORIZE_TWO
		{
			d_type last = MD(r, cols-1);
			v2si c = {f.data.d, f.data.d};
			v2si* cur = (v2si*)&(MD(r, 0));
			v2si* end = (v2si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)/=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifdef VECTORIZE_FOUR
		{
			d_type last = MD(r, cols-1);
			v4si c = {f.data.d, f.data.d, f.data.d, f.data.d};
			v4si* cur = (v4si*)&(MD(r, 0));
			v4si* end = (v4si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)/=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifndef VECTORIZE_TWO
#ifndef VECTORIZE_FOUR
		for(int i=0; i<cols-1; i++) {
			MD(r, i)/=f.data.d;
		}
#endif
#endif



	}



	inline void add_row(int r, bignum f)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
#ifdef ENABLE_CHECKS
		for(int i=r*mcols; i<r*mcols+cols-1; i++) {
			cmatrix[i]+=f;
		}
#endif

		if(big_rows[r]){
			add_row_i(r, f);
			return;
		}
		if(f.infinite){
			infinitize_row(r);
			add_row_i(r, f);
			return;
		}

		//long int max = labs(dmatrix[r*mcols].d);
		long int max = labs(MD(r,0));
		//for(int i=r*mcols+1; i<end; i++) {
		//	if(labs(dmatrix[i].d)>max)
		//		max = labs(dmatrix[i].d);
		//}
		for(int i=1; i<cols-1; i++) {
			if(labs(MD(r,i))>max)
				max = labs(MD(r,i));
		}
		if(bignum::a_overflow(max, f.data.d)){
			infinitize_row(r);
			add_row_i(r, f);
			return;
		}

		//for(int i=r*mcols; i<end; i++) {
		//	dmatrix[i].d+=f.data.d;
		//}

#ifdef VECTORIZE_TWO
		{
			d_type last = MD(r, cols-1);
			v2si c = {f.data.d, f.data.d};
			v2si* cur = (v2si*)&(MD(r, 0));
			v2si* end = (v2si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)+=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifdef VECTORIZE_FOUR
		{
			d_type last = MD(r, cols-1);
			v4si c = {f.data.d, f.data.d, f.data.d, f.data.d};
			v4si* cur = (v4si*)&(MD(r, 0));
			v4si* end = (v4si*)&(MD(r, cols-1));
			for(; cur <end; cur++) {

				(*cur)+=c;
				//MD(r, i)*=f.data.d;
			}
			MD(r, cols-1) = last;
		}
#endif

#ifndef VECTORIZE_TWO
#ifndef VECTORIZE_FOUR

		for(int i=0; i<cols-1; i++) {
			MD(r,i)+=f.data.d;
		}
		return;
#endif
#endif

	}

	inline ~matrix()
	{
		for(int r=0; r < rows; r++) {
			if(!big_rows[r]) continue;
			delete_bigrow(r);
		}
		delete[] big_rows;
		delete[] dmatrix;
#ifdef ENABLE_CHECKS
		delete[] cmatrix;
#endif
	}

	inline void delete_bigrow(int r){
		//for(int i=r*mcols; i < end; i++) {
		//	mpz_clear(dmatrix[i].i);
		//}
		for(int i=0; i < cols; i++) {
			mpz_clear(MI(r,i));
		}
	}

	string to_string()
	{
		string res;
		if(vars != NULL){
			for(int c=0; c<cols-2; c++) {
				if((int)vars->size()>c)
					res+=(*vars)[c];
				else res+="<u>";
				res+="\t";
			}
			res+="[c]\t[p]";
			res+="\n";
		}
		for(int r=0; r < rows; r++) {
			for(int c=0; c<cols; c++) {
				res+=get(r,c).to_string();
				if(c<cols-1) res+="\t";
			}
			if(big_rows[r]) res+=" (b)";
			res+="\n";
		}
		return res;
	}
	friend ostream& operator <<(ostream &os,const matrix &obj);

	//----------------------------------------------------------
	/*
	 * Simplex specific functions for the matrix are below here.
	 */
	//----------------------------------------------------------

	inline bignum get_coef_gcd(int r)
	{
		if(big_rows[r])
		{
			mpz_t gcd;
			//mpz_init_set(gcd, dmatrix[r*mcols].i);
			mpz_init_set(gcd, MI(r,0));
			mpz_abs(gcd, gcd);
			//for(int i= r*mcols+1; i < r*mcols+cols-2; i++){
			//	mpz_gcd(gcd, gcd, dmatrix[i].i);
			//}
			for(int i= 1; i < cols-2; i++){
				mpz_gcd(gcd, gcd, MI(r,i));
			}
			bignum b(gcd);
			mpz_clear(gcd);
			return b;
		}
		//long int gcd = labs(dmatrix[r*mcols].d);
		long int gcd = labs(MD(r,0));
		//for(int i= r*mcols+1; i < r*mcols+cols-2; i++){
		//	gcd = bignum::compute_int_gcd(gcd, dmatrix[i].d);
		//}
		for(int i= 1; i < cols-2; i++){
			gcd = bignum::compute_int_gcd(gcd, MD(r,i));
		}
		return bignum(gcd);

	}

	inline vector<string> & get_vars()
	{
		return *vars;
	}


	/*
	 * Returns the pivot element of row r
	 */
	inline int get_pivot(int r)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
		if(!big_rows[r]){
			//return dmatrix[r*mcols+(cols-1)].d;
			return MD(r, cols-1);
		}
		return get(r, cols-1).to_int();
	}

	inline bignum get_constant(int r)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
		if(big_rows[r]){
			//return bignum(dmatrix[r*mcols+(cols-2)].i);
			return bignum(MI(r, cols-2));
		}
		//return bignum(dmatrix[r*mcols+(cols-2)].d);
		return bignum(MD(r, cols-2));
	}

	inline void set_constant(int r, bignum  b)
	{
		set(r, cols-2, b);
	}

	inline void set_pivot(int r, int p)
	{
		set(r, cols-1, p);
	}

	/*
	 * Returns the index of the first positive
	 * coefficient in row r.
	 */
	inline int get_first_positive_index(int r)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r<rows);
		}
		if(!big_rows[r]) {
			for(int c=0; c < cols-2; c++) {
				//if(dmatrix[row+c].d>0)
				//	return c;
				if(MD(r,c)>0)
					return c;
			}
			return -1;
		}

		for(int c=0; c < cols-2; c++) {
			//if(mpz_cmp_si(dmatrix[row+c].i, 0)>0)
			//	return c;
			if(mpz_cmp_si(MI(r,c), 0)>0)
				return c;
		}
		return -1;
	}



	void pivot(int pivot_row, int pivot_index, bool simplify = true)
	{
		if(CHECK_BOUNDS){
			assert(pivot_row>=0 && pivot_row<rows-1);
			assert(pivot_index>=0 && pivot_index< cols-2);
		}

		bignum pc = get(pivot_row, pivot_index);
		if(pc<0)
			flip_row_sign(pivot_row);

		/*
		 * First, if pivot row is bignum, we turn everything big.
		 */
		if(big_rows[pivot_row]){
			for(int r=0; r<rows; r++) {
				if(big_rows[r]) continue;
				infinitize_row(r);
			}
			pivot_i(pivot_row, pivot_index, simplify);
			return;
		}
#ifdef ENABLE_CHECKS
		/*
		 * Consistency checking only works if everything is a bignum
		 */
		assert(false);
#endif
		//record the pivot index
		set(pivot_row, cols-1, pivot_index);

		//long int pivot_max = labs(dmatrix[pivot_row*mcols].d);
		long int pivot_max = labs(MD(pivot_row, 0));
		//for(int i= pivot_row*mcols+1; i < pivot_row*mcols+cols-1; i++){
		//	if(labs(dmatrix[i].d) > pivot_max){
		//		pivot_max = labs(dmatrix[i].d);
		//	}
		//}
		for(int i= 1; i < cols-1; i++){
			if(labs(MD(pivot_row, i)) > pivot_max){
				pivot_max = labs(MD(pivot_row, i));
			}
		}

		//long int pivot_c = dmatrix[pivot_row*mcols+pivot_index].d;
		long int pivot_c = MD(pivot_row,pivot_index);
		for(int r=0; r < rows; r++) {
			if(r==pivot_row) continue;

			if(big_rows[r]){
				pivot_row_d_i(pivot_row, pivot_index, pivot_c, r);
				simplify_row_i(r);
				continue;
			}

			//long int cur_c = dmatrix[r*mcols+pivot_index].d;
			long int cur_c = MD(r,pivot_index);
			long int gcd = bignum::compute_int_gcd(pivot_c, cur_c);
			if(gcd == 0) continue;
			long int f_pivot =  cur_c / gcd;
			long int f_cur =  pivot_c / gcd;

			if(f_cur<0) {
				f_cur = -f_cur;
				f_pivot = -f_pivot;
			}

			/*
			 * If we don't have digits left for the multiplication, upgrade to
			 * bignums.
			 */
			if(bignum::m_overflow(f_cur, cur_c) ||
					bignum::m_overflow(f_pivot, pivot_c ))
			{

				infinitize_row(r);
				multiply_row(r, f_cur);
				sub_multiply_row_d_i(r,  pivot_row, f_pivot);
				simplify_row_i(r);
				continue;
			}
			multiply_row(r, f_cur);
			if(big_rows[r]){
				sub_multiply_row_d_i(r,  pivot_row, f_pivot);
				simplify_row_i(r);
				continue;
			}
			sub_multiply_row(pivot_max, r, pivot_row, f_pivot);
			if(simplify) simplify_row(r);
		}

#ifdef ENABLE_CHECKS
			for(int r=0; r < rows-1; r++) {
				int c_pivot = get_pivot(r);
				assert(get(r, c_pivot)>0);
				for(int r2=0; r2<rows; r2++) {
					if(r2 == r) continue;
					assert(get(r2, c_pivot) == 0);
				}

			}
#endif
	}




//-------------------------------------------------------------
void multiply(matrix & op, matrix & result)
{
	assert(cols == op.rows);
	assert(result.rows == rows);
	assert(result.cols == op.cols);

	for(int r=0; r < result.rows; r++)
	{
		for(int c=0; c < result.cols; c++)
		{
			result.set(r,c,dot_product(r,c, op));
		}
	}

}

inline bignum dot_product(int r, int cc, matrix &op)
{
	bignum res;
	for(int c=0; c < cols; c++) {
		bignum my_e = get(r, c);
		bignum other_e = op.get(c, cc);
		res+=my_e*other_e;
	}
	return res;
}




void compute_redundant_rows(std::set<int> &red_rows)
{
	matrix m(rows+1, cols+2);
	for(int r=0; r < rows; r++)
	{
		for(int c=0; c <cols; c++)
		{
			m.set(r,c,get(r,c));
		}
	}

	map<int, int> row_map;
	for(int r=0; r <rows; r++) {
		int pivot_c = -1;
		for(int c=0; c < cols; c++) {
			if(row_map.count(c) >0) continue;
			if(m.get(r, c) == 0) continue;
			pivot_c = c;
			row_map[pivot_c] = r;
			break;
		}
		if(pivot_c == -1){
			red_rows.insert(r);
			continue;
		}
		m.pivot(r, pivot_c);
	}

}

bignum invert(matrix & result)
{

	assert(rows == cols);
	assert(result.cols == rows);
	assert(result.cols == result.rows);

	matrix m(rows+1, 2*cols+2);
	for(int r=0; r < rows; r++){
		for(int c=0; c < cols; c++) {
			m.set(r, c, get(r,c));
		}
		m.set(r, cols+r, 1);
	}

	map<int, int> row_map;

	for(int r=0; r <rows; r++) {
		int pivot_c = -1;
		for(int c=0; c < cols; c++) {
			if(row_map.count(c) >0) continue;
			if(m.get(r, c) == 0) continue;
			pivot_c = c;
			row_map[pivot_c] = r;
			break;
		}
		//system was linearely dependent
		assert(pivot_c != -1);
		m.pivot(r, pivot_c);
	}


	bignum gcd = 0;
	bignum lcm = 1;

	for(int pivot_c = 0; pivot_c < cols; pivot_c++) {
		assert(row_map.count(pivot_c) > 0);
		int row = row_map[pivot_c];
		bignum p_coef = m.get(row, pivot_c);
		gcd = p_coef.compute_gcd(lcm);
		bignum n_coef = p_coef.divexact(gcd);
		if(n_coef < 0) n_coef = -n_coef;
		lcm*= n_coef;
	}

	for(int pivot_c = 0; pivot_c < cols; pivot_c++) {
		int row = row_map[pivot_c];
		bignum p_coef = m.get(row, pivot_c);
		assert(lcm.divisible(p_coef));
		bignum factor = lcm.divexact(p_coef);
		m.multiply_row(row, factor);
	}


	for(int orig_c = 0; orig_c<cols; orig_c++) {
		int row = row_map[orig_c];
		for(int c =0; c < cols; c++){

			result.set(orig_c,c, m.get(row,c+cols));
		}
	}


	return lcm;

}

void vector_multiply(bignum * b, bignum* res)
{
	for(int r = 0; r < rows; r++) {
		bignum cur_res = 0;
		for(int c=0; c < cols; c++) {
			bignum a_rc = get(r, c);
			cur_res += a_rc*b[c];
		}
		res[r] = cur_res;
	}
}

void row_vector_multiply(bignum * b, bignum* res)
{
	for(int c = 0; c < cols; c++) {
		bignum cur_res = 0;
		for(int r=0; r < rows; r++) {
			bignum a_rc = get(r, c);
			cur_res += a_rc*b[r];
		}
		res[c] = cur_res;
	}
}

//-------------------------------------------------------------


private:


	inline void add_row_i(int r, bignum & f)
	{
		if(f.infinite) {
			//for(int i = r*mcols; i<end; i++) {
			//	mpz_add(dmatrix[i].i, dmatrix[i].i, f.data.i);
			//}
			for(int i = 0; i<cols-1; i++) {
				mpz_add(MI(r, i), MI(r, i), f.data.i);
			}
			return;
		}
		mpz_t temp;
		mpz_init_set_si(temp, f.data.d);
		//for(int i = r*mcols; i<end; i++) {
		//	mpz_add(dmatrix[i].i, dmatrix[i].i, temp);
		//}

		for(int i = 0; i<cols-1; i++) {
			mpz_add(MI(r, i), MI(r, i), temp);
		}
		mpz_clear(temp);
	}

	inline void multiply_row_i(int r, bignum & f)
	{
		if(f.infinite) {
			/*for(int i = r*mcols; i<end; i++) {
				mpz_mul(dmatrix[i].i, dmatrix[i].i, f.data.i);
			}*/
			for(int i = 0; i<cols-1; i++) {
				mpz_mul(MI(r, i), MI(r, i), f.data.i);
			}
			return;
		}
		//for(int i = r*mcols; i<end; i++) {
		//	mpz_mul_si(dmatrix[i].i, dmatrix[i].i, f.data.d);
		//}
		for(int i = 0; i<cols-1; i++) {
			mpz_mul_si(MI(r, i), MI(r, i), f.data.d);
		}
	}

	inline void divide_row_i(int r, bignum & f)
	{
		if(f.infinite) {
			for(int i = 0; i<cols-1; i++) {
				mpz_divexact(MI(r, i), MI(r,i), f.data.i);
			}
			return;
		}
		for(int i = 0; i<cols-1; i++) {

			mpz_divexact_ui(MI(r,i), MI(r,i), f.data.d);
		}
	}

	inline void simplify_row(int r)
	{
		if(CHECK_BOUNDS){
			assert(r>=0 && r< rows);
		}
		if(big_rows[r]){
			simplify_row_i(r);
			return;
		}
		long int gcd = labs(MD(r,0));
		for(int i= 1; i < cols-1; i++) {
			gcd = bignum::compute_int_gcd(gcd, MD(r,i));
		}
		if(gcd == 0 || gcd == 1) return;
		for(int i = 0; i <cols-1; i++) {
			MD(r,i)/=gcd;
		}
	}



	inline void simplify_row_i(int r)
	{
		mpz_t gcd;
		mpz_init_set(gcd, MI(r,0));
		mpz_abs(gcd, gcd);
		for(int i=1; i < cols-1; i++) {
			mpz_gcd(gcd, gcd, MI(r,i));
		}
		if(mpz_cmp_si(gcd, 0) ==0 || mpz_cmp_si(gcd, 1) ==0){
			mpz_clear(gcd);
			return;
		}
		for(int i=0; i < cols-1; i++) {
			mpz_divexact(MI(r,i), MI(r,i), gcd);
		}
		mpz_clear(gcd);
	}

	inline void pivot_row_d_i(int pivot_row, int pivot_index,
			long int piv_c, int r)
	{
		if(CHECK_BOUNDS){
			assert(big_rows[r]);
			assert(!big_rows[pivot_row]);
		}


		mpz_t pivot_c;
		mpz_init_set_si(pivot_c, piv_c);


		mpz_t cur_c;
		mpz_t gcd;
		mpz_t f_pivot;
		mpz_t f_cur;

		mpz_init(cur_c);
		mpz_init(gcd);
		mpz_init(f_pivot);
		mpz_init(f_cur);

		mpz_set(cur_c, MI(r,pivot_index));
		mpz_gcd(gcd, pivot_c, cur_c);
		if(mpz_cmp_si(gcd, 0) == 0){
			mpz_clear(pivot_c);
			mpz_clear(cur_c);
			mpz_clear(gcd);
			mpz_clear(f_pivot);
			mpz_clear(f_cur);
			return;
		}

		mpz_divexact(f_pivot, cur_c, gcd);
		mpz_divexact(f_cur, pivot_c, gcd);
		if(mpz_cmp_si(f_cur, 0)<0)
		{
			mpz_neg(f_pivot, f_pivot);
			mpz_neg(f_cur, f_cur);
		}
		mpz_t cur;
		mpz_init(cur);
		for(int c=0; c<cols-1; c++) {
			mpz_mul(MI(r, c), MI(r, c), f_cur);
			mpz_set_si(cur, MD(pivot_row, c));
			mpz_submul(MI(r, c), cur, f_pivot);
		}
		mpz_clear(cur);

		mpz_clear(pivot_c);
		mpz_clear(cur_c);
		mpz_clear(gcd);
		mpz_clear(f_pivot);
		mpz_clear(f_cur);
	}


	/*
	 * Dest is bignum, pivot row is not. Dest has already been mutiplied.
	 */
	inline void sub_multiply_row_d_i(int dest_r, int pivot_r,  long int f_pivot)
	{
		mpz_t f_piv;
		mpz_t cur;
		mpz_init(cur);
		mpz_init_set_si(f_piv, f_pivot);
		for(int c=0; c<cols-1; c++) {
			mpz_set_si(cur, MD(pivot_r, c));
			mpz_submul(MI(dest_r, c), cur, f_piv);
		}
		mpz_clear(f_piv);
		mpz_clear(cur);
	}


	/*
	 * This function assumes that both the pivot row and the dest row
	 * are currently NOT bignums. Max is maximum abs value in pivot row.
	 */
	inline void sub_multiply_row(long int max, int dest_r, int pivot_r,
			long int f_pivot)
	{
		if(bignum::m_overflow(max, f_pivot))
		{
			infinitize_row(dest_r);
			sub_multiply_row_d_i(dest_r, pivot_r, f_pivot);
			return;
		}
		long int max_dest = MD(dest_r, 0);
		for(int i=1; i < cols-1; i++) {
			if(labs(MD(dest_r, i)) > max_dest) {
				max_dest = labs(MD(dest_r, i));
			}
		}
		long int max_pf = max*f_pivot;
		if(bignum::a_overflow(max_pf, max_dest))
		{
			infinitize_row(dest_r);
			sub_multiply_row_d_i(dest_r, pivot_r, f_pivot);
			return;
		}

#ifdef VECTORIZE_TWO
		{
			d_type last = MD(dest_r, cols-1);
			v2si c = {f_pivot, f_pivot};
			v2si* l = (v2si*)&MD(dest_r, 0);
			v2si* l_end = (v2si*)&MD(dest_r, cols-1);
			v2si* r = (v2si*)&MD(pivot_r, 0);
			for(; l<l_end; l++, r++) {
				(*l) -= (*r)*c;
			}
			MD(dest_r, cols-1) = last;
		}
#endif

#ifdef VECTORIZE_FOUR
		{
			d_type last = MD(dest_r, cols-1);
			v4si c = {f_pivot, f_pivot, f_pivot, f_pivot};
			v4si* l = (v4si*)&MD(dest_r, 0);
			v4si* l_end = (v4si*)&MD(dest_r, cols-1);
			v4si* r = (v4si*)&MD(pivot_r, 0);
			for(; l<l_end; l++, r++) {
				(*l) -= (*r)*c;
				//MD(r, i)*=f.data.d;
			}
			MD(dest_r, cols-1) = last;
		}
#endif

#ifndef VECTORIZE_TWO
#ifndef VECTORIZE_FOUR

		for(int c=0; c < cols-1; c++) {
			MD(dest_r, c) -= MD(pivot_r, c) * f_pivot;
		}
#endif
#endif


	}

	inline void pivot_i(int pivot_row, int pivot_index, bool simplify)
	{
		mpz_set_si(MI(pivot_row, cols-1), pivot_index);

		//now, all of the matix is a bignum.
		mpz_t pivot_c;
		mpz_init_set(pivot_c, MI(pivot_row, pivot_index));

		mpz_t cur_c;
		mpz_t gcd;
		mpz_t f_pivot;
		mpz_t f_cur;

		mpz_init(cur_c);
		mpz_init(gcd);
		mpz_init(f_pivot);
		mpz_init(f_cur);

#ifdef ENABLE_CHECKS
		cmatrix[pivot_row*mcols+cols-1] = pivot_index;
#endif

		for(int r=0; r < rows; r++){
			if(r==pivot_row) continue;

#ifdef ENABLE_CHECKS
			bignum b_pivot_c = cmatrix[pivot_row*mcols+pivot_index];
			bignum b_cur_c = cmatrix[r*mcols+pivot_index];
			bignum b_gcd = b_cur_c.compute_gcd(b_pivot_c);
			bignum b_f_pivot = b_cur_c/b_gcd;
			bignum b_f_cur = b_pivot_c/b_gcd;
			assert(b_f_cur >= 0);
			for(int c=0; c<cols-1; c++) {
				cmatrix[r*mcols+c]*=b_f_cur;
				cmatrix[r*mcols+c]-=cmatrix[pivot_row*mcols+c]*b_f_pivot;
			}
#endif


			mpz_set(cur_c, MI(r, pivot_index));
			if(mpz_cmp_si(cur_c, 0) == 0) continue;
			mpz_gcd(gcd, pivot_c, cur_c);
			if(mpz_cmp_si(gcd, 0) == 0) continue;
			mpz_divexact(f_pivot, cur_c, gcd);
			mpz_divexact(f_cur, pivot_c, gcd);
			if(mpz_cmp_si(f_cur, 0)<0)
			{
				mpz_neg(f_pivot, f_pivot);
				mpz_neg(f_cur, f_cur);
			}

			for(int c=0; c<cols-1; c++) {
				mpz_mul(MI(r, c), MI(r, c), f_cur);
				mpz_submul(MI(r, c),
						MI(pivot_row, c), f_pivot);
			}
			if(simplify) simplify_row_i(r);

		}
		mpz_clear(pivot_c);
		mpz_clear(cur_c);
		mpz_clear(gcd);
		mpz_clear(f_pivot);
		mpz_clear(f_cur);

#ifdef ENABLE_CHECKS
		check_consistency();
#endif
	}


	inline void infinitize_row(int r)
	{
		for(int i = cols-1; i >= 0; i--)
		{
			long int val = MD(r, i);
			mpz_init_set_si(MI(r, i), val);
			bignum t(MI(r,i));
		}
		big_rows[r] = true;
	}

	void check_consistency()
	{

#ifdef ENABLE_CHECKS
		cout << "checking consistency..." << endl;

		for(int r=0; r < rows; r++) {
			for(int c=0; c < cols; c++){
				int index = r*mcols +c;
				bignum b = bignum(dmatrix[index].i);
				if(b != cmatrix[index]){
					cout << "Error: " << r << " " << c << endl;
					assert(false);
				}

			}
		}
#endif


	}


};

#endif /* MATRIX_H_ */
