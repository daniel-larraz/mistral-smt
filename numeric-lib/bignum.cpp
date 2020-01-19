#include "bignum.h"
#include <stdlib.h>


ostream& operator <<(ostream &os,const bignum &_obj)
{
	bignum & obj = (bignum&) _obj;
      if(!obj.is_infinite())
      	os<<obj.data.d;
      else{
	char *str;
	str = mpz_get_str(NULL, 10, obj.data.i);
	 os<<str;
	 free(str);
	}
      return os;
}


