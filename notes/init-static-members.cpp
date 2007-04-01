#include <iostream>
using namespace std;

struct s { 
  // this is illegal (no obvious reason why the standard should make it so)
  static int fld = 0;
  int nonstatic;
};

struct t {
  static int fld ;
  int nonstatic;
};
int t::fld = 1;

struct u { 
  // but this is legal 
  static const int fld = 0;
  int nonstatic;
};

struct v {
  static const int fld;
  int nonstatic;
};

const int v::fld = 3;


int main() 
{
  cout << s::fld << " " << t::fld << " " << u::fld << " " << v::fld << endl;
  return 0;
}
