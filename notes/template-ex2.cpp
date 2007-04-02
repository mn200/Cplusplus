#include <iostream>
using namespace std;

/* demonstrates how template parameters affect qualified names.  Basically,
   only the "top" name in a chain of qualifiers is susceptible to replacement.
*/

namespace T {
  struct U { U(int n) { cout << "In T::U" << endl; } };
}

template <class T, class U> struct Foo : public T::U {
  int x;
  U my_u;
  Foo(int n) : T::U(n), x(n + 1), my_u(n + 2)  {}
};

struct bar {
  int y;
  bar(int x) : y(x) {}
};

struct baz {
  struct U {
    int z;
    U(int i) : z(i) {}
  };
  int w;
};

int main()
{
  Foo<baz,bar> x(4);
  cout << x.x << ", " << x.z << endl;
  return 0;
}
