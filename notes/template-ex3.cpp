#include <iostream>
using namespace std;

/* illustrates that nested classes can themselves be templates */

template <class T> struct Foo {
  int x;
  T &data;
  Foo(T item) : x(0), data(item) { }
  template <class U> struct Bar {
    int y;
    U data;
    T ref;
  };
  Bar<T *> tptr;
};

int main()
{
  Foo<int> f(4);
  Foo<int>::Bar<char> b;
  b.y = b.ref = 3;
  b.data = 'c';
  cout << f.data << " " << b.ref << endl;
  return 0;
}


