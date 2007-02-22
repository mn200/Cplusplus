#include <iostream>

class A {
public:
  int x,y;
};

template <int A::*ptr> class Foo {
public:
  Foo(const A &a) : item(a.*ptr) { };
  const int &item;
};

template <class T> class Bar {
public:
  T x;
};

template <class T> class Bar<T *> {
public:
  T x;
  Bar() { x = 0; }
};


int main()
{
  A a = {3,4};
  Bar<int> b = {3};
  Foo<&A::y> f(a);
  std::cout << f.item << std::endl;
  return 0;
}


