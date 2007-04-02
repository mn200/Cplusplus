#include <iostream>

template <int n, int m = n> struct sum
{
  static int value() { return n + m; };
};

struct bar {
  int fld1;
  int fld2;
  bar() : fld1(3), fld2(4) { }
};

struct baz {
  int fld1;
};

template <class T, int T::* p = &T::fld1>
struct foo {
  int value() { T *q = new T; return q->*p; }
};



int main()
{
  std::cout << sum<3>::value() << std::endl;
  std::cout << sum<3,4>::value() << std::endl;
  foo<bar> x;
  foo<bar, &bar::fld2> y;
  std::cout << x.value() << ", " << y.value() << std::endl;
  return 0;
}
