#include <iostream>
using namespace std;

template <int &i, int f(int)> struct ROI {
  static const int &value() { return i; }
  static int apply (int x) { return f(x); }
  static int init;
};

// note how this code causes arbitrary stuff to happen at
// initialisation, before main is entered.
template <int &i, int f(int)> int ROI<i,f>::init = f(i);

template <class T, int n> T tempfn(int m)
{
  T temp1(1), temp2(2);
  cout << "Doing a tempfn comparisonX" << endl;
  if (m < n) return temp1;
  else return temp2;
}

template <class T> struct Foo
{
  typename T::sub data;
  typename T::INT x;
  void inc() { data ++; }
  int myvalue() {
    typedef ROI<T::sub::stat, tempfn<int,0> > roi;
    return roi::apply(roi::value());
  }
};

struct Base {
  struct sub {
    int x;
    void operator++(int) { x++; }
    sub() : x(0) {}
    static int stat;
  };
  typedef int INT;
};

int Base::sub::stat = 1;

ostream &operator<<(ostream &os, const Base::sub &s)
{
  return os << s.x;
}

int main()
{
  Foo<Base> f;
  f.inc();
  cout << f.data << " " << f.myvalue() << endl;
  return 0;
}
