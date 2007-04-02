#include <iostream>
#include <string>
using namespace std;

// first, a demonstration that classes (only) can be partially specialised.

template <class T, int N> struct foo {
  T data;
  int value() { return data.size(); }
  int bar() { return N; }
};

// this next would be an error because there is no "type" foo<int, N>
// in which the member function could live.  Contrast this with the
// overriding definition below of foo<short,0>::value.

// template <int N> int foo<int, N>::bar() { return 3; }


// without this, main below is in error, because there is an attempt to call
// a size member function on an int
template <int N> struct foo<int, N> {
  int data;
  int value() { return data; }
  int qux() { return 102; }
};


// demonstrates that template specialisations can be provided at the member
// function level.  (See 14.5.4.3)  This also implicitly instantiates the
// more general template, providing the explicit class with a definition of
// bar too.

template <> int foo<short, 0>::value() { return data + 1; }

// could go on to override other known to exist fields
// template <> int foo<short,0>::bar() { return 101; }

// but this fails, because qux doesn't live in the general template
// template <> int foo<short,0>::qux() { return 3; }

template <> struct foo<string,0> {
  int x;
  int value();
};

// must leave out the template<> here
// template<>
int foo<string,0>::value() { return x; }

int main()
{
  foo<int,4> f = {3};
  foo<short,0> g = {4};
  foo<string,0> h = {5};
  cout << f.value() << endl;
  // if the line below is uncommented it's an error, as the parameterised
  // template type foo<int, N> can't use the more general struct's definition
  // of bar
  // cout << f.bar() << endl;

  // but the following works:
  cout << g.bar() << " " << g.value() << endl;

  // complete specialisation where the class is given works slightly
  // differently.
  cout << h.value() << endl;
  return 0;
}
