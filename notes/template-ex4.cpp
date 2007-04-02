#include <iostream>
#include <string>
using namespace std;

struct foo {
  template <class T> int f(const T &x) { return x + data; }
  int data;
};

int main()
{
  foo v = {1};
  string s = "Hello, world\n";
  cout << v.f('c') << endl;
  // cout << v.f(s) << endl;  fails because there is no way of adding an
  //                          integer to a string, no string::operator+(int)
  //                          function
  return 0;
}
