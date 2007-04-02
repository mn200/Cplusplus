#include <iostream>
using namespace std;

// template template parameters don't have to have names

template <template <class, int> class U> struct X
{
  U<int,4> data;
};

template <class T, int N> struct Array
{
  T data[N];
};

int main()
{
  X<Array> foo;
  foo.data.data[0] = 3;
  cout << foo.data.data[0] << endl;
  return 0;
}
