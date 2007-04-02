#include <iostream>
using namespace std;

template <class T>
class Test {
  T sample;
public:
  static T add(const T &t1, const T&t2) { return t1 + t2; }
  static T identity(const T&t) { return t; }
};

struct foo { int x, y; };

int main()
{
  foo f = {1,2};
  foo g = Test<foo>::identity(f);
  int x = Test<int>::add(1,2);
  cout << g.y << " " << x << endl;
  return 0;
}
