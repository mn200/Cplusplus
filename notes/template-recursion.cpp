#include <iostream>
using namespace std;

template<class T> struct SUC {
  static int value() { return 1 + T::value(); }
};
struct ZERO {
  static int value() { return 0; }
};

typedef SUC<ZERO> ONE;
typedef SUC<ONE> TWO;
typedef SUC<TWO> THREE;

template <class T1, class T2> struct add { };

template <class T1, class T2> struct add<SUC<T1>, T2>
{
  static int value() { return SUC< add<T1,T2> >::value(); }
};

template <class T2> struct add<ZERO, T2>
{
  static int value() { return T2::value(); }
};

template <class T1, class T2> struct mult { };
template <class T1, class T2> struct mult<SUC<T1>, T2>
{
  static int value() { return add<T2, mult<T1,T2> >::value(); }
};

template <class T2> struct mult<ZERO, T2>
{
  static int value() { return 0; }
};

int main()
{
  cout << "Two: " << TWO::value() << endl;
  cout << "Two + Two: " << add<TWO,TWO>::value() << endl;
  cout << "Two * Three: " << mult<TWO,THREE>::value() << endl;
  cout << "Three * Two: " << mult<THREE,TWO>::value() << endl;
}
