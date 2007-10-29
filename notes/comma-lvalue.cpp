#include <iostream>
using namespace std;

int main()
{
  int x = 0, y = 1;
  (y++,x) = 3;
  cout << x << ", " << y << endl;  // prints 3, 2
  return 0;
}


