#include <iostream>
#include <vector>

using namespace std;

// ancestors, and hence mem-initialisors can involve template calls

template <class T>
class List : public vector<T>
{
public:
  List() : vector<T>(100) {
    this->at(0) = T(1);
  }
};

int main()
{
  List<int> l;
  cout << l[0] << endl;
  return 0;
}


