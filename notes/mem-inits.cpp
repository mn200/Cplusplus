#include <cstring>

class B {
  int x;
public:
  B(int i) : x(i) {}
};

class C : public B {
  char *ptr;
  int sz;
public:
  C(char *cptr, int i)
    : B(ptr[i]), ptr(cptr), sz(strlen(ptr)) { }
};
