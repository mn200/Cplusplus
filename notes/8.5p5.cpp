#include <cstdio>

struct B1 {
  int i;
  B1() { printf("B1\n"); i = 1; }
};

struct B2 {
  int j;
};

struct D1 : virtual public B2, public B1 {
  int k;
  D1() { printf("D1\n"); k = 3; }
};

struct D2 : virtual public B2 {
  int m;
};

class E : public D1, public D2 {
  int n;
};

class F : public E
{
  int p;
public:
  F() : E(), p(6) { printf("F\n"); }
};

