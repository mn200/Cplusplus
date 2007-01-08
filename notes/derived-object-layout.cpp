#include <cstddef>
class B1 { public: int bfld; } ;

class B2 { int x; } ;

class V { int y; } ;

class D1 : public B1, public B2, virtual public V { int d; } ;

class F : public D1 { int f; } ;

// I think we can calculate an approximation of the offset of B1 within
// D1 with the following:

ptrdiff_t b1_off(const D1 &d)
{
  const char *cptr1 = (const char *)&d;
  const char *cptr2 = (const char *)&d.bfld;
  return cptr2 - cptr1;
}

// If I then have

bool test()
{
  F fobj;  D1 dobj;
  return (b1_off(fobj) == b1_off(dobj));
}

int main()
{
  return test();
}
