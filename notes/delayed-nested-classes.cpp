struct C {
  int x;
  struct D;
  struct D *p;
  int f();
};

struct C::D {
  int y;
  D() { y = 3; }
};

struct C f(int i)
{
  C c = {i,0};
  return c;
}

int C::f() {
  D d;
  return d.y;
}



