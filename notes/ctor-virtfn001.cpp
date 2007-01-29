#include <cstdio>

class B {
public:
  int x;
  virtual int f() { printf("In B::f\n"); return 3; }
  B() {
    printf("Entering B's constructor\n");
    x = f();
    printf("Leaving B's constructor\n");
  }
};

class D : public B {
public:
  int f() { printf("In D::f\n"); return 4; }
  D() {}
};

int main()
{
  D d;
  B *b = &d;
  printf("d.x = %d, result of b->f() = %d\n", d.x, b->f());
  return 0;
}

