#include <cstdio>

class B {
public:
  int b;
};

class D1 : virtual public B {
public:
  int x;
};

class D2 : virtual public B {
public:
  int y;
};

class D3 : virtual public B {
public:
  int z;
};

class E : public D1, public D2, public D3 {
public:
  int e;
};

void print_layout(unsigned char *p, unsigned sz)
{
  for (unsigned i = 0; i < sz; i++)
    printf("%2d (%p): %02x\n", i, p + i, p[i]);
}

void D2print(class D2 &d)
{
  printf("Sizeof D2: %d\n", sizeof(d));
  print_layout((unsigned char *)(&d), sizeof(d));
  printf("d.y: %d\n", d.y);
  printf("d.b: %d (at address %p)\n", d.b, &d.b);
}

int main(void)
{
  E e;
  e.e = 9;
  e.b = 4;
  e.x = 1;
  e.y = 2;
  e.z = 3;
  printf("*** An E\n");
  print_layout((unsigned char *)(&e), sizeof(e));
  D2print(e);
  D1 d;
  d.x = 1;
  d.b = 7;
  printf("*** A D1\n");
  print_layout((unsigned char *)(&d), sizeof(d));
  return 0;
}

