#include <iostream>

class B {
public:
  virtual int f() { std::cout << "B's f\n"; return 3; }
  virtual ~B() { }
};

class C1 : virtual public B {
};

class C2 : virtual public B {
public:
  virtual int f() { std::cout << "C2's f\n"; return 4; }
};

class D : public C1, public C2 {
};

int dosomething(C1 &cref)
{
  return cref.f();
}

int main()
{
  D d;
  return dosomething(d);
}

