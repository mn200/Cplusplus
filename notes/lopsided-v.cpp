#include <iostream>

class B {
public:
  virtual void f() { std::cout << "B's f\n"; }
  virtual ~B() { }
};

class Left1 : public B { };

class Left2 : public Left1 {
public:
  virtual void f() { std::cout << "Left2's f\n";  }
};

class Right {
public:
  virtual void f() { std::cout << "Right's f\n"; }
  virtual ~Right() { }
};

class D : public Left2, public Right { };

void dosomething(Left1 &l1ref) { l1ref.f(); }

int main()
{
  D d;
  // d.f();  would be statically ambiguous
  dosomething(d);
  return 0;
}

