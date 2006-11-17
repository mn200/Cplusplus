/* Illustrates the gist of 12.6.2 p2: to construct the base class whose name
   is masked by the member with the same name, the mem-initialisor in the
   constructor for D has to use a qualified name to "reach" the class */

class B {
  int x;
public:
  B(int n) { x = n; }
};

class D : public B {
  int y;
  int B;
public:
  D(int n) : ::B(n), y(n + 1), B(n)  { }
};

int main()
{
  D d(4);
  return 0;
}

