struct C {
  static int x;
  struct N {
    int y;
    int f() { return x + y; }
  };
};

int C::x = 2;

int main()
{
  C::N n;
  // this is in error, because x is not a member of C::N
  n.y = C::N::x;
  return n.y;
}
