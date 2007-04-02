template <class T, int I> struct A {
  void f();
};

template <class T, int I> void A<T,I>::f() { }

template <class T> struct A<T,2> {
  void f();
  void g();
  void h();
};

template <class T> void A<T,2>::g() { }

template <> void A<char,2>::h() { }

int main()
{
  A<char,0> a0;
  A<char,2> a2;
  a0.f();
  a2.g();
  a2.h();
  a2.f();
  return 0;
}
