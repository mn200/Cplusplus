template <class T> struct Foo {
  static int sdata;
  T cdata;
  int somefunction();
  Foo(T n) : cdata(n) {}
};

template <class T> struct Foo<T *> {
  int somefunction();
  int myint;
  Foo() : myint(101) { }
};

int main()
{
  Foo<int> f(3);
  Foo<int *> g;
  return f.somefunction() + g.somefunction();
}

template <class T> int Foo<T>::sdata = 4;

template <class T> int Foo<T *>::somefunction()
{
  return myint;
}

template <class T> int Foo<T>::somefunction() { return cdata + sdata; }
