template <class T> struct Foo { static int f(); };
template <class T> int Foo<T>::f() { return 3; }

template <class T> struct Bar { static int f(); };
template <class T> int Bar<T>::f() { return 4; }

template <template <class> class A> struct Baz { static int g(); };

template <template <class> class A>
int Baz<A>::g() {
  return A<int>::f();
}

int main() { return Baz<Foo>::g(); }
