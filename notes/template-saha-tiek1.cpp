template <class T>
class A {
  static T f(int);
};

template <class T>
class B {
  static A<T*> g(int);
};

template <class T>
A<T *> B<T>::g(int n) { return A<T *>::f(n); }

