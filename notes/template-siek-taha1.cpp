// the action of S&T's instantiation relation would instantiate A on an
// argument of shape T* when the member function definition was encountered.

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

int main()
{
  return 3;
}
