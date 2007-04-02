/* gcc says the following is an error.  It's not 100% clear to me where the
   standard requires this. */

template <class T> class Foo {
public:
  T data;
  template <class T> int f (T x) { return x.size(); }
};

