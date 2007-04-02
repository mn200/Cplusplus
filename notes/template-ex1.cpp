template <class T> class TimesTwo {
public:
  T data1, data2;
  TimesTwo(T x) : data1(x), data2(x) {}
};

TimesTwo<int> i(3);

