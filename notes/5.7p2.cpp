#include <iostream>

int main()
{
  // can subtract pointers regardless of cv-qualifications
  int array[10];
  int *ptr1 = array;
  const int *ptr2 = array + 1;
  int * const ptr3 = array + 2;
  std::cout << (ptr3 - ptr1) << ", " << (ptr2 - ptr1) << "\n";
  return 0;
}


