/* The const int i; declaration is an error (8.5 p9).  The declaration
   of d1 and d2 give those objects indeterminate values.  The
   declaration of c is fine because there is a visible user-defined
   default constructor.  An implicit constructor is not good enough.
*/

class C {
public:
  int x;
  C() { x = 2; }
};

struct D { int x,y; };

D d1, d2;

const C c;

const int i;

int main()
{
  return 0;
}
