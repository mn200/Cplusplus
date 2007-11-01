// This program compiles because the use of the class X name in the
// struct puts the name X into the top-level namespace, making it
// valid inside the definition of F (though X remains an incomplete
// type the whole time).

// My model's name resolution doesn't handle this correctly.

 struct A
 {
   class X* px;
   // putting
   // class X { int x; };
   // here leads to undefined behaviour because the px declaration really should be to
   // an X outside the class, and declaring it inside messes that up.

   // Evidence: switching the order of the two declarations gives
   // different g++ behaviours.
 };

 void F(X*)
 {
 }

 int main()
 {
 }
