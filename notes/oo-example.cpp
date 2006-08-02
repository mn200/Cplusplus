class B {
public:
  virtual int f() { return 3; }
};

   class D1 : public B {
   public:
     int f() { return 4; }
   };

   class D2 : public D1 { };

   int g(class B *b)
   {
     return b->f();
   }

   int main()
   {
     D2 d;
     return g(&d);
   }
