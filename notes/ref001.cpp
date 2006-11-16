/* Illustrates that the scope of initialisor is covered by the
   declared variable, even for references.  In other words, this
   program won't return 101 (in fact it's actually undefined, and will
   possibly crash). */

int x = 101;

int f(int i)
{
  int &x = x;
  return x + i;
}

int main()
{
  return f(0);
}
