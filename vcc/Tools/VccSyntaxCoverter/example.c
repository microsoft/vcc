int foo(int x spec(int y))
  requires(x > y)
  requires(x > 0 &&
           y >= x)
  ensures(result >= x)
  writes(&someglobal)
{
  spec(int aa, bb;)
  speconly(
    aa = 10; // some interesting comment
    bb = 20;
  )
  x = 10;
  speconly(aa = 7;) // something here as well
  expose(&something) {
    x++;
  }
  assert(forall(int x; unsigned y; x > y; x + y > z));
  assert(forall(int x; x > 0));
  assert(forall(int x; x > 0) && forall(int x; x > 0));
}
