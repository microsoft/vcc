#include <vcc.h>

int min(int a, int b)
{
  int res;
  _(assume \true)
  res = a < b ? a : b;
  _(assert res <= a && res <= b)
}

#define LIMIT 1000
int main()
{
  int position = 0, newPos;
  // ...
  _(assert \true)
  position = min(newPos, LIMIT);
  _(assume position <= newPos && position <= LIMIT)
  _(assert position <= LIMIT)
  // ...
  return 0;
}

/*`
Verification of min succeeded.
Verification of main succeeded.
`*/
