#include <vcc.h>

/*{begin}*/
_(datatype List {
    case nil();
    case cons(int v, List l);
})
/*{app}*/
_(def List app(List x, List y) {
  switch(x) {
    case nil(): return y;
    case cons(v,l): return cons(v, app(l,y));
  }
})
/*{appAssoc}*/
_(def void appAssoc(List x, List y, List z) 
_(ensures app(x,app(y,z)) == app(app(x,y),z))
{	
  switch (x) {
    case nil(): return;
    case cons(v,l): appAssoc(l,y,z); return;
  }
})
/*{rev}*/
_(def List rev(List x) {
  switch(x) {
    case nil(): return nil();
    case cons(v,l): return app(rev(l),cons(v,nil()));
  }
})

_(def void appNil(List x)
_(ensures app(x,nil()) == x)
{
  switch (x) {
    case nil(): return;
    case cons(v,l): appNil(l); return;
  }
})

_(def void revApp(List x, List y)
_(ensures rev(app(x,y)) == app(rev(y),rev(x)))
{
  switch (x) {
    case nil(): appNil(rev(y)); return;
    case cons(v,l): 
      revApp(l,y);
      appAssoc(rev(y),rev(l),cons(v,nil()));
      return;
  }
})

_(def void revRev(List x) 
_(ensures rev(rev(x)) == x) 
{
  switch(x) {
    case nil(): return;
    case cons(v,l): 
      revRev(l);
      revApp(rev(l),cons(v,nil()));
      return;
  }
})
/*{end}*/
/*`
Verification of app succeeded.
Verification of appAssoc succeeded.
Verification of rev succeeded.
Verification of appNil succeeded.
Verification of revApp succeeded.
Verification of revRev succeeded.
`*/
