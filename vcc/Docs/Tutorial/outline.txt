- max:       requires/ensures: Function contracts
- sqrt:      invariant, overflows: Statement annotations
- lsearch:   arrays, quantification: Arrays
- swap:      writes(...): Framing
- partition: calls (call swap()): Calls
- SafeString: invariants: Object invariants
--- indexOf: wrapped(...)
--- replace: expose(...)
--- create(): wrap(); extent()
- hashtable from ints to strings with wrap-around: dynamic ownership
- dynamically allocated string: static ownership + array object
- a list: reachability relation in ghost state, abstraction
- make the hashtable real with the list: more abstraction?

- spin lock: atomic updates, volatiles
- rundown for 2-state invariants
- concurrent set: set is the abstraction

- storage allocator (from k&r): reinterpretation


- bv_lemma
- visible state: lock-protected hashtable

struct SafeString {
  unsigned len;
  char content[MAX];
  invariant(len < MAX)
}

struct SafeString {
  unsigned len;
  char *content;
  invariant(keeps(as_array(content, len)))
}

- stack:     object invariants
--- peek():       wrapped(...)
--- push()+pop(): expose(...) {}
--- create():     wrap(); extent()
- 
- generalized stack of void*: dynamic ownership, more quantification
- put the array outside of the stack
