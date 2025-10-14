```litex
prop in_a_or_b(x, a, b set):
    or:
        x $in a
        x $in b

fn union(a, b set) set:
    forall x a => x $in union(a, b)
    forall x b => x $in union(a, b)
    forall x union(a, b) => $in_a_or_b(x, a, b)

have a, b set
forall x a => x $in union(a, b)
forall x b => x $in union(a, b)
forall x union(a, b) => $in_a_or_b(x, a, b), x $in a or x $in b
```
