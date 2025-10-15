```litex
claim:
    forall s, s2 set:
        s := {x Z: 1 <= x, x < 10, x % 2 = 0}
        s2 := {2, 4, 6, 8}
        =>:
            s = s2
    prove:
        prove_by_enum(x s2):
            x $in s
        prove_in_range(1, 10, x s):
            x $in s2

```
