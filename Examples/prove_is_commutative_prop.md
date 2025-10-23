```litex
prop p(x, y N)
know forall x, y N: not $p(x, y) <=> x = y

prove_is_commutative_prop(not $p(x, y)):
    prove:
        not $p(x, y)
        x = y
        y = x
        not $p(y, x)
    prove:
        not $p(y, x)
        y = x
        x = y
        not $p(x, y)

forall x, y N: not $p(x, y) <=> not $p(y, x)

prop q(x, y N)
know forall x, y N: $q(x, y) <=> x = y

prove_is_commutative_prop($q(x, y)):
    prove:
        $q(x, y)
        x = y
        y = x
        $q(y, x)
    prove:
        $q(y, x)
        y = x
        x = y
        $q(x, y)

forall x, y N: $q(x, y) <=> $q(y, x)
```
