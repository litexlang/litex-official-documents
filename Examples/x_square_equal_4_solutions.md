```litex
claim:
    forall x R: or(x = 2, x = -2) => x ^ 2 = 4
    prove:
        prove_in_each_case:
            or(x = 2, x = -2)
            =>:
                x ^ 2 = 4
            prove:
                2 ^ 2 = 4
            prove:
                -2 ^ 2 = 4

```
