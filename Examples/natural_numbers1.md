```litex
# This file is translation of Lean4 code website https://leanprover-community.github.io/theories/naturals.html to Litex code.

4 + 1 + 1 = 6
4 - 3 =1
5 -6 != 0
1 != 0
4 * 7 = 28

forall m, n, p N:
    m + p = n + p
    =>:
        m + p - p = n + p - p
        # m = n

forall a, b, c N:
    a * (b + c) = a * b + a * c

# Basic facts like this will be implemented in standard library.
know @less_is_preserved_by_addition(m N, n N, p N):
    m + p < n + p
    =>:
        m < n

know:
    forall a, b, n N:
        n > 0
        a > b
        =>:
            a ^ n > b ^ n

forall a, b N:
    a + 1 < b + 1
    =>:
        $less_is_preserved_by_addition(a, b, 1)

forall a, b, n N:
    n > 0
    a > b
    =>:
        a ^ n > b ^ n

```
