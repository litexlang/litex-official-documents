```
have x R
prop p(a, b R)
know forall a R: $p(a, x)

prove:
    have x R
    $p(1, x) # This matches the outside know forall a R: $p(a, x), but this x is different from the outside x
```