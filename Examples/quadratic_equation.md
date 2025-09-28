```litex
claim:
    forall a, b, x R:
        x^2 + 2 * a * x + b = 0
        a^2 - b >= 0
        =>:
            or:
                x = -a + sqrt(a^2 - b)
                x = -a - sqrt(a^2 - b)
    prove:
        =:
            sqrt(a^2 - b) * sqrt(a^2 - b)
            sqrt(a^2 - b) ^ 2
            a^2 - b
        =:
            (x + a - sqrt(a^2 - b)) * (x + a + sqrt(a^2 - b))
            x ^ 2 + 2 * a * x + a^2 - sqrt(a^2 - b) ^ 2
            x ^ 2 + 2 * a * x + a^2 - (a^2 - b)
            x ^ 2 + 2 * a * x + b
            0
        $product_is_0_then_at_least_one_factor_is_0(x + a - sqrt(a^2 - b), x + a + sqrt(a^2 - b))
        
        prove_in_each_case:
            or:
                x + a + sqrt(a^2 - b) = 0
                x + a - sqrt(a^2 - b) = 0
            =>:
                or:
                	x = -a + sqrt(a^2 - b)
                    x = -a - sqrt(a^2 - b)
            prove:
                x + a + sqrt(a^2 - b) + (-a - sqrt(a^2 - b)) = 0 + (-a - sqrt(a^2 - b))
                x = 0 + (-a - sqrt(a^2 - b))
                x = -a - sqrt(a^2 - b) 
            prove:
                x + a - sqrt(a^2 - b) + (-a + sqrt(a^2 - b)) = 0 + (-a + sqrt(a^2 - b))
                x = 0 + (-a + sqrt(a^2 - b))
                x = -a + sqrt(a^2 - b)
```
