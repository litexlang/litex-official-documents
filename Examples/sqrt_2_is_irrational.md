```litex
# prove sqrt(2) is irrational
# 证明 sqrt(2) 是无理数

fn logBase(x, y N) N:
    dom:
        x != 0

know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)

know forall x N: x != 0 => logBase(x, x) = 1

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        sqrt(2) > 0
        have x, y st $rational_positive_number_representation_in_fraction(sqrt(2))
        
        x = sqrt(2) * y
        x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)
        sqrt(2) ^ 2 = 2
        x ^ 2 = 2 * (y ^ 2)

        logBase(2, x ^ 2) = logBase(2, 2 * (y ^ 2))     
        logBase(2, x ^ 2) = 2 * logBase(2, x)
        logBase(2, y ^ 2) = 2 * logBase(2, y)

        logBase(2, 2 * (y ^ 2)) = logBase(2, 2) + logBase(2, y ^ 2)
        logBase(2, 2) = 1
        logBase(2, 2 * (y ^ 2)) = 1 + logBase(2, y ^ 2)

        logBase(2, x ^ 2) = 1 + 2 * logBase(2, y)
        2 * logBase(2, x) = 1 + 2 * logBase(2, y)

        =:
            0
            (2 * logBase(2, x)) % 2            
            (1 + 2 * logBase(2, y)) % 2
            
        =:
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 2 * logBase(2, y)) % 2
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 0) % 2
            1
        0 = 1
```
