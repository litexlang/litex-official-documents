"""litex
# definition of a group, and prove R and Z are groups
# 定义一个群，并证明 R 和 Z 是群

prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):
    forall x s, y s, z s:
        mul(mul(x, y), z) = mul(x, mul(y, z))
    forall x s:
        mul(x, inv(x)) = e
        mul(inv(x), x) = e
    forall x s:
        mul(x, e) = x
        mul(e, x) = x

# function negate is defined to be the negation of a real number, i.e. negate(x) = -x is always true. The existence of negation function is by common sense.
# The reason why The inverse (negation) operator, when applied to an integer argument, returns another integer. This follows directly from the definition of integers, so it is built into Litex.
# The proof cannot be carried out in ℕ because the following statement does not remain valid in the following line.
# The following statement is does not work: 
# forall x N: negate(x) = -x, -x $in N, negate(x) $in N
forall x Z: negate(x) = -x, -x $in Z, negate(x) $in Z

have fn inverse(x Z) Z = negate(x)

forall x Z:
    negate(x) = -x = inverse(x)
    x + inverse(x) = x + (-x) = 0
    inverse(x) $in Z

# The reason we don't write the inverse operator directly as -, but use negate instead, is that - would be interpreted as subtraction of two real numbers here.
$is_group(Z, +, inverse, 0)
"""