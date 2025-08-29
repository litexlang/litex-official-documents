# Example 1: Learn By Example

Examples are essential for effective learning. Run and write the following codes yourself! You can learn Litex simply by remembering the examples in the Tutorial, but if you only memorize the explanatory sentences without looking at the examples, you won’t really learn it.

## Situations where named forall statements are useful

```litex
know forall a, b, c R: a < b, b < c => a < c
let a, b, c R: a < b, b < c
# a < c # This does not work!
```

If you run `a < c`, you will get an unknown. This is because Litex uses `match and substitution` to use known facts to check if a new statement is true. In this case, we do not know which `b` is used by `forall a, b, c R: a < b, b < c => a < c` to prove `a < c`, so `a < c` still can not be proved.

So how do we express: It is known as axiom (definition of `<`) that for all `a`, `b`, `c` in `R`, if `a < b` and `b < c`, then `a < c`?

It turns out we can give a name to the forall statement by defining a new proposition.

```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c
    <=>:
        a < c

know forall a, b, c R: a < b, b < c => $transitivity_of_less(a, b, c)

let a, b, c R: a < b, b < c
$transitivity_of_less(a, b, c)
a < c
```

When `$transitivity_of_less(a, b, c)` is true, Litex automatically infers all facts that are logically equivalent to it.

In this example, `$transitivity_of_less(x, y, z)` states that `x < z` is equivalent to `x < y` and `y < z` being true. By substituting `x = a`, `y = b`, and `z = c`, we obtain `a < c`. Since Litex knows these two statements are equivalent, `a < c` is automatically established.
