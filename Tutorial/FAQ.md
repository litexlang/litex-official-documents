# FAQ: Frequently Asked Questions

1. Why the following code does not work?

```
know forall x, y R: x * y = 0 => or(x = 0, y = 0)
let a,b R
know a*b=0
or(a=0,b=0)
```

Answer: The reason why it does not work, is related to how an `or` statement is executed.

When the Litex kernel reads `or(a=0,b=0)`, it will check if `a = 0` is true or not under the assumption that `b = 0` is not true. However, when we use `forall x, y R: x * y = 0 => or(x = 0, y = 0)` to check whether `a = 0` is true, it the kernel could not know what `y = b` just by reading `a = 0`.

To fix this, give a name to the known fact `forall x, y R: x * y = 0 => or(x = 0, y = 0)`.

Example 1:

```litex
know @product_zero_implies_or(x, y R):
    x * y = 0
    =>:
        or(x = 0, y = 0)
let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```

Example 2:

```litex
prop product_zero_implies_or(x, y R):
    x * y = 0
    <=>:
        or(x = 0, y = 0)
know forall x, y R: x * y = 0 => $product_zero_implies_or(x, y)

let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```

