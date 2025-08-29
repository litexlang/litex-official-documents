# In

`in` is a built-in proposition in Litex. It is used when you want to claim an object is in a set. Since `in` facts are everywhere, Litex allows you to omit it in most cases. For example:

```litex
let n N
n $in N
```

`let n N` here has two effects:

1. Declare an object in current environment (context). For example, object `n` now exists in current environment. You can use it later.

2. Assume `n` is in set `N`. It has the same effect as `know n $in N`.

```litex
forall x N:
    x $in N
```

`x N` in `forall x N` is the same as `x $in N`.

```litex
fn f(x N) N
```

`x N` in `fn f(x N) N` means the parameter `x` that is passed to `f` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

```litex
prop p(x N)
```

`x N` in `prop p(x N)` means the parameter `x` that is passed to `p` is must satisfy `x $in N`, i.e. The domain of the first parameter `x` is subset of `N`.

As you can see, `in` is everywhere, in explicit and implicit ways.