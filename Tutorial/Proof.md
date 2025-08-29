# Proof

`prove` provides a sub-environment that does not affect the part out of its sub-environment. In this case, `x` in different Prove block works individually:

```litex
prove:
    let x N_pos:
        x = 1
    or:
        x = 1
        x = 2

prove:
    let x R:
        not x < 0
    x >= 0

let x N:
    x = 0
x = 0
```

Imagine you are writing a long proof, and you want to write scratches independent of the main proof just for helping yourself to think. You can use `prove` to write them.

> Note: In this case, if you make claim of `let x N` before all Prove block, Litex would report an Error. Because you claimed `x` in parent-environment first and sub-environment would be affected.

