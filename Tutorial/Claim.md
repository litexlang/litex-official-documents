## Claim: Organize Your Proof into Sub-Proofs

_There is nothing without a reason._

_— Leibniz_

Math is hard. It is important to organize your proof well. The best way to do so is to divide a long proof into a series of independent sub-proofs and then combine them together. We call it `divide and conquer`, which is also a common strategy in many other tasks like building a house, writing code, etc. In such case, `claim` keyword can help you.

## Use of `claim`

```
claim:
    fact_you_want_to_prove
    prove:
        ....
```

`fact_you_want_to_prove` can be a specific fact or a universal fact.

For example

``` litex
exist_prop x N st exist_natural_number_larger_than(y N):
    x > y

claim:
    $exist_natural_number_larger_than(1)
    prove:
        let x N: x = 2
        2 > 1
        x > 1
        exist x st $exist_natural_number_larger_than(1)
        $exist_natural_number_larger_than(1)

$exist_natural_number_larger_than(1) # true, because $exist_natural_number_larger_than(1) is proved in the claim statement
# x = 2 is not visible out of the prove block, because x is declared in the prove block locally
```

When proving a specific fact, you can use `prove` block to prove it. After all statements in `prove` block are executed, Litex will check if `fact_you_want_to_prove` is true.

You can also claim a universal fact. This is exactly how mathematicians keep their proofs clean.

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)

claim:
    forall x R: $g(x) => $q(x)
    prove:
        $s(x)
        $q(x)
```

The `claim forall` construct works as follows:

* It creates a **new local proof environment**.
* In this environment, the domain assumptions are set to `true` by default.
* All statements inside the block are then executed.
* Once the `prove` block finishes, Litex checks whether the conclusion of the universal statement has indeed been derived.

  * If yes, the proof is complete.
  * If not, Litex reports an error.
* Afterward, the universal fact is added to the **global environment**, while the intermediate steps inside the `prove` block do **not** affect the global state.

*This mirrors the real process of solving a math problem: you are given a set of objects and assumptions, and your task is to prove a conclusion. In Litex, this is formalized exactly as a `claim forall` statement.*

You can use `claim` to make something affect part out of the Prove sub-environment:

```litex
claim:
    @p(x N):
        x > 1
        =>:
            x > -1
    prove:
        $larger_is_transitive(x, 1, -1)
        x > -1

let a N:
    a > 1
$p(a)
a > -1
```

`larger_is_transitive(x, y, z R)` is a built-in Proposition of Litex that means: x, y, z in R, x > y and y > z <=> x > z. You claimed a Proposition `p(x N)` in Claim block and prove it in Prove block. But you can still use it out of the sub-environment.

## Claim without purpose

When you just want ot write a piece of scratch without affecting the global environment, you can use `claim` without a purpose.

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

## Inline Claim

Multiline claim takes up much space, here is a short one:

```
claim fact:
    prove statement
    ...
```

```
claim fact prove_by_contradiction:
    prove statement
    ...
```

For example:

```litex
let x R: x = 11

claim x = 11:
    x = 11

claim forall y: x = y => y = 11:
    y = 11

claim x = 11 prove_by_contradiction:
    x = 11
```

This will make code much shorter and cleaner.