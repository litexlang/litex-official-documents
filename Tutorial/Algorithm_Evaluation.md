# Algorithm And Evaluation

_Algorithms + Data Structures = Programs_

_- Niklaus Wirth_

Computation and proof are quite different. Proof involves transformations between symbols that are meaningless at the literal level (for example, `have little_bird R = 1`—when defining a new object here, I could call it `pinky_pig` or `grey_dog`, it doesn't matter; only the name used later changes). Computation transforms symbols that are meaningful at the literal level into new symbols that are meaningful at the literal level (for example, in `1 + 3`, the `1` and `3` are meaningful at the literal level; writing `2` instead of `1` would be completely different).

The computer revolution is primarily a revolution about computation. Even when we write variables (for example, in C we write `int x = 1;`), when the computer works, it reads the value stored at the address corresponding to `x`. (If we view address-value pairs as dictionary key-value pairs, then the computer only cares about the value, not the key; but mathematical proof sometimes considers the key—when matching and substituting in proofs, most mathematical objects don't have so-called numerical values—and sometimes considers the value—during evaluation and computation.)

Mathematics still involves quite a bit of evaluation and computation. For example, here we define a function `f(x)` that equals `x + 1` when `x > 0`, equals `0` when `x = 0`, and equals `x - 1` when `x < 0`.

```litex
fn f(x R) R
know:
    forall x R: x > 0 => f(x) = x + 1
    forall x R: x < 0 => f(x) = x - 1
    f(0) = 0

algo f(x):
    if x = 0:
        return 0
    if x > 0:
        # it's ok to write `x + 2` here. But when you eval f(1), it does not work. Because it is impossible to verify f(1) = 1 + 2, and the evaluation fails.
        return x + 1
    if x < 0:
        return x - 1

eval f(1) # Invoke condition if x > 0, verify whether return value 1 + 1 equals to f(1)
f(1) = 2

eval f(-1) # Invoke condition if x < 0, verify whether return value -1 + 1 equals to f(-1)
f(-1) = -2

eval f(0) # Invoke x = 0
f(0) = 0

have a R = 2
eval f(a) # replace a with its value 2, eval f(2)
f(a) = 3

eval f(f(a)) # replace f(a) with its value 3, eval f(3)
f(f(a)) = 4
```

*algo* defines an execution flow to compute `f`, while *eval* executes it.

In *eval funcName(params)*, `funcName` must be a function and must have a corresponding *algo* to execute it. `params` is a set of parameters, and what you pass in must have a clear numerical value (either a number, an expression composed of basic arithmetic operations on numbers, or a symbol that has already been explicitly known to equal a numerical value).

*algo* records how to compute a function. Unlike general programming languages, litex ensures that your return value in the current case is indeed equal to your function, and it must be able to prove this. For example, if you write `if x > 0: return x + 1` in your algo, that works because `forall x R: x > 0 => f(x) = x + 1`. But if you write `if x > 0: return x + 2`, then when executing `f(1)`, it will fail because it's impossible to prove `f(1) = 1 + 2`.

Sometimes you cannot directly prove that the return value equals your function. In such cases, you need to write some intermediate steps. For example:

```litex
prop p(x R):
    x > 2

fn f(x R) R
know:
    forall x R: $p(x) => f(x) = x - 2
    forall x R: not $p(x) => f(x) = 0

algo f(x):
    if x > 2:
        $p(x)
        return x - 2
    if x <= 2:
        claim:
            not $p(x) 
            prove_by_contradiction:
                $p(x)
                x > 2
                not x <= 2
        return 0

have a, b R = 3, -1

eval f(3)
f(3) = 1

eval f(-1)
f(-1) = 0
```

In the above example, when evaluating `f(3)`, we first need to prove `not $p(3)` by contradiction.

The following example demonstrates how to use recursion. This is important because many mathematical concepts are defined recursively. Even addition is defined this way.

```litex
fn f(x R) R
know:
    f(0) = 0
    forall n R: f(n) = f(n - 1) + 1

algo f(x):
    if x = 0:
        return 0
    if x > 0:
        return f(x - 1) + 1 
    if x < 0:
        f(x+1) = f(x+1-1) + 1 = f(x) + 1
        f(x) = f(x+1) - 1
        return f(x+1) - 1

have a, b R = 3, -1

eval f(-1)
f(-1) = -1

eval f(3)
f(3) = 3

```

Note: If you try to `eval f(1.5)` here, it will result in an infinite loop. This is because you can keep calling `f` indefinitely, but it will never terminate. The purpose of `algo` is to help you automatically write some evaluation steps, and an infinite loop is equivalent to the user continuously writing intermediate steps that are unrelated to the final result. Although these intermediate steps are correct, they don't actually serve a purpose. litex does not check whether your algorithm halts.