# Function: The Glue of Symbols

_Function: a mathematical correspondence that assigns exactly one element of one set to each element of the same or another set_

_— Merriam-Webster Dictionary_

Functions are among the most fundamental concepts in mathematics.
Litex, as a **non-Turing-complete domain language** designed purely for reasoning, treats functions in a way that is quite different from programming languages like Python or C.

This gap becomes clear once we compare the concept of a *function* in reasoning (mathematics) with that in programming:

* In **programming languages** (e.g. Python, Lean), a function is a block of executable code that performs computation or side effects.
* In **mathematics**, a function is not executable code. Instead, it is a **symbolic constructor** that builds a new symbol from input symbols. You can think of it as *glue* that binds symbols together.

In both math and programming, the common feature is that functions use `()` to wrap inputs and produce new expressions. For example, `square_root(x)` in mathematics simply denotes a new symbol formed from `x`. No computation happens.

---

## Builtin Functions

`+`, `-`, `*`, `/`, `^`, `%`, are builtin functions. Their daily properties are already in the Litex kernel.

```litex
1 + 1 = 2
2 * (1 + 1) = 3 + 1
have x, y, z R
(x + 1) ^ 2 = x ^ 2 + 2 * x + 1
(x + y) * (x + z) = x ^ 2 + x * y + x * z + y * z
x + z = z + x
```

Besides builtin functions, Litex allows you to define your own functions.

---

## Defining a Function with an Existence Guarantee

In programming, defining a function only requires writing a block of code.
In mathematics, however, *declaring a new function must come with a proof of its existence*. Otherwise, the declaration is unsafe and could lead to contradictions.

Litex provides two ways to define functions.

---

### 1. Define a Function and Prove its Existence

When declaring a new object with existence guarantee, we use `have` keyword. When declaring a function with existence guarantee, we use `have fn` keyword.

Syntax:

```
have fn:
    function_name(x1 set1, x2 set2, ...) return_set:
        domain_fact1
        ...
        then:
            conclusion1
            ...
    prove:
        statement1
        ...
    have object_such_that_satisfy_all_conclusions_of_this_function_and_in_return_set
```

**Example:**

```litex
have fn:
    a(x R) R:
        x > 0
        =>:
            a(x) > 0
    prove:
        x > 0
    have x
```

Explanation:

* In the `prove` section, the parameters of the function (here `x`) are assumed to satisfy the domain condition (`x > 0`).
* We must then provide an object that lies in the return set and satisfies all the conclusions (`a(x) > 0`).
* If we define `a(x) = x`, then `a(x) > 0` holds whenever `x > 0`.
* Writing `have x` ensures the existence of such a function.

Thus, the function `a` is safely defined. Its existence is guaranteed by the `have` statement.

### 2. Define a Function by Equality

In daily math, when we want to define a function, we just write `g(x) = x` or `s(x) = x^2` or `q(x) = x^2 + 1` etc. In Litex, we can do the same thing in a more concise way.

```
have fn f(param1 set1, param2 set2, ...) return_set = expression
``` 

For example

```litex
have fn g(x R) R = x
have fn s(x R) R = x^2
have fn q(x R) R = x^2 + 1
```

They are equivalent to the following:

```litex
have fn:
    g(x R) R:
        g(x) = x
    prove:
        x = x
    have x

have fn:
    s(x R) R:
        s(x) = x^2
    prove:
        x^2 = x^2
    have x^2

have fn:
    q(x R) R:
        q(x) = x^2 + 1
    prove:
        x^2 + 1 = x^2 + 1
    have x^2 + 1
```

### Conclusion

As usual, `have` keyword is used to declare a new object with ensuring its existence. Ensuring the existence of a function is not a trivial task, so we need to prove it.

---

### 2. Define a Function without Existence Proof

Sometimes we simply want to introduce a function symbol with certain properties, without proving existence.
For example, the square root function:

```litex
fn square_root(x R) R:
    dom:
        x >= 0
    =>:
        square_root(x) * square_root(x) = x
```

⚠️ **Note:** This style of definition does not guarantee that such a function exists. For safety, Litex will later support `set_defined_by_replacement`, which ensures existence.

Here:

* `fn` introduces a new function.
* `square_root` is its name.
* `(x R)` specifies the parameter `x` belongs to `R`.
* The last `R` specifies the *range* of the function.
* `dom` specifies domain restrictions (`x >= 0`).
* The `=>` section states the properties the function satisfies.

So, `square_root(-1)` is invalid, since `-1` does not satisfy the domain.

When writing `fn` to declare a function, fact about that function are known without verification:

```
forall param1 paramSet1, ..., paramN paramSetN:
    ...
    =>:
        ...
```

for example, the following fact is known after you define function `square_root`

```
forall x R:
    x >= 0
    =>:
        square_root(x) $in R
        square_root(x) * square_root(x) = x
```

Note: You can refer to the function itself in domain fact. For example, you should not do this:

```
fn f(x R) R:
    f(x) > 0
    =>:
        ...
```

---

## Compact Styles of Function Definition

Litex encourages short, clean definitions. For example, we can omit `dom` explicitly:

```litex
fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x
```

Or even inline:

```litex
fn square_root(x R) R: x >= 0 => square_root(x) * square_root(x) = x
```

Other shorthand examples:

```litex
fn f(x R) R
fn f2(x R) R: x > 0
fn f3(x R) R => f3(x) > 0
fn f4(x R) R: x > 0 => f4(x) > 0
```

Equivalent to the expanded forms:

```litex
fn f(x R) R
fn f2(x R) R:
    dom:
        x > 0
fn f3(x R) R:
    f3(x) > 0
fn f4(x R) R:
    x > 0
    =>:
        f4(x) > 0
```

---

## Calling a Function

Function calls in Litex look exactly like in mathematics:

```litex
fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x

square_root(4) $in R
```

⚠️ Important: Litex **does not compute**.
`square_root(4)` does **not** equal `2`. Instead, it denotes "some value in `R` such that `square_root(x)^2 = x` when `x = 4`." The actual value is irrelevant; only the existence matters.

You should not pass parameters which do not satisfy the domain of the function. For example

```litex
have cartoon_characters nonempty_set, oddie_bird, carmela_bird cartoon_characters
fn fuse_characters(x, y cartoon_characters) cartoon_characters

# You can not add two cartoon characters, because + takes real numbers as parameters.
# oddie_bird + carmela_bird = oddie_bird + carmela_bird

fuse_characters(oddie_bird, carmela_bird) $in cartoon_characters
```

You can not write `oddie_bird + carmela_bird`, because `+` takes real numbers as parameters. You can call `fuse_characters(oddie_bird, carmela_bird)` to get a new cartoon character because it is defined as a function that takes cartoon characters as parameters.

## Parameters must satisfy domain fact of function

```litex
fn f(x R) R:
    x > 0
    =>:
        f(x) > 0

f(-1) > 0
```

You can not write `f(-1)`, because `-1` does not satisfy the domain fact `x > 0`. If you run the above code, it will output an error like this:

```
failed to check param(s) (-1 * 1) satisfy domain of
fn (x R) R:
    dom
        x > 0
    =>
        f(x) > 0
```

---

## Function Templates and `let`

Functions are also objects. Thus, with `let`, we can declare functions from templates.

```litex
# function template
fn_template finite_sequence(s set, max N):
    fn (n N) R:
        dom:
            n < max

let n N

# declare a function from the template
let fs1 finite_sequence(R, 10):
    fs1(n) = n * n
```

This is shorthand for:

```litex
fn_template finite_sequence(s set, max N):
    fn (n N) R:
        dom:
            n < max

let fs1 finite_sequence(R, 10):

know forall n N => fs1(n) = n * n
```

---

✨ In short:

* In **programming**, a function executes.
* In **Litex**, a function is a **symbolic constructor**, a piece of glue that builds new symbols from old ones.
* To define functions safely, one must ensure existence, either by proof or by replacement.
