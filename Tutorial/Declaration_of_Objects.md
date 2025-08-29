# Declaration of Objects: The Nouns of Logic

Modern mathematics is built on set theory. In Litex, to stay consistent with this foundation, whenever you declare a new object, you must also specify the set it belongs to.

```litex
have a N, b Q, c R
let e N, f Q, g R
```

There are two main ways to declare an object:

1. **`have`** – the *safe* way. The set must be non-empty (i.e., `$exist_in(setName)` must be true, such as `$exist_in(R)`), or the set must be explicitly declared as a `set` or `nonempty_set`.

   > Note: `set $in set` is **not** true in Litex, as this would violate the rules of set theory.

2. **`let`** – the *unsafe* way. The set which the object belongs to might be empty, and you can even attach arbitrary properties to the object.

## The Power (and Danger) of `let`

The simplest usage is to assign a known property:

```litex
let a N: a = 2
```

But `let` can also bind *contradictory* or unsafe properties:

```litex
let a N: a = 2, a = 3
```

What? `a` is both 2 and 3? Yes. In Litex, `let` is intentionally powerful and allows you to bind **any** properties to an object.

Why such freedom? Because when defining **axioms** and making **assumptions**, this flexibility is essential.

For example, the existence of the empty set is itself an axiom:

```litex
let self_defined_empty_set set: forall x obj => not x $in self_defined_empty_set
```

## Declaring Objects with `let`

In mathematics, anything can be treated as an *object*. To use an object in Litex, you must declare it first.

```
let object_name set_name
```

Example:

```litex
let n N
```

Here `n` is an object in the natural numbers `N`.

* Objects must be declared before use.
* Object names must be unique. You cannot `let a N` twice.

You can declare multiple objects at once:

```litex
let n N, m N
```

This is equivalent to:

```litex
let n N
let m N
```

### Syntactic Sugar for Shared Sets

If multiple objects belong to the same set, you can group them:

```litex
let n, m N
```

This also works with other keywords like `fn`, `forall`, and `prop`.

You can also mix sets in one line:

```litex
let n, m N, z Z
```

Or even declare an object inside a set you just defined:

```litex
let s set, n s
```

> Note: The order matters — `s` must be declared before `n`, otherwise Litex won’t know what `s` is.

## Adding Restrictions at Declaration

You can attach facts directly when declaring objects.

Example: two natural numbers `n` and `m` with conditions `n > 0` and `m > n`:

```litex
let n, m N:
    n > 0
    m > n
```

Or declare a system of equations:

```litex
let x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
```

## Declaring with `have`

While `let` assumes nothing, `have` requires proof that the object’s set is **non-empty**.

### Declaring Non-Empty Sets

You can define a non-empty set by enumerating its elements:

```litex
have set s1 := {1, 2, 3}
```

Or by restricting an existing domain:

```litex
have set s2 := n N:
    n > 0
    n < 4
```

Here `s1` is explicitly finite, while `s2` is defined by conditions. They are different, even though both happen to describe `{1, 2, 3}`.

### Declaring Objects from Existential Propositions

If you’ve proven an existential proposition, you can declare an object satisfying it:

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y

know forall y N_pos => $larger_than(y)

let m N_pos

have x st $larger_than(m)

x $in R
x > m
```

Here, `x` is guaranteed to exist because `$larger_than(m)` has been proven.

### Declaring Objects in Built-In Sets

```litex
have n N, z Z, q Q, r R, c C
```

You can also declare objects in custom sets, provided you prove the set is non-empty:

```litex
let s set
know $exist_in(s)

have n s
```

`exist_in` is a built-in existential proposition. In fact:

```
have n s
```

is equivalent to:

```
have n st $exist_in(s)
```

## The Difference Between `let` and `have`

Although both declare objects, they differ in a fundamental way:

* **`have`**: the object’s existence is guaranteed. Litex checks that the set is non-empty.
* **`let`**: no existence check is performed. You can declare anything — even contradictory objects — which is useful for assumptions and axioms.

In short:

* Use **`have`** when you want *safe, guaranteed existence*.
* Use **`let`** when you need *freedom*, even at the cost of safety.

### Declaration of finite sets

