# prove_algo and by

_Computer science is a science of abstraction. ... An algorithm is a precise and unambiguous specification of a sequence of steps that can be carried out mechanically._

_— Foundations of Computer Science, by Alfred V.Aho and Jeffrey D. Ullman_

`prove_algo` is a keyword to define a piece of logic that can be used to prove a proposition. This is similar to `algo` in general programming languages, but it is used to prove propositions instead of computing values.

Many mathematical proofs follow similar patterns. If two proof segments differ only in the objects involved while the predicates (props) and steps are identical, there is no need to write them repeatedly—you can give that proof process a name and invoke it with the `by` keyword.

```litex
prove_algo solve_linear_equation(a, b, c, d, e, f, x ,y):
    # check if the equation is solvable, condition of the algorithm
    a * e - b * d != 0
    a * x + b * y = c
    d * x + e * y = f

    # solve for y
    d * (a * x + b * y) = d * a * x + d * b * y = d * c
    a * (d * x + e * y) = d * a * x + a * e * y = a * f
    d * c - a * f = d * a * x + d * b * y - (d * a * x + a * e * y) = (d * b - a * e) * y
    y = (d * c - a * f) / (d * b - a * e)
    
    # solve for x
    e * (a * x + b * y) = e * a * x + e * b * y = e * c
    b * (d * x + e * y) = b * d * x + b * e * y = b * f
    e * c - b * f = e * a * x + e * b * y - (b * d * x + b * e * y) = (e * a - b * d) * x
    x = (e * c - b * f) / (e * a - b * d)

    return

let x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14

by solve_linear_equation(2, 3, 10, 4, 5, 14, x, y):
    x = -4
    y = 6
```

This proof process effectively substitutes the objects referenced in `by` into the `prove_algo`, instantiates that `prove_algo`, runs the entire proof procedure, and then emits the results established inside back to the location where `by` was called.

Any proof pattern can be abstracted into a `prove_algo`, and then be called by `by` to prove a proposition.

Another example:

```litex
prop p(x R):
    x = 1

prove_algo A(x):
    if x = 1:
        $p(x)
        return
    if x != 1:
        claim:
            not $p(x)
            prove_by_contradiction:
                $p(x)
                x = 1
        return

have x R = 3
by A(x): # open a local environment with x = 3, emit only x = 3 to the current environment
    not $p(x)

have a R = 1
by A(a) # run everything in current environment, no local environment is opened

by A(2+2): not $p(4) # you can also write it inline like this
```

In this example, you can use `by A(x)` to prove `not $p(x)`, and you can also use `by A(2+2)` to prove `not $p(4)` because both invoke the proof process `A(x)`.


## Syntax

The syntax is:

Case 1: When you write the result derived by `by` after the colon, `by` opens a local environment to call the `prove_algo`, copies all of that proof’s steps to the spot where `by` appears, and running the `prove_algo` leaves the outer environment untouched. Once the expression after the colon is proven, it’s released into the current environment

Case 2: When `by` is not followed by a colon, the call works mechanically—substitute the arguments into the `prove_algo`, instantiate it, and copy every instantiated proof step to the location where `by` was invoked.

Note: This allows users to recursively generate code. Because humans can write infinite proof processes that are meaningless to the final result, litex's `by` keyword may also recursively call itself indefinitely, causing an infinite loop.

## A Very Interesting Example

It's possible to define lisp-like data structure in Litex. Thank Chenxuan Huang for the example.

```litex
have U nonempty_set
have nil U
fn l(p U) U => l(nil) = nil
fn r(p U) U => r(nil) = nil
fn cons(x U, y U) U => l(cons(x,y))=x, r(cons(x,y))=y, cons(x, y) != nil
know @cons_is_unique(x0,y0,x1,y1 obj): cons(x0, y0) = cons(x1, y1) => x0 = x1, y0 = y1

# important properties
# every element in U is either nil or a cons of something

exist_prop x,y obj st has_lr(p U):
    cons(x, y) = p
know forall p U: p != nil => $has_lr(p)


fn nth(x N_pos, p U) U
know:
    forall p U => nth(1, p) = l(p)
    forall x N_pos, p U: x > 1 => nth(x, p) = nth(x-1, r(p))

prove_algo table_nth(x, p):
    if x = 1:
        nth(1, p) = l(p)
        return
    if x > 1:
        nth(x, p) = nth(x-1, r(p))
        by table_nth(x-1, r(p))
        return

have px U
by table_nth(2, px)
nth(2, px) = l(r(px)) # this does not work
```