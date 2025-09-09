# Appendix: Litex is Turing Complete

One of the greatest joys of maintaining open-source software is being part of a passionate community. Often, people in the community know the language even better than its creator! Two community experts have proven that Litex is Turing-complete from two different perspectives, and here are their code examples.

1. Provided by Chenxuan Huang. He uses SKI combinator to prove the Turing completeness of Litex.

```litex
have Term nonempty_set
have I, S, K Term
fn app(a Term, b Term) Term

have Value nonempty_set
have I0, K0, S0 Value
fn K1(a Term) Value
fn S1(a Term) Value
fn S2(a Term, b Term) Value

have List nonempty_set
have Nil List
fn Cons(x Term, xs List) List

have Machine nonempty_set
fn M0(x Term, stk List) Machine
fn M1(x Value, stk List) Machine
fn M2(x Value) Machine

fn step(m Machine) Machine
know:
    # M0 steps down
    forall x, y Term, l List:
        step(M0(app(x, y), l)) = M0(x, Cons(y, l))
    forall l List:
        step(M0(I, l)) = M1(I0, l)
        step(M0(K, l)) = M1(K0, l)
        step(M0(S, l)) = M1(S0, l)

    # M1 perform the combinators' actions
    step(M1(I0, Nil)) = M2(I0)
    step(M1(K0, Nil)) = M2(K0)
    step(M1(S0, Nil)) = M2(S0)
    forall x Term, l List:
        step(M1(I0, Cons(x, l))) = M0(x, l)
        step(M1(K0, Cons(x, l))) = M1(K1(x), l)
        step(M1(S0, Cons(x, l))) = M1(S1(x), l)
        step(M1(K0(x), Nil)) = M2(K0(x))
        step(M1(S1(x), Nil)) = M2(S1(x))
    forall x, y Term, l List:
        step(M1(K0(x), Cons(y, l))) = M0(x, l)
        step(M1(S1(x), Cons(y, l))) = M1(S2(x, y), l)
        step(M1(S2(x, y), Nil)) = M2(S2(x, y))
    forall x, y, z Term, l List:
        step(M1(S2(x, y), Cons(z, l))) = M0(app(app(x, z), app(y, z)), l)

    # M2 ends the evaluation
    forall x Value:
        step(M2(x)) = M2(x)

fn evalm(m Machine) Machine
know:
    forall x Term, l List:
        evalm(M0(x, l)) = evalm(step(M0(x, l)))
    forall x Value, l List:
        evalm(M1(x, l)) = evalm(step(M1(x, l)))
    forall x Value:
        evalm(M2(x)) = M2(x)

have program0 Term
know:
    program0 = app(I, K)

# now to execute the program ...
step(M0(program0, Nil)) = M0(I, Cons(K, Nil))
evalm(M0(program0, Nil)) = evalm(M0(I, Cons(K, Nil)))
# add more steps as necessary...
```

2. Provided by Changyang Zhu. He uses the Y-combinator to prove the Turing completeness of Litex.

```litex
have Term nonempty_set
have I, S, K, C_, B, U Term
fn app(a Term, b Term) Term

# I = Lambda x.x
# S = lambda xyz.(xz)(yz)
# K = lambda xy.x
# C_ = lambda xyz.xzy
# B = lambda xyz.x(yz)
# U = lambda x.xx

have Value nonempty_set
have I0, K0, S0, C0, B0, U0 Value
fn K1(a Term) Value
fn S1(a Term) Value
fn S2(a Term, b Term) Value
fn C1(a Term) Value
fn C2(a Term, b Term) Value
fn B1(a Term) Value
fn B2(a Term, b Term) Value
fn U1(a Term) Value

have List nonempty_set
have Nil List
fn Cons(x Term, xs List) List

have Machine nonempty_set
fn M0(x Term, stk List) Machine
fn M1(x Value, stk List) Machine
fn M2(x Value) Machine

know:
    # M0 steps down
    forall x, y Term, l List:
        M0(app(x, y), l) = M0(x, Cons(y, l))
    forall l List:
        M0(I, l) = M1(I0, l)
        M0(K, l) = M1(K0, l)
        M0(S, l) = M1(S0, l)
        M0(C_, l) = M1(C0, l)
        M0(B, l) = M1(B0, l)
        M0(U, l) = M1(U0, l)

    # M1 perform the combinators' actions
    M1(I0, Nil) = M2(I0)
    M1(K0, Nil) = M2(K0)
    M1(S0, Nil) = M2(S0)
    M1(C0, Nil) = M2(C0)
    M1(B0, Nil) = M2(B0)
    M1(U0, Nil) = M2(U0)
    forall x Term, l List:
        M1(I0, Cons(x, l)) = M0(x, l)
        M1(U0, Cons(x, l)) = M0(app(x, x), l)
        M1(K0, Cons(x, l)) = M1(K1(x), l)
        M1(S0, Cons(x, l)) = M1(S1(x), l)
        M1(C0, Cons(x, l)) = M1(C1(x), l)
        M1(B0, Cons(x, l)) = M1(B1(x), l)
        M1(K0(x), Nil) = M2(K0(x))
        M1(S1(x), Nil) = M2(S1(x))
        M1(C1(x), Nil) = M2(C1(x))
        M1(B1(x), Nil) = M2(B1(x))
    forall x, y Term, l List:
        M1(K0(x), Cons(y, l)) = M0(x, l)
        M1(S1(x), Cons(y, l)) = M1(S2(x, y), l)
        M1(C1(x), Cons(y, l)) = M1(C2(x, y), l)
        M1(B1(x), Cons(y, l)) = M1(B2(x, y), l)
        M1(S2(x, y), Nil) = M2(S2(x, y))
        M1(C2(x, y), Nil) = M2(C2(x, y))
        M1(B2(x, y), Nil) = M2(B2(x, y))
    forall x, y, z Term, l List:
        M1(S2(x, y), Cons(z, l)) = M0(app(app(x, z), app(y, z)), l)
        M1(C2(x, y), Cons(z, l)) = M0(app(app(x, z), y), l)
        M1(B2(x, y), Cons(z, l)) = M0(app(x, app(y, z)), l)

have Y Term
know:
    Y = app(app(B, U), app(app(C_, B), U))

have F Term

have program Term
know:
    program = app(Y, F)

# Hereby we noticed that "step" and "evalm" are only symbols that require transitivity
# Thus we use "=" to simplify the program
# You can expand it to "step" and "evalm" if you want

know forall a, b Term: M0(a, Nil) = M0(b, Nil) => a = b
=:
    M0(program, Nil)
    M0(app(Y, F), Nil)
    M0(app(app(app(B, U), app(app(C_, B), U)), F), Nil)
    M0(app(app(B, U), app(app(C_, B), U)), Cons(F, Nil))
    M0(app(B, U), Cons(app(app(C_, B), U), Cons(F, Nil)))
    M0(B, Cons(U, Cons(app(app(C_, B), U), Cons(F, Nil))))
    M1(B0, Cons(U, Cons(app(app(C_, B), U), Cons(F, Nil))))
    M1(B1(U), Cons(app(app(C_, B), U), Cons(F, Nil)))
    M1(B2(U, app(app(C_, B), U)), Cons(F, Nil))
    M0(app(U, app(app(app(C_, B), U), F)), Nil)
    M0(U, Cons(app(app(app(C_, B), U), F), Nil))
    M1(U0, Cons(app(app(app(C_, B), U), F), Nil))
    M0(app(app(app(app(C_, B), U), F), app(app(app(C_, B), U), F)), Nil)

=:
    M0(app(app(app(C_, B), U), F), Nil)
    M0(app(app(C_, B), U), Cons(F, Nil))
    M0(app(C_, B), Cons(U, Cons(F, Nil)))
    M0(C_, Cons(B,Cons(U, Cons(F, Nil))))
    M1(C0, Cons(B,Cons(U, Cons(F, Nil))))
    M1(C1(B), Cons(U, Cons(F, Nil)))
    M1(C2(B, U), Cons(F, Nil))
    M0(app(app(B, F), U), Nil)

app(app(app(C_, B), U), F) = app(app(B, F), U)

=:
    M0(program, Nil)
    M0(app(app(app(app(C_, B), U), F), app(app(app(C_, B), U), F)), Nil)
    M0(app(app(app(B, F), U), app(app(B, F), U)), Nil)
    M0(app(app(B, F), U), Cons(app(app(B, F), U), Nil))
    M0(app(B, F), Cons(U, Cons(app(app(B, F), U), Nil)))
    M0(B, Cons(F, Cons(U, Cons(app(app(B, F), U), Nil))))
    M1(B0, Cons(F, Cons(U, Cons(app(app(B, F), U), Nil))))
    M1(B1(F), Cons(U, Cons(app(app(B, F), U), Nil)))
    M1(B2(F, U), Cons(app(app(B, F), U), Nil))
    M0(app(F, app(U, app(app(B, F), U))), Nil)

=:
    M0(app(U, app(app(B, F), U)), Nil)
    M0(U, Cons(app(app(B, F), U), Nil))
    M0(app(app(app(B, F), U), app(app(B, F), U)), Nil)
    M0(program, Nil)

app(U, app(app(B, F), U)) = program

=:
    M0(program, Nil)
    M0(app(F, app(U, app(app(B, F), U))), Nil)
    M0(app(F, program), Nil)

program = app(F, program)
app(Y, F) = app(F, app(Y, F))

# Thus, we've proved the property of Y-combinator
# Y F = F(Y F)
```