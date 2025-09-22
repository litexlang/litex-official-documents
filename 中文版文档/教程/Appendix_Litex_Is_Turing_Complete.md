# 附录：Litex 是图灵完备的吗？

_...以无限磁带形式获得的无限内存容量，磁带被标记成方块，每个方块上可以打印一个符号。在任何时刻，机器中都有一个符号；它被称为扫描符号。机器可以改变扫描符号，其行为部分由该符号决定，但磁带上其他地方的符号不影响机器的行为。但是，磁带可以通过机器来回移动，这是机器的基本操作之一。因此，磁带上的任何符号最终都可能有机会。_

_-- 艾伦·图灵__

维护开源软件的最大乐趣之一就是成为充满激情的社区的一部分。通常，社区中的人甚至比其创造者更了解语言！一些社区专家试图从两个不同的角度证明 Litex 是图灵完备的，这里是他们的代码示例。真的感谢他们的奉献。我们希望更多的人能加入我们，让 Litex 变得更好。随时在 [zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/) 上提交您有趣的想法！

他们的证明没有完全验证。随时指出他们证明的任何问题！

1. 由黄晨轩提供。他使用 SKI 组合子来证明 Litex 的图灵完备性。

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

2. 由朱成阳提供。他使用 Y 组合子来证明 Litex 的图灵完备性。

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
