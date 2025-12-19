# Learn by Examples

_Tell me and I forget. Teach me and I remember. Involve me and I learn._

_– Benjamin Franklin_

There is no better way to learn than by doing. Previously we learned the basic knowledge of Litex, in a rather abstract way. Let's see some examples to see how Litex works in practice.

## Solve Linear Equations

Senario: We know `3 * x + 6 = 0`, we want to solve for `x = -2`.

Method1: Solve it directly.

```litex
let x R: 3 * x + 3 = 0
3 * x = -3
x = -3 / 3 = -1
```

This is already very simple. However, we can enclose the solving process in a proposition, and use it later.

Method2: Use the `solve_linear_equation` function.

```litex
know imply solve_linear_equation(a, b, x R):
    a != 0
    a * x + b = 0
    =>:
        x = -b / a

let x R: 3 * x + 3 = 0
$solve_linear_equation(3, 3, x)
x = -1
```

x = -1 is proved because x = (-3 / 3) is true by the validation of solve_linear_equation.

By enclosing the solving process in a proposition, we can not only prove the solution, but also use it later. This is very useful when we want to prove similar problems in similar ways in the future.

Next we solve multi-variable linear equations.

Senario: We know `3 * x + 4 * y + 5 = 0`, `6 * x + 7 * y + 8 = 0`, we want to solve for `x = 1`, `y = -2`.

Method1: Solve it directly.

```litex
let x, y R: 3 * x + 4 * y + 5 = 0, 6 * x + 7 * y + 8 = 0
2 * (3 * x + 4 * y + 5) = 2 * 0 = 6 * x + 8 * y + 10 = 6 * x + 7 * y + 8
6 * x + 8 * y + 10 - (6 * x + 7 * y + 8) = y + 2 = 0 - 0 = 0
y = -2
3 * x + 4 * (-2) + 5 = 3 * x - 3 = 0
3 * x - 3 + 3 = 0 + 3 = 3 = 3 * x
x = 3 / 3 = 1
```

As you can see, solving a multi-variable linear equation is much more complicated than solving a single-variable linear equation. Many steps of moving terms around are required. That's why we need to use the `solve_linear_equation2` proposition to enclose the solving process.

Method2: Use the `solve_linear_equation2` function.

```litex
know imply solve_linear_equation2(a, b, c, d, e, f, x, y R):
    a * x + b * y + c = 0
    d * x + e * y + f = 0
    a * e - b * d != 0
    =>:
        x = (b * f - c * e) / (a * e - b * d)
        y = (c * d - a * f) / (a * e - b * d)

let x, y R: 3 * x + 4 * y + 5 = 0, 6 * x + 7 * y + 8 = 0
$solve_linear_equation2(3, 4, 5, 6, 7, 8, x, y)
x = 1
y = -2 
```

You just need to provide the coefficients of the equations, and the final equation is proved directly by the validation of solve_linear_equation2.