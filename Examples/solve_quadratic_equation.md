```litex
know @solve_quadratic_equation(a, b, c, x R):
    b ^ 2 - 4 * a * c >= 0
    x ^ 2 + b * x + c = 0
    =>:
        or:
            x = (-b + sqrt(b ^ 2 - 4 * a * c)) / (2 * a)
            x = (-b - sqrt(b ^ 2 - 4 * a * c)) / (2 * a)

let x R: x^2 + 2 * x + 1 = 0

$solve_quadratic_equation(1, 2, 1, x)
prove_in_each_case:
    or:
        x = (-2 + sqrt(2 ^ 2 - 4 * 1 * 1)) / (2 * 1)
        x = (-2 - sqrt(2 ^ 2 - 4 * 1 * 1)) / (2 * 1)
    =>:
        x = -1
    prove:
        x = (-2 + sqrt(0)) / (2 * 1) = -1
    prove:
        x = (-2 - sqrt(0)) / (2 * 1) = -1
```
