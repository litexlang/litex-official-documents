```litex
# Multivariate linear equation example: Solve the equation 2x + 3y = 10 and 4x + 5y = 14.
# 多元线性方程组：解方程 2x + 3y = 10 和 4x + 5y = 14。

let x R, y R:
  2 * x + 3 * y = 10
  4 * x + 5 * y = 14

2 * (2 * x + 3 * y) = 2 * 10 = 4 * x + 6 * y
y = (4 * x + 6 * y) - (4 * x + 5 * y) = 2 * 10 - 14 = 6
2 * x + 3 * 6 = 10
2 * x + 18 - 18 = 10 - 18 = -8
x = (2 * x) / 2 = -8 / 2 = -4
```
