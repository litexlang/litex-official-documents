```litex
fn f(x Z) Z:
    when: x % 2 = 0 =>f(x+1) = f(x) + 1
    when: x % 2 = 1 =>f(x+1) = f(x) + 2
know f(0) = 0
f(1) = f(0) + 1 = 1

claim forall x Z: x % 2 = 0 => f(x) = f(x - 1) + 2:
    (x - 1) % 2 = (x % 2 - 1 % 2) % 2 = (-1) % 2 = 1
    f(x - 1 + 1) = f(x - 1) + 2 = f(x)

claim forall x Z: x % 2 = 1 => f(x) = f(x - 1) + 1:
    (x - 1) % 2 = (x % 2 - 1 % 2) % 2 = 0 % 2 = 0
    f(x - 1 + 1) = f(x - 1) + 1 = f(x)

algo f(x):
    if x % 2 = 0:
        return f(x - 1) + 2
    if x % 2 = 1:
        return f(x - 1) + 1
```
