# 等于：为什么 `=` 统治数学

_等于：以相同方式对待或影响所有对象。_

_— 韦氏词典_

`=` 是数学中最重要的命题。它用于在两个对象之间建立相等关系。换句话说，当 `x = y` 时，`x` 和 `y` 之间不再有任何区别。例如：

```litex
let x N, y N:
    x = y
    x > 0

y > 0
```

最后一个语句 `y > 0` 为真，因为 `x = y` 和 `x > 0` 为真。如您所见，一旦两个对象相等，它们就可以在任何上下文中互换使用。

您可以将 `a = b` 视为 `a` 是 `b` 的别名，或 `b` 是 `a` 的别名。

由于 `=` 如此重要，它拥有最丰富的内置支持。我们将逐一介绍它们。

## 字面上相同

验证两个对象是否相等的最基本和基础的方法是检查它们是否是字面上相同的对象。例如：

```litex
have x N
x = x
x + 2 = x + 2
```

最终，在 `=` 的左右两边建立相等性的方法是它们作为字符串完全相同（唯一的例外是在比较数字字面量时）。

## 使用已知的相等传递性来证明相等

相等的最基本属性是它是传递的。例如：

```litex
let a, b, c R:
    a = b
    b = c

a = c
```

如何使用相等的传递性来验证 `a = c`？当 `a = b` 已知为真时，Litex 内核意味着一个字典，将 `a` 和 `b` 都映射到共享集合 {a, b}。然后 `b = c` 已知，我们将 `c` 放入集合并将 `a`、`b`、`c` 映射到 {a, b, c}。现在我们知道 `a` 和 `c` 在同一个集合中，所以 `a = c` 为真。这就是如何使用相等的传递性来证明相等。

这里有一个更复杂的例子：

```litex
let a, b, c, d, e R:
    (a + 2) * d * e = a
    a = c

(a + 2) * d * e = c
```

如何使用相等的传递性来验证 `(a + 2) * d * e = c`？当 `(a + 2) * d * e = a` 已知为真时，Litex 内核意味着一个字典，将 `(a + 2) * d * e` 和 `a` 都映射到共享集合 {(a + 2) * d * e, a}。然后 `a = c` 已知，我们将 `c` 放入集合并将 `a`、`c`、`(a + 2) * d * e` 映射到 {a, c, (a + 2) * d * e}。现在我们知道 `(a + 2) * d * e` 和 `c` 在同一个集合中，所以 `(a + 2) * d * e = c` 为真。注意除了像 `a` 这样的单词符号外，像 `(a + 2) * d * e` 这样的对象也被称为符号，由多个单词组成的符号（在 Litex 中，多词符号通常具有 functionName(parameter1, parameter2, ...) 的形状）。

## 函数的两个返回值

包含的符号通常不是字面上相同的，例如：

```litex
let a, b, c R:
    (a * 2) + b = c
fn f(a, b R) R
f(a, c) = f(a, (a * 2) + b)
```

没有已知的事实语句说 `f(a, c) = f(a, (a * 2) + b)`，也没有传递的东西，为什么它仍然有效？

事实证明，Litex 归纳地检查两个符号的相等性。现在，左边是函数的返回值（在这种情况下，左边是函数 `f` 的返回值，参数为 `a` 和 `c`：f(a, c)），右边也是函数的返回值（在这种情况下，右边是函数 `f` 的返回值，参数为 `a` 和 `(a * 2) + b`）。现在，Litex 内核检查两个函数是否相等（在这种情况下，`f` = `f`），如果两个函数相等，则检查它们的第一个参数是否相等（在这种情况下，`a` = `a`），然后检查它们的第二个参数是否相等（在这种情况下 `c` = `(a * 2) + b`，这是真的，因为已知为真）。

上述例子非常具有代表性，因为在大多数情况下，字面相等不起作用。当我们处理符号时，我们经常处理函数，在许多情况下我们想要用相等的参数替换其中的一些参数。这种功能对于这种情况是必不可少的。

这里有一个更复杂的例子，字面上不同的函数名、参数，但所有这些字面上不同的东西都是相等的

```litex
let a, b, c, d R:
    a = 2
    b = c * a
    c + a = (b + 10) * d

fn f(a, b, c R) R
fn g(a, b, c R) R
know f = g

f(a, b, c + a) = g(2, c * a, (b + 10) * d)
```

如果您运行上述代码，您可能会收到这样的消息：

```
f = g
is true. proved by
known fact:
f = g
a = 2
is true. proved by
known fact:
a = 2
b = (c * a)
is true. proved by
known fact:
b = (c * a)
(c + a) = ((b + 10) * d)
is true. proved by
known fact:
(c + a) = ((b + 10) * d)
---
Success! :)
```

上述消息意味着 `f = g` 为真，因为 `f = g` 已知为真，`a = 2` 为真，因为 `a = 2` 已知为真，`b = (c * a)` 为真，因为 `b = (c * a)` 已知为真，`(c + a) = ((b + 10) * d)` 为真，因为 `(c + a) = ((b + 10) * d)` 已知为真。由于函数名相等 `f = g`，参数相同 `a = 2`，`b = c * a`，`c + a = (b + 10) * d`。因此，`f(a, b, c + a) = g(2, c * a, (b + 10) * d)` 为真。

## 数值相等

当 `=` 的左边和右边都是数字时，Litex 将使用内置功能来验证它们是否相等。例如：

```litex
1 + 1 = 2
4 / 2 = 2
3 * (2 + 5) = 9 + 12
(3 + 4) / (2 + 5) = 7 / 7
```

## 多项式展开和组合

当 `=` 的左边和右边都是符号且相关函数是基本数值函数如 `+`、`-`、`*`、`/`、`^` 时，Litex 将使用内置功能来验证它们是否相等。

Litex 具有内置的多项式简化/展开/因式分解，允许用户直接操作符号多项式，而无需手动展开或组合同类项。这对于许多数学任务非常方便，包括代数推理、求解方程、约简/化简、表达式简化/常量折叠、构建或验证复杂公式等。

例如：

```litex
let x, y R: y != 0
(x + 2 * y) * y = x * y + y * y * (3 - 1)
(10 * x + 20 * y) / 10 = x + 2 * y
x ^ 2 = x * x
(x ^ 2 * y + y ^ 2) / y = x ^ 2 + y
```

## 多行方程

Litex 提供 `=:` 来表达多行方程：

```litex
let x, y R:
    x = -4
    y = 6
=:
    2 * x + 3 * y
    2 * -4 + 3 * 6
    10
=:
    4 * x + 5 * y
    4 * -4 + 5 * 6
    14
```

您也可以在一行中写它：

```litex
let x, y R: x = -4, y = 6
=(2 * x + 3 * y, 2 * -4 + 3 * 6, 10)
=(4 * x + 5 * y, 4 * -4 + 5 * 6, 14)
```

`=:` 和 ` =()` 是 `=` 的语法糖。以下两段代码是等价的：

```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R:
    veryLongSymbol = veryLongSymbol2
    veryLongSymbol2 = veryLongSymbol3
    veryLongSymbol3 = veryLongSymbol4
    veryLongSymbol4 = veryLongSymbol5
    veryLongSymbol5 = veryLongSymbol6
```

```litex
let veryLongSymbol, veryLongSymbol2, veryLongSymbol3, veryLongSymbol4, veryLongSymbol5, veryLongSymbol6 R:
    =:
        veryLongSymbol
        veryLongSymbol2
        veryLongSymbol3
        veryLongSymbol4
        veryLongSymbol5
        veryLongSymbol6
```

如您所见，`=:` 和 `=()` 让您免于写很多 `=` 语句。当您写长方程并使用相等的传递性来证明相等时，这特别有用。
