# 函数：符号的胶水

函数是数学中最基本的概念之一。
Litex 作为纯粹为推理设计的**非图灵完备域语言**，以与 Python 或 C 等编程语言截然不同的方式处理函数。

一旦我们比较推理（数学）中的*函数*概念与编程中的概念，这种差距就变得清晰：

* 在**编程语言**中（例如 Python、Lean），函数是执行计算或副作用的可执行代码块。
* 在**数学**中，函数不是可执行代码。相反，它是从输入符号构建新符号的**符号构造函数**。您可以将其视为将符号绑定在一起的*胶水*。

在数学和编程中，共同特征是函数使用 `()` 包装输入并产生新表达式。例如，数学中的 `square_root(x)` 只是表示从 `x` 形成的新符号。没有计算发生。

---

## 内置函数

`+`、`-`、`*`、`/`、`^`、`%` 是内置函数。它们的日常属性已经在 Litex 内核中。

```litex
1 + 1 = 2
2 * (1 + 1) = 3 + 1
have x, y, z R
(x + 1) ^ 2 = x ^ 2 + 2 * x + 1
(x + y) * (x + z) = x ^ 2 + x * y + x * z + y * z
x + z = z + x
```

除了内置函数外，Litex 允许您定义自己的函数。

---

## 定义具有存在保证的函数

在编程中，定义函数只需要编写代码块。
然而，在数学中，*声明新函数必须伴随其存在性的证明*。否则，声明是不安全的，可能导致矛盾。

Litex 提供两种定义函数的方法。

---

### 1. 定义函数并证明其存在性

当声明具有存在保证的新对象时，我们使用 `have` 关键字。当声明具有存在保证的函数时，我们使用 `have fn` 关键字。

语法：

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

**示例：**

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

解释：

* 在 `prove` 部分，函数的参数（这里是 `x`）被假设满足域条件（`x > 0`）。
* 然后我们必须提供一个位于返回集中并满足所有结论（`a(x) > 0`）的对象。
* 如果我们定义 `a(x) = x`，那么每当 `x > 0` 时 `a(x) > 0` 成立。
* 写 `have x` 确保这样的函数存在。

因此，函数 `a` 被安全定义。其存在性由 `have` 语句保证。

### 2. 通过等式定义函数

在日常数学中，当我们想要定义函数时，我们只是写 `g(x) = x` 或 `s(x) = x^2` 或 `q(x) = x^2 + 1` 等。在 Litex 中，我们可以以更简洁的方式做同样的事情。

```
have fn f(param1 set1, param2 set2, ...) return_set = expression
``` 

例如

```litex
have fn g(x R) R = x
have fn s(x R) R = x^2
have fn q(x R) R = x^2 + 1
```

它们等价于以下内容：

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

### 结论

通常，`have` 关键字用于声明具有确保其存在性的新对象。确保函数的存在性不是一项微不足道的任务，所以我们需要证明它。

---

### 2. 定义没有存在性证明的函数

有时我们只是想引入具有某些属性的函数符号，而不证明存在性。
例如，平方根函数：

```litex
fn square_root(x R) R:
    dom:
        x >= 0
    =>:
        square_root(x) * square_root(x) = x
```

这里：

* `fn` 引入新函数。
* `square_root` 是其名称。
* `(x R)` 指定参数 `x` 属于 `R`。
* 最后的 `R` 指定函数的*范围*。
* `dom` 指定域限制（`x >= 0`）。
* `=>` 部分说明函数满足的属性。

所以，`square_root(-1)` 无效，因为 `-1` 不满足域。

⚠️ **注意：** 这种定义风格不保证这样的函数存在。为了安全起见，Litex 稍后将支持 `set_defined_by_replacement`，这确保存在性。

注意：您可以在域事实中引用函数本身。例如，您不应该这样做：

```
fn f(x R) R:
    f(x) > 0
    =>:
        ...
```

---

## 函数定义的紧凑风格

Litex 鼓励简短、清晰的定义。例如，我们可以明确省略 `dom`：

```litex
fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x
```

甚至内联：

```litex
fn square_root(x R) R: x >= 0 => square_root(x) * square_root(x) = x
```

其他简写示例：

```litex
fn f(x R) R
fn f2(x R) R: x > 0
fn f3(x R) R => f3(x) > 0
fn f4(x R) R: x > 0 => f4(x) > 0
```

等价于展开形式：

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

## 调用函数

Litex 中的函数调用看起来与数学中完全一样：

```litex
fn square_root(x R) R:
    x >= 0
    =>:
        square_root(x) * square_root(x) = x

square_root(4) $in R
```

⚠️ 重要：Litex **不计算**。
`square_root(4)` **不等于** `2`。相反，它表示"`R` 中的某个值，使得当 `x = 4` 时 `square_root(x)^2 = x`。" 实际值无关紧要；只有存在性重要。

您不应该传递不满足函数域的参数。例如

```litex
have cartoon_characters nonempty_set, oddie_bird, carmela_bird cartoon_characters
fn fuse_characters(x, y cartoon_characters) cartoon_characters

# You can not add two cartoon characters, because + takes real numbers as parameters.
# oddie_bird + carmela_bird = oddie_bird + carmela_bird

fuse_characters(oddie_bird, carmela_bird) $in cartoon_characters
```

您不能写 `oddie_bird + carmela_bird`，因为 `+` 接受实数作为参数。您可以调用 `fuse_characters(oddie_bird, carmela_bird)` 来获得新的卡通角色，因为它被定义为接受卡通角色作为参数的函数。

## 参数必须满足函数的域事实

```litex
fn f(x R) R:
    x > 0
    =>:
        f(x) > 0

f(-1) > 0
```

您不能写 `f(-1)`，因为 `-1` 不满足域事实 `x > 0`。如果您运行上述代码，它将输出如下错误：

```
failed to check param(s) (-1 * 1) satisfy domain of
fn (x R) R:
    dom
        x > 0
    =>
        f(x) > 0
```

---

## 函数模板和 `let`

函数也是对象。因此，使用 `let`，我们可以从模板声明函数。

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

这是以下内容的简写：

```litex
fn_template finite_sequence(s set, max N):
    fn (n N) R:
        dom:
            n < max

let fs1 finite_sequence(R, 10):

know forall n N => fs1(n) = n * n
```

---

✨ 简而言之：

* 在**编程**中，函数执行。
* 在**Litex**中，函数是**符号构造函数**，是从旧符号构建新符号的胶水。
* 要安全地定义函数，必须确保存在性，要么通过证明，要么通过替换。
