# Know：明智地使用它

## 使用 `know` 假设事实

通常我们需要假设某些事实而不是证明它们。例如，当引入具有特定属性的新对象时，或当使用定理作为前提而不经过其完整证明时。在这种情况下，我们使用 `know` 关键字。

有两种使用 `know` 的方法：**多行**和**内联**。

### 多行

写 `know:` 并在下面列出事实。每个事实本身可以是内联或多行的。

```litex
know:
    fact_1
    fact_2
    ...
```

示例（这里的事实是平凡的，只是为了演示）：

```litex
know:
    1 > 0
    forall x R:
        x $in R
    forall x R => x $in R
    2 > 1
```

### 内联

写 `know` 后跟一系列内联事实。特定事实以 `,` 结尾，普遍事实以 `;` 结尾。最后的结束标记可以省略。

```litex
know specific_fact_1, universal_fact_1; specific_fact_2, universal_fact_2; ...
```

示例：

```litex
know 1 > 0, forall x R => x $in R; forall x R => x $in R; 2 > 1
```

---

## 何时使用 `know`

### 1. 将事实绑定到命题

您可以声明一个命题并将等价事实附加到它：

```litex
prop n_larger_than_10(n N_pos) # declare a proposition
know forall n N_pos => n > 10 <=> $n_larger_than_10(n)
```

等价于：

```litex
prop n_larger_than_10(n N_pos):
    n > 10
```

虽然在数学上相同，但明确声明等价性使定义更清晰。Litex 的内核在给出时也会自动推断相关的等价性，这使得证明更直接。

---

### 2. 定义公理

公理是假设为真而不需要证明的。使用 `know` 来引入它们：

```litex
know forall x N => x >= 0
```

---

### 3. 假设定理而不证明

有时您想使用结果而不形式化它们。例如：

```litex
prop fermat_last_theorem(x, y, z, n N_pos): n >= 3 <=> x^n + y^n = z^n
know forall x, y, z, n N_pos: n >= 3 => $fermat_last_theorem(x, y, z, n)
```

费马大定理，由安德鲁·怀尔斯在 1994 年证明，极其难以形式化。然而 Litex 让您直接用 `know` 使用它，所以您可以基于既定结果构建，而不被其复杂性所阻碍。

---

### 4. 将属性绑定到对象或函数

如果关于对象的事实太少，您无法从中推导出太多。这就是为什么我们在定义对象或函数时经常绑定相关事实。

```litex
let n N_pos
know n > 10
```

等价于：

```litex
let n N_pos: n > 10
```

另一个例子：

```litex
fn fibonacci(n N_pos) N_pos
know fibonacci(1) = 1, fibonacci(2) = 1, forall n N_pos => fibonacci(n+2) = fibonacci(n+1) + fibonacci(n)
```

或对于函数：

```litex
fn g(x R) R
fn s(x R) R
fn q(x R) R
know forall x R => g(x) + s(x) + q(x) = g(x) + 17
```

---

## 小心使用 `know`

`know` 可以使**任何**语句为真。

```litex
know 1 = 2
1 = 2   # true, because you know 1 = 2
1 != 2  # also true, because 1 != 2 is a built-in fact
```

如这个例子所示，粗心使用 `know` 可能破坏一致性。明智地使用它。

---

## 结论

`know` 是一个强大的工具。您可以使用它来：

1. 将事实绑定到命题
2. 定义公理
3. 假设定理而不证明
4. 将属性绑定到对象和函数

没有严格的规则——当它使您的代码更清晰和更容易阅读时使用 `know`，但总是要谨慎。
