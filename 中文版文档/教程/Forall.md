# Forall 语句：强制启用推理无限扩展

数学从根本上说是从先前建立的事实中推导新事实。其中，**普遍事实**（以 `forall` 开头的语句，也称为 `forall` 语句）起着核心作用：它们允许我们推导出无限多个特定实例。

例如，普遍语句

```litex
forall x N_pos => x $in N
```

可以生成无限多个 `x $in N` 形式的特定语句：

```
1 $in N
2 $in N
...
```

由于有无限多个正自然数，这个单一的普遍语句产生了无限多个真语句。

---

## Litex 中的普遍事实

Litex 中的普遍语句表达"对于所有...，如果某些假设成立，那么某些结论随之而来"的思想。

这里有一个平凡但有效的例子：

```litex
forall x N_pos:
    x $in N_pos
```

这读作：*对于 `N_pos`（正自然数集合）中的所有 `x`，`x` 在 `N_pos` 中。*
假设和结论是相同的，所以语句总是为真。

---

## `forall` 的语法

完整语法是：

```
forall parameter1 set1, parameter2 set2, ...:
    domFact1
    domFact2
    ...
    =>:
        thenFact1
        thenFact2
        ...
```

这意味着：*对于 set1 中的所有 parameter1，set2 中的所有 parameter2，...，如果域事实（domFacts）得到满足，那么结论（thenFacts）为真。*
您可以将域事实视为参数所需的**限制或假设**。

符号 `$in` 是 Litex 中的内置命题，意思是"在...中"。所以您可以写：

```litex
1 $in N_pos
```

或等价地：

```litex
$in(1, N_pos)
```

两者都断言明显的事实：*对于 `N_pos` 中的所有 `x`，`x` 在 `N_pos` 中。*

---

## 内联普遍语句

Litex 还支持紧凑的**内联形式**：

```
forall parameter1 set1, parameter2 set2, ... : inline domain facts => inline conclusion facts
```

内联事实遵循两个规则：

1. **特定事实** 后跟 `,`
2. **普遍事实** 后跟 `;`

示例：

```litex
forall x N_pos => x $in N_pos
forall x N_pos: forall y N_pos: y > x => y > x; x > 10 => forall y N_pos: y > x => y > x; x > 10
```

（第二个例子故意无意义——它只是演示嵌套内联普遍事实的语法。）

---

## 带限制的普遍事实

通常，我们想要表达带有额外限制的普遍语句。例如：

*对于所有实数 `x` 和 `y`，如果 `x > 0` 且 `y > 0`，那么 `x > 0` 且 `y > 0`。*

在 Litex 中：

```litex
know forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

为了使这样的声明更简洁，Litex 允许您在特定上下文中省略一些保留字。例如，`dom` 可以隐藏：

```litex
forall x, y R:
    x > 0
    y > 0
    =>:
        x > 0
        y > 0
```

内联版本是

```litex
forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

如果 `x` 已经被声明在 `N_pos`（正自然数集合）中，则无需重述其域。类似地，`iff` 有时可以省略。

因此，开头例子的规范形式将是：

```litex
forall x N_pos:
    =>:
        x $in R
```

内联版本是

```litex
forall x N_pos => x $in R
```

---

## 等价事实

有时，您想要断言两个结论在相同限制下是**等价的**。在这种情况下，您可以添加一个 `iff` 块：

```litex
forall x R:
    dom:
        x > 1
    =>:
        not x = 2
    <=>:
        x != 2
```

内联版本是

```litex
forall x R: x > 1 => not x = 2 <=> x != 2
```

> **注意：** 此格式仅支持 `fact_1 <=> fact_2` 形式的等价。两个事实必须在逻辑上等价。

## 示例

普遍语句在数学中无处不在，所以我们将在以下部分看到许多示例来帮助您理解如何使用它们。

有时，命题具有反射性质。例如，成为朋友是对称关系。

```litex
have people nonempty_set
have oddie_bird, hippo_dog people
prop we_are_friends(x, y people)
know:
    forall x, y people => $we_are_friends(x, y) <=> $we_are_friends(y, x)
    $we_are_friends(oddie_bird, hippo_dog)
$we_are_friends(hippo_dog, oddie_bird)
```

## 如果您的普遍事实中的要求是错误的会发生什么？

假设我们有以下代码

```litex
forall x, y R:
    2 * x + 3 * y = 4
    4 * x + 6 * y = 7
    =>:
        =:
            2 * (2 * x + 3 * y)
            2 * 4
            4 * x + 6 * y
            7
        7 = 8
```

等等，为什么 `7 = 8` 没有任何矛盾就为真？

答案是普遍事实中的要求是错误的。没有这样的 `x` 和 `y` 满足要求。验证不会造成任何麻烦的原因是，不存在这样的 `x` 和 `y` 可以匹配普遍事实的要求。所以新验证的事实永远不会被用来验证其他事实。
