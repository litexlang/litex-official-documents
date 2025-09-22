# Exist

## 什么是存在命题

在逻辑和数学中，**存在命题**是断言*至少存在一个对象满足某个属性*的语句。通常写为：

$$
\exists x \, P(x)
$$

其中：

* $\exists$ 意思是"存在"，
* $x$ 是变量，
* $P(x)$ 是关于 $x$ 的属性或谓词。

**直观理解：**

* 例如，"存在一个整数 $x$ 使得 $x^2 = 4$" 是一个存在命题，因为 $x = 2$ 或 $x = -2$ 满足它。
* 它是**全称命题**的对立面，全称命题断言*所有对象都满足一个属性*，写为 $\forall x \, P(x)$。

**要点：**

1. 如果至少有一个例子满足 $P(x)$，则命题为真。
2. 如果没有对象满足 $P(x)$，则命题为假。
3. 在形式证明中，证明存在命题通常涉及提供一个**见证**——满足该属性的 $x$ 的明确例子。

如果您愿意，我也可以解释存在命题和全称命题之间**证明策略的差异**——这是形式逻辑中微妙但重要的一点。

**存在命题**可以用带否定的全称命题来表达。具体来说：

$$
\exists x \, P(x) \quad \text{等价于} \quad \neg \forall x \, \neg P(x)
$$

**直觉：**

* "存在一个 $x$ 使得 $P(x)$ 为真" 意味着**不是**对所有 $x$ 都有 $P(x)$ 为假。
* 换句话说，如果对所有 $x$ 都有 $P(x)$ 为假（$\forall x \, \neg P(x)$）是真的，那么显然没有 $x$ 满足 $P(x)$。
* 所以断言存在在逻辑上等同于否认对所有 $x$ 都有 $P(x)$ 为假。

**示例：**

* 存在："存在一个整数 $x$ 使得 $x^2 = 4$" → $\exists x \, (x^2 = 4)$
* 全称否定："不是对所有整数 $x$ 都有 $x^2 \neq 4$" → $\neg \forall x \, (x^2 \neq 4)$

两个语句在逻辑上等价。由于 forall 在 Litex 中起核心作用，存在命题也是语言的重要组成部分。

在 Litex 中，要表达 not forall，您首先定义一个存在命题，然后使用这个存在事实的验证来表示全称语句的否定。

## 声明存在命题

您可以声明一个存在命题 `larger_than`（对于 `R` 中所有 `y` 且 `y > 0`，存在 `R` 中的 `x` 使得 `x > y`）：

```litex
exist_prop x R st larger_than(y R):
    dom:
        y > 0
    <=>:
        x > y
```
`exist_prop` 是存在命题的保留字。`st` 意思是*使得*。如您所见 `exist_prop ... st ...` 是声明存在命题时的固定匹配。

您也可以隐藏 `dom`：

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y
```

如果您将 `y` 放在 `N_pos` 中，您也可以隐藏 `iff`：

```litex
exist_prop x R st larger_than(y N_pos):
    x > y
```

## 证明声明的存在命题

当被调用时，存在命题的行为与普通命题完全相同。例如，这里我们假设 `larger_than` 对于 `N_pos` 中的所有 `y` 都为真，我们声明存在某个大于 2 的对象。

```litex
exist_prop x R st larger_than(y R):
    x > y

know forall y R => $larger_than(y)

$larger_than(2)
```

但是，存在命题和普通命题之间有一个很大的区别。您可以通过提供特定对象来证明存在命题。例如，这里我们通过提供 `3` 来证明 `larger_than(2)`：

```litex
exist_prop x R st larger_than(y R):
    x > y

exist 3 st $larger_than(2)
```

由于 `not exist` 等价于 `forall not`，当存在事实的反面为真时，相关的 `forall not` 事实自动为真。参见以下示例：

```litex
prop q(x R, y R)

exist_prop x R st p(y R):
    $q(x, y)

know not $p(2)

forall x R:
    not $q(x, 2)
```

与编程语言不同，在编程语言中您可以声明任何东西而不检查其存在性，Litex 以及数学都要求您在使用对象之前声明其存在性。

## 与 Have 一起工作

数学和编程之间的一个很大区别是，数学要求您在使用对象之前证明其存在性，而在 Python 或 C 中编程时您不必这样做。在 Litex 中，`have` 关键字允许您声明一个具有存在承诺的新对象。

`have` 关键字可以与存在事实一起工作。

```
have object1, object2, ... st $existential_fact(param1, ...)
```

当 `$existential_fact(param1, ...)` 为真时，上述 `have` 语句有效。新对象 `object1, ...` 被声明，具有基于 `existential_fact` 定义的相应属性。

例如

```litex
exist_prop x R st exist_number_larger_than(y R):
    x > y

exist 17 st $exist_number_larger_than(1)

$exist_number_larger_than(1)

have a st $exist_number_larger_than(1)

a $in R
a > 1
```

在这种情况下，我们使用 `17` 来证明 `$exist_number_larger_than(1)`，`have a st $exist_number_larger_than(1)` 声明一个具有属性 `a $in R` 和 `a > 1` 的对象 a。注意 `a = 17` 是未知的，因为 `have` 语句是从满足 `exist_number_larger_than` 属性的对象中选择一个。
