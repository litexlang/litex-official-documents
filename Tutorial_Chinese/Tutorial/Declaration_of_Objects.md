# 对象声明：逻辑的名词

_数学不过是在纸上用无意义的标记按照某些简单规则进行的游戏。_

_— 大卫·希尔伯特_

现代数学建立在集合论之上。在 Litex 中，为了与这个基础保持一致，每当您声明一个新对象时，您还必须指定它所属的集合。

```litex
have a N, b Q, c R
let e N, f Q, g R
```

声明对象有两种主要方式：

1. **`have`** – *安全*的方式。集合必须是非空的（即 `$exist_in(setName)` 必须为真，如 `$exist_in(R)`），或者集合必须明确声明为 `set` 或 `nonempty_set`。

   > 注意：`set $in set` 在 Litex 中**不是**真的，因为这会违反集合论的规则。

2. **`let`** – *不安全*的方式。对象所属的集合可能为空，您甚至可以将任意属性附加到对象上。

## `let` 的力量（和危险）

最简单的用法是分配已知属性：

```litex
let a N: a = 2
```

但 `let` 也可以绑定*矛盾的*或不安全的属性：

```litex
let a N: a = 2, a = 3
```

什么？`a` 既是 2 又是 3？是的。在 Litex 中，`let` 故意强大，允许您将**任何**属性绑定到对象上。

为什么有这样的自由？因为当定义**公理**和做出**假设**时，这种灵活性是必不可少的。

例如，空集的存在本身就是一个公理：

```litex
let self_defined_empty_set set: forall x obj => not x $in self_defined_empty_set
```

### 当自定义存在事实为真时声明对象

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

### 通过枚举拥有有限集合

当我们还是孩子时，我们学到的关于数学的第一件事是从 `1` 数到 `5`。因此 Litex 允许您通过枚举定义集合。（不要低估枚举：事实上，我们能够通过枚举定义有限集合的根本原因是由集合论的公理保证的——这是相当深刻的。）

```litex
have set one_to_five := {1,2,3,4,5}
```

如果集合是有限的，那么要证明对于该集合中的每个 x 某个属性成立，我们可以简单地逐个检查每个元素。这样，与无限集合的一般情况不同，结论可以通过直接遍历集合中的所有元素来获得。

```
prove_over_finite_set:
    forall x one_to_five:
        or(x = 1, x = 2, x = 3, x = 4, x = 5)
    prove:

```

如您所见，当没有什么需要证明时，您可以在 `prove` 部分什么都不写（`or(x = 1, x = 2, x = 3, x = 4, x = 5)` 当 x 在 one_to_five 中时立即为真）。

### 拥有作为另一个集合子集的集合，其项目具有某些属性

通常，我们给定一个集合，我们想要获得该集合的一个子集，其项目具有某些属性。即 y∈ {x∈A: P(x) 为真} <=> (y∈A 且 P(y) 为真)。

如何定义 {x∈A: P(x) 为真}？

```litex
prop P(x R)

have set s := x R:
    $P(x)
```

## 使用 `let` 声明对象

在数学中，任何东西都可以被视为*对象*。要在 Litex 中使用对象，您必须首先声明它。

```
let object_name set_name
```

示例：

```litex
let n N
```

这里 `n` 是自然数 `N` 中的一个对象。

* 对象必须在使用前声明。
* 对象名称必须唯一。您不能两次 `let a N`。

您可以一次声明多个对象：

```litex
let n N, m N
```

这等价于：

```litex
let n N
let m N
```

### 共享集合的语法糖

如果多个对象属于同一集合，您可以将它们分组：

```litex
let n, m N
```

这也适用于其他关键字，如 `fn`、`forall` 和 `prop`。

您也可以在一行中混合集合：

```litex
let n, m N, z Z
```

甚至可以在您刚刚定义的集合中声明对象：

```litex
let s set, n s
```

> 注意：顺序很重要——`s` 必须在 `n` 之前声明，否则 Litex 不会知道 `s` 是什么。

## 在声明时添加限制

您可以在声明对象时直接附加事实。

示例：两个自然数 `n` 和 `m`，条件为 `n > 0` 和 `m > n`：

```litex
let n, m N:
    n > 0
    m > n
```

或声明方程组：

```litex
let x, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
```

## 使用 `have` 声明

虽然 `let` 不假设任何东西，但 `have` 需要证明对象的集合是**非空的**。

### 声明非空集合

您可以通过枚举其元素来定义非空集合：

```litex
have set s1 := {1, 2, 3}
```

或通过限制现有域：

```litex
have set s2 := n N:
    n > 0
    n < 4
```

这里 `s1` 明确是有限的，而 `s2` 由条件定义。它们是不同的，尽管两者都恰好描述 `{1, 2, 3}`。

### 从存在命题声明对象

如果您已经证明了存在命题，您可以声明满足它的对象：

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y

know forall y N_pos => $larger_than(y)

let m N_pos

have x st $larger_than(m)

x $in R
x > m
```

这里，`x` 被保证存在，因为 `$larger_than(m)` 已经被证明。

### 在内置集合中声明对象

```litex
have n N, z Z, q Q, r R, c C
```

您也可以在自定义集合中声明对象，前提是您证明集合是非空的：

```litex
let s set
know $exist_in(s)

have n s
```

`exist_in` 是内置的存在命题。实际上：

```
have n s
```

等价于：

```
have n st $exist_in(s)
```

## `let` 和 `have` 的区别

虽然两者都声明对象，但它们在根本方式上不同：

* **`have`**：对象的存在得到保证。Litex 检查集合是非空的。
* **`let`**：不执行存在性检查。您可以声明任何东西——甚至是矛盾的对象——这对假设和公理很有用。

简而言之：

* 当您想要*安全、保证的存在*时使用 **`have`**。
* 当您需要*自由*时使用 **`let`**，即使以安全为代价。

### 有限集合的声明
