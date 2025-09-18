# 命题：逻辑的动词

命题是可以为真或假的东西——它是一个一般语句形式，通常涉及变量或占位符。事实语句是一个命题，其中所有变量都被具体值替换（或以其他方式完全指定），以便其真值在给定上下文中确定。

例如

```litex
have human nonempty_set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

`intelligent` 是一个命题。`$intelligent(Jordan)` 是一个事实语句。（`$` 用于区分特定事实和函数）

另一个例子是：在 `1 > 0` 中，`1 > 0` 是一个事实语句，`>` 是一个命题。事实语句可以为真或假，但不能同时为真和假。事实语句 `1 > 0` 为真。事实语句 `0 > 1` 为假。

这样思考：在日常表达中，有主语和谓语；而在推理语言中，*命题*像动词一样起作用，其参数是主语。这个动作的结果只能是**真、未知、错误或假**。

命题的完整定义是：

```
prop propName(parameter1 set1, parameter2 set2, ...):
    domFact1
    domFact2
    ...
    <=>:
        iffFact1
        iffFact2
        ...
```

或者您可以在第一行写 `dom`：

```
prop propName(parameter1 set1, parameter2 set2, ...):
    dom:
        domFact1
        domFact2
        ...
    <=>:
        iffFact1
        iffFact2
        ...
```

它读作：propName 接受 set1 中的 parameter1，set2 中的 parameter2，...，参数必须满足 domFact1，domFact2，...。当参数的要求得到满足时，$propName(parameter1, parameter2, ...) 为真当且仅当 iffFact1，iffFact2，... 都为真。

当没有域事实时，您可以隐藏 `<=>`：

```
prop propName(parameter1 set1, parameter2 set2, ...):
    iffFact1
    iffFact2
    ...
```

有时我们只想声明一个命题而不指定它等价于什么事实。您可以写

```
prop propName(parameter1 set1, parameter2 set2, ...)
```

例如，我们声明一个命题 `p`，在几行代码后我们为它设置等价事实。注意这并不意味着任何东西都可以导致这个命题。

```litex
prop sum_larger_than_0(x, y R)

# ... lines of code

know forall x, y R => $sum_larger_than_0(x, y) <=> x + y > 0
```

此外，您可以在声明时指定命题的域而不指定其等价定义。稍后，您可以添加等价定义。

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0

# ... lines of code

know forall x, y, z R: x > 0, y > 0, z > 0 => $can_form_a_triangle(x, y, z) <=> x + y > z, x + z > y, y + z > x
```

在 Litex 中，`dom` 对应于数学写作中的"域"。它指定允许传递给命题的参数范围。

在日常数学写作中，我们通常将定义放在一行上。Litex 允许您这样做，这为您节省了很多行。以下是一些示例：

```litex
prop p(x, y R)
prop p3(x, y R) <=> x > y
prop p4(x, y R): x > y <=> x + y > 10
```
等价的多行版本这样写：

```litex
prop p(x, y R)
prop p3(x, y R):
    x > y
prop p4(x, y R):
    x > y
    <=>:
        x + y > 10
```

当我们知道或证明一个事实为真时，Litex 自动知道所有等价事实都为真。例如：

当 `$transitivity_of_less(a, b, c)` 为真时，Litex 自动推断所有在逻辑上等价于它的事实。

在这个例子中，`$transitivity_of_less_operator(x, y, z)` 声明 `x < z` 等价于 `x < y` 和 `y < z` 为真。通过替换 `x = a`，`y = b`，和 `z = c`，我们得到 `a < c`。由于 Litex 知道这两个语句是等价的，`a < c` 被自动建立。

这种等价事实的自动推导是 Litex 的基本特征。没有它，即使我们有像

```
forall a, b, c R: a < b, b < c => a < c
```

这样的语句，我们也无法在某些情况下直接证明 `a < c`——因为我们可能不知道正在使用哪个特定的 `b` 来满足全称语句。

通过为 `forall` 语句分配名称并通过该命题名称验证它，Litex 然后可以自动得出结论所有等价事实，确保像 `a < c` 这样的结果立即被知道。

另一个例子是关于三角不等式的：

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0
    <=>:
        x + y > z
        x + z > y
        y + z > x
```

## 声明空命题

此外，您可以声明一个没有任何逻辑但只有名称的命题，如下行所示，这意味着 `N_pos` 中的 `x`、`y`、`z` 在任何情况下都能形成三角形。显然，根据我们的知识，这个命题是假的。但您仍然可以声明它。

```litex
prop can_form_a_triangle(x, y, z N_pos)
```

当然，您可以声明一个只有额外限制而没有逻辑的命题，如下行所示，它表达了与上述行类似的含义：

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0
```

> 注意：如果您的命题中只有 dom，您不能再隐藏 `dom`。否则 Litex 会误解您的行与只有 `iff` 的命题情况。

## 调用命题

声明命题后，您可以在任何地方用前缀 `$` 调用它：

```litex
prop can_form_a_triangle(x, y, z R):
    x > 0
    y > 0
    z > 0
    <=>:
        x + y > z
        x + z > y
        y + z > x

$can_form_a_triangle(3, 4, 5)
```

如果命题声明中只有两个对象在括号中，您也可以这样调用它：

```litex
prop divisible_by(n, m R):
    m != 0
    <=>:
        n % m = 0

6 $divisible_by 3
```

## 一个例子

我们已经知道如何声明新对象和命题，这里是一个完整的例子，带您走过我们已经知道的内容。以下示例显示了传递性、交换性、自反性（这是关系的最基本属性）如何在 Litex 中形式化。

```litex
let happy_baby_characters set
let little_little_monster, big_big_monster, boss, happy_superman happy_baby_characters

# Transitivity
prop is_leader_of(x, y happy_baby_characters)
know big_big_monster $is_leader_of little_little_monster, boss $is_leader_of big_big_monster
prop is_leader_is_transitive(x, y, z happy_baby_characters):
    x $is_leader_of y
    y $is_leader_of z
    <=>:
        x $is_leader_of z
know forall x, y, z happy_baby_characters: x $is_leader_of y, y $is_leader_of z => $is_leader_is_transitive(x, y, z)
$is_leader_is_transitive(boss, big_big_monster, little_little_monster)
boss $is_leader_of little_little_monster

# Commutativity
prop is_enemy_of(x, y happy_baby_characters)
know forall x, y happy_baby_characters => x $is_enemy_of y <=> y $is_enemy_of x; happy_superman $is_enemy_of big_big_monster
big_big_monster $is_enemy_of happy_superman

# Reflexivity
prop is_friend_of(x, y happy_baby_characters)
know forall x happy_baby_characters => x $is_friend_of x
little_little_monster $is_friend_of little_little_monster
```

如您所见，这个例子并不那么"数学"。推理在我们的生活中无处不在，无时无刻不在发生！
