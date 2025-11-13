# Mathematical Principles of Litex

Jiachen Shen, Founder of Litex

_If you define the problem correctly, you almost have the solution._

_- Steve Jobs_

_If you tell people where to go, but not how to get there, you'll be amazed by the results._

_- General George S.Patton_

_Everything should be made as simple as possible, but not simpler._

_- Albert Einstein_

Litex是一门实用主义的语言。它的作者想要设计一套语言，足够直观让所有人都能使用和理解。litex在一边在实现中被设计出来。最终作者找到了一套非常自洽，简单（但不能更简单了），绝对正确的原则来实现整个语言（希望真的如此！）。本章节主要介绍litex的语句，分别对应了哪些常见的数学命题。这是litex的严格性基石，因为litex它忠实地按照这些数学规则是怎么运行的来运行。

statement 
Litex 代码中的语句是程序执行的最小单位，每个语句代表Litex的一个操作。每一段Litex代码都是由很多的litex语句构成的，正如一篇文章有很多句子构成那样。比如`a = 1`表示询问a是否等于1，`have a R = 1`表示定义对象a是一个实数，等于1.

Litex语句分

1. 定义型(definition statement)，如 `prop` 语句用来定义命题

2. 事实型(factual statement)，如 `1 + 1 = 2` 用来询问litex是否`1 + 1`等于2。所有事实型语句

3. 证明策略（prove strategy），如 `prove_by_contradiction`表示用反证法来证明

4. 辅助型(auxiliary statements)，如 `import` 表示引用一个包或文件

## 定义型语句

自然语言中，最基本的句子的写法就是谓词加名词的写法。Litex沿用相似的思路来设计

### 定义谓词

在数学中，谓词是用来做逻辑判断的。比如谓词等于（equals，在数学里的写法是=），就是用来做逻辑判断两个符号是否相等的。除了等号，大于小于，这样最常见的谓词已经被litex内置好了，用户有时候自己想要定义一些谓词。比如我们定义”是正实数“，”是素数“这样子。

自定义谓词主要分两种：非存在性的命题（普通命题），和存在性命题

1. prop 用来定义非存在性的命题

例：

```litex
prop is_positive_real_number(x R):
    x > 0
```

2. exist_prop 用来定义存在性命题

例：

```litex
exist_prop x R st any_real_number_has_another_real_number_than_itself(y R):
    x > y
```

### 定义名词

数学中，名词又称Object（又称，对象）。一句话有名词有动词，才能被做判断正确与否。比如`1 + 1 = 2`这里，谓词是`=`，名词是`1 + 1`和`2`，

有哪些对象？，原子型和函数型

原子型：由单独的第一个单词组成，比如 `1`, `+`, `something`

复合型：语法 对象0(对象1，对象2..., 对象N)。其中对象0是函数名，对象1到对象N是函数的参数。比如`f(1, 2)`的函数名是`f`，参数是`1`和`2`。有时候我们也会把函数名写在参数中间，比如`1 + 2`中的函数名是`+`，参数是`1`和`2`。像加减乘除这样的常见运算符，我们可以写成中缀表示，用户自己定义的函数，尽量写成函数名在头部的格式

有时候函数名也会作为参数传到函数里。比如对函数f求导时，函数f就是求导符号的参数。甚至有时函数名是一个复合型的对象。比如`f(1,2)(3,4)`中，`f(1,2)`的返回值是一个函数，它读入`3`,`4`作为参数。

可见有时我们需要定义原子，有时候需要定义函数以形成复合型的对象

和定义谓词不同，我们定义名词（对象）的时候，需要验证对象的存在性。比如我们不能定义既大于0又小于0的数。

#### 定义对象，并检查存在性

1. have object1, object2 ... st $some_exist_prop(param1, param2...)

2. have object1 nonempty_set

3. have set object1 = {item1, item2, ...}

4. have set object1 = {item parent_set: fact1, fact2, ...}

5. have object1 set_name = item_from_that_set

6. have fn:
    (param1, ...) return_set:
        domain_fact1
        ...
        =>:
            then_fact1
            ...

#### 不检查存在性，直接定义

如果我们需要默认一些东西的存在性（有时这是必要的，比如一个东西的存在是被证明了的，但是你又不想花大力气去用litex把这个东西的存在性自己写出来，想要基于这个已知事实直接开始干自己关心的问题），那就可以用


1. let 定义对象

不证明大于0，小于1的数的存在性，直接定义出来x满足这些条件

```litex
let x R: x > 0, x < 1
```

2. fn 定义函数

不证明是否存在f真的满足f(x) = f(x) ^ 2，直接让f有这些性质（这样的函数其实是存在的，比如f(x) = 1就行）

```litex
fn f(x R) R:
    f(x) = f(x) ^ 2
```

## 事实型语句

事实型语句，又称逻辑表达式(Logical Expression)，布尔表达式（Boolean Expression）。在litex中，所有事实型语句的最终结果是true或unknown, error。在验证事实时，litex会基于一些规则来验证当前的事实是否正确。如果所有规则都没能验证出来，则结果是unknown。（注意：这里有两种情况：1. 如果你这个事实本来就是false的，比如`1 = 2`，litex会告诉你unknown，因为确实不可能找到相应的规则让它正确；2. 如果你这个事实是对的，但你跳步了，那也可能unknown，比如费马大定理被证明是对的，但是因为你跳步了导致litex的规则没法一步步都验证出来，litex也会告诉你unknown。）你可以把litex想象成非常死板，但非常快的的老师，他只能用特定的验证方式来验证事实，不能像人一样有想象力地跳步。

1. 特定事实

1.1 普通事实（不涉及存在性）

1.1.1 等号

本质上，=也是一个prop。但等号的证明比其他prop特殊很多。等号有传递性，交换性这样的一般的prop没有的性质。等号在数学里有独特的地位，因为一旦object1 = object2, 他们就立刻有了彼此的所有性质，他们就“等效”了。任何其他prop，都不可能有这样的效果。不管是证明等号，还是用两个object相等这个性质去证明有关这两个object的其他性质，Litex都提供了非常强大的支持。

1.1.2 非等号

```litex
17 > 2
prop larger_than(x, y R):
    x > y
$larger_than(17, 2)
```

例如 `17 > 2` 这样的prop是内置的prop。我们也可以自己定义prop，比如 `$larger_than(17, 2)` 表示17大于2。

1.2 存在性事实

```litex
exist_prop x R st larger_than(y R):
    x > y
exist 17 st $larger_than(1)
```

例如 如 `exist 17 R st $exist_number_larger_than(1)` 表示存在17这个数，它比1大

如果之前证明过了 `exist ... st $some_exist_prop(param1, ...)`，那么`$some_exist_prop(param1, ...)`就被自动证明了。之后可以配合 `have xxx, ... st $some_exist_prop(param1, ...)` 来声明一个对象xxx...，它满足`$some_exist_prop(param1, ...)`。

2. forall事实

3. or事实

4. intensional set 事实

5. enumeration set 事实

6. 连续等于

object1 = object2 = object3 = ... = objectN = objectN_plus_1

这其实是 object1 = object2, object2 = object3, ... , objectN-1 = objectN 的简写。在运行的时候，先验证第一个等号：object1 = object2，再验证第二个等号 object3 = object2, 如果没证明出来就 object3 = object1, 如果还是没证明出来就是unknown。同理，证明第N个等号时，我们一次证明 ObjectN_plus_1 等于 Object, Object2, ..., ObjectN。只要某个等号被证明出来了，我们就认为 object1 = objectN_plus_1 被证明出来了。如果全部都没有证明出来，就是unknown。

### Notes

注意到litex和python的区别。litex如果你一个语句是true，那么这个true是不可能作为后面的语句的参数而出现的。这个true只是告诉litex能继续验证下去（如果一个语句不是true，是unknown或者error，那litex就不会继续验证下去了）。python如果你一个语句是true，那么这个true可以作为后面的语句的参数而出现。比如`a = 1 == 1\nprint(a)`。可以看到litex，或者说数学，和python的思维方式是有区别的。

## 证明策略

证明策略的设计，是和一阶逻辑中的关键词、和集合论的公理有对应关系的。比如`not`对应的就是`prove_by_contradiction`，`or`对应`prove_in_each_case`，`prove_by_induction`对应数学归纳法。

1. prove_in_each_case

对应一阶逻辑的or

2. prove_by_contradiction

对应一阶逻辑的not

3. prove_by_enum 

对应集合论公理中的用枚举法定义一个集合

4. prove_in_range

对应整数的序关系和枚举的关系。比如如果`x > 1, x < 10`，那么x只可能是2,3,4,5,6,7,8,9。它的另一一个意义是让重复性很强的证明过程更简洁。比如你要证明997是素数，那就要一个个地写`997 % 2 = 1, 997 % 2 != 0`，写上几百个后，就能知道forall x N: x >= 2 => 997 % x != 0。这写起来太麻烦了，prove_in_range就是为了解决这个问题。

## 辅助关键词

1. know

know 的意义主要有

1. 定义公理和不言自明的定义。比如并集这个概念，是集合论的公理。按照它的定义`forall a, b set: forall x a => x $in union(a, b)`。那么我们就可以写`know forall a, b set: forall x a => x $in union(a, b)`。

2. 假设一个事实，但不证明它。比如你要用费马大定理来证明一个事实，但是又不想证明费马大定理，那就用know直接让它成立

3. 默认一些事实，让证明先暂时能通过，未来想到这个事实的证明的时候再把know换掉

4. 如果我们是想证明有特定性质的东西的性质的时候，比如我们像证明一个大于1小于3的数一定大于0小于5，那么我们写`have x R\nknow x > 1, x < 3`。这样litex就能知道x大于1小于3，然后继续证明x大于0小于5。但这其实不是最好的写法，因为这里的know污染了整个环境。更好的写法是`prove forall x R: x > 1, x < 3 => x > 0, x < 5:\n...`。因为这样哪怕forall里的条件是有问题的，那这也不会影响大环境，因为大环境里不会有任何对象满足这些forall条件。比如说我们想要证明一个同时等于1和2的数，它同时等于1和2，那么这种条件显然就是错的，你在大环境里写`know x = 1, x = 2`，litex就会认为x同时等于1和2，然后`1=2`就能被证明了，这很不好；更好的方式是`prove forall x R: x = 1, x = 2 => x = 1, x = 2:\n...`。因为这样哪怕forall里的条件是有问题的，那这也不会影响大环境，因为大环境里不会有任何对象满足这些forall条件，哪怕这个事实`forall x R: x = 1, x = 2 => x = 1, x = 2`被证明是对的，它也不会被任何litex的验证规则利用上来证明进一步的事实。

2. import



3. prove_is_commutative_prop, prove_is_transitive_prop

4. fn_template

5. claim

6. prove

## Thanks