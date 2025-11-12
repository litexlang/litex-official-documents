# Mathematical Principles of Litex

statement 
Litex 代码中的语句是程序执行的最小单位，每个语句代表Litex的一个操作。每一段Litex代码都是由很多的litex语句构成的，正如一篇文章有很多句子构成那样。比如`a = 1`表示询问a是否等于1，`have a R = 1`表示定义对象a是一个实数，等于1.

Litex语句分

1. 定义型(definition statement)，如 `prop` 语句用来定义命题

2. 事实型(factual statement)，如 `1 + 1 = 2` 用来询问litex是否`1 + 1`等于2

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

事实型语句，又称逻辑表达式(Logical Expression)，布尔表达式（Boolean Expression）。

1. 特定事实

1.1 普通事实（不涉及存在性）

1.2 存在性事实

2. forall事实

3. or事实

4. intensional set 事实

5. enumeration set 事实

## 证明策略

证明策略的设计，是和一阶逻辑中的关键词、和集合论的公理有对应关系的。比如`not`对应的就是`prove_by_contradiction`，`or`对应`prove_in_each_case`，`prove_by_induction`对应数学归纳法。

1. prove_in_each_case


2. prove_by_contradiction


3. prove_by_enum 


4. prove_in_range


## 辅助关键词

1. know

2. import

3. prove_is_commutative_prop, prove_is_transitive_prop

4. fn_template

5. claim

6. prove