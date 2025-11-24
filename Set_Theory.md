# How Litex Corresponds to Peano Axioms, ZFC Axioms and Other Mathematical Principles

This document demonstrates how Litex statements correspond to mathematical statements, establishing that Litex's design is grounded in rigorous mathematical foundations. The mathematical principles presented here are essential knowledge for anyone interested in understanding how mathematics works, as well as for all undergraduate mathematics students. Readers will discover that the rich and diverse world of mathematics is actually built from a small set of axioms and inference rules.

We reference Chapters 2 and 3 of Terence Tao's *Analysis I*, which provides an excellent introduction to the foundations of mathematics for beginners. [Analysis I](https://tiu-edu.uz/media/books/2024/05/28/1664976801.pdf)

# Natural Numbers

**Definition: Natural Numbers**

The set of natural numbers $\mathbf{N}$ consists of all non-negative integers: $\mathbf{N} := \{0, 1, 2, 3, 4, \ldots\}$. Each element of this set is called a natural number.

**Litex对应**：
- **关键词**：`N`（内置集合）
- **表达式**：`N` 是Litex的内置自然数集合
- **示例**：
```litex
have n N
n $in N
0 $in N
1 $in N
```
- **说明**：`N`是Litex的内置关键字，表示自然数集合，包含0, 1, 2, 3, ...

**Axiom: Successor**

For any natural number $n$, its successor $n++$ (or $n+1$) is also a natural number. In symbols: $n \in \mathbf{N} \implies n++ \in \mathbf{N}$.

**Litex对应**：
- **关键词**：内置算术运算
- **表达式**：`forall n N => n + 1 $in N`
- **示例**：
```litex
have n N
n + 1 $in N
```
- **说明**：Litex中自然数的后继运算通过`+ 1`表示，这是内置的算术运算

**Definition: Natural Number Notation**

We define natural numbers recursively: $1 := 0++$, $2 := 1++$, $3 := 2++$, and so on. Each natural number is the successor of the previous one.

**Litex对应**：
- **关键词**：数字字面量，内置算术
- **表达式**：数字`1`, `2`, `3`等是内置字面量
- **示例**：
```litex
1 = 0 + 1
2 = 1 + 1
3 = 2 + 1
```
- **说明**：Litex直接支持数字字面量，这些数字的自然数性质是内置的

**Axiom: Zero is Not a Successor**

Zero is not the successor of any natural number. For every natural number $n$, we have $n++ \neq 0$. In symbols: $\forall n \in \mathbf{N}, n++ \neq 0$.

**Litex对应**：
- **关键词**：`forall`, `!=`
- **表达式**：`forall n N => n + 1 != 0`
- **示例**：
```litex
know forall n N => n + 1 != 0
```
- **说明**：这是自然数的基本性质，可以通过`know`声明为公理

**Axiom: Injectivity of Successor**

Different natural numbers have different successors. If $n \neq m$ for natural numbers $n$ and $m$, then $n++ \neq m++$. Equivalently, if two natural numbers have the same successor, then they must be equal: $n++ = m++ \implies n = m$. In symbols: $\forall n, m \in \mathbf{N}, (n \neq m \implies n++ \neq m++) \iff (n++ = m++ \implies n = m)$.

**Litex对应**：
- **关键词**：`forall`, `=>`, `<=>`, `=`, `!=`
- **表达式**：`forall n, m N: (n != m => n + 1 != m + 1) <=> (n + 1 = m + 1 => n = m)`
- **示例**：
```litex
know forall n, m N: (n != m => n + 1 != m + 1) <=> (n + 1 = m + 1 => n = m)
```
- **说明**：这是自然数后继的唯一性公理

**Axiom: Mathematical Induction**

If a property $P(n)$ holds for $n=0$, and whenever it holds for some natural number $n$, it also holds for $n++$, then $P(n)$ holds for all natural numbers $n$. In symbols: $(P(0) \land (\forall n \in \mathbf{N}, P(n) \implies P(n++))) \implies (\forall n \in \mathbf{N}, P(n))$.

**Litex对应**：
- **关键词**：`prove_by_induction`
- **表达式**：`prove_by_induction($prop(x, n), n, base_case)`
- **示例**：
```litex
prop p(x R, n N)
let x R
know $p(x, 0)
know forall n N: $p(x, n) => $p(x, n + 1)

prove_by_induction($p(x, n), n, 0)
```
- **说明**：`prove_by_induction`是Litex内置的数学归纳法证明策略

**Assumption: Existence of Natural Numbers**

We assume that there exists a set $\mathbf{N}$ satisfying all the axioms above. The elements of this set are called natural numbers.

**Litex对应**：
- **关键词**：`N`（内置）
- **表达式**：`N`是Litex的内置集合，满足所有自然数公理
- **示例**：
```litex
N $in set
0 $in N
```
- **说明**：`N`是Litex的内置集合，其存在性和性质由系统保证

**Definition: Addition**

Addition of natural numbers is defined recursively. For any natural number $m$, we define $0 + m := m$. If we have defined $n + m$, then we define $(n++) + m := (n + m)++$. In symbols: $0 + m := m$; $(n++) + m := (n + m)++$.

**Litex对应**：
- **关键词**：`+`（内置运算符）
- **表达式**：加法是Litex的内置运算
- **示例**：
```litex
have m N
0 + m = m
have n N
(n + 1) + m = (n + m) + 1
```
- **说明**：`+`是Litex的内置算术运算符，满足自然数加法的递归定义

**Definition: Positive Natural Numbers**

A natural number $n$ is positive if and only if it is not equal to 0. In symbols: $n > 0 \iff n \neq 0$.

**Litex对应**：
- **关键词**：`>`, `!=`, `N_pos`
- **表达式**：`n > 0 <=> n != 0`，或使用内置集合`N_pos`
- **示例**：
```litex
have n N
n > 0 <=> n != 0

# 或使用内置集合
have n N_pos
n > 0
```
- **说明**：`N_pos`是Litex的内置集合，表示正自然数

**Definition: Ordering of Natural Numbers**

For natural numbers $n$ and $m$, we say $n$ is greater than or equal to $m$ (written $n \geq m$ or $m \leq n$) if there exists a natural number $a$ such that $n = m + a$. We say $n$ is strictly greater than $m$ (written $n > m$ or $m < n$) if $n \geq m$ and $n \neq m$. In symbols: $n \geq m \iff \exists a \in \mathbf{N}, n = m + a$; $n > m \iff (n \geq m) \land (n \neq m)$.

**Litex对应**：
- **关键词**：`>=`, `>`, `exist`, `=`
- **表达式**：`n >= m <=> exist a N: n = m + a`; `n > m <=> (n >= m), (n != m)`
- **示例**：
```litex
have n, m N
n >= m <=> exist a N: n = m + a
n > m <=> (n >= m), (n != m)
```
- **说明**：`>=`和`>`是Litex的内置比较运算符

**Definition: Multiplication**

Multiplication of natural numbers is defined recursively. For any natural number $m$, we define $0 \times m := 0$. If we have defined $n \times m$, then we define $(n++) \times m := (n \times m) + m$. In symbols: $0 \times m := 0$; $(n++) \times m := (n \times m) + m$.

**Litex对应**：
- **关键词**：`*`（内置运算符）
- **表达式**：乘法是Litex的内置运算
- **示例**：
```litex
have m N
0 * m = 0
have n N
(n + 1) * m = (n * m) + m
```
- **说明**：`*`是Litex的内置算术运算符，满足自然数乘法的递归定义

**Definition: Exponentiation**

Exponentiation for natural numbers is defined recursively. For any natural number $m$, we define $m^0 := 1$ (in particular, $0^0 := 1$). If $m^n$ has been defined, then we define $m^{n++} := m^n \times m$. In symbols: $m^0 := 1$ (in particular, $0^0 := 1$); $m^{n++} := m^n \times m$.

**Litex对应**：
- **关键词**：`^`（内置运算符）
- **表达式**：幂运算是Litex的内置运算
- **示例**：
```litex
have m N
m ^ 0 = 1
0 ^ 0 = 1
have n N
m ^ (n + 1) = (m ^ n) * m
```
- **说明**：`^`是Litex的内置幂运算符，满足自然数幂的递归定义

# Set Theory

**Definition: Sets**

A set is an unordered collection of objects. For example, $\{3,8,5,2\}$ is a set. If $x$ is an object and $A$ is a set, we say $x$ is an element of $A$ (written $x \in A$) if $x$ belongs to the collection; otherwise we say $x \not\in A$.

**Litex对应**：
- **关键词**：`set`, `$in`, `have set`
- **表达式**：`have set A = {item1, item2, ...}` 或 `have set A = {x parent_set: fact1, ...}`
- **示例**：
```litex
# 枚举定义集合
have set A = {3, 8, 5, 2}
have x A
x $in A

# 或使用not
not x $in A
```
- **说明**：`set`是Litex的内置关键字，`$in`是成员关系谓词

**Axiom: Sets are Objects**

Every set is also an object. This means that sets can be elements of other sets. For any sets $A$ and $B$, it is meaningful to ask whether $A \in B$. In symbols: $A$ is a set $\implies A$ is an object.

**Litex对应**：
- **关键词**：`set`, `obj`, `$in`
- **表达式**：`forall s set => s $in obj`
- **示例**：
```litex
know forall s set => s $in obj

have set A
A $in obj
have set B
A $in B  # 可以询问A是否是B的元素
```
- **说明**：在Litex中，集合也是对象，可以成为其他集合的元素

**Definition: Equality of Sets**

Two sets $A$ and $B$ are equal (written $A = B$) if and only if they contain exactly the same elements. That is, every element of $A$ is an element of $B$, and every element of $B$ is an element of $A$. In symbols: $A = B \iff (\forall x, x \in A \iff x \in B)$.

**Litex对应**：
- **关键词**：`=`, `forall`, `$in`, `<=>`
- **表达式**：`forall A, B set: A = B <=> (forall x A => x $in B), (forall x B => x $in A)`
- **示例**：
```litex
know:
    forall A, B set:
        A = B
        <=>:
            forall x A:
                x $in B
            forall x B:
                x $in A
```
- **说明**：集合相等通过外延公理定义，这是Litex内置的等号语义

**Axiom: Empty Set**

There exists a set $\emptyset$ (called the empty set) that contains no elements. For every object $x$, we have $x \not\in \emptyset$. In symbols: $\exists \emptyset, \forall x, x \not\in \emptyset$.

**Litex对应**：
- **关键词**：`have set`, `{}`, `exist`, `not`, `$in`
- **表达式**：`have set empty_set = {}` 或 `exist empty_set set: forall x obj => not x $in empty_set`
- **示例**：
```litex
# 通过枚举定义空集
have set empty_set = {}

# 或通过存在性公理
know @exist empty_set set st exist_empty_set():
    =>:
        forall x obj:
            not x $in empty_set
```
- **说明**：空集可以通过枚举`{}`定义，也可以通过存在性公理声明

**Axiom: Singleton and Pair Sets**

For any object $a$, there exists a set $\{a\}$ (called a singleton set) containing only $a$. For any objects $a$ and $b$, there exists a set $\{a,b\}$ (called a pair set) containing exactly $a$ and $b$. In symbols: $\forall a, \exists \{a\}, \forall y, (y \in \{a\} \iff y = a)$; $\forall a, b, \exists \{a,b\}, \forall y, (y \in \{a,b\} \iff (y = a \lor y = b))$.

**Litex对应**：
- **关键词**：`have set`, `{}`, `or`, `=`
- **表达式**：`have set s = {a}` 或 `have set s = {a, b}`
- **示例**：
```litex
# 单元素集合
have a obj
have set singleton = {a}
have y singleton
y = a

# 双元素集合
have a, b obj
have set pair = {a, b}
have y pair
y = a or y = b
```
- **说明**：通过枚举法定义集合，对应配对公理

**Axiom: Pairwise Union**

For any two sets $A$ and $B$, there exists a set $A \cup B$ (called the union of $A$ and $B$) whose elements are all objects that belong to $A$ or $B$ (or both). In symbols: $\forall A, B, \exists A \cup B, \forall x, (x \in A \cup B \iff (x \in A \lor x \in B))$.

**Litex对应**：
- **关键词**：`union`, `or`, `$in`
- **表达式**：`union(A, B)` 或通过函数定义
- **示例**：
```litex
# 通过know声明并集公理
know forall A, B set: forall x A => x $in union(A, B)
know forall A, B set: forall x B => x $in union(A, B)

# 使用
have set A, set B
have x union(A, B)
x $in A or x $in B
```
- **说明**：并集可以通过`know`声明为公理，或通过函数定义

**Axiom: Specification (Separation)**

For any set $A$ and any property $P(x)$, there exists a set $\{x \in A : P(x)\}$ whose elements are exactly those elements $x$ of $A$ for which $P(x)$ is true. In symbols: $\forall A, \exists \{x \in A : P(x)\}, \forall y, (y \in \{x \in A : P(x)\} \iff (y \in A \land P(y)))$.

**Litex对应**：
- **关键词**：`have set`, `{x parent_set: fact1, ...}`, `prop`
- **表达式**：`have set s = {x A: $P(x)}`
- **示例**：
```litex
have set A
prop P(x A)

have set s = {x A: $P(x)}
have y s
y $in A
$P(y)
```
- **说明**：分离公理通过Litex的内涵集合定义语法直接实现

**Definition: Subsets**

For sets $A$ and $B$, we say $A$ is a subset of $B$ (written $A \subseteq B$) if every element of $A$ is also an element of $B$. We say $A$ is a proper subset of $B$ (written $A \subsetneq B$) if $A \subseteq B$ and $A \neq B$. In symbols: $A \subseteq B \iff (\forall x, x \in A \implies x \in B)$; $A \subsetneq B \iff (A \subseteq B \land A \neq B)$.

**Litex对应**：
- **关键词**：`$is_subset_of`, `forall`, `=>`, `!=`
- **表达式**：`A $is_subset_of B <=> forall x A => x $in B`; `A $is_proper_subset_of B <=> (A $is_subset_of B), (A != B)`
- **示例**：
```litex
have set A, set B
A $is_subset_of B <=> forall x A => x $in B

# 真子集
A $is_proper_subset_of B <=> (A $is_subset_of B), (A != B)
```
- **说明**：子集关系可以通过谓词定义，或使用内置的`$is_subset_of`

**Definition: Intersection**

The intersection of two sets $S_1$ and $S_2$, denoted $S_1 \cap S_2$, is the set of all elements that belong to both $S_1$ and $S_2$. In symbols: $S_1 \cap S_2 := \{x \in S_1 : x \in S_2\}$; $x \in S_1 \cap S_2 \iff (x \in S_1 \land x \in S_2)$.

**Litex对应**：
- **关键词**：`have set`, `{x parent_set: fact}`, `$in`
- **表达式**：`have set intersection = {x S1: x $in S2}`
- **示例**：
```litex
have set S1, set S2
have set intersection = {x S1: x $in S2}
have y intersection
y $in S1
y $in S2
```
- **说明**：交集通过分离公理（内涵集合定义）实现

**Definition: Set Difference**

For sets $A$ and $B$, the set difference $A \setminus B$ (also written $A - B$) is the set of all elements of $A$ that do not belong to $B$. In symbols: $A \setminus B := \{x \in A : x \not\in B\}$; $x \in A \setminus B \iff (x \in A \land x \not\in B)$.

**Litex对应**：
- **关键词**：`have set`, `{x parent_set: not fact}`, `not`, `$in`
- **表达式**：`have set difference = {x A: not x $in B}`
- **示例**：
```litex
have set A, set B
have set difference = {x A: not x $in B}
have y difference
y $in A
not y $in B
```
- **说明**：差集通过分离公理和否定实现

**Definition: Functions**

A function $f : X \to Y$ from set $X$ to set $Y$ is defined by a property $P(x,y)$ such that for every $x \in X$, there is exactly one $y \in Y$ for which $P(x,y)$ is true. The function $f$ assigns to each input $x \in X$ the unique output $f(x) \in Y$ satisfying $P(x,f(x))$. In symbols: $f : X \to Y$; $\forall x \in X, \exists! y \in Y, P(x,y)$; $y = f(x) \iff P(x,y)$.

**Litex对应**：
- **关键词**：`have fn`, `fn`, `prop`, `exist_prop`
- **表达式**：`have fn f(x X) Y` 或通过`exist_prop`定义
- **示例**：
```litex
# 通过have fn定义函数
have fn f(x X) Y
# 函数满足唯一性：forall x X => exist! y Y: y = f(x)

# 或通过exist_prop定义
prop P(x X, y Y)
know forall x X => exist! y Y: $P(x, y)
have fn f(x X) Y:
    $P(x, f(x))
```
- **说明**：函数定义需要证明存在性和唯一性，`have fn`会检查这些条件

**Definition: Equality of Functions**

Two functions $f : X \to Y$ and $g : X \to Y$ with the same domain and range are equal (written $f = g$) if and only if they agree on all inputs: $f(x) = g(x)$ for all $x \in X$. In symbols: $f = g \iff (\forall x \in X, f(x) = g(x))$.

**Litex对应**：
- **关键词**：`=`, `forall`
- **表达式**：`f = g <=> forall x X => f(x) = g(x)`
- **示例**：
```litex
have fn f(x X) Y
have fn g(x X) Y
f = g <=> forall x X => f(x) = g(x)
```
- **说明**：函数相等通过外延性定义，这是Litex内置的等号语义

**Definition: Function Composition**

For functions $f : X \to Y$ and $g : Y \to Z$, the composition $g \circ f : X \to Z$ is defined by $(g \circ f)(x) := g(f(x))$ for all $x \in X$.

**Litex对应**：
- **关键词**：`have fn`, 函数复合
- **表达式**：`have fn composition(x X) Z = g(f(x))`
- **示例**：
```litex
have fn f(x X) Y
have fn g(y Y) Z
have fn composition(x X) Z = g(f(x))
```
- **说明**：函数复合通过函数定义和函数调用实现

**Definition: Injective Functions**

A function $f : X \to Y$ is injective (or one-to-one) if different inputs produce different outputs: $x \neq x' \implies f(x) \neq f(x')$. Equivalently, $f$ is injective if $f(x) = f(x') \implies x = x'$. In symbols: $f$ is injective $\iff (\forall x, x' \in X, x \neq x' \implies f(x) \neq f(x')) \iff (\forall x, x' \in X, f(x) = f(x') \implies x = x')$.

**Litex对应**：
- **关键词**：`prop`, `forall`, `=>`, `=`, `!=`
- **表达式**：`prop is_injective(f fn(X, Y)): forall x, x' X: f(x) = f(x') => x = x'`
- **示例**：
```litex
have fn f(x X) Y
prop is_injective(f fn(X, Y)):
    forall x, x' X:
        f(x) = f(x')
        =>:
            x = x'
```
- **说明**：单射性可以通过命题定义

**Definition: Surjective Functions**

A function $f : X \to Y$ is surjective (or onto) if every element of $Y$ is the image of some element of $X$. That is, for every $y \in Y$, there exists $x \in X$ such that $f(x) = y$. In symbols: $f$ is surjective $\iff f(X) = Y \iff (\forall y \in Y, \exists x \in X, f(x) = y)$.

**Litex对应**：
- **关键词**：`prop`, `forall`, `exist`, `=`
- **表达式**：`prop is_surjective(f fn(X, Y)): forall y Y => exist x X: f(x) = y`
- **示例**：
```litex
have fn f(x X) Y
prop is_surjective(f fn(X, Y)):
    forall y Y:
        =>:
            exist x X: f(x) = y
```
- **说明**：满射性可以通过命题和存在量词定义

**Definition: Bijective Functions**

A function $f : X \to Y$ is bijective (or invertible) if it is both injective and surjective. In symbols: $f$ is bijective $\iff (f$ is injective $\land f$ is surjective$)$.

**Litex对应**：
- **关键词**：`prop`, `,`（合取）
- **表达式**：`prop is_bijective(f fn(X, Y)): $is_injective(f), $is_surjective(f)`
- **示例**：
```litex
have fn f(x X) Y
prop is_bijective(f fn(X, Y)):
    $is_injective(f)
    $is_surjective(f)
```
- **说明**：双射是单射和满射的合取

**Definition: Image of a Set**

For a function $f : X \to Y$ and a subset $S \subseteq X$, the image of $S$ under $f$ is the set $f(S) := \{f(x) : x \in S\}$. This set is a subset of $Y$.

**Litex对应**：
- **关键词**：`have set`, `{f(x): x parent_set}`
- **表达式**：`have set image = {f(x): x S}`（需要替换公理支持）
- **示例**：
```litex
have fn f(x X) Y
have set S = {x X: ...}
# 通过替换公理定义像集（目前需要通过know假设）
know exist set image: forall y Y => (y $in image <=> exist x S: f(x) = y)
```
- **说明**：像集的定义需要替换公理，Litex目前暂不支持，但可以通过`know`假设

**Definition: Inverse Image**

For a function $f : X \to Y$ and a subset $U \subseteq Y$, the inverse image of $U$ under $f$ is the set $f^{-1}(U) := \{x \in X : f(x) \in U\}$. In symbols: $f(x) \in U \iff x \in f^{-1}(U)$.

**Litex对应**：
- **关键词**：`have set`, `{x parent_set: fact}`
- **表达式**：`have set inverse_image = {x X: f(x) $in U}`
- **示例**：
```litex
have fn f(x X) Y
have set U = {y Y: ...}
have set inverse_image = {x X: f(x) $in U}
have z inverse_image
f(z) $in U
```
- **说明**：逆像通过分离公理（内涵集合定义）实现

**Axiom: Power Set (Function Space)**

For sets $X$ and $Y$, there exists a set $Y^X$ consisting of all functions from $X$ to $Y$. A function $f$ belongs to $Y^X$ if and only if $f : X \to Y$. In symbols: $\forall X, Y, \exists Y^X, \forall f, (f \in Y^X \iff (f : X \to Y))$.

**Litex对应**：
- **关键词**：`fn_template`, `$in`
- **表达式**：`fn_template power_set(X set, Y set): fn (x X) Y`
- **示例**：
```litex
have set X, set Y
fn_template power_set(X set, Y set):
    fn (x X) Y

have fn f(x X) Y
f $in power_set(X, Y)
```
- **说明**：幂集公理通过`fn_template`实现，表示所有从X到Y的函数集合

**Axiom: Union**

For any set $A$ whose elements are themselves sets, there exists a set $\bigcup A$ whose elements are all objects that belong to at least one element of $A$. In symbols: $\forall A, \exists \bigcup A, \forall x, (x \in \bigcup A \iff (\exists S \in A, x \in S))$.

**Litex对应**：
- **关键词**：`union`, `exist`, `$in`
- **表达式**：`union(A)` 或通过函数定义
- **示例**：
```litex
# 通过know声明并集公理
know forall A set: forall x A => (x $in set => forall y x => y $in union(A))

# 使用
have set A
have x union(A)
exist S A: x $in S
```
- **说明**：广义并集可以通过`know`声明为公理，或通过函数定义

**Definition: Ordered Pair**

An ordered pair $(x,y)$ is an object with $x$ as its first component and $y$ as its second component. Two ordered pairs are equal if and only if their corresponding components are equal: $(x,y) = (x',y') \iff (x = x' \land y = y')$.

**Litex对应**：
- **关键词**：函数调用语法 `(x, y)` 或通过函数定义
- **表达式**：有序对可以通过函数或元组语法表示
- **示例**：
```litex
# 有序对可以通过函数表示
have fn pair(x obj, y obj) obj
know forall x, y, x', y' obj: pair(x, y) = pair(x', y') <=> (x = x'), (y = y')

# 或使用内置语法（如果支持）
have x, y obj
(x, y) = (x', y') <=> (x = x'), (y = y')
```
- **说明**：有序对可以通过函数定义，或使用Litex的内置元组语法（如果支持）

**Definition: Cartesian Product**

For sets $X$ and $Y$, the Cartesian product $X \times Y$ is the set of all ordered pairs $(x,y)$ where $x \in X$ and $y \in Y$. In symbols: $X \times Y := \{(x,y) : x \in X, y \in Y\}$; $a \in (X \times Y) \iff (\exists x \in X, \exists y \in Y, a = (x,y))$.

**Litex对应**：
- **关键词**：`have set`, `{pair(x, y): x X, y Y}`, `exist`
- **表达式**：`have set cartesian_product = {pair(x, y): x X, y Y}`（需要替换公理）
- **示例**：
```litex
have set X, set Y
# 通过替换公理定义笛卡尔积（目前需要通过know假设）
know exist set cartesian_product: forall a obj => (a $in cartesian_product <=> exist x X, exist y Y: a = pair(x, y))
```
- **说明**：笛卡尔积的定义需要替换公理，Litex目前暂不支持，但可以通过`know`假设

**Definition: Ordered $n$-tuple and $n$-fold Cartesian Product**

For a natural number $n$, an ordered $n$-tuple $(x_1, \ldots, x_n)$ is a collection of $n$ objects. Two $n$-tuples are equal if and only if all their corresponding components are equal: $(x_i)_{1 \leq i \leq n} = (y_i)_{1 \leq i \leq n} \iff (\forall 1 \leq i \leq n, x_i = y_i)$.

For sets $X_1, \ldots, X_n$, their Cartesian product $\prod_{i=1}^n X_i$ (also written $X_1 \times \ldots \times X_n$) is the set of all $n$-tuples $(x_1, \ldots, x_n)$ where $x_i \in X_i$ for all $1 \leq i \leq n$. In symbols: $\prod_{1 \leq i \leq n} X_i := \{(x_i)_{1 \leq i \leq n} : x_i \in X_i \text{ for all } 1 \leq i \leq n\}$.

**Litex对应**：
- **关键词**：函数，`forall`, `=`
- **表达式**：n元组可以通过函数表示，n重笛卡尔积需要替换公理
- **示例**：
```litex
# n元组可以通过函数表示
have fn tuple(n N, i N_pos: i <= n) obj
know forall n N, x1, ..., xn obj, y1, ..., yn obj: 
    tuple(n, 1) = x1, ..., tuple(n, n) = xn,
    tuple(n, 1) = y1, ..., tuple(n, n) = yn
    =>:
        (forall i N_pos: i <= n => tuple(n, i) = tuple(n, i)) <=> (x1 = y1, ..., xn = yn)

# n重笛卡尔积（需要替换公理）
know exist set product: forall a obj => (a $in product <=> exist tuple: forall i N_pos: i <= n => tuple(i) $in Xi)
```
- **说明**：n元组和n重笛卡尔积可以通过函数和替换公理定义

## 整理

1. **对集公理 (Axiom of Pairing)**  
   对任意集合 \(u,v\)，存在集合 \(\{u,v\}\)。

```litex
have a, b set
have set s = {a, b}
```

2. **幂集公理 (Axiom of Power Set)**  
   对任意集合 \(X\)，存在集合 \(\mathcal{P}(X)\)，包含 \(X\) 的所有子集。

```litex
fn power_set(X set) set

know forall X set: forall s set: s $is_subset_of X => s $in power_set(X) <=> forall x power_set(X): x $is_subset_of X
```

3. **并集公理 (Axiom of Union)**  
   对任意集合族 \(F\)，存在集合 \(\bigcup F\)，包含 \(F\) 中元素的元素。

```litex
fn union_of_family(F set) set:
    forall x F:
        x $in set
    =>:
        forall x union_of_family(F):
            x $in F
        forall x F:
            x $is_subset_of union_of_family(F)
            
```

4. **子集公理 (Axiom Schema of Separation)**  
   可用性质从集合中分离出子集。

```litex
have s set
prop p(x s)
have set s = {x s: $p(x)}
```

## ZFC 公理和皮亚诺公理

### ZFC 公理系统（Zermelo-Fraenkel Set Theory with Choice）

ZFC公理系统是现代数学的基础，包含以下10条公理：

#### 1. 外延公理 (Axiom of Extensionality)

**数学表示**：
$$\forall A, B \text{ set}: A = B \iff (\forall x, x \in A \iff x \in B)$$

两个集合相等当且仅当它们有相同的元素。

#### 2. 空集公理 (Axiom of Empty Set)

**数学表示**：
$$\exists \emptyset \text{ set}: \forall x, x \not\in \emptyset$$

存在一个不包含任何元素的集合。

#### 3. 配对公理 (Axiom of Pairing)

**数学表示**：
$$\forall a, b \text{ obj}: \exists \{a,b\} \text{ set}: \forall y, (y \in \{a,b\} \iff (y = a \lor y = b))$$

对于任意两个对象$a$和$b$，存在一个集合只包含$a$和$b$。

#### 4. 并集公理 (Axiom of Union)

**数学表示**：
$$\forall A \text{ set}: \exists \bigcup A \text{ set}: \forall x, (x \in \bigcup A \iff (\exists S \in A, x \in S))$$

对于任意集合$A$（其元素都是集合），存在一个集合$\bigcup A$，包含$A$中所有集合的所有元素。

#### 5. 幂集公理 (Axiom of Power Set)

**数学表示**：
$$\forall X \text{ set}: \exists \mathcal{P}(X) \text{ set}: \forall S, (S \in \mathcal{P}(X) \iff S \subseteq X)$$

对于任意集合$X$，存在一个集合$\mathcal{P}(X)$，包含$X$的所有子集。

#### 6. 分离公理 (Axiom Schema of Separation)

**数学表示**：
$$\forall A \text{ set}, \forall P: \exists \{x \in A : P(x)\} \text{ set}: \forall y, (y \in \{x \in A : P(x)\} \iff (y \in A \land P(y)))$$

对于任意集合$A$和性质$P$，存在一个集合包含$A$中所有满足$P$的元素。

#### 7. 替换公理 (Axiom Schema of Replacement)

**数学表示**：
$$\forall F \text{ function}, \forall A \text{ set}: \exists F(A) \text{ set}: \forall y, (y \in F(A) \iff (\exists x \in A, y = F(x)))$$

对于任意函数$F$和集合$A$，存在一个集合包含$F$在$A$上的像。

#### 8. 无穷公理 (Axiom of Infinity)

**数学表示**：
$$\exists I \text{ set}: (\emptyset \in I \land (\forall x \in I, x \cup \{x\} \in I))$$

存在一个包含自然数的集合。

#### 9. 正则公理 (Axiom of Regularity / Foundation)

**数学表示**：
$$\forall A \text{ set}: (A \neq \emptyset \implies (\exists x \in A, \forall y \in A, y \not\in x))$$

每个非空集合都包含一个与它不相交的元素。

#### 10. 选择公理 (Axiom of Choice)

**数学表示**：
$$\forall F \text{ non-empty family of sets}: \exists f \text{ choice function}: (\forall A \in F, f(A) \in A)$$

对于任意非空集合族，存在一个选择函数。

---

### 皮亚诺公理 (Peano Axioms)

皮亚诺公理系统定义了自然数的基本性质：

#### 1. 0是自然数

**数学表示**：
$$0 \in \mathbf{N}$$

#### 2. 后继公理 (Successor Axiom)

**数学表示**：
$$\forall n \in \mathbf{N}, n++ \in \mathbf{N}$$

如果$n$是自然数，则$n++$（$n$的后继）也是自然数。

#### 3. 0不是任何数的后继

**数学表示**：
$$\forall n \in \mathbf{N}, n++ \neq 0$$

#### 4. 后继的唯一性 (Injectivity of Successor)

**数学表示**：
$$\forall n, m \in \mathbf{N}, (n++ = m++ \implies n = m)$$

不同的自然数有不同的后继。等价地，如果两个自然数的后继相等，则这两个自然数相等。

#### 5. 数学归纳法 (Induction Axiom)

**数学表示**：
$$\forall P: (P(0) \land (\forall n \in \mathbf{N}, P(n) \implies P(n++))) \implies (\forall n \in \mathbf{N}, P(n))$$

如果性质$P$满足：
- $P(0)$成立
- 对于任意自然数$n$，如果$P(n)$成立，则$P(n++)$也成立

那么$P(n)$对所有自然数$n$都成立。

---

### 说明

- **ZFC公理系统**：ZFC是Zermelo-Fraenkel集合论加上选择公理，是现代数学的基础。所有数学对象都可以在ZFC框架内定义。
- **皮亚诺公理**：皮亚诺公理定义了自然数的基本性质，是算术的基础。自然数集合$\mathbf{N}$的存在性由ZFC的无穷公理保证。
- **Litex中的对应**：Litex通过内置关键字（如`set`、`$in`、`N`等）和语法（如`{x A: P(x)}`）直接支持这些公理，使得数学表达更加自然和直观。
