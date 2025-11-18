# 自然数 (Natural Numbers)

Definition 2.1.1. (Informal) A natural number is any element of the set $\mathbf{N}:=\{0,1,2,3,4,\ldots\}$, which is the set of all the numbers created by starting with 0 and then counting forward indefinitely. We call $\mathbf{N}$ the set of natural numbers.
$\mathbf{N} := \{0, 1, 2, 3, 4, \ldots\}$

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

Axiom 2.2. If $n$ is a natural number, then $n++$ is also a natural number.
$n \in \mathbf{N} \implies n++ \in \mathbf{N}$

**Litex对应**：
- **关键词**：内置算术运算
- **表达式**：`forall n N => n + 1 $in N`
- **示例**：
```litex
have n N
n + 1 $in N
```
- **说明**：Litex中自然数的后继运算通过`+ 1`表示，这是内置的算术运算

Definition 2.1.3. We define 1 to be the number 0++, 2 to be the number (0++)++, 3 to be the number ((0++)++)++, etc. (In other words, 1:=0++, 2:=1++, 3:=2++, etc.)
$1 := 0++$, $2 := 1++$, $3 := 2++$, etc.

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

Axiom 2.3. 0 is not the successor of any natural number; i.e., we have $n++ \neq 0$ for every natural number $n$.
$\forall n \in \mathbf{N}, n++ \neq 0$

**Litex对应**：
- **关键词**：`forall`, `!=`
- **表达式**：`forall n N => n + 1 != 0`
- **示例**：
```litex
know forall n N => n + 1 != 0
```
- **说明**：这是自然数的基本性质，可以通过`know`声明为公理

Axiom 2.4. Different natural numbers must have different successors; i.e., if $n$, $m$ are natural numbers and $n \neq m$, then $n++ \neq m++$. Equivalently, if $n++ = m++$, then we must have $n = m$.
$\forall n, m \in \mathbf{N}, (n \neq m \implies n++ \neq m++) \iff (n++ = m++ \implies n = m)$

**Litex对应**：
- **关键词**：`forall`, `=>`, `<=>`, `=`, `!=`
- **表达式**：`forall n, m N: (n != m => n + 1 != m + 1) <=> (n + 1 = m + 1 => n = m)`
- **示例**：
```litex
know forall n, m N: (n != m => n + 1 != m + 1) <=> (n + 1 = m + 1 => n = m)
```
- **说明**：这是自然数后继的唯一性公理

Axiom 2.5 (Principle of mathematical induction). Let $P(n)$ be any property pertaining to a natural number $n$. Suppose that $P(0)$ is true, and suppose that whenever $P(n)$ is true, $P(n++)$ is also true. Then $P(n)$ is true for every natural number $n$.
$(P(0) \land (\forall n \in \mathbf{N}, P(n) \implies P(n++))) \implies (\forall n \in \mathbf{N}, P(n))$

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

Assumption 2.6. (Informal) There exists a number system $\mathbf{N}$, whose elements we will call natural numbers, for which Axioms 2.1-2.5 are true.
$\exists \mathbf{N}$ such that Axioms 2.1-2.5 hold

**Litex对应**：
- **关键词**：`N`（内置）
- **表达式**：`N`是Litex的内置集合，满足所有自然数公理
- **示例**：
```litex
N $in set
0 $in N
```
- **说明**：`N`是Litex的内置集合，其存在性和性质由系统保证

Definition 2.2.1 (Addition of natural numbers). Let $m$ be a natural number. To add zero to $m$, we define $0 + m := m$. Now suppose inductively that we have defined how to add $n$ to $m$. Then we can add $n++$ to $m$ by defining $(n++) + m := (n + m)++$.
$0 + m := m$; $(n++) + m := (n + m)++$

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

Definition 2.2.7 (Positive natural numbers). A natural number $n$ is said to be positive iff it is not equal to 0.
$n > 0 \iff n \neq 0$

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

Definition 2.2.11 (Ordering of the natural numbers). Let $n$ and $m$ be natural numbers. We say that $n$ is greater than or equal to $m$, and write $n \geq m$ or $m \leq n$, iff we have $n = m + a$ for some natural number $a$. We say that $n$ is strictly greater than $m$, and write $n > m$ or $m < n$, iff $n \geq m$ and $n \neq m$.
$n \geq m \iff \exists a \in \mathbf{N}, n = m + a$; $n > m \iff (n \geq m) \land (n \neq m)$

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

Definition 2.3.1 (Multiplication of natural numbers). Let $m$ be a natural number. To multiply zero to $m$, we define $0 \times m := 0$. Now suppose inductively that we have defined how to multiply $n$ to $m$. Then we can multiply $n++$ to $m$ by defining $(n++) \times m := (n \times m) + m$.
$0 \times m := 0$; $(n++) \times m := (n \times m) + m$

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

Definition 2.3.11 (Exponentiation for natural numbers). Let $m$ be a natural number. To raise $m$ to the power 0, we define $m^0 := 1$; in particular, we define $0^0 := 1$. Now suppose recursively that $m^n$ has been defined for some natural number $n$, then we define $m^{n++} := m^n \times m$.
$m^0 := 1$ (in particular, $0^0 := 1$); $m^{n++} := m^n \times m$

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

# 集合论 (Set Theory)

Definition 3.1.1. (Informal) We define a set $A$ to be any unordered collection of objects, e.g., $\{3,8,5,2\}$ is a set. If $x$ is an object, we say that $x$ is an element of $A$ or $x \in A$ if $x$ lies in the collection; otherwise we say that $x \not\in A$.
$A$ is a set; $x \in A$ or $x \not\in A$

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

Axiom 3.1 (Sets are objects). If $A$ is a set, then $A$ is also an object. In particular, given two sets $A$ and $B$, it is meaningful to ask whether $A$ is also an element of $B$.
$A$ is a set $\implies A$ is an object

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

Definition 3.1.4 (Equality of sets). Two sets $A$ and $B$ are equal, $A = B$ iff every element of $A$ is an element of $B$ and vice versa. To put it another way, $A = B$ if and only if every element $x$ of $A$ belongs also to $B$, and every element $y$ of $B$ belongs also to $A$.
$A = B \iff (\forall x, x \in A \iff x \in B)$

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

Axiom 3.2 (Empty set). There exists a set $\emptyset$, known as the empty set, which contains no elements, i.e., for every object $x$ we have $x \not\in \emptyset$.
$\exists \emptyset, \forall x, x \not\in \emptyset$

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

Axiom 3.3 (Singleton sets and pair sets). If $a$ is an object, then there exists a set $\{a\}$ whose only element is $a$, i.e., for every object $y$, we have $y \in \{a\}$ if and only if $y = a$; we refer to $\{a\}$ as the singleton set whose element is $a$. Furthermore, if $a$ and $b$ are objects, then there exists a set $\{a,b\}$ whose only elements are $a$ and $b$; i.e., for every object $y$, we have $y \in \{a,b\}$ if and only if $y = a$ or $y = b$; we refer to this set as the pair set formed by $a$ and $b$.
$\forall a, \exists \{a\}, \forall y, (y \in \{a\} \iff y = a)$; $\forall a, b, \exists \{a,b\}, \forall y, (y \in \{a,b\} \iff (y = a \lor y = b))$

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

Axiom 3.4 (Pairwise union). Given any two sets $A$, $B$, there exists a set $A \cup B$, called the union $A \cup B$ of $A$ and $B$, whose elements consists of all the elements which belong to $A$ or $B$ or both. In other words, for any object $x$: $x \in A \cup B \iff (x \in A \text{ or } x \in B)$.
$\forall A, B, \exists A \cup B, \forall x, (x \in A \cup B \iff (x \in A \lor x \in B))$

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

Axiom 3.5 (Axiom of specification). Let $A$ be a set, and for each $x \in A$, let $P(x)$ be a property pertaining to $x$ (i.e., $P(x)$ is either a true statement or a false statement). Then there exists a set, called $\{x \in A : P(x) \text{ is true}\}$ (or simply $\{x \in A : P(x)\}$ for short), whose elements are precisely the elements $x$ in $A$ for which $P(x)$ is true. In other words, for any object $y$: $y \in \{x \in A : P(x)\} \iff (y \in A \land P(y) \text{ is true})$.
$\forall A, \exists \{x \in A : P(x)\}, \forall y, (y \in \{x \in A : P(x)\} \iff (y \in A \land P(y)))$

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

Definition 3.1.15 (Subsets). Let $A,B$ be sets. We say that $A$ is a subset of $B$, denoted $A \subseteq B$, iff every element of $A$ is also an element of $B$, i.e. For any object $x$, $x \in A \implies x \in B$. We say that $A$ is a proper subset of $B$, denoted $A \subsetneq B$, if $A \subseteq B$ and $A \neq B$.
$A \subseteq B \iff (\forall x, x \in A \implies x \in B)$; $A \subsetneq B \iff (A \subseteq B \land A \neq B)$

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

Definition 3.1.23 (Intersections). The intersection $S_1 \cap S_2$ of two sets is defined to be the set $S_1 \cap S_2 := \{x \in S_1 : x \in S_2\}$. In other words, $S_1 \cap S_2$ consists of all the elements which belong to both $S_1$ and $S_2$.
$S_1 \cap S_2 := \{x \in S_1 : x \in S_2\}$; $x \in S_1 \cap S_2 \iff (x \in S_1 \land x \in S_2)$

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

Definition 3.1.27 (Difference sets). Given two sets $A$ and $B$, we define the set $A - B$ or $A \setminus B$ to be the set $A \setminus B := \{x \in A : x \not\in B\}$. In other words, $A \setminus B$ consists of all the elements of $A$ which do not belong to $B$.
$A \setminus B := \{x \in A : x \not\in B\}$; $x \in A \setminus B \iff (x \in A \land x \not\in B)$

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

Definition 3.3.1 (Functions). Let $X,Y$ be sets, and let $P(x,y)$ be a property pertaining to an object $x \in X$ and an object $y \in Y$, such that for every $x \in X$, there is exactly one $y \in Y$ for which $P(x,y)$ is true (this is sometimes known as the vertical line test). Then we define the function $f : X \to Y$ defined by $P$ on the domain $X$ and range $Y$ to be the object which, given any input $x \in X$, assigns an output $f(x) \in Y$ defined to be the unique object $f(x)$ for which $P(x,f(x))$ is true. Thus, for any $x \in X$ and $y \in Y$: $y = f(x) \iff P(x,y)$ is true.
$f : X \to Y$; $\forall x \in X, \exists! y \in Y, P(x,y)$; $y = f(x) \iff P(x,y)$

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

Definition 3.3.7 (Equality of functions). Two functions $f : X \to Y$ and $g : X \to Y$ with the same domain and range are said to be equal, $f = g$ if and only if $f(x) = g(x)$ for all $x \in X$.
$f = g \iff (\forall x \in X, f(x) = g(x))$

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

Definition 3.3.10 (Composition). Let $f : X \to Y$ and $g : Y \to Z$ be two functions, such that the range of $f$ is the same set as the domain of $g$. We then define the composition $g \circ f : X \to Z$ of the two functions $g$ and $f$ to be the function defined explicitly by the formula $(g \circ f)(x) := g(f(x))$.
$(g \circ f)(x) := g(f(x))$

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

Definition 3.3.14 (One-to-one functions). A function $f$ is one-to-one (or injective) if different elements map to different elements: $x \neq x' \implies f(x) \neq f(x')$. Equivalently, a function is one-to-one if $f(x) = f(x') \implies x = x'$.
$f$ is injective $\iff (\forall x, x' \in X, x \neq x' \implies f(x) \neq f(x')) \iff (\forall x, x' \in X, f(x) = f(x') \implies x = x')$

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

Definition 3.3.17 (Onto functions). A function $f$ is onto (or surjective) if $f(X) = Y$, i.e., every element in $Y$ comes from applying $f$ to some element in $X$. For every $y \in Y$, there exists $x \in X$ such that $f(x) = y$.
$f$ is surjective $\iff f(X) = Y \iff (\forall y \in Y, \exists x \in X, f(x) = y)$

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

Definition 3.3.20 (Bijective functions). Functions $f : X \to Y$ which are both one-to-one and onto are also called bijective or invertible.
$f$ is bijective $\iff (f$ is injective $\land f$ is surjective$)$

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

Definition 3.4.1 (Images of sets). If $f : X \to Y$ is a function from $X$ to $Y$, and $S$ is a set in $X$, we define $f(S)$ to be the set $f(S) := \{f(x) : x \in S\}$; this set is a subset of $Y$, and is sometimes called the image of $S$ under the map $f$.
$f(S) := \{f(x) : x \in S\}$

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

Definition 3.4.4 (Inverse images). If $U$ is a subset of $Y$, we define the set $f^{-1}(U)$ to be the set $f^{-1}(U) := \{x \in X : f(x) \in U\}$. In other words, $f^{-1}(U)$ consists of all the elements of $X$ which map into $U$: $f(x) \in U \iff x \in f^{-1}(U)$.
$f^{-1}(U) := \{x \in X : f(x) \in U\}$; $f(x) \in U \iff x \in f^{-1}(U)$

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

Axiom 3.10 (Power set axiom). Let $X$ and $Y$ be sets. Then there exists a set, denoted $Y^X$, which consists of all the functions from $X$ to $Y$, thus $f \in Y^X \iff$ ($f$ is a function with domain $X$ and range $Y$).
$\forall X, Y, \exists Y^X, \forall f, (f \in Y^X \iff (f : X \to Y))$

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

Axiom 3.11 (Union). Let $A$ be a set, all of whose elements are themselves sets. Then there exists a set $\bigcup A$ whose elements are precisely those objects which are elements of the elements of $A$, thus for all objects $x$: $x \in \bigcup A \iff (x \in S$ for some $S \in A$).
$\forall A, \exists \bigcup A, \forall x, (x \in \bigcup A \iff (\exists S \in A, x \in S))$

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

Definition 3.5.1 (Ordered pair). If $x$ and $y$ are any objects (possibly equal), we define the ordered pair $(x,y)$ to be a new object, consisting of $x$ as its first component and $y$ as its second component. Two ordered pairs $(x,y)$ and $(x',y')$ are considered equal if and only if both their components match, i.e. $(x,y) = (x',y') \iff (x = x' \text{ and } y = y')$.
$(x,y) = (x',y') \iff (x = x' \land y = y')$

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

Definition 3.5.4 (Cartesian product). If $X$ and $Y$ are sets, then we define the Cartesian product $X \times Y$ to be the collection of ordered pairs, whose first component lies in $X$ and second component lies in $Y$, thus $X \times Y = \{(x,y) : x \in X, y \in Y\}$ or equivalently $a \in (X \times Y) \iff (a = (x,y)$ for some $x \in X$ and $y \in Y$).
$X \times Y := \{(x,y) : x \in X, y \in Y\}$; $a \in (X \times Y) \iff (\exists x \in X, \exists y \in Y, a = (x,y))$

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

Definition 3.5.7 (Ordered $n$-tuple and $n$-fold Cartesian product). Let $n$ be a natural number. An ordered $n$-tuple $(x_i)_{1 \leq i \leq n}$ (also denoted $(x_1, \ldots, x_n)$) is a collection of objects $x_i$, one for every natural number $i$ between 1 and $n$; we refer to $x_i$ as the $i$th component of the ordered $n$-tuple. Two ordered $n$-tuples $(x_i)_{1 \leq i \leq n}$ and $(y_i)_{1 \leq i \leq n}$ are said to be equal iff $x_i = y_i$ for all $1 \leq i \leq n$. If $(X_i)_{1 \leq i \leq n}$ is an ordered $n$-tuple of sets, we define their Cartesian product $\prod_{1 \leq i \leq n} X_i$ (also denoted $\prod_{i=1}^n X_i$ or $X_1 \times \ldots \times X_n$) by $\prod_{1 \leq i \leq i \leq n} X_i := \{(x_i)_{1 \leq i \leq n} : x_i \in X_i \text{ for all } 1 \leq i \leq n\}$.
$(x_i)_{1 \leq i \leq n} = (y_i)_{1 \leq i \leq n} \iff (\forall 1 \leq i \leq n, x_i = y_i)$; $\prod_{1 \leq i \leq n} X_i := \{(x_i)_{1 \leq i \leq n} : x_i \in X_i \text{ for all } 1 \leq i \leq n\}$

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