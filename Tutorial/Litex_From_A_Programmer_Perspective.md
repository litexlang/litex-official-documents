# Litex: From A Programmer Perspective

_If you define the problem correctly, you almost have the solution._

_- Steve Jobs_

Litex is a pragmatic language. Its author aimed to design a language intuitive enough for everyone to use and understand. Litex was designed alongside its implementation. Eventually, the author found a set of very self-consistent, simple (but not simpler), and absolutely correct principles to implement the entire language (hopefully this is truly the case!). This chapter mainly introduces Litex statements and how they correspond to common mathematical propositions. This is the foundation of Litex's rigor, because Litex faithfully operates according to how these mathematical rules work.

**Statement**

Statements in Litex code are the smallest units of program execution. Each statement represents an operation in Litex. Every piece of Litex code consists of many Litex statements, just as an article consists of many sentences. For example, `a = 1` asks whether `a` equals 1, and `have a R = 1` defines an object `a` that is a real number equal to 1.

Litex statements are divided into:

1. **Definition statements**, such as the `prop` statement used to define predicates for propositions

2. **Factual statements**, also called propositions, such as `1 + 1 = 2`, which asks Litex whether `1 + 1` equals 2. All factual statements require a predicate to determine truth or falsity. For example, `1 + 1 = 2` is a proposition, and `=` is the predicate.

3. **Proof strategies**, such as `prove_by_contradiction`, which represents proof by contradiction

4. **Auxiliary statements**, such as `import`, which imports a package or file

## Definition Statements

In natural language, the most basic sentence structure is predicate plus noun. Litex follows a similar design approach.

### Defining Predicates

In mathematics, predicates are used for logical judgments. For example, the equality predicate (written as `=` in mathematics) is used to logically determine whether two symbols are equal. Besides equality, common predicates like greater than and less than are already built into Litex. Users sometimes want to define their own predicates, such as "is a positive real number" or "is a prime number".

Custom predicates are mainly divided into two types: non-existential propositions (ordinary propositions) and existential propositions.

1. `prop` is used to define predicates for non-existential propositions

Example:

```litex
prop is_positive_real_number(x R):
    x > 0
```

2. `exist_prop` is used to define predicates for existential propositions

Example:

```litex
exist_prop x R st any_real_number_has_another_real_number_than_itself(y R):
    x > y
```

### Defining Nouns

In mathematics, nouns are also called Objects. A sentence needs both nouns and verbs (predicates) to be judged as true or false. For example, in `1 + 1 = 2`, the predicate is `=`, and the nouns are `1 + 1` and `2`.

What types of objects are there? Atomic and functional.

**Atomic**: Consists of a single word, such as `1`, `+`, `something`

**Compound**: Syntax is `object0(object1, object2, ..., objectN)`, where `object0` is the function name, and `object1` through `objectN` are the function's parameters. For example, in `f(1, 2)`, the function name is `f`, and the parameters are `1` and `2`. Sometimes we also write the function name between parameters, such as in `1 + 2`, where the function name is `+`, and the parameters are `1` and `2`. Common operators like addition, subtraction, multiplication, and division can be written in infix notation. User-defined functions should preferably be written with the function name at the beginning.

Sometimes the function name itself is passed as a parameter to a function. For example, when taking the derivative of function `f`, the function `f` is the parameter of the derivative symbol. Sometimes the function name is even a compound object. For example, in `f(1,2)(3,4)`, `f(1,2)` returns a function that takes `3` and `4` as parameters.

Thus, sometimes we need to define atomic objects, and sometimes we need to define functions to form compound objects.

Unlike defining predicates, when we define nouns (objects), we need to verify the existence of the object. For example, we cannot define a number that is both greater than 0 and less than 0.

#### Defining Objects and Checking Existence

1. **Defining objects from existential propositions**

`have object1, object2 ... st $some_exist_prop(param1, param2...)`

Corresponds to the Axiom of Choice. If there exist objects such that a proposition holds, then we can extract some object satisfying that proposition.

```litex
exist_prop x R st larger_than(y R):
    x > y
exist 17 st $larger_than(1)
have x st $larger_than(1)
x > 1
```

Note: The `x` defined here is not necessarily `17`, but rather some number satisfying the proposition (i.e., greater than 1).

2. **Defining objects from non-empty sets**

`have object1 some_nonempty_set`

Extracts an element from a non-empty set, corresponding to the Axiom of Choice.

```litex
have s nonempty_set
have x s
x $in s
```

3. **Defining sets by enumeration**

`have set object1 = {item1, item2, ...}`

Corresponds to the Pairing Axiom and Union Axiom in set theory (essentially enumeration).

```litex
have set s = {1, 2, 3}
have x s
x = 1 or x = 2 or x = 3
```

Note: Objects within `{}` cannot be duplicated. For example, you cannot write `s = {1, 1, 2, 3}` because `1` is repeated. If `x` is in `s`, then `x` has the property `x = 1 or x = 2 or x = 3`.

4. **Defining sets by intension**

`have set object1 = {item parent_set: fact1, fact2, ...}`

Corresponds to the Axiom Schema of Separation in set theory.

```litex
have set s = {x R: x > 0, x < 1}
have x s
x > 0
x < 1
```

Note: You cannot write `{x set: ...}` because `set $in set` does not hold (`set` is not a set). You must write `{x some_set: ...}`, where `some_set` is a set, such as `R`.

5. **Defining an object equal to some expression**

`have object1 set_name = item_from_that_set`

The existence of the object is directly obtained by equating it to a known object.

```litex
have a R = 1
```

Directly set `a = 1`, so `a` has the property `a = 1`. Note that you cannot write `have a N = 1.1` because `1.1` is not an element of `N`.

6. **Defining a function equal to some expression**

`have fn function_name(param1 set1, param2 set2, ...) return_set = expression`

The existence of the function is directly obtained by equating it to an expression.

```litex
have fn f(x R) R = x
f(1) = 1
```

7. **Defining functions by cases**

```
have fn function_name(param1 set1, param2 set2, ...) return_set =:
    case condition1 = expression1
    case condition2 = expression2
    ...
```

```litex
have fn f(x R) R =:
    case x > 0 = x
    case x <= 0 = 0
```

Defines function `f` such that when `x > 0`, `f(x) = x`; when `x <= 0`, `f(x) = 0`.

8. **Defining functions by conditions**

`have fn function_name(param1, ...) return_set:`
```
    domain_fact1
    ...
    =>:
        then_fact1
        ...
```

Note: This functionality may overlap with `exist_prop` combined with `have`. Whether to keep it is pending.

#### Defining Directly Without Checking Existence

If we need to assume the existence of something (sometimes this is necessary, for example, when something's existence has been proven, but you don't want to spend great effort writing out the proof of existence in Litex, and want to directly start working on your problem based on this known fact), we can use:

1. **`let` defines objects**

Without proving the existence of a number greater than 0 and less than 1, directly define `x` to satisfy these conditions.

```litex
let x R: x > 0, x < 1
```

2. **`fn` defines functions**

Without proving whether there exists an `f` that truly satisfies `f(x) = f(x) ^ 2`, directly let `f` have these properties (such functions do exist, for example, `f(x) = 1` works).

```litex
fn f(x R) R:
    f(x) = f(x) ^ 2
```

## Factual Statements

Factual statements, also called logical expressions or boolean expressions. In Litex, all factual statements ultimately result in `true`, `unknown`, or `error`. When verifying facts, Litex verifies whether the current fact is correct based on some rules. If all rules fail to verify it, the result is `unknown`. (Note: There are two cases here: 1. If your fact is actually false, such as `1 = 2`, Litex will tell you `unknown` because it's indeed impossible to find corresponding rules to make it correct; 2. If your fact is correct but you skipped steps, it may also be `unknown`. For example, Fermat's Last Theorem has been proven correct, but because you skipped steps, Litex's rules cannot verify it step by step, so Litex will also tell you `unknown`.) You can think of Litex as a very rigid but very fast teacher who can only verify facts using specific verification methods and cannot skip steps with imagination like humans.

1. **Specific facts**

1.1 **Ordinary facts (not involving existence)**

1.1.1 **Equality**

Essentially, `=` is also a propositional predicate. However, the proof of equality is much more special than other predicates. Equality has properties that general predicates don't have, such as transitivity and symmetry. Equality has a unique status in mathematics because once `object1 = object2`, they immediately have all of each other's properties—they are "equivalent". No other predicate can have such an effect. Whether proving equality or using the property that two objects are equal to prove other properties about these objects, Litex provides very powerful support.

1.1.2 **Non-equality**

```litex
17 > 2
prop larger_than(x, y R):
    x > y
$larger_than(17, 2)
```

For example, predicates like `17 > 2` are built-in. We can also define our own `prop` predicates, such as `$larger_than(17, 2)` meaning 17 is greater than 2.

1.2 **Existential facts**

```litex
exist_prop x R st larger_than(y R):
    x > y
exist 17 st $larger_than(1)
```

For example, `exist 17 R st $exist_number_larger_than(1)` means there exists the number 17, which is greater than 1.

If we have previously proven `exist ... st $some_exist_prop(param1, ...)`, then `$some_exist_prop(param1, ...)` is automatically proven. Afterward, we can use `have xxx, ... st $some_exist_prop(param1, ...)` to declare an object `xxx...` that satisfies `$some_exist_prop(param1, ...)`.

2. **`forall` facts**

Universal quantifier facts, expressing that for all objects satisfying certain conditions, some property holds.

Syntax:
```
forall x1 set1, x2 set2, ...:
    condition1
    condition2
    ...
    =>:
        conclusion1
        conclusion2
        ...
```

Or inline form:
```
forall x1 set1, x2 set2, ...: condition1, condition2, ... => conclusion1, conclusion2, ...
```

```litex
forall x R:
    x > 0
    =>:
        x + 1 > 1

# Inline form
forall x R: x > 0 => x + 1 > 1

# Multiple conditions
forall x, y R:
    x > 0
    y > 0
    =>:
        x + y > 0
        x * y > 0
```

3. **`or` facts**

Disjunctive facts, expressing that at least one condition holds.

Syntax:
```
or:
    fact1
    fact2
    ...
    factN
```

Or inline form:
```
fact1 or fact2 or ... or factN
```

```litex
let x R: x = 1

or:
    x = 1
    x = 2

# Inline form
x = 1 or x = 2

# Used in forall
know forall x R: x > 1 or x = 1 or x < 1
let x R
x > 1 or x = 1 or x < 1
```

4. **Intensional set facts**

Intensional set facts, used to express properties of elements in a set.

```litex
have set s = {x R: x > 0, x < 1}
have y s
y > 0
y < 1

# Used in forall
forall x s:
    x > 0
```

5. **Enumeration set facts**

Enumeration set facts, used to express properties of elements in finite sets.

```litex
have set s = {1, 2, 3}
have x s
x = 1 or x = 2 or x = 3

# Used in forall
forall x s:
    x > 0
```

6. **Chained equality**

`object1 = object2 = object3 = ... = objectN = objectN_plus_1`

This is actually a shorthand for `object1 = object2, object2 = object3, ..., objectN-1 = objectN`. At runtime, first verify the first equality: `object1 = object2`, then verify the second equality `object3 = object2`. If it's not proven, try `object3 = object1`. If it's still not proven, the result is `unknown`. Similarly, when proving the Nth equality, we prove that `objectN_plus_1` equals `object1, object2, ..., objectN` one by one. As long as some equality is proven, we consider `object1 = objectN_plus_1` to be proven. If none are proven, the result is `unknown`.

### Notes

Note the difference between Litex and Python. In Litex, if a statement is `true`, this `true` cannot appear as a parameter in subsequent statements. This `true` only tells Litex that it can continue verification (if a statement is not `true`, but `unknown` or `error`, Litex will not continue verification). In Python, if a statement is `true`, this `true` can appear as a parameter in subsequent statements. For example, `a = 1 == 1\nprint(a)`. You can see that Litex, or mathematics, has a different way of thinking compared to Python.

## Proof Strategies

The design of proof strategies corresponds to keywords in first-order logic and axioms in set theory. For example, `not` corresponds to `prove_by_contradiction`, `or` corresponds to `prove_in_each_case`, and `prove_by_induction` corresponds to mathematical induction.

| First-Order Logic & Mathematical Axiom Keywords | Corresponding Proof Strategy |
|--------------|--------------|
| `not` | `prove_by_contradiction` |
| `or` | `prove_in_each_case` |
| Mathematical Induction | `prove_by_induction` |
| Set Theory Axiom (enumeration for defining sets) | `prove_by_enum` |
| Ordering and enumeration of integers | `prove_in_range` |

1. **prove_in_each_case**

Corresponds to `or` in first-order logic. When you need to prove a fact that holds in multiple cases, you can prove it case by case.

Syntax:
```
prove_in_each_case:
    fact1 or fact2 or ... or factN
    =>:
        conclusion
    prove:
        # Assume fact1 holds, prove conclusion
        ...
    prove:
        # Assume fact2 holds, prove conclusion
        ...
    ...
```

```litex
let a R: a = 0 or a = 1

prove_in_each_case:
    a = 0 or a = 1
    =>:
        a >= 0
    prove:
        0 >= 0
    prove:
        1 >= 0
```

2. **prove_by_contradiction**

Corresponds to `not` in first-order logic. By assuming the negation of the conclusion and deriving a contradiction, we prove the original conclusion.

Syntax:
```
prove_by_contradiction:
    not conclusion  # Assume the negation of the conclusion
    ...
    # Derive a contradiction
    contradiction
```

```litex
prop p(x R)
prop q(x R)
know not $q(1)
know forall x R: $p(x) => $q(x)

claim:
    not $p(1)
    prove_by_contradiction:
        $p(1)  # Assume $p(1) holds
        $q(1)  # Derive $q(1) from $p(1) and known conditions
        # But we know not $q(1), contradiction
```

3. **prove_by_enum**

Corresponds to enumeration in set theory axioms. For finite sets, prove properties by enumerating each element.

Syntax:
```
prove_by_enum(x, set_name):
    property_to_prove
```

```litex
prop p(x R)
have set s = {1, 2, 3}

prove_by_enum(x, s):
    x > 0
```

4. **prove_in_range**

Corresponds to ordering and enumeration relations of integers. Used for enumeration proofs within integer ranges, particularly suitable for handling highly repetitive proof processes.

Syntax:
```
prove_in_range(x, lower_bound, upper_bound):
    property_to_prove
```

```litex
# Prove that for integers x with 1 < x < 10, we have x > 0
let x Z: x > 1, x < 10

prove_in_range(x, 2, 9):
    x > 0

# Prove that 997 is prime (simplified example)
# Need to prove forall x N: x >= 2, x < 997 => 997 % x != 0
prove_in_range(x, 2, 996):
    997 % x != 0
```

5. **prove_by_induction**

Corresponds to mathematical induction. Used to prove properties that hold for all natural numbers.

Syntax:
```
prove_by_induction($prop(x, n), n, base_case)
```

```litex
prop p(x R, n N_pos)
let x R
know forall n N_pos: n >= 1, $p(x, n) => $p(x, n+1)
know $p(x, 1)

prove_by_induction($p(x, n), n, 1)
```

## Auxiliary Keywords

1. **know**

The main purposes of `know` are:

1. Define axioms and self-evident definitions. For example, the concept of union is an axiom in set theory. According to its definition `forall a, b set: forall x a => x $in union(a, b)`, we can write `know forall a, b set: forall x a => x $in union(a, b)`.

2. Assume a fact without proving it. For example, if you want to use Fermat's Last Theorem to prove a fact, but don't want to prove Fermat's Last Theorem, use `know` to make it hold directly.

3. Assume some facts temporarily so that proofs can pass for now, and replace `know` with the actual proof when you think of it in the future.

4. If we want to prove properties of things with specific properties, for example, if we want to prove that a number greater than 1 and less than 3 must be greater than 0 and less than 5, we write `have x R\nknow x > 1, x < 3`. This way Litex knows that `x` is greater than 1 and less than 3, and can continue to prove that `x` is greater than 0 and less than 5. However, this is not the best way to write it, because `know` here pollutes the entire environment. A better way is `prove forall x R: x > 1, x < 3 => x > 0, x < 5:\n...`. This way, even if the conditions in `forall` are problematic, it won't affect the global environment, because there will be no objects in the global environment that satisfy these `forall` conditions. For example, if we want to prove that a number that equals both 1 and 2 equals both 1 and 2, such conditions are obviously wrong. If you write `know x = 1, x = 2` in the global environment, Litex will think that `x` equals both 1 and 2, and then `1=2` can be proven, which is very bad. A better way is `prove forall x R: x = 1, x = 2 => x = 1, x = 2:\n...`. This way, even if the conditions in `forall` are problematic, it won't affect the global environment, because there will be no objects in the global environment that satisfy these `forall` conditions. Even if the fact `forall x R: x = 1, x = 2 => x = 1, x = 2` is proven correct, it won't be used by any Litex verification rules to prove subsequent facts.

2. **import**

Import things from another file or folder.

Syntax:
```
import "file_path"
import "folder_path"
```

```litex
# Import a single file
import "examples/algorithm.md"

# Import a folder (will import main.lit in the folder)
import "tutorial"
```

3. **prove_is_commutative_prop, prove_is_transitive_prop**

Prove that a `prop` predicate has commutativity or transitivity. These properties will be used in subsequent proofs.

Syntax:
```
prove_is_commutative_prop($prop(x, y))
prove_is_transitive_prop($prop(x, y))
```

```litex
prop p(x R, y R)

# Prove commutativity
prove_is_commutative_prop(not $p(x, y))
# Afterward, if not $p(x, y) is not proven, Litex will try to prove not $p(y, x)
# If not $p(x, y) is proven, Litex will automatically prove $p(y, x)

# Prove transitivity
prove_is_transitive_prop($p(x, y))
# Afterward, if $p(x, z) is not proven, Litex will iterate through all known t such that $p(x, t) holds
# If some t satisfies $p(t, z), then $p(x, z) is proven
```

4. **fn_template**

According to the Power Set Axiom, there is a set $X^Y$, which is the set of all functions from $Y$ to $X$. `fn_template` is essentially used to define this set.

There are two ways to write `fn_template`. One is `fn(set_name, set_name2, ...) return_set_name`, for example, `fn(R)R` represents functions with domain `R` and codomain `R`.

The other is custom definition.

TODO: Essentially, the notation `fn(set_name, set_name2, ...) return_set_name` can already represent all power sets. However, because Litex needs to be user-friendly, when defining functions, in addition to defining the domain and codomain, we can also add additional conditions on the domain and codomain, for example:

```litex
fn f(x R) R:
    x > 0
    =>:
        f(x) > 0
```

This is equivalent to defining function `f` in `fn(R)R`, with domain `R`, codomain `R`, and satisfying `x > 0 => f(x) > 0`.

Another way to write this is:

```litex
have set positive_real_numbers = {x R: x > 0}
fn f(x positive_real_numbers) positive_real_numbers
```

This also works, but it's more cumbersome.

TODO: Should also introduce `have fn_template`

5. **claim**

Simulates the writing style of normal mathematics books, used to state a fact and provide a proof.

Syntax:
```
claim:
    fact_to_prove
    prove:
        # Proof steps
        ...

claim:
    fact_to_prove
    prove_by_contradiction:
        # Proof by contradiction steps
        ...
```

```litex
# Basic usage
claim:
    forall x R:
        x = 1
        =>:
            x > 0
    prove:
        1 > 0
        x > 0

# Using proof by contradiction
prop p(x R)
prop q(x R)
know not $q(1)
know forall x R: $p(x) => $q(x)

claim:
    not $p(1)
    prove_by_contradiction:
        $p(1)
        $q(1)
```

6. **prove**

Used to perform proofs in a local environment, and release the results to the current environment after the proof is complete.

Syntax:
```
prove some_facts:
    # 证明步骤
    ...
```

```litex
# prove will first run all proof processes below, then verify some_facts
# If it holds, some_facts will enter the current environment
prove forall x R: x > 1, x < 3 => x > 0, x < 5:
    x > 1
    x > 0
    x < 3
    x < 5

# Essentially equivalent to
claim:
    forall x R: x > 1, x < 3 => x > 0, x < 5
    prove:
        x > 1
        x > 0
        x < 3
        x < 5
```

## Keyword List

### First-Order Logic Keywords

| Keyword | Meaning | Description |
|--------|------|------|
| `forall` | Universal quantifier | Means "for all" or "any", e.g., `forall x R: x > 0` |
| `exist` | Existential quantifier | Means "there exists", e.g., `exist x R: x > 0`|
| `or` | Disjunction | Means "or" (inclusive disjunction), e.g., `x = 1 or x = 2` |
| `not` | Negation | Means "not", e.g., `not x = 0` |
| `=>` | Implication | Means "if...then", e.g., `forall x R: x > 0 => x + 1 > 1` |
| `<=>` | Equivalence/Biconditional | Means "if and only if", e.g., `forall x R: x > 0 <=> x + 1 > 1` |
| `=` | Equality | Means equality relation, e.g., `x = 1` |
| `!=` | Inequality | Means not equal, equivalent to `not x = y` |

**Notes**:
- Litex currently does not have an `and` (conjunction) keyword. This is because `,` can be used to represent conjunction. For example, `x = 1, y = 2` means x equals 1 and y equals 2.
- Litex does not support direct use of `not forall`. To express "not true for all x", you need to use the form `exist x: not ...`.
- `not exist` is equivalent to `forall not`, which can be expressed through universal quantifiers and negation. Once a `not exist` is proven, the corresponding `forall not` will also be automatically saved.

<!-- ### 集合论公理一览

现代数学建立在集合论（ZFC公理系统）之上。以下是标准的集合论公理：

| 公理名称 | 公理内容 | Litex中的对应 |
|---------|---------|--------------|
| **外延公理** (Axiom of Extensionality) | 两个集合相等当且仅当它们有相同的元素 | `forall A, B set: A = B <=> forall x A => x $in B; forall x B => x $in A` |
| **空集公理** (Axiom of Empty Set) | 存在一个不包含任何元素的集合 | `have self_defined_empty_set = {}` |
| **配对公理** (Axiom of Pairing) | 对于任意两个对象a和b，存在一个集合只包含a和b | `have a obj, b obj\nknow a != b\nhave set s = {a, b}` |
| **并集公理** (Axiom of Union) | 对于任意集合X，存在一个集合包含X中所有集合的所有元素 | ` ` |
| **幂集公理** (Axiom of Power Set) | 对于任意集合X，存在一个集合包含X的所有子集 | ` ` |
| **分离公理** (Axiom Schema of Separation) | 对于任意集合A和性质P，存在一个集合包含A中所有满足P的元素 | 通过`have set s = {x A: $P(x)}`语法实现 |
| **替换公理** (Axiom Schema of Replacement) | 对于任意函数F和集合A，存在一个集合包含F在A上的像 | 目前Litex暂不支持，可通过`know`假设 |
| **无穷公理** (Axiom of Infinity) | 存在一个包含自然数的集合 | `N`是Litex的内置集合 |
| **正则公理** (Axiom of Regularity) | 每个非空集合都包含一个与它不相交的元素 | `forall A set => (exist x A => exist y A => (not y $in set) or (forall z y => not z $in A))` |
| **选择公理** (Axiom of Choice) | 对于任意非空集合族，存在一个选择函数 | have ... st $some_exist_prop(...) 对应选择公理|

**说明**：
- 在Litex中，`set`和`$in`是内置关键字，行为与数学中的集合论一致
- `obj`是Litex的内置关键字，表示所有对象。他不是一个集合
- 分离公理通过Litex的集合定义语法`{x parent_set: fact1, fact2, ...}`来实现
- 替换公理涉及二阶逻辑，Litex目前暂不支持，但可以通过`know`关键字假设其成立
- 自然数集合`N`、整数集合`Z`、有理数集合`Q`、实数集合`R`、复数集合`C`都是Litex的内置集合
- litex中经常出现x1 set1, x2 set2, ...这样的语句，比如forall x1 set1, x2 set2, ...: ...这样的语句，其中x1, x2, ...是对象，set1, set2, ...是集合。但其实不完全是这样，set1, set2上可能出现set, nonempty_set, obj，这几个不是集合的对象。即虽然litex都是写xxx in yyy，但是yyy不一定是集合。比如xxx in set中，就是在说xxx是（is）集合（所有的set组成的全体，不是一个set），xxx in obj在说xxx是（is）对象，但是obj（包含所有东西）也不是一个集合，来说明x1是集合，而不是像x1 in R这样用in来表示某某元素在集合R里。注意到，如果右侧是set, obj这种东西，那就我们在自然语言表达时的谓词就是is；如果是set这种东西，那我们在自然语言表达时的谓词就是in。特别注意，litex中的 x $in set 其实意思是 x is a set，而不是，而不是在说x在集合构成的集合里。这里的in重载了is的语义。。 -->

## Thanks