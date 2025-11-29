# Factual Statements

_Geometry, like arithmetic, requires for its logical development only a small number of simple, fundamental principles._

_— David Hilbert_

Euclid showed us over 2000 years ago how 5 axioms could derive such a wonderful geometric world. Simple starting points often lead us into infinitely complex worlds. The same is true for mathematics. The foundation of modern mathematics is naive set theory, which doesn't have many axioms, and we even encountered the concept of sets in middle school. But it is precisely these simple and understandable rules that form the foundation of all mathematics. Before we move on, think about how powerful the idea is: with just very few absolutely accurate inference rules, plus a few axioms, we can derive a rich and diverse mathematical world. That is what math is all about.

By implementing those simple axioms and deduction rules in a software like Litex, we can write math in the form of code. That is what Litex is about. Easy to understand, right?

---

## Section 1: What Is a Factual Statement?

### Introduction

In this section, we'll explore the most fundamental concept in Litex: **Factual Statements**. These are the building blocks of all mathematical reasoning in Litex. By the end of this section, you'll understand what factual statements are, how they differ from other concepts, and the three possible outcomes they can have.

### From Natural Language to Litex

The most fundamental concept in both mathematics and **Litex** is the **Factual Statement**.

**Natural Language**: "One is greater than zero"  
**Litex**: `1 > 0` → **Outcome**: `true`

**Natural Language**: "Seventeen is less than forty-seven"  
**Litex**: `17 < 47` → **Outcome**: `true`

### The Three Possible Outcomes

A Factual Statement can take on exactly one of the following truth values:

**1. True** ✅

e.g. `1 > 0` is true

**2. Unknown** ❓

e.g. `0 > 1` is unknown. Actually it is false. In Litex, `unknown` is used in two situations: 
1. This is a true statement, but the user has not provided enough information to prove it
2. This is a false statement

**3. Error** ❌

e.g. `let birthday R: birthday = 2003.4.2` is error because `2003.4.2` is not a real number.

### Important Distinctions

Don't confuse a **Factual Statement** with a *true statement*. A Factual Statement might just as well be false, unknown, or even an error.

Don't confuse a **Factual Statement** with a *Proposition*. A Proposition is more like a "verb" waiting for its objects; once the objects are supplied, it turns into a Factual Statement.

**Example:**
- `prop intelligent(x human)` - This is a **Proposition** (a template)
- `$intelligent(Jordan)` - This is a **Factual Statement** (applying the proposition to a specific object)

### Summary

- Factual statements are the fundamental building blocks of Litex
- They can be true, unknown, or error
- They differ from propositions (which are templates)
- They differ from true statements (they can be false or unknown)

### Litex Syntax Reference

**Factual statement**: Any statement that can be evaluated (e.g., `1 > 0`, `x = y`)

**Proposition**: `prop propName(x set)` - a template for factual statements

**Outcomes**: `true`, `unknown`, or `error`

### Exercises

1. Which of the following are factual statements?
   - `1 + 1 = 2`
   - `prop p(x R)`
   - `let x R`

2. What is the outcome of `2 > 3`? Why?

3. Explain the difference between a proposition and a factual statement.

### Bonus: The Power of Simple Foundations

Euclid showed us over 2000 years ago how 5 axioms could derive such a wonderful geometric world. Simple starting points often lead us into infinitely complex worlds. The same is true for mathematics. With just very few absolutely accurate inference rules, plus a few axioms, we can derive a rich and diverse mathematical world. That is what math is all about.

---

## Section 2: Specific Facts - Building Blocks of Reasoning

### Introduction

In this section, we'll explore **specific facts**—the simplest type of factual statements. These are statements about specific objects, like "1 < 2" or "x = 5". By the end of this section, you'll understand how specific facts are constructed and how they form the foundation of all reasoning.

### From Natural Language to Litex

Just like in natural language, facts in mathematics are also composed of verbs and nouns. For example, in the statement "1 < 2", the verb is "<", while the arguments, 1 and 2, serve as nouns.

**Natural Language**: "Seventeen is less than forty-seven"  
**Litex**: `17 < 47`  
**Structure**: verb: `<`, nouns: `17`, `47`

**Natural Language**: "Seventeen times forty-seven equals seven hundred ninety-nine"  
**Litex**: `17 * 47 = 799`  
**Structure**: verb: `=`, nouns: `17 * 47`, `799`

### Examples of Specific Facts

Here are some examples:

```litex
17 < 47 # verb: <, nouns: 17, 47
17 * 47 = 799 # verb: =, nouns: 17 * 47, 799
17 != 47 # verb: !=, nouns: 17, 47
```

### Built-in vs Custom Propositions

Besides builtin propositions (verb) like `>`, `=`, `!=`, you can also use your own propositions using `prop` keyword.

**Built-in propositions:**
```litex
1 > 0
2 = 2
3 != 4
```

**Custom propositions:**
```litex
prop is_positive(x R)
$is_positive(5)  # Using custom proposition
```

### Summary

- Specific facts are statements about specific objects
- They consist of a verb (proposition) and nouns (objects)
- Built-in propositions like `>`, `=`, `!=` are always available
- Custom propositions can be defined with `prop`
- Specific facts are the building blocks of all reasoning

### Litex Syntax Reference

**Built-in propositions**: `=`, `!=`, `>`, `<`, `>=`, `<=`, `$in`

**Custom proposition**: `prop propName(x set)` - defines a new proposition

**Factual statement**: `$propName(object)` - applies proposition to object

**Infix notation**: For two-argument propositions, you can write `obj1 $prop obj2`

### Exercises

1. Write a specific fact stating that 5 is greater than 3.
2. Define a custom proposition `is_even(x N)` and write a factual statement using it.
3. Explain the structure of the factual statement `17 * 47 = 799`.

### Bonus: The Structure of Facts

In mathematics, every fact has a structure: a predicate (verb) and arguments (nouns). This structure is fundamental to how we reason. When we say "1 < 2", we're applying the "less than" predicate to the numbers 1 and 2. This same structure appears in Litex, making it natural and intuitive.

---

## Section 3: Universal Facts - The Power of `forall`

### Introduction

In this section, we'll explore **universal facts**—statements that begin with `forall`. These are incredibly powerful because they allow us to make general statements that apply to infinitely many specific cases. By the end of this section, you'll understand how to write and use universal facts effectively.

### From Natural Language to Litex

_Deduction: inference in which the conclusion about particulars follows necessarily from general or universal premises._

_— Merriam-Webster Dictionary_

Mathematics is fundamentally about deducing new facts from previously established ones. Among these, **universal facts** (statements beginning with `forall`, also called `forall` statements) play a central role: they allow us to derive infinitely many specific instances.

**Natural Language**: "For all positive natural numbers x, x is a natural number"  
**Litex**: `forall x N_pos => x $in N`

This single universal statement can generate infinitely many specific statements:

```
1 $in N
2 $in N
3 $in N
...
```

Since there are infinitely many positive natural numbers, this single universal statement gives rise to infinitely many true statements.

### Universal Facts in Litex

Universal statements in Litex express the idea of "for all …, if certain assumptions hold, then certain conclusions follow."

Here is a trivial but valid example:

```litex
forall x N_pos:
    x $in N_pos
```

This reads: *for all `x` in `N_pos` (the set of positive natural numbers), `x` is in `N_pos`.*  
The assumption and the conclusion are identical, so the statement is always true.

### Syntax of `forall`

The complete syntax is:

```litex
forall parameter1 set1, parameter2 set2, ...:
    domFact1
    domFact2
    ...
    =>:
        thenFact1
        thenFact2
        ...
```

This means: *for all parameter1 in set1, parameter2 in set2, …, if domain facts (domFacts) are satisfied, then the conclusions (thenFacts) are true.*  
You can think of domain facts as the **restrictions or assumptions** required for the parameters.

### The `$in` Proposition

The symbol `$in` is a built-in proposition in Litex that means "is in." So you can write either:

```litex
1 $in N_pos
```

or equivalently:

```litex
$in(1, N_pos)
```

Both assert the same fact.

### Inline Universal Statements

Litex also supports a compact **inline form**:

```litex
forall parameter1 set1, parameter2 set2, ... : inline domain facts => inline conclusion facts
```

Inline facts follow two rules:

1. A **specific fact** is followed by `,`
2. A **universal fact** is followed by `;`

**Examples:**

```litex
forall x N_pos => x $in N_pos
forall x N_pos: forall y N_pos: y > x => y > x; x > 10 => forall y N_pos: y > x => y > x; x > 10
```

### Universal Facts with Restrictions

Often, we want to express universal statements with additional restrictions. For instance:

*For all real numbers `x` and `y`, if `x > 0` and `y > 0`, then `x > 0` and `y > 0`.*

In Litex:

```litex
know forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

To make such declarations more concise, Litex lets you omit some reserved words in certain contexts. For example, `dom` can be hidden:

```litex
forall x, y R:
    x > 0
    y > 0
    =>:
        x > 0
        y > 0
```

Inline version:

```litex
forall x, y R: x > 0, y > 0 => x > 0, y > 0
```

### Equivalent Facts

Sometimes, you want to assert that two conclusions are **equivalent** under the same restrictions. In that case, you can add an `iff` block:

```litex
forall x R:
    dom:
        x > 1
    =>:
        not x = 2
    <=>:
        x != 2
```

Inline version:

```litex
forall x R: x > 1 => not x = 2 <=> x != 2
```

> **Note:** This format only supports equivalences of the form `fact_1 <=> fact_2`. Both facts must be logically equivalent.

### Examples

Universal statements are everywhere in math. Here's an example showing reflection properties:

```litex
have people nonempty_set
have oddie_bird, hippo_dog people
prop we_are_friends(x, y people)
know:
    forall x, y people => $we_are_friends(x, y) <=> $we_are_friends(y, x)
    $we_are_friends(oddie_bird, hippo_dog)
$we_are_friends(hippo_dog, oddie_bird)
```

### What Happens If Requirements Are Wrong?

Suppose we have the following code:

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

Wait, why is `7 = 8` true without any contradiction?

The answer is that the requirements in the universal fact are wrong. There is no such `x` and `y` that satisfies the requirements. The reason why validation won't cause any trouble is, no such `x` and `y` exists that can match the requirements of the universal fact. So the newly verified fact will never be used to verify other facts.

### Conditional Universal Facts

Sometimes, you want to express a universal fact without universal parameters. For example:

```litex
have x R

forall:
    x = 1
    =>:
        x = 1 * 1
```

Notice that no extra parameters are needed in the universal fact. What we are doing is: assuming a parameter defined elsewhere (not in the scope of the universal fact) and assuming it satisfies the requirements of the universal fact. This is very similar to `if` statement in programming languages. We actually allow you to use keyword `when` to do so in Litex:

```litex
have x R

when:
    x = 1
    =>:
        x = 1 * 1
```

This looks much more natural and readable, right?

### Summary

- Universal facts (`forall`) allow us to make general statements
- They can generate infinitely many specific instances
- Domain facts provide restrictions on parameters
- Inline form saves space for simple statements
- `when` can be used for conditional facts without parameters
- If requirements are impossible, the fact is vacuously true but never used

### Litex Syntax Reference

**Basic syntax**: `forall param1 set1, param2 set2, ...: domFacts => thenFacts`

**Inline syntax**: `forall param1 set1, param2 set2, ...: inline domFacts => inline thenFacts`

**Conditional**: `when: condition => conclusion` (equivalent to `forall:` without parameters)

**Equivalence**: `<=>` for equivalent facts

**Domain facts**: Restrictions that must be satisfied

**Then facts**: Conclusions that follow when domain facts are satisfied

### Exercises

1. Write a universal fact stating that all natural numbers are greater than or equal to zero.
2. Write a universal fact with restrictions: for all real numbers x and y, if x > 0 and y > 0, then x + y > 0.
3. Explain what happens when the requirements of a universal fact are impossible to satisfy.

### Bonus: The Infinite Power of `forall`

The ability to make universal statements is what makes mathematics so powerful. A single `forall` statement can capture an infinite number of specific facts. This is the essence of mathematical abstraction: finding patterns that apply universally, rather than checking each case individually.

---

## Section 4: Match and Substitution - How Verification Works

### Introduction

In this section, we'll explore the fundamental mechanism by which Litex verifies statements: **match and substitution**. This is how Litex derives new facts from established ones. By the end of this section, you'll understand exactly how Litex checks if a statement is true.

### From Natural Language to Litex

How does Litex verify a statement?  
It all comes down to **match and substitution**—as simple as pressing `Ctrl + F` in your browser.

There are only two ways to perform match and substitution:

1. **From special case to special case**
2. **From general case to special case**

### From Special Case to Special Case

If we know a fact is true, then whenever we recall it later, it remains true.

```litex
have a R # It means a is in set R (R: The set of all real numbers)
know a = 1
a = 1
```

Here, since we already know `a = 1`, reclaiming it simply reproduces the same fact.

**Natural Language**: "We know a equals 1, so a equals 1"  
**Litex**: `know a = 1` followed by `a = 1` → **Result**: Verified by known fact

### From General Case to Special Case

The other way is to move from a general rule to a specific instance.

```litex
# Define three propositions
prop g(x Q)
prop s(x Q)
prop q(x Q)

know $g(1)
know forall x Q => $s(x)
know $q(1)
know forall x N: x > 7 => $g(x)
know forall x Q: x > 17 => $g(x)
$g(17.17)
```

We want to verify whether `$g(17.17)` is true.

**The Process:**

1. Litex scans all known facts with the proposition name `g`. Other facts (like `$q(1)` or `forall x Q => $s(x)`) are ignored because they use different proposition names.

2. Relevant facts for `g` are:
   - `$g(1)` - specific fact
   - `forall x N: x > 7 => $g(x)` - universal fact
   - `forall x Q: x > 17 => $g(x)` - universal fact

3. Now we check:
   - **Fact 1:** `$g(1)` applies only to `x = 1`. Since `1 ≠ 17.17`, it doesn't help.
   - **Fact 2:** For all natural numbers greater than 7, `g(x)` holds. But `17.17 ∉ N`, so this fact does not apply.
   - **Fact 3:** For all rationals greater than 17, `g(x)` holds. Since `17.17 ∈ Q` and `17.17 > 17`, this fact applies!

4. Therefore, `$g(17.17)` is verified. Once obtained, `$g(17.17)` itself becomes a new fact that can be used in future reasoning.

### Summary

In short, **match and substitution** is the fundamental mechanism by which Litex derives new facts. With basic arithmetic and axioms built in, the entire mathematical system can be constructed step by step through this simple yet powerful method. It is just a miracle how we can build a whole mathematical system by this simple method!!

### Litex Syntax Reference

**Match**: Litex searches for known facts that match the pattern of the statement to verify

**Substitution**: When a universal fact matches, Litex substitutes the parameters with specific values

**Verification process**:
1. Search for matching facts
2. Check if conditions are satisfied
3. Substitute and verify
4. Add verified fact to known facts

### Exercises

1. Given:
   ```litex
   know forall x R: x > 0 => x^2 > 0
   ```
   How would Litex verify `5^2 > 0`?

2. Explain the difference between "from special case to special case" and "from general case to special case".

3. In the example above, why doesn't `$g(1)` help verify `$g(17.17)`?

### Bonus: The Elegance of Match and Substitution

Match and substitution is deceptively simple, yet incredibly powerful. It's the same mechanism humans use when reasoning: we recall general principles and apply them to specific situations. Litex just makes this process explicit and verifiable. This simplicity is what makes Litex so intuitive—it mirrors how we actually think about mathematics.

---

## Section 5: Other Types of Facts

### Introduction

In this section, we'll explore other types of facts beyond specific and universal facts: existential facts, negation, and disjunction. These complete the toolkit for expressing all kinds of mathematical statements.

### Existential Facts

There is another kind of specific fact that is called **existential facts**. It is used to prove the existence of an object.

```litex
exist_prop x R st larger_than(y R):
    y > 0
    <=>:
        x > y

know forall y R => $larger_than(y)
```

The above example defines an existential proposition `larger_than` (For all `y` in `R` and `y > 0`, there exists `x` in `R` such that `x > y`). We know by default that `larger_than` is true for all `y` in `R`.

Existential facts are used as opposite of universal facts. For example, to disprove `forall x R => x > 0`, we only need to find a single `x` that is smaller than 0. Litex does not support `not forall` directly. You have to declare the related existential fact and then use the validation of this existential fact to represent the negation of a universal statement.

### Not: Truth Only Matters When Something Can Be False

Any specific fact can be negated by `not`.

The following example shows how to negate a specific fact:

```litex
let x R: x > 5

not x <= 5
```

To prove the negation of a specific fact, you can use `prove_by_contradiction` in `claim` block. For example:

```litex
prop p(x R)
prop q(x R)
know forall x R: $p(x) => $q(x); not $q(1)
claim:
    not $p(1)
    prove_by_contradiction:
        $q(1) # is true, because $p(1) is assumed to be true
```

You cannot write `not forall` in Litex. When you want to negate a universal fact, you must declare an `exist_prop` first and try to prove the existence of such an item that leads to `not forall`.

You can also negate an existence-proposition fact:

```litex
exist_prop x N_pos st exist_positive_natural_number_smaller_than_given_real_number(y R):
    x < y

know not $exist_positive_natural_number_smaller_than_given_real_number(0)
```

`!=` means `not =`. For example:

```litex
let little_little_o, little_o R:
    little_little_o != little_o

not little_little_o = little_o # true
```

### Or: Inclusive Disjunction

`or` represents an inclusive disjunction, meaning at least one of the conditions is true. You can use it like:

```litex
let x R: x = 1

or:
    x = 1
    x = 2

x = 1 or x = 2
```

The syntax is:

```litex
or:
    specific_fact1
    specific_fact2
    ...
    specific_factN

specific_fact1 or specific_fact2 or ... or specific_factN
```

You can write specific facts under `or` facts.

`or` facts can be written in `forall` facts:

```litex
let s set, a s: forall x s => x = 1 or x = 2; not a = 1

a = 2
```

`or` can also appear as dom of a `forall` fact:

```litex
know forall x R: x = 1 or x = 2 => x < 3
```

**Note**: When writing expressions like `(x = 1 and y = 2) or (x = 0 and y = 3)`, since Litex currently does not have an `and` keyword, if you need to combine multiple facts with `and` within an `or` case, you must name these specific facts explicitly, and then Litex will perform the `and` operation for you.

```litex
let x, y R

prop p():
    x = 1
    y = 2

know:
    x = 1
    y = 2

prop q():
    x = 0
    y = 3

$p() or $q()
```

### Or & Prove In Each Case

`or` is often used with `prove_in_each_case` to prove a fact in each case.

```litex
let a R: a = 0 or a = 1

prove_in_each_case:
    a = 0 or a = 1
    =>:
        a >= 0
    prove:
        a = 0
    prove:
        a = 1
```

Without `prove_in_each_case`, Litex would never be able to express many mathematical facts. Read "prove_in_each_case" section for more details.

### How is Or Facts Executed?

When the Litex kernel reads `fact1 or fact2 or ... or factN`, it will check if `fact1` is true or not under the assumption that `fact2`, ..., `factN` are not true.

That explains why the following code does not work:

```litex
know forall x, y R: x * y = 0 => x = 0 or y = 0
let a,b R
know a*b=0
a=0 or b=0
```

**Answer**: The reason why it does not work is related to how an `or` statement is executed.

When the Litex kernel reads `a=0 or b=0`, it will check if `a = 0` is true or not under the assumption that `b = 0` is not true. However, when we use `forall x, y R: x * y = 0 => x = 0 or y = 0` to check whether `a = 0` is true, the kernel could not know what `y = b` just by reading `a = 0`.

To fix this, give a name to the known fact `forall x, y R: x * y = 0 => x = 0 or y = 0`.

**Example 1:**

```litex
know @product_zero_implies_or(x, y R):
    x * y = 0
    =>:
        x = 0 or y = 0
let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```

**Example 2:**

```litex
prop product_zero_implies_or(x, y R):
    x * y = 0
    <=>:
        x = 0 or y = 0
know forall x, y R: x * y = 0 => $product_zero_implies_or(x, y)

let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```

### Summary

- Existential facts prove the existence of objects
- `not` negates specific facts
- `or` represents inclusive disjunction
- `or` works with `prove_in_each_case` for case-by-case proofs
- `or` execution checks each case assuming others are false
- Named universal facts help with `or` verification

### Litex Syntax Reference

**Existential proposition**: `exist_prop x set st propName(params): definition`

**Negation**: `not fact` - negates a specific fact

**Disjunction**: `fact1 or fact2 or ... or factN` - at least one is true

**Prove in each case**: `prove_in_each_case: or_facts => conclusion prove: ... prove: ...`

**Named universal fact**: `know @name(params): conditions => conclusions`

### Exercises

1. Write an existential proposition stating that there exists a real number greater than any given positive number.
2. Negate the statement `x > 0` where x is a real number.
3. Write a statement using `or` that says a number is either 0, 1, or 2.

### Bonus: The Completeness of Facts

With specific facts, universal facts, existential facts, negation, and disjunction, we can express virtually any mathematical statement. This completeness is what makes Litex so powerful—it can capture the full richness of mathematical reasoning while remaining simple and intuitive.
