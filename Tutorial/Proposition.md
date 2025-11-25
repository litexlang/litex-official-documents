# Proposition: The Verbs of Logic

_Objects are typically noun phrases. Objects normally follow the verb in a clause._

_— Cambridge Dictionary_

---

## Section 1: Understanding Propositions

### Introduction

In this section, we'll explore **propositions**—the "verbs" of mathematical logic. Just as sentences in natural language have subjects and verbs, mathematical statements have objects (nouns) and propositions (verbs). By the end of this section, you'll understand what propositions are, how they differ from functions, and how to define and use them.

### From Natural Language to Litex

Math is the language of reasoning. Since it is a language, any sentence of it is composed of some objects (nouns) and a verb (proposition). For example, `1 + 1 = 2` is composed of object `1 + 1`, object `2`, and verb `=`.

**Natural Language**: "Jordan is intelligent"  
**Structure**: Subject (Jordan) + Verb (is intelligent)  
**Litex**: `$intelligent(Jordan)`  
**Structure**: Proposition (`intelligent`) + Object (`Jordan`)

A verb, in a mathematical sentence, is called proposition, at least in Litex. The result of any sentence is either true, unknown, or error.

**Important distinction**: Notice `+` is not considered a proposition, because it is a function, and there is no such thing as `1 + 1` is true or unknown. Function in math and Litex is just a symbol that is used to construct new symbols, not a verb for execution!

### Propositions vs Factual Statements

A proposition is something that can be true or false — it's a general statement form, often involving variables or placeholders. A factual statement is a proposition with all variables replaced by concrete values (or otherwise fully specified) so that its truth value is determined in a given context.

**Example:**

```litex
have human nonempty_set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

- `intelligent` is a **proposition** (a template)
- `$intelligent(Jordan)` is a **factual statement** (applying the proposition to a specific object)

The `$` symbol distinguishes a factual statement from a function.

### Another Example

In `1 > 0`, `1 > 0` is a factual statement, `>` is a proposition. A factual statement can be true or false, but not both. Factual statement `1 > 0` is true. Factual statement `0 > 1` is false.

**Think in this way**: In everyday expressions, there are subjects and predicates; whereas in reasoning language, a *proposition* functions like a verb, its parameters are the subjects. The outcome of this action can only be **true, unknown, error, or false**.

### Summary

- Propositions are the "verbs" of mathematical logic
- They are templates that become factual statements when applied to objects
- Functions (like `+`) are not propositions—they construct symbols, not statements
- The `$` prefix distinguishes factual statements from functions
- Propositions can have parameters (the "subjects")

### Litex Syntax Reference

**Proposition declaration**: `prop propName(parameter1 set1, parameter2 set2, ...)`

**Factual statement**: `$propName(object1, object2, ...)` - applies proposition to objects

**Built-in propositions**: `=`, `!=`, `>`, `<`, `>=`, `<=`, `$in`

**Infix notation**: For two-argument propositions, `obj1 $prop obj2`

### Exercises

1. What is the difference between a proposition and a function?
2. Define a proposition `is_positive(x R)` and write a factual statement using it.
3. In the statement `5 > 3`, identify the proposition and the objects.

### Bonus: The Grammar of Mathematics

Just as natural language has grammar (nouns, verbs, etc.), mathematics has its own structure. Propositions are the verbs that connect objects together to form meaningful statements. Understanding this structure helps you write more natural and correct Litex code.

---

## Section 2: Defining Propositions

### Introduction

In this section, we'll learn how to define propositions in Litex. You'll learn the complete syntax, how to specify domains, and how to define equivalent facts. By the end of this section, you'll be able to define your own propositions for any mathematical concept.

### From Natural Language to Litex

**Natural Language**: "A number is positive if and only if it is greater than zero"  
**Litex**: 
```litex
prop is_positive(x R):
    x > 0
```

**Natural Language**: "Three numbers can form a triangle if and only if each is positive and the sum of any two is greater than the third"  
**Litex**:
```litex
prop can_form_a_triangle(x, y, z R):
    x > 0
    y > 0
    z > 0
    <=>:
        x + y > z
        x + z > y
        y + z > x
```

### Complete Syntax

The complete definition of a proposition is:

```litex
prop propName(parameter1 set1, parameter2 set2, ...):
    domFact1
    domFact2
    ...
    <=>:
        iffFact1
        iffFact2
        ...
```

Or you can write `dom` explicitly:

```litex
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

**Reading**: propName takes parameter1 in set1, parameter2 in set2, ..., and parameters must satisfy domFact1, domFact2, ..., . When the requirements of parameters are satisfied, `$propName(parameter1, parameter2, ...)` is true if and only if iffFact1, iffFact2, ... are all true.

### Simplifying the Syntax

When there is no domain facts, you can hide `<=>`:

```litex
prop propName(parameter1 set1, parameter2 set2, ...):
    iffFact1
    iffFact2
    ...
```

### Declaring Without Definition

Sometimes we just want to declare a proposition without specifying what facts it is equivalent to. You can write:

```litex
prop propName(parameter1 set1, parameter2 set2, ...)
```

For example, we declare a proposition `p`, and after lines of code we set equivalent facts for it. Notice it does not mean that anything can lead to this proposition.

```litex
prop sum_larger_than_0(x, y R)

# ... lines of code

know forall x, y R => $sum_larger_than_0(x, y) <=> x + y > 0
```

### Specifying Domain Only

Also, you can specify the domain of a proposition at declaration time without specifying its equivalent definition. Later, you can add the equivalent definition.

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0

# ... lines of code

know forall x, y, z R: x > 0, y > 0, z > 0 => $can_form_a_triangle(x, y, z) <=> x + y > z, x + z > y, y + z > x
```

In Litex, `dom` corresponds to the "domain" in mathematical writing. It specifies the range of the parameters that are allowed to be passed to the proposition.

### Inline Definitions

In everyday mathematical writing, we usually put definitions on a single line. Litex allows you to do so, which saves you a lot of lines. Here are examples:

```litex
prop p(x, y R)
prop p3(x, y R) <=> x > y
prop p4(x, y R): x > y <=> x + y > 10
```

The equivalent multiline-version writes like this:

```litex
prop p(x, y R)
prop p3(x, y R):
    x > y
prop p4(x, y R):
    x > y
    <=>:
        x + y > 10
```

### Summary

- Propositions can be defined with complete syntax including domain and equivalent facts
- Domain facts (`dom`) specify restrictions on parameters
- Equivalent facts (`<=>`) define when the proposition is true
- You can declare propositions without definitions and add them later
- Inline syntax saves space for simple definitions

### Litex Syntax Reference

**Full syntax**: `prop name(params): domFacts <=> iffFacts`

**Domain only**: `prop name(params): dom: restrictions`

**Equivalent only**: `prop name(params): iffFacts`

**Declaration only**: `prop name(params)`

**Inline**: `prop name(params) <=> fact` or `prop name(params): condition <=> fact`

### Exercises

1. Define a proposition `is_even(n N)` that is true when n is even.
2. Define a proposition with domain restrictions: `is_positive_reciprocal(x, y R)` where x and y must be positive.
3. Write both inline and multiline versions of a proposition definition.

### Bonus: The Flexibility of Proposition Definitions

Litex gives you flexibility in how you define propositions. You can define everything at once, or build up the definition gradually. This flexibility mirrors how mathematicians work: sometimes we define concepts completely, sometimes we introduce them and fill in details later.

---

## Section 3: Using Propositions

### Introduction

In this section, we'll learn how to use propositions once they're defined. You'll learn how to call propositions, how Litex automatically infers equivalent facts, and how to work with named universal facts. By the end of this section, you'll be able to use propositions effectively in your proofs.

### From Natural Language to Litex

**Natural Language**: "Is 3, 4, 5 a valid triangle?"  
**Litex**: `$can_form_a_triangle(3, 4, 5)`

**Natural Language**: "For all real numbers x, y, z, if they can form a triangle, then x + y > z"  
**Litex**: 
```litex
know forall x, y, z R: $can_form_a_triangle(x, y, z) => x + y > z
```

### Calling a Proposition

After claiming a Proposition, you could call it anywhere with a prepend `$`:

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

If there is only two Objects in parentheses of Proposition claim, you could also call it like:

```litex
prop divisible_by(n, m R):
    m != 0
    <=>:
        n % m = 0

6 $divisible_by 3
```

### Automatic Inference of Equivalent Facts

When we know or proved a fact is true, Litex automatically knows all the equivalent facts are true.

**Example:**

```litex
prop transitivity_of_less_operator(x, y, z R):
    x < y
    y < z
    <=>:
        x < z

know forall a, b, c R: a < b, b < c => $transitivity_of_less_operator(a, b, c)
```

When `$transitivity_of_less_operator(a, b, c)` is true, Litex automatically infers all facts that are logically equivalent to it.

In this example, `$transitivity_of_less_operator(x, y, z)` states that `x < z` is equivalent to `x < y` and `y < z` being true. By substituting `x = a`, `y = b`, and `z = c`, we obtain `a < c`. Since Litex knows these two statements are equivalent, `a < c` is automatically established.

This automatic derivation of equivalent facts is an essential feature of Litex. Without it, even if we had a statement like:

```litex
forall a, b, c R: a < b, b < c => a < c
```

we would not be able to directly prove `a < c` in some situations—because we might not know which specific `b` is being used to satisfy the universal statement.

### Named Universal Facts

It is often we want to use a universal fact to check a specific fact. And we find that there are more parameters in the universal fact than the specific fact. For example:

```litex
know forall a, b, c R: a < b, b < c => a < c
let a, b, c R: a < b, b < c
# a < c # This does not work!
```

We cannot prove `a < c` since we do not know which `b` is used by `forall a, b, c R: a < b, b < c => a < c` to prove `a < c`.

It turns out we can give a name to the forall statement by defining a new proposition.

```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c
    <=>:
        a < c
know forall a, b, c R: a < b, b < c => $transitivity_of_less(a, b, c)

let a, b, c R: a < b, b < c
$transitivity_of_less(a, b, c)
a < c
```

However, this is not the best way to do it. Litex provides you a short way to do it.

```litex
know @transitivity_of_less(a, b, c R):
    a < b
    b < c
    =>:
        a < c
```

The above example means:

```litex
prop transitivity_of_less(a, b, c R):
    a < b
    b < c

know forall a, b, c R: $transitivity_of_less(a, b, c) => a < c
know forall a, b, c R: a < b, b < c => a < c
```

### Using Named Universal Facts

Named universal fact can be used in the following situations:

**1. Follow keyword `know`:**

```litex
know @name(parameter1 set1, parameter2 set2, ...):
    fact1
    fact2
    ...
    =>:
        then_fact1
        then_fact2
        ...
```

**2. Follow keyword `claim`:**

```litex
claim:
    @propName(parameter1 set1, parameter2 set2, ...):
        fact1
        fact2
        ...
        =>:
            then_fact1
            then_fact2
            ...
    prove:
        ...
```

**3. Use directly:**

```litex
@propName(parameter1 set1, parameter2 set2, ...):
    fact1
    fact2
    ...
    =>:
        then_fact1
        then_fact2
        ...
```

### Example: Transitive Relations

Sometimes, a proposition has transitive properties. For example, being colleagues is a transitive relation.

```litex
have people nonempty_set
have oddie_bird, hippo_dog, thin_penguin people
prop are_colleagues(x, y people)
know @are_colleagues_transitive(x, y, z people):
    $are_colleagues(x, y)
    $are_colleagues(y, z)
    =>:
    	$are_colleagues(x, z)
know:
    $are_colleagues(oddie_bird, hippo_dog)
    $are_colleagues(hippo_dog, thin_penguin)
$are_colleagues_transitive(oddie_bird, hippo_dog, thin_penguin)
$are_colleagues(oddie_bird, thin_penguin)
```

### Summary

- Propositions are called with `$propName(objects)`
- Two-argument propositions can use infix notation: `obj1 $prop obj2`
- Litex automatically infers equivalent facts from propositions
- Named universal facts (`@name`) provide a concise way to define and use universal statements
- Named universal facts can be used with `know`, `claim`, or directly

### Litex Syntax Reference

**Calling proposition**: `$propName(obj1, obj2, ...)`

**Infix notation**: `obj1 $prop obj2` (for two-argument propositions)

**Named universal fact**: `know @name(params): conditions => conclusions`

**Automatic inference**: Litex automatically knows equivalent facts when propositions are true

### Exercises

1. Define a proposition `is_friend(x, y people)` and call it for two specific people.
2. Use a named universal fact to express transitivity of friendship.
3. Explain how Litex automatically infers `a < c` from `$transitivity_of_less(a, b, c)`.

### Bonus: The Power of Named Universal Facts

Named universal facts combine the power of propositions with the convenience of universal statements. They let you give names to common proof patterns, making your code more readable and reusable. This is similar to how mathematicians name theorems: once you've proven a general pattern, you can refer to it by name rather than repeating the proof.

---

## Section 4: An Example - Relations and Their Properties

### Introduction

In this section, we'll work through a complete example showing how to formalize relations and their properties (transitivity, commutativity, reflexivity) in Litex. This will tie together everything we've learned about propositions.

### From Natural Language to Litex

We have already known how to declare new objects and propositions. Here is a thorough example that takes you to walk through what we have already known. The following example shows how transitivity, commutativity, reflexivity, which are the most basic properties of a relation, is formalized in Litex.

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

As you can see, this example is not that "math". Reasoning happen everywhere and every time in our life!

### Summary

- Relations can be defined as propositions
- Transitivity: if x relates to y and y relates to z, then x relates to z
- Commutativity: x relates to y if and only if y relates to x
- Reflexivity: every element relates to itself
- These properties can be formalized using propositions and universal facts

### Exercises

1. Define a relation `likes(x, y people)` and show it's symmetric (commutative).
2. Define a relation that is transitive but not symmetric.
3. Explain how the example above demonstrates transitivity.

### Bonus: Relations in Everyday Life

Relations aren't just mathematical abstractions—they appear everywhere in our daily lives. Friendships, leadership, preferences—all of these can be modeled as relations with specific properties. Litex lets you formalize and reason about these relationships just as you would mathematical ones.
