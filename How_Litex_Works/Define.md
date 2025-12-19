# Define

Version: 2025-12-18, Author: Jiachen Shen

_In mathematics you don't understand things. You just get used to them._

_- John von Neumann_

---

Every statement consists of verbs and nouns. Verbs are used to judge truth or falsity. Nouns are used to represent objects.

# Defining Nouns

Have Statement Execution Functions Documentation

This document lists all have-related AST statements and their execution functions.

## 1. HaveObjStStmt

syntax: have objects st some_exist_prop(params)

```litex
prop q(x, y R)
exist_prop x R p(y R):
    $q(x, y)
know $p(1)
have x st $p(1)
$q(x, 1) # true by definition of exist_prop p
```

Description:
- Verifies that the SpecFactStmt is satisfied
- Defines objects in the environment with properties by definition.

## 2. HaveObjInNonEmptySetStmt

syntax: have object from

Description:
- Verify that from is a non-empty set, or is a keyword (set, nonempty_set, finite_set)
- Define objects in the environment in that given nonempty set. When from is a keyword set, then $is_a_set(object) is true. When from is a keyword nonempty_set, then $is_a_nonempty_set(object) is true. When from is a keyword finite_set, then $is_a_finite_set(object) is true.

example:

```litex
have x R # R is a non-empty set, so you can take an element x from R
have y nonempty_set
have z y # $is_a_nonempty_set(y) is true, so you can take an element z from y
have w set # $is_a_set(w) is true, so w is a set
have v finite_set # $is_a_finite_set(v) is true, so v is a finite set
```

## 3. HaveObjEqualStmt

syntax: have object some_nonempty_set = some_other_object

Description:
- Verify that some_nonempty_set is a non-empty set
- some_other_object is an element of some_nonempty_set
- Define object with the equality fact: object = some_other_object

example:
```litex
have x R = 1
x = 1 # true by definition of equality
```

## 4. HaveFnEqualStmt

syntax: have fn function_name(param1 set1, param2 set2, ...) retSet = equalTo

Description:
- Verify that equalTo is an element of retSet
- Define the function with the equality fact

example:
```litex
have fn f(x, y R) R = x + y
f(1, 2) = 3
```

## 5. HaveFnEqualCaseByCaseStmt

syntax: 

have fn function_name(param1 set1, param2 set2, ...) retSet =:
    case condition1: value1
    case condition2: value2
    ...

Description:
- Verify condition1 or condition2 or ... is true
- Under each condition, value is in retSet

```litex
have fn f(x R) R =:
    case x > 0: x
    case x <= 0: 0

f(1) = 1
f(0) = 0
f(-1) = 0
```

## 6. HaveFnStmt

syntax: 
have fn:
    function_name(param1 set1, param2 set2, ...) retSet:
        domain_facts
        =>:
            then_facts
    prove:
        ...
    = value

We must prove the existence of the function by specifying a value for each element in the domain that satisfies the conditions.

Description:
- Verify that the prove facts are true when the domain facts are supposed to be true and parameters are instantiated.
- Verify value satisfies then facts and is in the retSet.

Example:

```litex
have fn:
    h(x R) R:
        x > 0
        =>:
            h(x) > 1
    prove:
        x + 1 > 1
    = x + 1
```

So we have a function h such that h(x) > 1 for all x > 0. `forall x R: h(x) = x + 1` is not emitted in the outer scope because it is part of the proof of the existence of the function h, not a fact.

## 7. HaveFnCaseByCaseStmt

syntax: 
have fn:
    function_name(param1 set1, param2 set2, ...) retSet:
        domain_facts
        ...
        =>:
            then_facts
            ...

        case condition1:
            proofs
            ...
        = value1
    
        case condition2:
            proofs
            ...
        = value2

Description:
- condition1 or condition2 or ... is true
- In each case, run the proofs and verify value satisfies then facts in fn definition and is in the retSet.

```litex
have fn:
    p(x R) R:
        x > 0
        =>:
            p(x) > x
    case 100 > x:
        do_nothing
    = 100
    case not 100 > x:
        x + 1 > x
    = x + 1
```

# Defining Verbs

Verbs in Litex are predicates—statements that can be evaluated as true or false. Unlike defining nouns (objects), defining verbs does not require proving existence. When you use a verb in a statement, it is prefixed with `$` to indicate it's a factual statement.

There are three types of verbs you can define in Litex: **prop predicates**, **exist_prop predicates**, and **implication facts**. Each serves a different purpose in mathematical reasoning.

## 1. Define prop predicate

**Syntax:**

```litex
prop predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts
```

**Description:**

Prop predicates are the most common way to define verbs in Litex. They establish a biconditional relationship (if and only if) between domain facts and the predicate itself. When a specific fact using this predicate is verified or known to be true, Litex automatically infers the corresponding facts from the definition.

**How it works:**

- The `domain_facts` specify the conditions under which the predicate applies
- The `iff_facts` specify what must be true when the predicate is true (and vice versa)
- When `$predicate_name(...)` is verified or known, Litex automatically knows that the `iff_facts` are true (with parameters substituted)
- Conversely, when the `iff_facts` are true and `domain_facts` are satisfied, the predicate is automatically known to be true

**Example:**

```litex
prop p(x, y R):
    x > y
    <=>:
        x + y > 10

let x, y R: $p(x, y) # Suppose $p(x, y) is true

x + y > 10 # true by definition of p
# Since $p(x, y) is true and x > y, we automatically know x + y > 10
```

## 2. Define exist_prop predicate

**Syntax:**

```litex
exist_prop variable_name set_name st predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts
```

**Description:**

Exist_prop predicates are used to express existential statements—statements about the existence of objects with certain properties. Unlike prop predicates, exist_prop predicates introduce a bound variable that represents the object whose existence is being asserted.

**How it works:**

- The `variable_name` is the bound variable that will be introduced when the existential statement is used
- The `set_name` specifies the set from which the variable is taken
- When you use `have variable st $predicate_name(...)`, Litex introduces a new object `variable` that satisfies the conditions in the definition
- The `iff_facts` can reference the bound variable to specify what properties it must have

**Example:**

```litex
exist_prop a R st exist_x_larger_than(x R):
    <=>:
        a > x

# First, we prove that such an object exists
claim:
    $exist_x_larger_than(1)
    prove:
        exist 2 st $exist_x_larger_than(1)  # 2 > 1, so the existential is true
        
$exist_x_larger_than(1)  # Now we know this is true

# Now we can introduce an object that satisfies the condition
have a st $exist_x_larger_than(1)
a $in R      # true: a is from R
a > 1        # true by definition of exist_x_larger_than
```

## 3. Define implication fact

**Syntax:**

```litex
imply fact_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    =>:
        then_facts
```

**Description:**

Implication facts express conditional relationships—if certain conditions hold, then certain conclusions follow. Unlike prop predicates which use biconditional (`<=>`), implication facts use one-way implication (`=>`).

**How it works:**

- The `domain_facts` specify the conditions under which the implication fact applies
- The `then_facts` specify the conclusions that follow when the premises are true
- When a specific implication fact is verified or known to be true, Litex automatically infers that the `then_facts` are true (with parameters substituted)
- Note that the reverse is not automatically true—knowing the `then_facts` does not automatically imply the `domain_facts`

```litex
prop p(x, y R)

know imply p_is_transitive(x R, y R, z R):
    x $p y
    y $p z
    =>:
        x $p z

let x, y, z R: x $p y, y $p z
$p_is_transitive(x, y, z)
x $p z
```

This is essential because verification process of Litex is based on match and substitution. 

## Important Note

In Litex, you don't need to name all facts explicitly, because Litex automatically searches for related facts in its knowledge base and uses them during verification. This automatic fact discovery greatly improves development efficiency—you can focus on the mathematical content rather than managing fact names and references manually.
