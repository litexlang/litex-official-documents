# Define

Version: 2025-12-18, Author: Jiachen Shen

_In mathematics you don't understand things. You just get used to them._

_- John von Neumann_

---

Every statement consists of verbs and nouns. Verbs are used to judge truth or falsity.

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

Unlike defining nouns, defining verbs does not require proving existence. When called, they have prefix `$`.

## 1. Define prop predicate

prop predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts

This is the most common way to define verbs. When specific fact is verified or known to be true, the fact from the corresponding prop definition is automatically known.

```litex
prop p(x, y R):
    x > y
    <=>:
        x + y > 10

let x, y R: $p(x, y) # Suppose $p(x, y) is true

x + y > 10 # true by definition of p
```

2. Define exist_prop predicate

```
exist_prop predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts
```

```litex
exist_prop a R st exist_x_larger_than(x R) :
    <=>:
        a > x

# claim spec fact prove
claim:
    $exist_x_larger_than(1)
    prove:
        exist 2 st $exist_x_larger_than(1)
        
$exist_x_larger_than(1)
        
have a st $exist_x_larger_than(1)
a $in R
a > 1
```

3. Define implication fact
```
imply fact_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    =>:
        then_facts
```

When a specific implication fact is verified or known to be true, the fact from the corresponding implication definition is automatically known.

Note: In Litex, you don't need to name all facts, because Litex automatically searches for related facts and uses them. This greatly improves development efficiency.
