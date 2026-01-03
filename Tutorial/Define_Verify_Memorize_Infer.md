# Define, Verify, Memorize, Infer

_Design is not just what it looks like and feels like. Design is how it works._

_- Steve Jobs_

Any mathematical statement has some of the following effects: Define, Verify, Memorize, Infer. Define is the process of defining a new object or a new proposition predicate. Verify is the process of verifying a statement. Memorize is the process of memorizing a new fact for future use. Infer is the process of inferring new facts from your newly memorized facts.

Any time you execute a statement in Litex, it prints out something like this

```litex
have x R = 1

prop larger_than_zero(x R):
    x > 0

$larger_than_zero(x)

x > 0
```

```
*** line 1 ***

--- statement ---

have x R = 1

--- definition ---

x is a new object
x = 1
x $in R

--- verification process ---

1 $in R
proved by builtin rules:
1 is literally a real number

*** line 1: success! ***

*** line 3 ***

--- statement ---

prop larger_than_zero(x R):
    <=>:
        x > 0

--- definition ---

larger_than_zero is a new prop

--- new fact ---

forall x R:
    $larger_than_zero(x)
    =>:
        x > 0
forall x R:
    x > 0
    =>:
        $larger_than_zero(x)

*** line 3: success! ***

*** line 6 ***

--- statement ---

$larger_than_zero(x)

--- new fact ---

$larger_than_zero(x)

--- verification process ---

$larger_than_zero(x)
proved by fact stored on line 6:
$larger_than_zero(x) is equivalent to $larger_than_zero(1) by replacing the symbols with their values

--- infer ---

derive facts from $larger_than_zero(x):
x > 0

*** line 6: success! ***

*** line 8 ***

--- statement ---

x > 0

--- new fact ---

x > 0

--- verification process ---

x > 0
proved by fact stored on line 8:
x > 0 is equivalent to 1 > 0 by replacing the symbols with their values

--- infer ---

x != 0
x >= 0
not x <= 0
x > (-1 * x)
(-1 * x) < 0
(1 / x) > 0
(x ^ 2) > 0
sqrt(x) > 0

*** line 8: success! ***

Success! :)
```

It prints out all effects of all the statements in the code, making both humans and AIs easier to understand how Litex works and learn it with ease.

## Define

A statement in natural language involves nouns and verbs. In math, we have objects and proposition predicates. For example, `2 > 1` is a statement that involves the objects `2` and `1` and the proposition predicate `>`. Besides builtin objects and predicates like `1`, `2`, `3`, `>`, `=`, `!=`, you can also define your own objects and predicates using `have`/ `let` and `prop` keywords.

```litex
have x R
```

In this case, `x` is defined to be an object in the set of real numbers.

```litex
prop is_positive_number_larger_than_one(x R):
    dom:
        x > 0
    <=>:
        x > 1
```

In this case, `is_positive_number_larger_than_one(x)` is defined to be a proposition predicate that is true when `x` is a positive number and greater than one.

Notice there are 2 major differences between objects and proposition predicates:

1. When defining an object (a noun), you must prove its existence. When defining a proposition predicate (a verb), you do not need to prove its existence. Notice a function is an object in Litex, but it is not a proposition predicate.

2. You can pass nouns into predicates, but you cannot pass predicates to predicates.

## Verify

The core functionality of Litex is to verify statements. When you write a statement in Litex, Litex will try to use memorized facts to verify the statement. If the statement is verified, Litex will memorize the fact for future use.

```litex
1 = 1
forall x R: x > 0 => x > -1
```

However, statements besides factual statements may also involve verification process. For example

```litex
have x R = 17.17
```

In this case, `17.17 $in R` is verified, and `x = 17.17` is defined.

## Memorize

Memorization is the process of storing facts in Litex's knowledge base. When you write a statement in Litex, Litex will memorize the fact for future use.

```litex
prop p(x R)
know $p(1) # $p(1) is true without verification, $p(1) is memorized
2 > 1 # 2 > 1 is true with verification, 2 > 1 is memorized
```

## Infer

Infer is the process of inferring new facts from your newly memorized facts. When you write a statement in Litex, Litex will infer the fact for future use.

```litex
have x {1, 2, 3}
```

Besides `x $in {1, 2, 3}`, you can also infer other facts from your newly memorized facts like `x = 1 or x = 2 or x = 3`.

## Conclusion

It's amazing how simple it is: Any mathematical statement has and only has one of the following effects: Define, Verify, Memorize, Infer. Since there are not many mathematical statements in Litex and in math in general, as long as you remember how each statement takes those effects, you can understand how Litex works, completely!