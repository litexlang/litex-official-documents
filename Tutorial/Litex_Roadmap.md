# Litex Roadmap

_All human knowledge begins with intuitions, thence passes to concepts and ends with ideas._

_- Kant_

There are two kinds of Litex statements:

1. **Factual statements**: Used for verification. Once verified, they are stored as known facts for future verification.

2. **Non-factual statements**: Not used for verification. They may define objects, import packages, etc.

## Factual Statements

**Structure**: Verb plus nouns.

Mathematical verification is essentially a game: introduce verbs (propositions/predicates) and nouns (objects), then verify that these objects satisfy the predicates. Some are easy to verify (e.g., `1 + 1 = 2`), others are hard (e.g., Fermat's Last Theorem).

Litex's strength lies in its few but effective verification mechanisms that help users verify factual statements. Other formal languages require extensive manual proof steps even for simple statements, but Litex's powerful and practical kernel handles most of the work automatically, making proofs much easier to write.

**Output**: `true`, `unknown`, or `error`

1. **true**: Litex found a proof. The proof process is printed.

2. **unknown**: Litex couldn't find a proof. The statement may be false, or your process may be incomplete, preventing Litex from verifying it using existing facts and verification mechanisms.

3. **error**: An error occurred. Possible causes: referencing a non-existent object, using function parameters outside the function's domain, or syntax errors.

> **Note**: Functions are objects, not proposition predicates. Predicates judge truth values; functions are special symbols that combine other objects (satisfying the function's domain) into new symbols. Functions can be passed as parameters to factual statements.

## Non-factual Statements

Mathematics isn't just about truth values. Some statements define objects or predicates. Without the ability to define objects and predicates, the mathematical world would be very limited. We use `prop` to define predicates and `have` to define objects.

Litex's built-in verification is simple. This makes it easy to learn and efficient to run, but special proof formats require additional keywords like `prove_by_contradiction` and `prove_case_by_case`.

## Effects of Litex Statements

When you execute a statement, Litex prints information about its effects. Every mathematical statement in Litex has exactly 4 types of effects: **define**, **verify**, **memorize**, and **infer**.

Example:

```litex
have a R = 17
```

Output:

```
*** line 1 ***

--- statement ---

have a R = 17

--- definition ---

a is a new object
a = 17
a $in R

--- verification process ---

17 $in R
proved by builtin rules:
17 is literally a real number

*** line 1: success! ***

Success! :)

```

A single statement can involve multiple effects. For example, `have a R = 17` primarily defines a new object `a` equal to 17, involving define, memorize, and verify effects. As you can see, it is very easy to understand how a statement works in Litex.

Here is another example:

```litex
prop p(x R)

know not exist z R st $p(z)
```

```
*** line 1 ***

--- statement ---

prop p(x R)

--- definition ---

p is a new prop

*** line 1: success! ***

*** line 3 ***

--- statement ---

know not exist z R st $p(z)

--- new fact ---

not exist z R st $p(z)

--- infer ---

forall z R:
    not $p(z)

--- warning ---

`know` saves the facts you write without verification. You may introduce incorrect facts by mistake. Use it with great caution!

*** line 3: success! ***

Success! :)
```

As you can see, since `not exist` is equivalent to `forall not`, the litex kernel automatically infers that and memorize it. Inference often occurs when 1. Litex generates simple facts for you, e.g. when `a > 0`, litex generates `1 / a > 0`, `a != 0` for you. 2. Equivalent facts, like situation here.

Fortunately, there aren't many types of common mathematical statements, and Litex expresses their functions clearly. You don't need to learn much! If you encounter something unfamiliar, consult the Tutorial.

## Conclusion

Keep in mind the following points before moving on, I believe it will help you understand Litex better.

1. There are 2 kinds of statements in Litex: factual statements for verification and if it is verified, it will be memorized for future use. Non-factual statements for definition, special proof strategy, or other functionalities.

2. A factual statement is composed of one verb called proposition and some nouns called objects. The output of a factual statement might be true, unknown or error.

3. A statement may has some of the 4 effects: define, verify, memorize, infer.

## More Examples

Run the following code to see how statements take these effects.

```litex
have x set = {x R: x > 0}
17 $in x
```

```litex
know forall x R: exist z R: z > x
have y R st y > 100
```

```litex
let x R, y R:
    2 * x + 3 * y = 100
    x + 4 * y = 17

2 * (x + 4 * y) = 2 * 17 = 2 * x + 8 * y = 34
2 * x + 3 * y - (2 * x + 8 * y) = 100 - 34 = -5 * y
y = (100 - 34) / (-5)
```

```litex
prop a_larger_than_1_real_number_is_smaller_than_17(x R):
    dom:
        x > 1
    <=>:
        x < 17

$a_larger_than_1_real_number_is_smaller_than_17(7)
```

```litex
have x set = {1, 2, 3}
forall y x: y = 1 or y = 2 or y = 3
```

```litex
have fn f(x, y R) R = x + y
f(1, 2) = 1 + 2 = 3
```

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)
    not $q(17)

# short version
prove_by_contradiction not $g(17):
    $s(17)
    $q(17)

claim:
    not $g(17)
    prove_by_contradiction:
        $s(17)
        $q(17)
```