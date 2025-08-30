# Proposition: The Verbs of Logic

A proposition is something that can be true or false — it’s a general statement form, often involving variables or placeholders. A factual statement is a proposition with all variables replaced by concrete values (or otherwise fully specified) so that its truth value is determined in a given context.

For example

```litex
have human nonempty_set, Jordan human
prop intelligent(x human)
know forall x human => $intelligent(x)
$intelligent(Jordan)
```

`intelligent` is a proposition. `$intelligent(Jordan)` is a factual statement. (`$` is for the difference between a specific fact and a function)

Another example is: In `1 > 0`, `1 > 0` is a factual statement, `>` is a proposition. A factual statement can be true or false, but not both. Factual statement `1 > 0` is true. Factual statement `0 > 1` is false.

Think in this way: In everyday expressions, there are subjects and predicates; whereas in reasoning language, a *proposition* functions like a verb, its parameters are the subjects. The outcome of this action can only be **true, unknown, error, or false**.

The complete definition of a proposition is:

```
prop propName(parameter1 set1, parameter2 set2, ...):
    domFact1
    domFact2
    ...
    <=>:
        iffFact1
        iffFact2
        ...
```

Or you can write `dom` in the first line:

```
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

It reads: propName takes parameter1 in set1, parameter2 in set2, ..., and parameters must satisfy domFact1, domFact2, ..., . When the requirements of parameters are satisfied, $propName(parameter1, parameter2, ...) is true if and only if iffFact1, iffFact2, ... are all true.

When there is no domain facts, you can hide `<=>`:

```
prop propName(parameter1 set1, parameter2 set2, ...):
    iffFact1
    iffFact2
    ...
```

Sometimes we just want to declare a proposition without specifying what facts it is equivalent to. You can write

```
prop propName(parameter1 set1, parameter2 set2, ...)
```

For example, we declare a proposition `p`, and after lines of code we set equivalent facts for it. Notice it does not mean that anything can leads to this proposition.

```litex
prop sum_larger_than_0(x, y R)

# ... lines of code

know forall x, y R => $sum_larger_than_0(x, y) <=> x + y > 0
```

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

When we know or proved a fact is true, Litex automatically know all the equivalent facts are true. For example:

When `$transitivity_of_less(a, b, c)` is true, Litex automatically infers all facts that are logically equivalent to it.

In this example, `$transitivity_of_less_operator(x, y, z)` states that `x < z` is equivalent to `x < y` and `y < z` being true. By substituting `x = a`, `y = b`, and `z = c`, we obtain `a < c`. Since Litex knows these two statements are equivalent, `a < c` is automatically established.

This automatic derivation of equivalent facts is an essential feature of Litex. Without it, even if we had a statement like

```
forall a, b, c R: a < b, b < c => a < c
```

we would not be able to directly prove `a < c` in some situations—because we might not know which specific `b` is being used to satisfy the universal statement.

By assigning a name to a `forall` statement and verifying it through that proposition name, Litex can then automatically conclude all equivalent facts, ensuring that results like `a < c` are immediately known.

Another example is about the triangle inequality:

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0
    <=>:
        x + y > z
        x + z > y
        y + z > x
```

## Claim an empty Proposition

Also, you can claim a Proposition without any logic but only a name like the following line, which means `x`, `y`, `z` in `N_pos` is able to form triangles in any situation. Obviously, this proposition is false with the knowledge we have. But you can still claim it anyway.

```litex
prop can_form_a_triangle(x, y, z N_pos)
```

Absolutely, you can claim a Proposition with only additional restrictions and no logic like the following lines, which express the similar meaning like the above line:

```litex
prop can_form_a_triangle(x, y, z R):
    dom:
        x > 0
        y > 0
        z > 0
```

> Note: If there is only dom in your Proposition, you can't hide `dom` anymore. Or Litex would misunderstand your lines with the situation that Proposition with `iff` only.

## Call a Proposition

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

## An example

We have already known how to declare new objects and propositions, here is a through example that takes you to walk through what we have already known. The following example shows how transitivity, commutativity, reflexivity, which are the most basic properties of a relation, is formalized in Litex.

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