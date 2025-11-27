# Equality: The Foundation of All Mathematics

_If it looks like a duck, swims like a duck, and quacks like a duck, then it probably is a duck._

_- Duck Test_

---

## The Fundamental Role of Equality

Equality (`=`) is the **most fundamental proposition** in mathematics. It is not merely one proposition among many; rather, **all other propositions depend on equality** for their definition and verification.

In mathematics and Litex, equality serves as the foundation because:

Equality makes symbols that are literally different have the same meaning. A symbol can be an atom (like `1`, `a`) or a function expression (like `1 + 2`, `f(x)`). When we say two symbols are equal, we mean they have completely identical meaning, even though they may look different.

**Example 1: Equality makes different literal symbols equivalent**

```litex
# Numeric equality: 1 + 1 and 2 are different symbols, but equal
1 + 1 = 2

# Variable equality: 20 * x and y + z are different symbols, but equal
have x R
have y R = 3 * x
have z R = 17 * x
20 * x = 3 * x + 17 * x = y + z

# Function equality: f(a) and g(b) are different symbols, but equal
have fn f(a R) R = a
have fn g(a R) R = f(a)
have a R
have b R = a
f(a) = g(b)
```

In all these cases, equality connects symbols that are literally different but semantically identical.

**Example 2: Other propositions depend on equality for verification**

```litex
# We know a > b is true
let a, b, c R:
    a > b
    a = c

# Because a = c, we can substitute c for a
# Therefore c > b is also true
c > b

prop p(a R)
know $p(a)
$p(c) # $p(c) is true because $p(a) is true and a = c
```

When `a = c` is known, `a` can be equivalently replaced with `c` in any proposition. This is why `c > b` is verified: Litex substitutes `c` for `a` in the known fact `a > b`. **In essence, equality means that different symbols (whether atoms like `1`, `a`, or function expressions like `1 + 2`, `f(x)`) have completely identical meaning.**

## How Litex Verifies Equality

When proving equality, Litex tries each step in order from the first to the last.

1. **Step 1: Simplify numeric expressions**

If both sides of the equality are numeric expressions, Litex simplifies and actually computes them.

**Note**: This is string matching, not floating-point arithmetic. When division doesn't result in an integer, the `/` is preserved. For example, `2/3 = 4/6` is not verified by computing the actual values, but by proving that `3 * 4 = 2 * 6`.

2. **Step 2: Search known facts**

Before searching known facts, we need to understand how Litex stores equality facts. The storage method for equality facts differs from other facts because equality has special properties such as transitivity and symmetry.

**Storage Mechanism**: Litex uses a hashmap to store equality relations. For each group of equal symbols, Litex creates an equivalence set and maps each symbol in the set to this set.

**Example**: Suppose we know that symbols `a`, `1+b`, and `f(c)` are equal. Litex creates an equivalence set `{a, 1+b, f(c)}` and maps each symbol to this set:
- `equalityMap["a"] = {a, 1+b, f(c)}`
- `equalityMap["1+b"] = {a, 1+b, f(c)}`
- `equalityMap["f(c)"] = {a, 1+b, f(c)}`

Similarly, if symbols `h` and `8+t` are equal, they form another equivalence set:
- `equalityMap["h"] = {h, 8+t}`
- `equalityMap["8+t"] = {h, 8+t}`

**Merging Equivalence Sets**: When we prove a new equality relation that connects two different equivalence sets, Litex merges them. For example, if we prove `a = 8 + t`, then the set containing `a`, `{a, 1+b, f(c)}`, and the set containing `8+t`, `{h, 8+t}`, are merged into a new equivalence set `{a, 1+b, f(c), h, 8+t}`. All related symbols are then updated to point to this merged set:
- `equalityMap["a"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["1+b"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["f(c)"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["h"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["8+t"] = {a, 1+b, f(c), h, 8+t}`

In this way, by checking whether two symbols are in the same equivalence set, Litex can quickly determine if they are equal.

**How does this storage relate to proving symbol equality?**

For example, if we want to prove `1 + b = h`, we check whether `equalityMap["1+b"]` and `equalityMap["h"]` are in the same equivalence set. If they are, then `1 + b = h` is true. If we find they are indeed equal, then it's verified.

Another example: if we want to prove `2 - 1 + b = h`, we find that `2-1+b` hasn't appeared before in the entire project, so there's no key for it in `equalityMap`. However, `equalityMap` has a key `"h"`, so we iterate through all symbols in `"h"`'s list to see if any equals `2-1+b`. If we find a match, it's verified. For example, when iterating through `{a, 1+b, f(c), h, 8+t}`, we find that `2-1+b = 1+b`, so it's verified.

3. **Function names and all function parameters are equal**

```litex
have fn f(a R) R = a
let g fn(R) R: g = f
have a R
have b R = a
f(a) = g(b)
```

How is `f(a) = g(b)` verified? There are no keys for `f(a)` and `g(b)` in `equalityMap` because they were just defined.

When both sides of the equality are function expressions rather than atoms, Litex recursively unwraps them, proving new equality facts. For example, here it proves `f = g`, then verifies that their parameters are equal, i.e., `a = b`.

Since `f(a)` and `g(b)` are both function expressions, not atoms, we need to recursively unwrap them. First, we verify that the function heads `f` and `g` are equal, then verify that their parameters `a` and `b` are equal. If they all match, it's verified.

4. **Verify using known forall facts**

```litex
prop p(x, y R)
know forall x, y R: $p(x, y) => x = y
let a, b R: $p(a, b)
a = b
```

Litex internally maintains a dedicated storage for known forall facts, called `ForallFactMap`. Each map's key is a proposition name, and the value is a list of related forall facts. For example, when you use `know` or prove a fact yourself, and learn that `forall x, y R: $p(x, y) => x = y` is true, then `ForallFactMap["="]` will add `forall x, y R: $p(x, y) => x = y` to its list.

When we want to prove `a = b`, we iterate through all forall facts in `ForallFactMap["="]`. During iteration, we see `forall x, y R: $p(x, y) => x = y`. We then verify: if we substitute `x` with `a` and `y` with `b`, are `a $in R`, `b $in R`, and `$p(a, b)` true? If yes, we then verify whether the corresponding `x = y` with `x` and `y` replaced by `a` and `b` respectively, i.e., `a = b`, is true. If that's also true, then it's verified.