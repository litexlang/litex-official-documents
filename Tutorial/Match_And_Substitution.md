# Match and Substitution: The Fundamental Mechanism of Litex

_万物之始，大道至简，衍化至繁. (All begins in simplicity; the Way is simple, yet gives rise to the complex.)_

_-- 老子 (Lao Tzu)_

How does Litex verify a statement?
It all comes down to **match and substitution**—as simple as pressing `Ctrl + F` in your browser.

There are only two ways to perform match and substitution:

1. **From special case to special case**
2. **From general case to special case**

## From Special Case to Special Case

If we know a fact is true, then whenever we recall it later, it remains true.

```litex
have a R # It means a is in set R (R: The set of all real numbers)
know a = 1
a = 1
```

Here, since we already know `a = 1`, reclaiming it simply reproduces the same fact.

## From General Case to Special Case

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
To do this, Litex scans all known facts with the proposition name `g`. Other facts (like `$q(1)` or `forall x Q => $s(x)`) are ignored because they use different proposition names.

Relevant facts for `g` are:

1. `$g(1)`
2. `forall x N: x > 7 => $g(x)`
3. `forall x Q: x > 17 => $g(x)`

Now we check:

* **Fact 1:** `$g(1)` applies only to `x = 1`. Since `1 ≠ 17.17`, it doesn’t help.
* **Fact 2:** For all natural numbers greater than 7, `g(x)` holds. But `17.17 ∉ N`, so this fact does not apply. (Q means the set of all rational numbers, N means the set of all natural numbers)
* **Fact 3:** For all rationals greater than 17, `g(x)` holds. Since `17.17 ∈ Q` and `17.17 > 17`, this fact applies.

Therefore, `$g(17.17)` is verified. Once obtained, `$g(17.17)` itself becomes a new fact that can be used in future reasoning.

## Summary

In short, **match and substitution** is the fundamental mechanism by which Litex derives new facts. With basic arithmetic and axioms built in, the entire mathematical system can be constructed step by step through this simple yet powerful method. It is just a miracle how we can build a whole mathematical system by this simple method!!