# Set: Where Modern Mathematics is Built Upon

Modern math is built upon set theory. In Litex, to ensure correctness and be more aligned with modern math, when the user wants to declare a new object, he must say which set it belongs to.

```litex
have a N, b Q, c R
let e N, f Q, g R
```

The keyword `set` is useless, unless there is a proposition that works together with it. In our case, as how math works, it is the keyword `in`.

```litex
have a N
a $in N
```

Actually, `have a N` has two effects: 1. declare an object `a` in current environment (context). 2. assume `a` is in set `N`, similar to `know a $in N`.

As `in` serves many use cases in math, it also serves many use cases in Litex.

1. serves as companion to `set`.

```litex
have a N
a $in N
```

2. A function satisfy a function template also uses the keyword `in`.

```litex
fn_template self_defined_seq(s set):
    fn (n N) s

fn f(n N) R

f $in self_defined_seq(R)
```

3. As parameter condition for everything: function, proposition, etc.

It is easy to introduce wrong facts if we do not have `set` requirement of things that might receive parameters. For example, it is strange to pass a set object to `+` (e.g. It is strange to say `empty_set + empty_set` ). It's also strange to say `2 $in 1` because 1 is not a set. To solve such ambiguity, we use `in` to require the parameter to be in a set at definition time.

(It sort of has the same functionality as `type` in programming languages like C, Java, TypeScript, etc. The user can only pass parameters that satisfy certain conditions to a function, proposition, etc.)