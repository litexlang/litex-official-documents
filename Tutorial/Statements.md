# Statements

_You can checkout any time you like but you can never leave._

_— Hotel California_

In Litex, any statement has three possible outcomes: **true, unknown, or error**. 

When your factual statement is proven true, or other types of statements are correctly executed, the result is **true**.

For example:

```litex
1 = 1 # true
let a R # Successfully declared a real number
```

If you enter a factual statement but the interpreter cannot find the corresponding known fact or built-in rule, it outputs **unknown**.

```litex
# The follow code will output unknown
1 = 2
```

When you write an invalid sentence, such as operating on an undeclared object or entering a syntactically incorrect sentence, it results in an **error**.

```litex
# The follow code will output error
You can checkout any time you like but you can never leave.
What the F**K are you talking about?
```

A very common mistake is

```litex
# The follow code will output error
1
```

You can not just write `1` and expect it to be true. `1` is  not a statement. You can write `1 = 1` to make it a statement.

```litex
1 = 1
```

Notice that these three kinds of outputs are produced by the Litex kernel **to the outside world of Litex**. They are not passed along to other Litex statements. This is different from programming: in programming, a statement’s output can often be used as the input of another statement (for example, in Python the result of `1 != 2` can be stored in a variable, and that variable can then be passed as a parameter to another statement). Just like the song "Hotel California" says: "You can checkout any time you like but you can never leave.", you can see whether a statement is true, unknown, or error by yourself, but that return value of the statement is not passed along to other statements.

This design actually makes sense. When a human is reasoning about mathematics, they see a sentence, and the outcome of that sentence (whether it’s correct, incorrect, or ill-formed) is registered in their mind—rather than being written down as an intermediate value for the next sentence to consume.

If an **unknown** or **error** occurs, the Litex kernel will terminate the current execution and notify you of the issue. If everything you wrote is correct, then the result is **success**!
