# Statements

_You can checkout any time you like but you can never leave._

_— Hotel California_

In Litex, any statement has three possible outcomes: **true, unknown, or error**. 

When your factual statement is proven true, or other types of statements are correctly executed, the result is **true**.

If you enter a factual statement but the interpreter cannot find the corresponding known fact or built-in rule, it outputs **unknown**.

When you write an invalid sentence, such as operating on an undeclared object or entering a syntactically incorrect sentence, it results in an **error**.

Notice that these three kinds of outputs are produced by the Litex kernel **to the outside world of Litex**. They are not passed along to other Litex statements. This is different from programming: in programming, a statement’s output can often be used as the input of another statement (for example, in Python the result of `1 != 2` can be stored in a variable, and that variable can then be passed as a parameter to another statement).

This design actually makes sense. When a human is reasoning about mathematics, they see a sentence, and the outcome of that sentence (whether it’s correct, incorrect, or ill-formed) is registered in their mind—rather than being written down as an intermediate value for the next sentence to consume.

If an **unknown** or **error** occurs, the Litex kernel will terminate the current execution and notify you of the issue. If everything you wrote is correct, then the result is **success**!
