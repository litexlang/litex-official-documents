# Specific Facts: Building Blocks of Reasoning

Just like in natural language, facts in mathematics are also composed of verbs and nouns. For example, in the statement 1 < 2, the verb is “<”, while the arguments, 1 and 2, serve as nouns. We call facts of this form specific facts, to distinguish them from universal facts that begin with forall.

Here are some examples:

```litex
17 < 47 # verb: <, nouns: 17, 47
17 * 47 = 799 # verb: =, nouns: 17 * 47, 799
17 != 47 # verb: !=, nouns: 17, 47
```

Besides builtin propositions (verb) like `>`, `=`, `!=`, you can also use your own propositions using `prop` keyword.