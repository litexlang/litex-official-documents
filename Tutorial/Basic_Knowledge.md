# Basic Knowledge: Everyday Math, the Litex Way

_Common Sense Is Not So Common_

_— Voltaire_

---

## Section 1: Numbers and Arithmetic

### Introduction

In this section, we'll explore how Litex handles numbers and basic arithmetic operations. You'll learn that Litex recognizes numbers directly—just like in everyday mathematics—and supports all the arithmetic operations you're familiar with. By the end of this section, you'll be able to write and verify numerical expressions in Litex as naturally as you write them on paper.

### From Natural Language to Litex

In mathematics, we often make statements like:
- "One plus one equals two"
- "Three is greater than zero"
- "Two is not equal to three"

In Litex, these translate directly to code:

```litex
1 + 1 = 2
3 > 0
2 != 3
```

Just as you would write `1 + 1 = 2` on paper, you write it the same way in Litex. The language understands numbers like `0`, `3.14159`, `-1` without any special declaration.

### Working with Arithmetic

Litex has built-in support for all common arithmetic operations. You can write complex expressions just as you would in mathematics:

```litex
0 * 4 + (9 - 3) * (2 - 1) = 6
1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55
```

**What Litex understands:**
- **Functional operators**: `+` (addition), `-` (subtraction), `*` (multiplication), `/` (division), `%` (modulo), `^` (exponentiation)
- **Factual operators**: `=` (equality), `!=` (inequality), `>` (greater than), `<` (less than), `>=` (greater than or equal), `<=` (less than or equal)

The inequality operator `!=` is equivalent to `not 2 = 3`, but the former is more concise and readable.

### Symbolic Arithmetic

Polynomials appear everywhere in mathematics. Unlike many formal languages, Litex has **native support for polynomials**, making them much easier to write and read.

In mathematics, we might say: "For any real numbers x, y, and z, the product (x + z²) · (x + 7y) equals x² + 7xy + xz² + 7yz²."

In Litex:

```litex
have x R, y R, z R
(x + z * z) * (x + 7 * y) = x * x + 7 * y * x + z * x * z + y * (3 + 4) * z * z
```

Litex can automatically verify polynomial identities through expansion and combination. Many fundamental algebraic facts are built-in:

```litex
# Distributive laws
forall a, b, c R => (a + b) * c = a * c + b * c
forall a, b, c R => a * (b + c) = a * b + a * c

# Associative laws
forall a, b, c R => (a + b) + c = a + (b + c)
forall a, b, c R => (a * b) * c = a * (b * c)

# Commutative laws
forall a, b R => a * b = b * a, a + b = b + a
```

### Summary

- Numbers in Litex work exactly as they do in everyday mathematics
- All standard arithmetic operators are built-in and work intuitively
- Litex has native support for polynomial manipulation
- Algebraic identities can be verified automatically

### Litex Syntax Reference

**Numeric literals**: Write numbers directly: `0`, `1`, `-1`, `3.14159`, etc.

**Arithmetic operators**:
- `+` : addition
- `-` : subtraction
- `*` : multiplication
- `/` : division
- `%` : modulo
- `^` : exponentiation

**Comparison operators**:
- `=` : equality
- `!=` : inequality (equivalent to `not ... = ...`)
- `>`, `<`, `>=`, `<=` : ordering relations

**Universal quantification**: `forall a, b, c R => ...` means "for all real numbers a, b, c, ..."

### Exercises

1. Write a Litex statement expressing that 5 plus 3 equals 8.
2. Write a Litex statement expressing that for any real numbers a and b, a + b equals b + a.
3. Verify the following polynomial identity in Litex:
   ```litex
   have x R, y R
   (x + y) * (x - y) = x * x - y * y
   ```

### Bonus: Solving Equations

Here's a complete example of solving a system of equations in Litex:

```litex
let x R, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14

# Multiply the first equation by 2
2 * (2 * x + 3 * y) = 2 * 10
4 * x + 6 * y = 20

# Subtract the second equation
(4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14
y = 6

# Substitute back
2 * x + 3 * 6 = 10
2 * x + 18 = 10
2 * x = -8
x = -4
```

Step by step, we find: $y = 6, \quad x = -4$

---

## Section 2: Sets

### Introduction

Modern mathematics is built on set theory. In Litex, sets are fundamental—when you declare an object, you must specify which set it belongs to. This section introduces Litex's built-in sets and how to work with them. You'll learn that Litex provides direct support for the number systems you use every day.

### From Natural Language to Litex

In mathematics, we say things like:
- "17 is a natural number"
- "-30 is an integer"
- "Every rational number is also a real number"

In Litex, these become:

```litex
17 $in N
-30 $in Z
forall x Q => x $in R
```

### Built-in Number Systems

Litex provides built-in support for commonly used sets:

- `N`: natural numbers (0, 1, 2, 3, ...)
- `N_pos`: positive natural numbers (1, 2, 3, ...)
- `Z`: integers (..., -2, -1, 0, 1, 2, ...)
- `Q`: rational numbers (fractions)
- `R`: real numbers
- `C`: complex numbers

### Working with Sets

Many fundamental facts about these sets are built into Litex:

```litex
# Natural numbers
17 $in N
0 $in N

# Integers
-47 + 17 $in Z
-30 $in Z

# Rational numbers
17.17 $in Q
3 / 2 $in Q

# Subset relationships
forall x Q => x $in R
forall x Z => x $in Q
forall x N => x $in Z
```

**What these statements mean:**
- `17 $in N` means "17 is in the set of natural numbers"
- `forall x Q => x $in R` means "for every rational number x, x is also a real number"

### What's Not in These Sets

It's equally important to understand what doesn't belong:

```litex
# Examples of not in N (natural numbers)
not -1 $in N
not 3.5 $in N
not (-1 * 1) $in N

# Examples of not in Z (integers)
not 3.5 $in Z
not (3 / 2) $in Z

# Examples of not in N_pos (positive integers)
not -1 $in N_pos
not 0 $in N_pos
not 3.5 $in N_pos
```

### Summary

- Litex requires you to specify which set an object belongs to
- Common number systems are built-in: N, Z, Q, R, C
- Subset relationships are automatically recognized
- The `$in` operator checks membership in a set

### Litex Syntax Reference

**Set membership**: `x $in S` means "x is an element of set S"

**Universal quantification with sets**: `forall x S => ...` means "for all x in set S, ..."

**Negation**: `not x $in S` means "x is not an element of set S"

**Built-in sets**:
- `N`: natural numbers
- `N_pos`: positive natural numbers  
- `Z`: integers
- `Q`: rational numbers
- `R`: real numbers
- `C`: complex numbers

### Exercises

1. Write a Litex statement expressing that 42 is a natural number.
2. Write a Litex statement expressing that every integer is also a rational number.
3. Which of the following are true? Write Litex statements to check:
   - Is 0.5 in the set of natural numbers?
   - Is -5 in the set of integers?
   - Is 2.5 in the set of rational numbers?

### Bonus: Why Sets Matter

In Litex, when you want to declare a new object, you must say which set it belongs to:

```litex
have a N, b Q, c R
let e N, f Q, g R
```

This ensures correctness and aligns with modern mathematics. The keyword `set` works together with `$in` to express membership. When you write `have a N`, Litex does two things:
1. Declares an object `a` in the current environment
2. Assumes `a` is in set `N`, similar to `know a $in N`

This requirement prevents errors like trying to add two sets together or checking if a number is in another number.

---

## Section 3: Symbols and Values

### Introduction

In Litex, everything is a symbol. Symbols can equal other symbols, and when two symbols are equal, they are interchangeable and share all properties. This section explains how Litex handles symbols and their values, which is crucial for understanding how verification works.

### From Natural Language to Litex

In mathematics, we often say:
- "Let x equal 1"
- "If we know that a equals 5, then a is greater than 0"

In Litex:

```litex
let x R: x = 1
# Now we can use x = 1 in verification

let a R: a = 5
a > 0  # Litex verifies this automatically
```

### Symbols Are Interchangeable

Everything in Litex is a symbol. When two symbols are equal, they are completely interchangeable:

```litex
let x R, y R: x = y
# Now x and y share all properties
# If we know x > 0, then y > 0 automatically
```

### Values and Verification

When one side of an equality is a numerical value, Litex remembers it as the value of the symbol on the other side:

```litex
let a, b R: a = 1, 2 = b
```

In this case:
- `1` is the value of `a`
- `2` is the value of `b`

**How verification works:**

When Litex verifies statements about a symbol, it:
1. First tries to replace the symbol with its known value
2. If verification works with the value, it's done
3. If not, it uses the symbol as-is for verification

**Example:**

```litex
let x R: x = 1
# We want to prove x > 0
x > 0
```

Litex automatically replaces `x` with `1`, checks `1 > 0`, and verifies it immediately. You don't need to write `1 > 0, x > 0` and use substitution manually.

### Summary

- Everything in Litex is a symbol
- Equal symbols are interchangeable and share properties
- Litex remembers numerical values of symbols
- Verification automatically uses known values when possible

### Litex Syntax Reference

**Equality**: `x = y` means "x equals y"

**Assignment with value**: `let x R: x = 1` declares x and assigns it the value 1

**Multiple assignments**: `let a, b R: a = 1, 2 = b` assigns values to multiple symbols

**Value substitution**: Litex automatically substitutes known values during verification

### Exercises

1. Declare a real number x with value 3, then verify that x > 0.
2. Declare two real numbers a and b such that a = 5 and b = 10. Verify that a + b = 15.
3. If x = y and we know x > 0, what can we say about y? Write Litex code to demonstrate.

### Bonus: The Power of Symbolic Computation

The value system in Litex enables powerful symbolic reasoning. Consider:

```litex
let x R: x = 2
let y R: y = 3

# These are automatically verified:
x + y = 5
x * y = 6
x^2 + y^2 = 13
```

Litex doesn't just store values—it uses them intelligently during verification, making proofs more natural and less verbose.

---

## Section 4: Comments

### Introduction

Good documentation is essential for understanding code. Litex supports comments that help you explain your reasoning and make your code more readable. This section covers the different types of comments available in Litex and when to use them.

### From Natural Language to Litex

When writing mathematics, we often add notes like:
- "Let x be a real number greater than 1"
- "This step uses the distributive property"

In Litex, these become comments:

```litex
# Let x be a real number greater than 1
let x R:
    x > 1
```

### One-Line Comments

Use `#` for single-line comments:

```litex
# This is a comment explaining the next line
let x R: x = 1

# Comments can appear after code too
x + 1 = 2  # This is automatically verified
```

### Multi-Line Comments

Litex supports multi-line comments using quotation marks. The number of quotes determines how they're displayed:

**Single quote `"`** - Markdown style comment:
```litex
"
This is a multi-line comment
that will be displayed as markdown
when rendered
"
```

**Double quotes `""`** - LaTeX style comment:
```litex
""
This is a multi-line comment
that will be displayed as LaTeX comment
when rendered
""
```

**Triple quotes `"""`** - Also LaTeX style:
```litex
"""
This is a multi-line comment
using triple quotes
"""
```

### When to Use Comments

Comments are helpful for:
- Explaining your reasoning
- Documenting complex steps
- Making your code self-documenting
- Helping the system understand your intent

**Example:**

```litex
# Solve the system: 2x + 3y = 10, 4x + 5y = 14
let x R, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14

# Multiply the first equation by 2
2 * (2 * x + 3 * y) = 2 * 10

# Subtract to eliminate x
(4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14
y = 6
```

### Summary

- Use `#` for single-line comments
- Use `"`, `""`, or `"""` for multi-line comments
- Comments help both humans and the system understand your code
- Good comments make proofs more readable and maintainable

### Litex Syntax Reference

**Single-line comment**: `# comment text`

**Multi-line comment (Markdown style)**: 
```litex
"
comment text
"
```

**Multi-line comment (LaTeX style)**:
```litex
""
comment text
""
```

or

```litex
"""
comment text
"""
```

### Exercises

1. Add a comment explaining what the following code does:
   ```litex
   let x R: x = 5
   x * 2 = 10
   ```

2. Write a multi-line comment explaining the steps in solving a quadratic equation.

3. Add appropriate comments to make this code more readable:
   ```litex
   let a R, b R, c R
   a = 1
   b = 2
   c = 3
   a + b + c = 6
   ```

### Bonus: Comments as Documentation

Comments in Litex serve dual purposes:
1. **Human readability**: Help other mathematicians (and future you) understand your reasoning
2. **System assistance**: Provide context that helps Litex's verification system understand your intent

Well-commented code is easier to debug, maintain, and extend. Think of comments as a conversation with your future self about why you made certain choices.

---

## Wrap-Up

Looks simple, doesn't it? Litex is designed to be **concise, readable, and close to everyday math**. 

In this tutorial, we've covered:
- **Numbers and Arithmetic**: How Litex handles numbers and operations just like everyday mathematics
- **Sets**: Built-in number systems and set membership
- **Symbols and Values**: How Litex treats everything as symbols and uses values for verification
- **Comments**: How to document your code effectively

At first, you might still make mistakes when writing your own proofs—and that's perfectly fine. Practice makes perfect. In the following tutorials, we'll guide you through more advanced features of Litex, so you can confidently express and verify mathematics the Litex way.

---

## Appendix: What does "Litex is easy to learn" mean?

When learning a formal language, we need to learn its syntax and semantic rules. Some languages have very few syntax and semantic rules. The advantage is that they are abstract enough to express all of mathematics; the disadvantage is that they are very unintuitive, and it's unclear how to use such abstract rules to write everyday mathematics. That is: learning the rules of the language, and learning how to use the language to express the everyday mathematics we want to express—the sum of these two tasks is the cost of learning a language.

Some languages have simple rules, such as Metamath, but because the rules are too abstract, most people cannot see how to connect these rules with the mathematics in their minds. Some languages have barriers in both rules and usage, such as Lean, which requires learning type theory and then writing mathematics within the framework of type theory. Both of them have found their own good balance in implementation-complexity, language intuitiveness, and logical expressiveness; while Litex chooses a different balance—with a larger kernel, but it is very intuitive and has good expressiveness.

Litex chooses axioms and inference rules that are the most intuitive, few in number, and directly relatable to *everyday mathematical expressions*. With these rules, users don't need to learn anything new—they can simply write Litex the same way they write mathematics in their daily practice. In summary, because Litex is close to everyday mathematical expression, it has unique advantages in both dimensions: learning the language rules and learning how to use these rules to express mathematics.
