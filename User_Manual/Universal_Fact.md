```markdown
# Universal Fact

## Description

`forall` is used to establish a universal rule or fact. It declares that for any objects matching specific types and domain conditions, a certain conclusion holds.

## Syntax
```
forall param1 set1, param2 set2, ... : dom: condition1 ... =>: conclusion_fact
```

## Examples

```litex
# Transitivity of inequality
forall x, y, z R:
    dom:
        x < y
        y < z
    =>:
        x < z
# Simple inline forall
forall n N: n > 0 => n + 1 > 1
```
## Semantics
Execution of this statement has the following effects:

1.It creates a "Universal Fact" (UniFactStmt) in the environment.

2.It allows the Litex engine to perform Universal → Specific matching. If the engine later encounters specific objects that satisfy the dom conditions, it can automatically infer the => conclusion.

3.If used inside a  know block, it asserts this fact is true.

## Notes
Universal facts are essential for defining axioms and theorems that apply to infinite sets.