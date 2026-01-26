# Function Definitions

## Description

Functions in Litex can be defined in two ways: using `let fn` (to assume a function exists with certain properties) or `have fn` (to explicitly construct a function and prove its existence). 

## Syntax

###  Let fn (Assumption)
Used to declare a function signature and its behavior without proving it is well-defined.
```
let fn func_name(param1 type1, ...) return_type:
    dom:
        preconditions
    =>:
        postconditions/definition
```
### Have fn (Construction)
Used to define a function where you must prove the definition is valid.
```
#Define by Equality 
Have fn func_name(param1,type1,...) return_type =specific function

#Define with Proof
Have fn:
     func_name(param1,type1,...) return_type:
                    Dom:
                    =>:
                     Specific properties
            witness: #prove existence

#Case by case definition
Have fn func_name(param1,type1,...) return_type =:
                                case condition1: specific_value
                                case condition2: specific_value
                                ......
```

## Examples
```litex
# Assume a function f exists such that f(x) > x for all positive x
let fn f(x R) R:
    dom: 
        x > 0
    =>: 
        f(x) > x

#Define by Equality   
have fn q(x R) R = x^2 + 1

#Define with Proof
have fn:
        h(x R) R:
            x > 0
            =>:
                h(x) > 1
        witness:
            do_nothing
        = 100

#Case by case definition
have fn g(x R) R =:
            case x = 2: 3
            case x != 2: 4

```

## Semantics
### let fn
Semantics
When this statement is executed:

1. The symbol f is registered in the current environment. Its type is recorded as a function mapping from set A to set B.

2. The logical constraints in dom (e.g., P(x)) are stored as the precondition for calling f.

3. The system assumes that for any x in A satisfying P(x), the result f(x) satisfies the postcondition Q(f(x)). No proof is performed; this is taken as an axiom in the current context.

### have fn ... =
Semantics
When this statement is executed:

1. The system creates a temporary local scope.

2. A generic variable x (the parameter) is introduced into this scope, with the assumption that x is in A.

3. The expression on the right-hand side (expression) is analyzed.

4. The system verifies that expression evaluates to an object belonging to the return set B.

5. If verification succeeds, f(x) is defined as expression. The symbol f is available in the outer scope.

### have fn ... prove
Semantics

1. A temporary verification scope is created.

2. The statements inside the prove block are executed sequentially.

3.The final statement in the proof block must be an equality or an object, denoted here as result_object.

4. The system verifies that result_object belongs to set B.


### have fn ... cases
Semantics
1.Completeness Check: The system verifies that the logic in cases covers the domain (or is a valid tautology/axiom).

2.Branch Iteration: The system iterates through each case block.

3.Case Assumption: The specific condition Ci(x) is assumed to be true.

4.Branch Verification:The statements (or proof steps) inside the case block are executed.

