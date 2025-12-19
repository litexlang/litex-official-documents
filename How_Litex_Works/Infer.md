# Infer

version: 2025-12-19, under drastic revision

_Before you speak, you are its master; after you speak, you are its slave._

_— Chinese Proverb_

InferenceEngine Automatic Inference Functions Documentation

This document describes all automatic inference functions performed by the InferenceEngine.
These functions are automatically triggered when certain facts are introduced into the environment.

============================================================================
1. TRUE $IN FACT INFERENCES
============================================================================

The InferenceEngine performs various inferences when a true $in fact (x $in S) is introduced,
depending on the type of set S.

trueInFact
----------
Trigger: When a true $in fact is introduced (x $in S)
Inference: Dispatches to appropriate inference handlers based on the type of set S

trueInFactByFnTemplate
----------------------
Trigger: When x $in fnTemplate(...)
Inference: Derives a universal fact from the function template definition and stores
           the function-template satisfaction relationship

trueInFactByFnTemplateFnObj
---------------------------
Trigger: When x $in fnTemplateFnObj
Inference: Inserts the function x into the function template table

trueInFactByCart
----------------
Trigger: When x $in cart(S1, S2, ..., Sn)
Inference: If x is in a cartesian product, then each component of x is in the corresponding set.
           Generates: a[i] $in Si for each i, dim(a) = n, is_tuple(a)

trueInFactInCart
----------------
Trigger: When obj $in cart(S1, S2, ..., Sn)
Inference: Generates:
           - a[i] $in Si for each i (each component is in the corresponding set)
           - dim(a) = n (dimension equals the number of sets)
           - is_tuple(a) (the object is a tuple)

trueInFactByListSet
-------------------
Trigger: When x $in listSet(e1, e2, ..., en)
Inference: If x is in a finite list set, then x equals one of the elements.
           Generates: x = e1 or x = e2 or ... or x = en

trueInFactInListSet
-------------------
Trigger: When obj $in listSet(e1, e2, ..., en)
Inference: Generates an OR fact indicating that obj equals one of the list set elements.
           Result: obj = e1 or obj = e2 or ... or obj = en

trueInFactBySetBuilder
----------------------
Trigger: When x $in {y in T: P(y)}
Inference: If x is in a set builder, then x is in the parent set T and satisfies all intentional facts P(x).
           Generates: x $in T, and all instantiated intentional facts P(x)

trueInFactInSetBuilder
----------------------
Trigger: When obj $in {param in parentSet: facts}
Inference: Generates:
           - obj $in parentSet (membership in parent set)
           - All instantiated intentional facts from the set builder

trueInFactByRangeOrClosedRange
-------------------------------
Trigger: When x $in range(a, b) or x $in closed_range(a, b)
Inference: Generates:
           - x $in Z (integer membership)
           - x >= a (lower bound)
           - x < b (for range) or x <= b (for closed_range)
           - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, etc.)

trueInFactByNPos
----------------
Trigger: When x $in NPos (positive natural numbers)
Inference: Generates:
           - x $in N, x $in Q, x $in R (number type memberships)
           - x > 0, x >= 1 (positivity facts)
           - Additional derived facts from comparison postprocessing (e.g., x != 0, x^2 > 0, sqrt(x) > 0, etc.)

============================================================================
2. TRUE EQUALITY FACT INFERENCES
============================================================================

The InferenceEngine performs various inferences when a true equality fact (x = y) is introduced,
depending on the types of x and y.

newTrueEqual
------------
Trigger: When a true equality fact is introduced (x = y)
Inference: Dispatches to appropriate equality inference handlers

trueEqualFactByCart
-------------------
Trigger: When x = cart(x1, x2, ..., xn)
Inference: Generates:
           - is_cart(x) fact
           - dim(x) = len(cart.Params) fact
           - proj(x, i+1) = cart.Params[i] facts for each i

trueEqualFactByTuple
---------------------
Trigger: When dealing with tuple equality (tuple = tuple, obj = tuple, or tuple = obj)
Inference: Handles three cases:
           - (.., …) = (.., ..): tuple = tuple (generates equal facts for each corresponding element)
           - a = (.., ..): obj = tuple (generates obj[index] = tuple[i] for each index)
           - (.., ..) = a: tuple = obj (same as above, reversed)

trueEqualByLeftAtEachIndexIsEqualToTupleAtCorrespondingIndex
-------------------------------------------------------------
Trigger: When obj = tuple
Inference: Generates obj[index] = tuple[i] facts for each index

trueEqualByLeftAndRightAreBothTuple
------------------------------------
Trigger: When tuple = tuple
Inference: Generates equal facts for each corresponding element

trueEqualFactByListSet
----------------------
Trigger: When x = {1, 2, 3} (list set equality)
Inference: If the right side is a list set, it creates:
           - An OR fact indicating that x equals one of the list set elements
           - count(x) = len(listSet) fact
           - is_finite_set(x) fact

============================================================================
3. PURE FACT POST-PROCESSING INFERENCES
============================================================================

The InferenceEngine performs post-processing inferences when pure facts are introduced.

newPureFact
-----------
Trigger: When a pure fact is introduced
Inference: Dispatches to appropriate handlers based on whether it's builtin, user-defined prop, or exist prop

equalTupleFactPostProcess
--------------------------
Trigger: When equal_tuple(a, b, dim) fact is introduced
Inference: Automatically derives a[i] = b[i] for i from 1 to dim

newFalseExist
-------------
Trigger: When a false exist fact is introduced
Inference: Currently returns empty (no additional inference)

newTrueExist
------------
Trigger: When a true exist fact is introduced (have(exist ... st ...))
Inference: Generates the corresponding exist fact and processes iff/then facts

newFalseExistFact_EmitEquivalentUniFact
----------------------------------------
Trigger: When a false exist fact is introduced (not exist)
Inference: Converts to equivalent universal fact: not exist => forall not.
           Generates: forall x, if conditions then not conclusion

============================================================================
4. BUILTIN PROPERTY INFERENCES
============================================================================

The InferenceEngine performs various inferences for builtin properties, especially comparison operations.

BuiltinPropExceptEqualPostProcess
----------------------------------
Trigger: When a builtin property fact is introduced (except equality)
Inference: Dispatches to appropriate builtin property handlers

builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsZero
-----------------------------------------------------------------------
Trigger: When x > 0
Inference: Generates:
           - x != 0, x >= 0, not x <= 0
           - x > -x, -x < 0
           - 1/x > 0, x^2 > 0, sqrt(x) > 0

builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsZero
---------------------------------------------------------------------------
Trigger: When x >= 0
Inference: Generates:
           - abs(x) = x
           - x >= -x
           - sqrt(x) >= 0

builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsZero
--------------------------------------------------------------------
Trigger: When x < 0
Inference: Generates:
           - x != 0, x <= 0, not x >= 0
           - x < -x, -x > 0
           - 1/x < 0, x^2 > 0

builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsZero
-------------------------------------------------------------------------
Trigger: When x <= 0
Inference: Generates:
           - abs(x) = -x
           - x <= -x
           - -x >= 0

builtinPropExceptEqualPostProcess_WhenPropIsGreaterAndRightParamIsNotZero
--------------------------------------------------------------------------
Trigger: When x > c (where c != 0)
Inference: Generates:
           - x != c, x >= c, not x <= c
           - c < x, not c >= x
           - x - c > 0, x - c >= 0
           - c - x < 0, c - x <= 0

builtinPropExceptEqualPostProcess_WhenPropIsLargerEqualAndRightParamIsNotZero
------------------------------------------------------------------------------
Trigger: When x >= c (where c != 0)
Inference: Generates:
           - not x < c
           - c <= x, not c > x
           - x - c >= 0
           - c - x <= 0

builtinPropExceptEqualPostProcess_WhenPropIsLessAndRightParamIsNotZero
-----------------------------------------------------------------------
Trigger: When x < c (where c != 0)
Inference: Generates:
           - x != c, x <= c, not x >= c
           - c > x, not c <= x
           - x - c < 0, x - c <= 0
           - c - x > 0, c - x >= 0

builtinPropExceptEqualPostProcess_WhenPropIsLessEqualAndRightParamIsNotZero
---------------------------------------------------------------------------
Trigger: When x <= c (where c != 0)
Inference: Generates:
           - not x > c
           - c >= x, not c < x
           - x - c <= 0
           - c - x >= 0

subsetOfFactPostProcess
------------------------
Trigger: When subset_of(A, B) fact is introduced
Inference: Generates: forall x in A, x $in B

falseEqualFact
--------------
Trigger: When x != y fact is introduced
Inference: Generates: x - y != 0

============================================================================
5. BUILTIN PROPERTY INFERENCES (ie_builtin_props.go)
============================================================================

equalSetFactPostProcess
------------------------
Trigger: When equal_set(a, b) fact is introduced
Inference: Creates an equality fact a = b and collects derived facts

============================================================================
6. USER-DEFINED PROPERTY INFERENCES
============================================================================

newUserDefinedTruePureFactByDef
--------------------------------
Trigger: When a user-defined true pure fact is introduced and has a property definition
Inference: Derives facts from the property definition using iff and implication rules:
           - Iff facts: facts that are equivalent (when the prop is true, these facts are also true)
           - Implication facts: facts that are implied (when the prop is true, these facts follow)

============================================================================
HELPER FUNCTIONS
============================================================================

storeSpecFactInMemAndCollect
-----------------------------
Purpose: Helper function to store a fact in memory and collect its string representation
         for tracking derived facts
