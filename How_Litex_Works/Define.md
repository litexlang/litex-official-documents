# Define

_Young man, in mathematics you don't understand things. You just get used to them._

_- John von Neumann_

Version: 2025-12-18

任何语句都由动词和名词组成。动词用于判断对错.

## 定义动词

和定义名词不同，定义动词是不需要证明存在性的

1. 定义prop predicate

prop predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts

2. 定义exist_prop predicate

exist_prop predicate_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    <=>:
        iff_facts

3. 定义implication fact

imply fact_name(parameter1 set1, parameter2 set2, ...):
    domain_facts
    =>:
        then_facts

注意：litex里你不需要给所有的事实取名，因为litex会自动搜索相关的事实并使用它们。这大大提高了开发效率。

## 定义名词

Have Statement Execution Functions Documentation

This document lists all have-related AST statements and their execution functions.

============================================================================
1. HaveObjStStmt
============================================================================
AST Type: HaveObjStStmt
Execution Function: haveObjStStmt(stmt *ast.HaveObjStStmt, requireMsg bool) ExecRet

example:

```litex
prop q(x, y R)
exist_prop x R p(y R):
    $q(x, y)
know $p(1)
have x st $p(1)
$q(x, 1)
```

Description:
- Verifies that the SpecFactStmt is satisfied
- Defines objects in the environment with their corresponding sets, properties by definition.

============================================================================
2. HaveObjInNonEmptySetStmt
============================================================================
AST Type: HaveObjInNonEmptySetStmt
Execution Function: haveObjInNonEmptySetStmt(stmt *ast.HaveObjInNonEmptySetStmt) ExecRet
Location: executor/exec_have.go:240

Description:
- For each object, verifies that the set is non-empty
- Defines objects in the environment with their corresponding sets
- Uses DefLetStmt to define objects

============================================================================
3. HaveObjEqualStmt
============================================================================
AST Type: HaveObjEqualStmt
Execution Function: haveObjEqualStmt(stmt *ast.HaveObjEqualStmt) ExecRet
Location: executor/exec_have.go:204

Description:
- For each object:
  * Verifies that objEqualTo is defined or is a function satisfying its requirements
  * Verifies that objEqualTo is in objSet
  * Defines the object with DefLetStmt, including equality fact
  * Checks that atoms in objEqualTo are defined or builtin

============================================================================
4. HaveFnEqualStmt
============================================================================
AST Type: HaveFnEqualStmt
Execution Function: haveFnEqualStmt(stmt *ast.HaveFnEqualStmt) ExecRet
Location: executor/exec_have.go:264

Description:
- Verifies that retSet is a set
- Checks function equality statement (checkFnEqualStmt):
  * Creates new environment
  * Defines parameters in the new environment
  * Verifies that equalTo is in retSet
- Defines the function using DefFnStmt with equality fact in thenFacts

Helper Function: checkFnEqualStmt(stmt *ast.HaveFnEqualStmt) (ExecRet, error)
Location: executor/exec_have.go:290

============================================================================
5. HaveFnEqualCaseByCaseStmt
============================================================================
AST Type: HaveFnEqualCaseByCaseStmt
Execution Function: haveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) ExecRet
Location: executor/exec_have.go:660

Description:
- Verifies that retSet is a set
- Checks function equality case-by-case statement (checkHaveFnEqualCaseByCaseStmt):
  * For each case: verifies return value is in retSet (checkCaseReturnValueInRetSet)
  * Verifies all cases cover the domain (checkAtLeastOneCaseHolds)
  * Verifies cases don't overlap (checkCasesNoOverlap)
- Builds thenFacts: for each case, if condition holds, function equals corresponding return value
- Defines the function using DefFnStmt with thenFacts

Helper Functions:
- checkHaveFnEqualCaseByCaseStmt(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error)
  Location: executor/exec_have.go:719
- checkCaseReturnValueInRetSet(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (ExecRet, error)
  Location: executor/exec_have.go:743
- checkAtLeastOneCaseHolds(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error)
  Location: executor/exec_have.go:778
- checkCasesNoOverlap(stmt *ast.HaveFnEqualCaseByCaseStmt) (ExecRet, error)
  Location: executor/exec_have.go:808
- checkCaseNoOverlapWithOthers(stmt *ast.HaveFnEqualCaseByCaseStmt, caseIndex int) (ExecRet, error)
  Location: executor/exec_have.go:820

============================================================================
6. HaveFnStmt
============================================================================
AST Type: HaveFnStmt
Execution Function: haveFnStmt(stmt *ast.HaveFnStmt) ExecRet
Location: executor/exec_have.go:327

Description:
- Verifies the have function statement (checkHaveFnStmt):
  * Verifies retSet is a set
  * Verifies each paramSet is a set
  * Defines parameters in new environment
  * Executes proof statements
  * Verifies that HaveObjSatisfyFn is in retSet
  * Declares function locally
  * Adds fact that function equals HaveObjSatisfyFn
  * Verifies all thenFacts are true
- Defines the function using DefFnStmt

Helper Function: checkHaveFnStmt(stmt *ast.HaveFnStmt) (ExecRet, error)
Location: executor/exec_have.go:343

============================================================================
7. HaveFnCaseByCaseStmt
============================================================================
AST Type: HaveFnCaseByCaseStmt
Execution Function: haveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) ExecRet
Location: executor/exec_have.go:433

Description:
- Verifies the have function case-by-case statement (checkHaveFnCaseByCaseStmt):
  * Verifies each paramSet is a set
  * Verifies retSet is a set
  * For each case: verifies proof and return value (verifyHaveFnCaseByCase_OneCase)
  * Verifies all cases cover the domain (checkAtLeastOneCaseHolds_ForHaveFn)
  * Verifies cases don't overlap (checkCasesNoOverlap_ForHaveFn)
  * Builds thenFacts: for each case, if condition holds, function equals corresponding return value
- Defines the function using DefFnStmt

Helper Functions:
- checkHaveFnCaseByCaseStmt(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, []ast.FactStmt, error)
  Location: executor/exec_have.go:449
- verifyHaveFnCaseByCase_OneCase(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (ExecRet, error)
  Location: executor/exec_have.go:521
- checkAtLeastOneCaseHolds_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, error)
  Location: executor/exec_have.go:573
- checkCasesNoOverlap_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt) (ExecRet, error)
  Location: executor/exec_have.go:603
- checkCaseNoOverlapWithOthers_ForHaveFn(stmt *ast.HaveFnCaseByCaseStmt, caseIndex int) (ExecRet, error)
  Location: executor/exec_have.go:615

============================================================================
8. HaveCartSetStmt
============================================================================
AST Type: HaveCartSetStmt
Execution Function: haveCartSetStmt(stmt *ast.HaveCartSetStmt) ExecRet
Location: executor/exec_have.go:170

Description:
- Checks that cart has at least 2 parameters
- Verifies that each parameter of cart is a set
- Defines the new set variable using DefLetStmt
- Stores the equal fact: x = cart(a, b, c, ...)

============================================================================
9. HaveObjFromCartSetStmt
============================================================================
AST Type: HaveObjFromCartSetStmt
Execution Function: haveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) ExecRet
Location: executor/exec_have.go:865

Description:
- Checks the statement (checkHaveObjFromCartSetStmt):
  * Verifies each parameter of cart is a set
  * Verifies equalTo is a tuple
  * Verifies tuple length matches cart parameters length
  * Verifies each element of equalTo is in corresponding cart set
- Post-processes (postProcessHaveObjFromCartSetStmt):
  * Adds obj in cart(...) fact
  * Adds obj = equalTo fact
  * Adds obj[i] = equalTo[i] for each i
  * Adds dim(obj) = len(cartSet.Params)

Helper Functions:
- checkHaveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) ExecRet
  Location: executor/exec_have.go:885
- postProcessHaveObjFromCartSetStmt(stmt *ast.HaveObjFromCartSetStmt) ExecRet
  Location: executor/exec_have.go:931

============================================================================
10. HaveCartWithDimStmt
============================================================================
AST Type: HaveCartWithDimStmt
Execution Function: (Not implemented)
Location: N/A

Description:
- This statement type exists in AST but does not have an execution function yet.
- It is defined in ast/ast_statements.go:491

============================================================================
SUMMARY
============================================================================

Total Have Statement Types: 10
Implemented Execution Functions: 9
Unimplemented: 1 (HaveCartWithDimStmt)

All execution functions are located in executor/exec_have.go except for the
dispatcher which is in executor/exe_statements.go.

