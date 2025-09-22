# Not：只有当某些东西可能为假时，真理才重要。

任何特定事实都可以用 `not` 否定。

以下示例显示如何否定特定事实：

```litex
let x R: x > 5

not x <= 5
```

要证明特定事实的否定，您可以在 `claim` 块中使用 `prove_by_contradiction`。例如：

```litex
prop p(x R)
prop q(x R)
know forall x R: $p(x) => $q(x); not $q(1)
claim:
    not $p(1)
    prove_by_contradiction:
        $q(1) # is true, because $p(1) is assumed to be true
```

您不能在 Litex 中写 `not forall`。当您想要否定普遍事实时，您必须首先声明一个 `exist_prop` 并尝试证明存在这样的项目导致 `not forall`。

您也可以否定存在命题事实：

```litex
exist_prop x N_pos st exist_positive_natural_number_smaller_than_given_real_number(y R):
    x < y

know not $exist_positive_natural_number_smaller_than_given_real_number(0)
```
