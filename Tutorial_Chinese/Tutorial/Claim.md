## 声明：将您的证明组织成子证明

_软件开发中最根本的问题是复杂性。处理复杂性只有一种基本方法：分而治之。_

_— 比雅尼·斯特劳斯特鲁普_

数学很难。很好地组织您的证明很重要。最好的方法是将长证明分解为一系列独立的子证明，然后将它们组合在一起。我们称之为`分而治之`，这也是许多其他任务（如建造房屋、编写代码等）的常见策略。在这种情况下，`claim` 关键字可以帮助您。

## `claim` 的使用

```
claim:
    fact_you_want_to_prove
    prove:
        ....
```

`fact_you_want_to_prove` 可以是特定事实或普遍事实。

例如

``` litex
exist_prop x N st exist_natural_number_larger_than(y N):
    x > y

claim:
    $exist_natural_number_larger_than(1)
    prove:
        let x N: x = 2
        2 > 1
        x > 1
        exist x st $exist_natural_number_larger_than(1)
        $exist_natural_number_larger_than(1)

$exist_natural_number_larger_than(1) # true, because $exist_natural_number_larger_than(1) is proved in the claim statement
# x = 2 is not visible out of the prove block, because x is declared in the prove block locally
```

当证明特定事实时，您可以使用 `prove` 块来证明它。在 `prove` 块中的所有语句执行完毕后，Litex 将检查 `fact_you_want_to_prove` 是否为真。

您也可以声明一个普遍事实。这正是数学家保持证明清洁的方式。

```litex
prop g(x R)
prop s(x R)
prop q(x R)

know:
    forall x R: $g(x) => $s(x)
    forall x R: $s(x) => $q(x)

claim:
    forall x R: $g(x) => $q(x)
    prove:
        $s(x)
        $q(x)
```

`claim forall` 构造的工作原理如下：

* 它创建一个**新的本地证明环境**。
* 在此环境中，域假设默认设置为 `true`。
* 然后执行块内的所有语句。
* 一旦 `prove` 块完成，Litex 检查普遍语句的结论是否确实已被推导出。

  * 如果是，证明完成。
  * 如果不是，Litex 报告错误。
* 之后，普遍事实被添加到**全局环境**中，而 `prove` 块内的中间步骤**不会**影响全局状态。

*这反映了解决数学问题的真实过程：您被给定一组对象和假设，您的任务是证明一个结论。在 Litex 中，这被精确地形式化为 `claim forall` 语句。*

您可以使用 `claim` 使某些东西影响证明子环境之外的部分：

```litex
claim:
    @p(x N):
        x > 1
        =>:
            x > -1
    prove:
        $larger_is_transitive(x, 1, -1)
        x > -1

let a N:
    a > 1
$p(a)
a > -1
```

`larger_is_transitive(x, y, z R)` 是 Litex 的内置命题，意思是：x, y, z 在 R 中，x > y 且 y > z <=> x > z。您在声明块中声明了一个命题 `p(x N)` 并在证明块中证明它。但您仍然可以在子环境之外使用它。

## 反证法

`prove_by_contradiction` 应该总是在声明块中使用。这里是一个经典例子，使用反证法证明 sqrt(2) 是无理数：
