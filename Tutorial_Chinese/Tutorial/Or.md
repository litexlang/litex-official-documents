# Or：停止非黑即白的思考

Or 表示包含性析取，意味着至少有一个条件为真。您可以这样使用它：

```litex
let x R: x = 1

or:
    x = 1
    x = 2

or(x = 1, x = 2)
```

语法是：

```
or:
    specific_fact1
    specific_fact2
    ...
    specific_factN

or(specific_fact1, specific_fact2, ..., specific_factN)
```

您可以在 `or` 事实下写特定事实。

`or` 事实可以写在 `forall` 事实中：

```litex
let s set, a s: forall x s => or(x = 1, x = 2); not a = 1

a = 2
```

`or` 也可以作为 `forall` 事实的 dom 出现

```litex
know forall x R: or(x = 1, x = 2) => x < 3
```

## Or 和 Prove In Each Case

`or` 经常与 `prove_in_each_case` 一起使用，以在每种情况下证明一个事实。

```litex
let a R: or(a = 0, a = 1)

prove_in_each_case:
    or(a = 0, a = 1)
    =>:
        a >= 0
    prove:
        a = 0
    prove:
        a = 1
```

没有 `prove_in_each_case`，Litex 永远无法表达许多数学事实。阅读"prove_in_each_case"部分了解更多详情。

## Or 事实如何执行？

当 Litex 内核读取 `or(fact1, fact2, ..., factN)` 时，它将在假设 `fact2`，...，`factN` 不为真的情况下检查 `fact1` 是否为真。

这解释了为什么以下代码不起作用：

```
know forall x, y R: x * y = 0 => or(x = 0, y = 0)
let a,b R
know a*b=0
or(a=0,b=0)
```

答案：它不起作用的原因与 `or` 语句的执行方式有关。

当 Litex 内核读取 `or(a=0,b=0)` 时，它将在假设 `b = 0` 不为真的情况下检查 `a = 0` 是否为真。但是，当我们使用 `forall x, y R: x * y = 0 => or(x = 0, y = 0)` 来检查 `a = 0` 是否为真时，内核无法仅通过读取 `a = 0` 就知道 `y = b`。

要修复这个问题，给已知事实 `forall x, y R: x * y = 0 => or(x = 0, y = 0)` 一个名称。

示例 1：

```litex
know @product_zero_implies_or(x, y R):
    x * y = 0
    =>:
        or(x = 0, y = 0)
let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```


## 特定事实、Or 事实和 Forall 事实

基本上有三种事实：特定事实（普通特定事实、存在事实）、`or` 事实和 `forall` 事实。

您不能在 `or` 下写 `or` 事实和 `forall` 事实。只允许特定事实。您可以在 `forall` 事实中写 `or` 事实和 `forall` 事实。
