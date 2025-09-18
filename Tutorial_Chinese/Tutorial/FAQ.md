# 常见问题：常见问题解答

_三人行，必有我师焉。(There must be someone I can learn from among the three people I walk with.)_

_— 孔子 (Confucius)_

1. 为什么以下代码不起作用？

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

示例 2：

```litex
prop product_zero_implies_or(x, y R):
    x * y = 0
    <=>:
        or(x = 0, y = 0)
know forall x, y R: x * y = 0 => $product_zero_implies_or(x, y)

let a,b R
know a*b=0
$product_zero_implies_or(a,b)
```
