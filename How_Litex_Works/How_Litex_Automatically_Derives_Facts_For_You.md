# How Litex Automatically Derives Facts For You

_Before you speak, you are its master; after you speak, you are its slave._

_— Chinese Proverb_

---

## Introduction

Litex has invested tremendous effort—indeed, most of its effort—into improving user experience. This means that **if the kernel can mechanically help users automatically derive facts, it will automatically derive and save them for you**. At the same time, Litex incorporates many techniques to help users think about mathematics the way they naturally think about mathematics in everyday life. This document explains how Litex achieves this goal.

The core philosophy behind Litex's automatic derivation is simple: **mathematics should feel natural, not mechanical**. When you write mathematics on paper, you don't manually track every single equality relation or substitution—your mind automatically connects related facts. Litex does the same: it automatically maintains equivalence sets, performs substitutions, simplifies expressions, and derives new facts from known ones, all behind the scenes, so you can focus on the mathematics itself.

基本的工作原理是：1. 验证factual statement 2. 保存这个 factual statement 3. 自动从这个factual statement 推理出来什么东西（我们称之为知道某个事实后的后处理）。如果是用 know 或者 let 时，验证的过程即第一步跳过了。

---

# 方法1：在保存好特定事实后，如果这个事实符合某种特性，那么或许可以推理出来什么东西

下面是一些语句，和他们对应的自动生成

1. a = {1, 2, 3} 的后处理 （比如 have set a = {1, 2, 3}）：

自动成立：
1. a $in set 
2. forall x obj: x $in a <=> x = 1 or x = 2 or x = 3 成立

2. x = cart(R, Q, Z) (比如 have set x = cart(R, Q, Z))

自动成立
1. $is_cart(x)
2. dim(x) = 3
3. proj(x, 1) = R
4. proj(x, 2) = Q
5. proj(x, 3) = Z
6. x $in set

# 方法2：如果一个事实符合某些条件，那么就有额外的特殊的验证方式

1. 如果等号或不等号左右两边全是数字表达式，那么litex会帮你计算

例子：

1 + 1 = 2
4 * 2 - 10 = -2 + (7 - 7)
7^2 = 49
2 / 3 = 4 / 6

加减乘的运算是用字符串去做计算（不是浮点数），所以理论上100位加100位在litex是可行的，甚至可以说是运算很快的

如果指数项是正整数，那我也帮你算出来。如果不是整数，那就不变

除号的验证并不是计算浮点数，而是会用除号的性质，把等式化成左右两边都是乘号和加号和指数的等号（a / b = c / d 化成 a * d = b * d。这里b和d不能是0），比如 2 / 3 = 4 / 6 先化成 2 * 6 = 3 * 4 这样。然后证明加减乘。

2 > 1
- 3 * 8 <= 0

不等号的验证和等号的验证类似，也是用字符串去做计算（不是浮点数），然后验证。

2. 如果左右两边全是多项式的加减乘除指数，那把左右两边约化

2.1 不含除号

(x + 1) * (x + 1) = x * x + 2 * x + 1

因为litex如果看到这种式子，会帮你自动化简成最简形式（按字典序排列的加法式子）（x * x + 2 * x + 1），然后帮你验证这个等式。如果左右两边的最简形态是一样的，那么等式就成立了。

2.2 含除号

(x + 1) * (x + 1) / y = x * x + 2 * x + 1 / (y + 1 - 1)

先化成乘法式子，然后约化，上面的式子等价于

(x + 1) * (x + 1) * (y + 1 - 1) = (x * x + 2 * x + 1) * y

3. 如果左边或者右边的符号有数值，那么litex会帮你验证这个等式

例子：

1 + 1 = 2
4 * 2 - 10 = -2 + (7 - 7)
7^2 = 49
2 / 3 = 4 / 6

4. 如果左边或者右边的符号有对应的值，那么litex会帮你验证这个等式

```litex
have a R = 1
a > 0
```

因为 1 是 a 的值，所以 a > 0 会因为已知 a = 1 而自动成立，a > 0 被替换成 1 > 0，然后验证 1 > 0 成立。