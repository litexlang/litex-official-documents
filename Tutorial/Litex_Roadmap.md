# Litex Roadmap

There are two kinds of Litex statements

1. factual statements 用来被验证。被验证后，被保留下来作为未来的验证已知事实

2. non-factual statements 不用来做验证。功能可能是定义object，import一个包等

## factual statements

构成：动词加若干名词

本质上数学验证就是在做这样的游戏：引入一些动词（数学里通常叫proposition predicate），引入一些名词（数学里通常叫object），然后验证这些object满足这些东西。有些很容易验证，比如`1 + 1 = 2`，有些很难验证，比如费马大定理。

Litex的一大特点是，有很少但很有效的验证机制帮用户去验证一个factual statement是否正确。其他形式化语言要求用户写很多很多的过程来验证一个很简单的东西，但litex强大且实用的内核帮用户省去了大部分力气，所以用litex写证明非常容易。

输出结果可能是true, unknown, error

1. true: litex内核帮你找到了一个办法证明。证明过程会被打印出来。

2. unknown: litex 没有帮你找到方法证明。你说的这句话可能本来就是错的，也可能是你的过程不完整所以litex不能靠已有的事实加上litex的验证机制来验证出来

3. error：错误。可能是你引入了不存在的object，可能是你你用了函数式object但函数里的参数不符合函数的定义域，可能是你没符合语法。

> 注意：函数是object，而不是proposition predicate。proposition predicate是用来判断对错的，函数只是一个能把其他的object（这些符号必须满足该函数的dom）用括号括起来形成新的符号的特殊符号。函数能被作为参数传过来作为factual statement的参数。

## non-factual statements

数学里不只是有判断对错。比如，有些语句是用来做定义啊。如果你不允许用户定义object，定义proposition predicate，那我们的数学世界就能处理的对象很少很少，一点也不精彩了，也不具备实际价值。我们通常用`prop`定义proposition predicate，用`have`定义object。

同时，litex的内置的验证方式很简单。好处是易于学习，运行机制简单高效，坏处是，一些特殊的数学验证格式就需要依赖额外的关键词去执行。`prove_by_contradiction`, `prove_case_by_case` 等。

## effects of litex statements

有时候你执行一个statement，litex会打印出一些信息。这些信息就是statement的effects。任何数学语句在litex中只有4种effect: define, verify, memorize, infer。

比如这里

```litex
have a R = 17
a > 0
```

会有下面的打印结果：

```
*** line 1 ***

--- statement ---

have a R = 17

--- definition ---

a is a new object
a = 17
a $in R

--- verification process ---

17 $in R
proved by builtin rules:
17 is literally a real number

*** line 1: success! ***

*** line 3 ***

--- statement ---

a > 0

--- new fact ---

a > 0

--- verification process ---

a > 0
proved by fact stored on line 3:
a > 0 is equivalent to 17 > 0 by replacing the symbols with their values

--- infer ---

a != 0
a >= 0
not a <= 0
a > (-1 * a)
(-1 * a) < 0
(1 / a) > 0
(a ^ 2) > 0
sqrt(a) > 0

*** line 3: success! ***

Success! :)

```

可以看到，一个语句可能涉及很多的effect。比如`have a R = 17`它的主要功能是定义一个新的object名为a，让它等于17。它的运行涉及了define, , memorize, verify 三种effect。而`a > 0` 这个factual statement涉及了verify, memorize, infer三种effect。

幸运的是，常用的数学语句的类型并不多，litex很直白的把它们的功能表达出来。所以你需要学的东西不多！如果遇到不懂的，来查询Tutorial也就OK了！