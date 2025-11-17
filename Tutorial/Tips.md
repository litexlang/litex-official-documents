# Tips

_Take the first step in faith. You don't have to see the whole staircase. Just take the first step._

_— Martin Luther King, Jr._

如果证明当前的specific fact时，当前specific fact 的参数数量，少于证明它所用的universal fact的参数数量，那么litex的匹配和替换验证法是不能工作的。比如

```
prop p(x R, y R)
know forall a, b, c R: $p(a, b), $p(b, c) => $p(a, c)
let a, b, c R: $p(a, b), $p(b, c)
$p(a, c)
```

是不工作的，因为 $p(a, c) 的参数数量少于forall a, b, c R: $p(a, b), $p(b, c) => $p(a, c)。所以我们找不到该forall事实中的b对应什么object，只知道a对应a，c对应c。

有什么办法能解决呢？

先来看看这个

```
prop p(x R, y R)
prop p2(x R, y R, z R):
    $p(x, y)
    $p(y, z)
know forall x, y, z R: $p2(x, y, z) => $p(x, z)
let x, y, z R: $p(x, y), $p(y, z)
$p(x, z)
```

还是不行！因为$p(x, z) 的证明需要用forall x, y, z R: $p2(x, y, z) => $p(x, z)的事实，但是$p2(x, y, z) 涉及到了3个参数，而$p(x, z) 只有2个参数。中间参数y没有被匹配到。

那么怎么解决呢？如果$p2(x, y, z) 的成立，能自动保存出来$p(x, z)就好了。就像$p2(x, y, z)的成立能自动让它的等价物$p(x, y), $p(y, z)被保存下来。那这样$p(x, z)就会因为$p2(x, y, z)的成立而自动被保存下来。

```litex
prop p(x R, y R)
know @p2(x R, y R, z R):
    $p(x, y)
    $p(y, z)
    =>:
        $p(x, z)
$p(x, z)
```

这里相当于同时做了两个事情：定义p2等价于$p(x, y), $p(y, z)，然后默认，当$p2(x, y, z)成立时，$p(x, z)也成立。 