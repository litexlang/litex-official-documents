# Equality: The Foundation of All Mathematics

_If it looks like a duck, swims like a duck, and quacks like a duck, then it probably is a duck._

_- Duck Test_

---

## The Fundamental Role of Equality

Equality (`=`) is the **most fundamental proposition** in mathematics. It is not merely one proposition among many; rather, **all other propositions depend on equality** for their definition and verification.

In mathematics and Litex, equality serves as the foundation because:

Equality makes symbols that are literally different have the same meaning. A symbol can be an atom (like `1`, `a`) or a function expression (like `1 + 2`, `f(x)`). When we say two symbols are equal, we mean they have completely identical meaning, even though they may look different.

**Example 1: Equality makes different literal symbols equivalent**

```litex
# Numeric equality: 1 + 1 and 2 are different symbols, but equal
1 + 1 = 2

# Variable equality: 20 * x and y + z are different symbols, but equal
have x R
have y R = 3 * x
have z R = 17 * x
20 * x = 3 * x + 17 * x = y + z

# Function equality: f(a) and g(b) are different symbols, but equal
have fn f(a R) R = a
have fn g(a R) R = f(a)
have a R
have b R = a
f(a) = g(b)
```

In all these cases, equality connects symbols that are literally different but semantically identical.

**Example 2: Other propositions depend on equality for verification**

```litex
# We know a > b is true
let a, b, c R:
    a > b
    a = c

# Because a = c, we can substitute c for a
# Therefore c > b is also true
c > b

prop p(a R)
know $p(a)
$p(c) # $p(c) is true because $p(a) is true and a = c
```

When `a = c` is known, `a` can be equivalently replaced with `c` in any proposition. This is why `c > b` is verified: Litex substitutes `c` for `a` in the known fact `a > b`. **In essence, equality means that different symbols (whether atoms like `1`, `a`, or function expressions like `1 + 2`, `f(x)`) have completely identical meaning.**

## How Litex Verifies Equality

证明时，会按顺序从第一步到最后一步试试

1. 第一步：如果左右两边都是数值表达式，那就化简，真的算出来

注意：是string匹配，不是浮点数运算；/除不尽的时候会保留/，比如 2/3 = 4/ 6不是真的算出来了它的值，而是在证明 3 *  4= 2 * 6

2. 第二步：搜索已知事实

在搜索已知事实之前，我们需要了解 Litex 是如何存储等号型事实的。等号型事实的存储方式与其他事实不同，这是因为等号具有传递性和对称性等特殊性质。

**存储机制**：Litex 使用一个哈希表（hashmap）来存储等号关系。对于每一组相等的符号，Litex 会创建一个等价集合（equivalence set），并将集合中的每个符号都映射到这个集合。

**示例**：假设我们已知符号 `a`、`1+b`、`f(c)` 是相等的，Litex 会创建一个等价集合 `{a, 1+b, f(c)}`，并将每个符号都映射到这个集合：
- `equalityMap["a"] = {a, 1+b, f(c)}`
- `equalityMap["1+b"] = {a, 1+b, f(c)}`
- `equalityMap["f(c)"] = {a, 1+b, f(c)}`

同样，如果符号 `h` 和 `8+t` 相等，它们会形成另一个等价集合：
- `equalityMap["h"] = {h, 8+t}`
- `equalityMap["8+t"] = {h, 8+t}`

**合并等价集合**：当我们证明新的等号关系时，如果它连接了两个不同的等价集合，Litex 会将这两个集合合并。例如，如果我们证明了 `a = 8 + t`，那么 `a` 所在的集合 `{a, 1+b, f(c)}` 和 `8+t` 所在的集合 `{h, 8+t}` 会被合并成一个新的等价集合 `{a, 1+b, f(c), h, 8+t}`。之后，所有相关的符号都会被更新为指向这个合并后的集合：
- `equalityMap["a"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["1+b"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["f(c)"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["h"] = {a, 1+b, f(c), h, 8+t}`
- `equalityMap["8+t"] = {a, 1+b, f(c), h, 8+t}`

这样，通过检查两个符号是否在同一个等价集合中，Litex 就能快速判断它们是否相等。

这样的存储和证明，和litex的证明符号相等有什么关系呢？

比如现在我要证明1 + b = h了。我就看看这个map中，EqualityMap["1+b"]和EqualityMap["h"]是否在同一个等价集合中。如果在，那么1 + b = h就是真的。现在发现他们刚好相等，那就OK了

再比如我要证明2 - 1 + b 等于h，那我发现2-1+b因为之前在整个项目里没出现过，所以equalityMap中没有这个key。但equalityMap里有key叫"h"，我就遍历"h"的list里的所有的符号，看看是不是和2-1+b相等。发现相等，那就OK了。比如我们遍历{a, 1+b, f(c), h, 8+t}时，发现2-1+b = 1+b，那就OK了。

3. 函数名和函数的每个参数都是相等的

```litex
have fn f(a R) R = a
let g fn(R) R: g = f
have a R
have b R = a
f(a) = g(b)
```

这里是如何验证 f(a) = g(b)的呢？equalityMap里是没有f(a)和g(b)的key的，因为它们刚刚才被定义。

如果等式左右两边的符号都是函数，而不是原子的时候，就会一层层拨开，即证明新的等号型事实， 比如这里的`f = g`，再一位位地验证它们的参数是不是相等，比如这里的`a = b`。

这里f(a)和g(b)都是函数式的，不是原子的，所以我们要一层层拨开，先验证函数头f和g是不是相等，再验证它们的参数a和b是不是相等。发现他们刚好相等，所以OK

4. 