# 介绍：开始 Litex 之旅

## 什么是 Litex

Litex(/lɪ'tɛks/) 是一种直观且可扩展的形式语言，用于编码您的推理。Litex 的名字来源于两个深刻影响其设计的语言的结合：Lisp 和 TeX。自 2024 年以来，Litex 与其设计并行开发，由创造者沈家辰开发，通过持续演进，现已发展成为一个向所有人开放的社区驱动项目。

既然 10 岁的孩子可以推理基础数学，那么即使是 10 岁的孩子也应该能够轻松学习和使用 Litex 来解决他们自己的问题。我们假设一个没有任何数学或编程背景的人可以在 1-3 小时内学会 Litex。别担心。如果您第一次不记得所有内容，这完全没问题。当您遇到特定问题时，回来复习本教程的相关部分同样有效。

像所有成功的编程语言一样，Litex 被设计为使用愉快且实用地解决实际问题。它的重点是扩展 AI 时代的形式推理。AI 和数学社区都需要一种简单、可访问的形式语言来集成到他们的工作流程中。Litex 满足这一需求，将形式化的努力从 10 倍降低到与自然写作相当。因此，在 Litex 中构建比传统形式系统（Lean、Coq、Isabelle 等）便宜和容易约 10 倍——这对 AI 和数学都是真正的益处。

Litex 的三个关键特征是：**直观、简单和表达力强**。

## 直观

Litex 支持数学中所有常见的表达，如数字、变量、函数等。

这里有一个例子：确定多元线性方程解的正确性：2x + 3y = 10, 4x + 5y = 14：

```litex
let x R, y R:
    2 * x + 3 * y = 10
    4 * x + 5 * y = 14
2 * (2 * x + 3 * y) = 2 * 10
4* x + 6 * y = 2 * 10
(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14
(4*x + 6 * y) - (4*x + 5 * y) = y
y  = 6
2 * x + 3 * 6 = 10
2 * x + 18 - 18 = 10 - 18
2 * x + 18 - 18 = -8
(2 * x) / 2 = -8 / 2
(2 * x) / 2 = x
x = -4
```

任何人都能理解上述代码。我们写数学的方式和我们写 Litex 的方式几乎没有区别。然而，像 Lean 这样的传统形式语言需要您学习很多复杂的语法和概念。

## 简单

在形式语言中编写数学的难度通常等于数学本身的难度加上在该形式语言中表达该数学的难度。Litex 的目标是将后者减少到尽可能接近零，让用户专注于数学本身而不是他们使用的语言。

这里有一个例子：证明 sqrt(2) 是无理数：

```litex
# prove sqrt(2) is irrational
# 证明 sqrt(2) 是无理数

fn logBase(x, y N) N:
    dom:
        x != 0

know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)

know forall x N: x != 0 => logBase(x, x) = 1

claim:
    not sqrt(2) $in Q
    prove_by_contradiction:
        sqrt(2) > 0
        have x, y st $rational_positive_number_representation_in_fraction(sqrt(2))
        
        x = sqrt(2) * y
        x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)
        sqrt(2) ^ 2 = 2
        x ^ 2 = 2 * (y ^ 2)

        logBase(2, x ^ 2) = logBase(2, 2 * (y ^ 2))     
        logBase(2, x ^ 2) = 2 * logBase(2, x)
        logBase(2, y ^ 2) = 2 * logBase(2, y)

        logBase(2, 2 * (y ^ 2)) = logBase(2, 2) + logBase(2, y ^ 2)
        logBase(2, 2) = 1
        logBase(2, 2 * (y ^ 2)) = 1 + logBase(2, y ^ 2)

        logBase(2, x ^ 2) = 1 + 2 * logBase(2, y)
        2 * logBase(2, x) = 1 + 2 * logBase(2, y)

        =:
            0
            (2 * logBase(2, x)) % 2            
            (1 + 2 * logBase(2, y)) % 2
            
        =:
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 2 * logBase(2, y)) % 2
            (1 % 2 + (2 * logBase(2, y)) % 2) % 2
            (1 + 0) % 2
            1
        0 = 1
```

Litex 代码相当直接。尝试自己阅读上述代码。这并不难。下面是 Lean 中的相同示例。

## 表达力强

数学研究抽象。它是关于在世界上找到最一般和抽象的模式。Litex 非常善于表达这样的模式。这里有一个例子：定义一个群，并证明 R 和 Z 是群。

```litex
prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):
    forall x s, y s, z s:
        mul(mul(x, y), z) = mul(x, mul(y, z))
    forall x s:
        mul(x, inv(x)) = e
        mul(inv(x), x) = e

fn inverse(x R)R:
    inverse(x) + x = 0

forall x R:
    inverse(x) + x = 0
    x + inverse(x) = 0

forall x Z:
    x + inverse(x) = 0
    inverse(x) = -x
    -x $in Z
    inverse(x) $in Z

$is_group(R, +, inverse, 0)
$is_group(Z, +, inverse, 0)
```

## 创造者的话

你好，我是沈家辰，一个黑客和 Litex 的创造者。它是一种用于形式化推理的计算机语言。计算是数学如何用于解决现实世界问题的方式。推理是我们如何丰富对世界的理解。这种知识完全不同于普通知识，因为它可以通过给定的规则集进行机械验证。数学、物理学、计算机科学都依赖于这种严格性。软件行业已经革命了我们如何计算，而 Litex 在这里改变我们如何推理。

好的艺术是让开发者快乐并让用户觉得有用的东西。我希望 Litex 能成为我作为创造者和其用户的好艺术。随时加入我们！从访问我们的 [网站](https://litexlang.com) 开始！感谢您的支持！

## 如何阅读本教程

Litex 的最大优势是其直观性。在理想情况下，我们希望用户可以在不学习的情况下阅读和使用 Litex！

阅读本教程时请不要感到任何压力——Litex 确实非常简单。本教程中的代码可以在您的浏览器中运行！运行它以第一次体验 Litex！

这个精简教程的目的是：

1. 记录最基本的 Litex 语法和关键词，确保用户没有歧义。
2. 为初学者提供一些参考示例。

不要忘记自己运行示例！如果您自己阅读和编写示例，您可以学得更快！

学习 Litex 的最佳方法是尝试自己编写教程中的示例，或将您关心的数学（或推理）翻译成 Litex。
