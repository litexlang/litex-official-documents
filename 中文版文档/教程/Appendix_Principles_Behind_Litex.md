# 附录：Litex 背后的原则

_在 Litex 上度过的每一天都是新冒险的一天。_

_- Litex 创造者沈嘉辰_

此文件包含来自 Litex 创造者的 Litex 背后的原则。请为乐趣而阅读，而不是为了任何实际目的。我在这里的描述和措辞可能有些模糊，因为整个项目的发展本质上是将模糊想法转化为清晰想法的过程。事实上，模糊的想法往往暗示着许多尚未探索的增长方向的可能性。

1. 您刚刚学会了 Litex 如何从基本部分构建数学，就像积木一样。总结一下，`匹配和替换`是从既定事实推导新事实的基本方法。只要基本算术和计数是内置的，我们就可以在 Lite 中通过这种方式构建整个数学系统。有例外。关于具有字面信息的符号的事实（例如数字如 1、2、3、计数等）不是以这种方式验证的。与计数相关的事实不是以这种方式验证的。有且仅有这两个例外。这些事实由 Litex 的内置规则验证，用户无需担心它们。

2. 伏尔泰曾经说过："常识并不那么常见。"在 Litex 的情况下，Litex 通过发现数学只不过是特殊类型的`匹配和替换`问题，使构建数学的过程变得像浏览器中的 `ctrl+f & ctrl+r /cmd+f & cmd+r` 一样简单。每个人都如此熟悉这个过程，但几乎没有人真正发现其重要性并使用这个想法来创建简单的形式语言。Litex 的真正魔力在于它的工作方式就像人们在日常生活中的思考方式一样。这对语言设计师来说是一个困难的魔法，因为它需要对数学本质和编程本质的深刻理解，但值得努力。

3. 在朴素集合论中，几乎所有日常数学都基于此，所有事实都通过一阶逻辑的`匹配和替换`推导，只有两个例外：1. 数学归纳法。2. 替换公理。这两个在 Litex 中是内置的。由于高阶逻辑是"将命题作为参数传递给另一个命题"，关于高阶逻辑的事实仍然通过`匹配和替换`验证。Litex 将在未来实现高阶逻辑。如果您仍然担心 Litex 是否严格，Litex 内核会打印出它如何验证语句，所以您可以看到它是如何工作的。

4. Litex 是一种非常简单的学习语言。事实上，我不确定是否应该使用"学习"来描述它。Litex 语言的大部分功能都是如此常识，以至于我们每天都用它来推理。我想人们不能"学习"他们已经知道的东西！很多人可能认为数学很难，但 Litex 所做的就是让数学变得像浏览器中的 `ctrl+f & ctrl+r /cmd+f & cmd+r` 一样简单。让更多人在数学的奇妙世界中找到乐趣！

5. 细心的读者可能担心 Litex 的基础不稳固，因为`匹配和替换`不是一个非常严格的概念。他们可能认为 Lean 基于的类型理论更稳固。我不同意。首先，Lean 中类型系统的内核只是一大块 C++ 代码，执行`匹配和替换`。其次，无论传统形式语言基于什么数学基础（在 Lean 的情况下，它是类型理论），它仍然是一种编程语言，与 Python 没有什么不同。Lean 的语法风格使其在编写形式证明方面变得更容易，但它仍然非常非常远离我们在做数学时真正思考的内容，因为 Lean 的语义仍然是编程语言。所有语言设计师都同意语义比语法更重要。Litex 的语义被设计为尽可能接近我们在日常生活中的思考方式。

6. 正如 Litex 从 Python 的语法中汲取灵感一样，这里我们使用 Python 之禅来建议 Litex 的推荐风格。

```
>>> import this
The Zen of Python, by Tim Peters

Beautiful is better than ugly.
Explicit is better than implicit.
Simple is better than complex.
Complex is better than complicated.
Flat is better than nested.
Sparse is better than dense.
Readability counts.
Special cases aren't special enough to break the rules.
Although practicality beats purity.
Errors should never pass silently.
Unless explicitly silenced.
In the face of ambiguity, refuse the temptation to guess.
There should be one-- and preferably only one --obvious way to do it.
Although that way may not be obvious at first unless you're Dutch.
Now is better than never.
Although never is often better than *right* now.
If the implementation is hard to explain, it's a bad idea.
If the implementation is easy to explain, it may be a good idea.
Namespaces are one honking great idea -- let's do more of those!
```

7. Litex 内核比 Lean 的内核大得多。这有两个原因。首先，构建数学基础有多种方法。Litex 使用集合论，而 Lean 使用类型理论。虽然两者在逻辑上等价，但类型理论更抽象。这种抽象有助于保持 Lean 内核小，但也使用户更难理解。由于大多数人在高中就接触集合论，如果目标是使形式语言广泛可访问，使用类型理论作为基础并不理想。其次，Lean 是一种编程语言。因为它是图灵完备的，Lean 将实现低级逻辑的责任转移给用户。这意味着用户必须基本上自己构建系统的部分，然后才能开始验证自己的语句——而且没有保证他们的实现是正确的。相比之下，Litex 在内核本身内处理低级逻辑。这允许用户完全专注于表达和验证他们的想法，并使 Litex 比大多数其他形式语言更容易使用且计算效率更高。Litex 中的每个设计选择都以用户友好性为最高优先级。Litex 专注于验证，这大大简化了用户体验。例如，Litex 内核自动搜索既定事实，所以用户不需要命名它们或记住他们正在使用哪些。在 Lean 或 Coq 中，这种支持不存在——用户必须基本上在验证甚至开始之前手动重新实现类似 Litex 的内核。这种负担不应该落在用户身上。

8. Litex 对数学有符号观点。`匹配和替换`的过程关心符号是什么，而不是符号意味着什么。

9. Prolog vs. Litex：Prolog 是与 Litex 最相似的编程语言。

相似性

两者都使用匹配和替换来推导事实。

两者都支持 ∃ 和 ∀ 量词。

差异

在 Prolog 中未知 = 假；在 Litex 中未知 = 未知。

Prolog = 编程语言；Litex = 推理语言。

Prolog 没有类型；Litex 有简单的集合系统。

Prolog 复杂；Litex 直观简单。

技术：Litex 命名 ∃，避免死锁，并允许无名的 ∀。

10. Litex 的演进和发展

_摸着石头过河。_

_-- 中国谚语__

_量变导致质变。_

_-- 黑格尔__

_更差更好。_

_-- 著名软件开发谚语__

_C++ 用户的估计数量在 1979 年是 1，1980 年是 16，1981 年是 38，1982 年是 85，...，1990 年是 150000，1991 年是 400000。换句话说，C++ 用户群体大约每 7.5 个月翻一番。_

_-- 比雅尼·斯特劳斯特鲁普，C++ 的历史：1979-1991__

Litex 采用使用驱动、示例优先的形式化方法。在发明阶段，Litex 的创造者不是基于复杂的理论构建，而是通过尝试用 Litex 表达真实的数学文本（如陶的《分析 I》或魏尔的《初学者数论》）来发展它。当使用现有功能难以或不可能形式化某些东西时，它会增长新的语言功能（语法和语义上）以使表达自然。每当 Litex 的创造者感到语言不够表达时，他就会添加新功能使其更具表达力。

有时新功能覆盖旧功能的功能，旧功能被新功能替换。这种试错、实践指导的开发使 Litex 独特地适应性强且直观。任何功能都经过仔细测试，看它是否尽可能有用和直观，以及它是否对现有功能无害。在大多数情况下，功能要么作为语法糖工作，显著提高代码的可读性和编写体验，要么是用户表达某些类型逻辑所必需的新功能。

Litex 旨在为用户服务。它不是设计完美形式语言的学术实验。它是帮助用户形式化数学、训练 AI 模型和其他任务的实用工具。因此，为了完成其使命，Litex 必须与用户一起成长。

Litex 开发遵循谦逊的[更差更好](https://www.dreamsongs.com/RiseOfWorseIsBetter.html)哲学。想想看：JavaScript 在其作为编程语言的设计中犯了每一个错误，同时通过服务用户最迫切的需求：互联网的语言，做对了所有事情，使自己成为世界上最有影响力的编程语言之一。Litex 不完美，但它足够实用。

很难知道如何实现 Litex。甚至更难知道要实现什么，不同的语言功能如何相互配合。由于 Litex 如此不同，Litex 的创造者必须通过试错来尝试实现它，而不是遵循任何现有理论或只是模仿现有形式语言。Litex 植根于其独特而简单的（然而，这种简单性并不容易实现。）想法，而不是理论。

Litex 的创造者希望 Litex 像 C++ 和其他编程语言一样获得指数级采用。它不需要辉煌的开始，但需要强大的引擎来成长。与形式语言的潜在用户数量相比，所有传统形式语言都很小。Litex 想要改变这一点。

这就是为什么 Litex 真的需要您的帮助：使用它、传播它、为它做出贡献、改进它、让它变得更好。
