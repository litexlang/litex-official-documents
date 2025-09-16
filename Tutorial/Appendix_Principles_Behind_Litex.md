# Appendix: Principles Behind Litex

_The most beautiful experience we can have is the mysterious. It is the fundamental emotion which stands at the cradle of true art and true science. Whoever does not know it and can no longer wonder, no longer marvel, is as good as dead and his eyes are dimmed._

_-- Albert Einstein_

This file contains principles behind Litex from the Litex creator. Read it for pleasure instead of for any practical purpose. My descriptions and wording here may be somewhat vague, because the development of the whole project is essentially the process of turning vague ideas into clear ones. In fact, vague ideas often hint at the possibility of many more directions for growth, which is not yet explored.

1. You just learned how Litex builds math from basic pieces, like building blocks. To sum up, `match and substitution` is the basic way of deriving new facts from established ones. We can construct the whole math system by this way in Lite as long as basic arithmetic and counting are built-in. There are exceptions. Facts about symbols with literal information (e.g. numbers like 1, 2, 3, counting etc) are not verified in this way. Facts related to counting are not verified in this way. There are and only these two exceptions. Those facts are verified by Litex's builtin rules, the user does not need to worry about them.

2. Voltaire once said: "Common sense is not so common." In the case of Litex, Litex makes the process of building math as easy as `ctrl+f & ctrl+r /cmd+f & cmd+r` in your browser, by discovering that math is nothing but a special kind of `match and substitution` problem. Everyone is so familiar with this process, but almost no one actually finds its significance and use this idea to create a simple formal language. The real magic of Litex is that it works just like how people think in daily life. This is a hard magic for the language designer, because it requires a deep understanding of both the nature of mathematics and the nature of programming, but is worth the effort.

3. In naive set theory, where almost all daily math is based on, all facts are derived by `match and substitution` using first-order logic, with only two exceptions: 1. mathematical induction. 2. the axiom of replacement. Those two are builtin in Litex. Since high-order logic is "passing proposition as parameter to another proposition", facts about high-order logic are still verified by `match and substitution`. Litex will implement high-order logic in the future. If you are still worried about whether Litex is rigorous, the Litex kernel prints out how it verifies the statement, so you can see how it works.

4. Litex is a very simple language to learn. In fact, I am not sure whether I should use "learn" to describe it. Most of Litex language features are so common sense that we use it everyday to reason. I guess people can not "learn" what they have already known! A lot of people may think math is hard, but what Litex does is to make math as easy as `ctrl+f & ctrl+r /cmd+f & cmd+r` in your browser. Let more people find pleasure in the wonderful world of math!

5. Carful readers may worry the foundation of Litex is shaky, because `match and substitution` is not a very rigorous concept. They might think Type theory, where Lean is based on, is more solid. I disagree. First, the kernel of type system in Lean is just a huge piece of C++ code, doing `match and substitution`. Second, no matter what mathematical foundation a traditional formal language is based on (in the case of Lean, it is Type theory), it is still a programming language, which is no different from Python. The syntax style of Lean makes it sort of easier to write formal proofs, but it is still very very far from what we are truly thinking when we are doing math, because the semantics of Lean is still a programming language. All language designers agree it is the semantic that matters more, not the syntax. Litex has a semantics designed to be as close to the way we think in daily life as possible.

6. Just as Litex draws inspiration from Python's syntax, here we use the Zen of Python to suggest a recommended style for Litex.

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

7. The Litex kernel is much larger than Lean's kernel. There are two reasons for that. First, there are multiple ways to build the foundations of mathematics. Litex uses set theory, while Lean uses type theory. Although the two are logically equivalent, type theory is more abstract. This abstraction helps keep the Lean kernel small, but also makes it harder for users to understand. Since most people are introduced to set theory in high school, it is not ideal to use type theory as the foundation if the goal is to make a formal language widely accessible. Second, Lean is a programming language. Because it is Turing-complete, Lean shifts the responsibility of implementing low-level logic to the user. This means that users must essentially build parts of the system themselves before they can even begin verifying their own statements — and there's no guarantee that their implementation is correct. In contrast, Litex handles low-level logic within the kernel itself. This allows users to focus entirely on expressing and verifying their ideas, and it makes Litex both easier to use and computationally more efficient than most other formal languages. Every design choice in Litex is made with user-friendliness as the top priority. Litex is focused solely on verification, which dramatically simplifies the user experience. For example, the Litex kernel automatically searches for established facts, so users don’t need to name them or remember which ones they’re using. In Lean or Coq, this kind of support doesn’t exist — the user must essentially reimplement a Litex-like kernel by hand before verification can even begin. This burden should not fall on the user.

8. Litex has a symbolic view of math. The process of  `match and substitution` cares about what a symbol is, not what a symbol means.

9. Prolog vs. Litex: Prolog is the programming language that is most similar to Litex.

Similarities

Both use match & substitution to derive facts.

Both support ∃ and ∀ quantification.

Differences

Unknown = false in Prolog; unknown = unknown in Litex.

Prolog = programming language; Litex = reasoning language.

Prolog has no types; Litex has simple set system.

Prolog is complex; Litex is intuitive and simple.

Technical: Litex names ∃, avoids deadlocks, and allows nameless ∀.

10. Evolution and Development of Litex

_Cross the river by feeling the stones._

_-- Chinese Proverb_

_Quantity changes lead to quality changes._

_-- Hegel_

_Worse is better._

_-- A Famous Software Development Proverb_

_Estimated number of users of C++ is 1 in 1979, 16 in 1980, 38 in 1981, 85 in 1982, ..., 150000 in 1990, 400000 in 1991. In other words, the C++ user population doubled every 7.5 months or so._

_-- Bjarne Stroustrup, A History of C++: 1979-1991_

Litex takes a use-driven, example-first approach to formalization. Instead of building on sophisticated theories, at its invention stage, the creator of Litex evolves it by trying to express real mathematical texts, like Tao's *Analysis I* or Weil's *Number Theory for Beginners* in Litex. When something is hard or impossible to formalize using existing features, it grows new language features (syntactically and semantically) to make expression natural. Any time the creator of Litex feels that the language is not expressive enough, he will add new features to make it more expressive. 

Sometimes the new feature covers the functionalities of the old one and the old one is replaced by the new one. This trial-and-error, practice-guided development makes Litex uniquely adaptable and intuitive. Any feature is added with careful test about whether it is as useful and intuitive as possible and whether it is not harmful to the existing features. In most cases, a feature either works as a syntactic sugar which significantly improves the readability and writing experience of the code, or it is a new feature that is necessary for the user to express certain types of logic.

Litex is designed to serve users. It is not an academic experiment to design the perfect formal language. It is a practical tool to help users formalize their math, train their AI models, and other tasks. Thus to fulfill its mission, Litex has to grow with its users. 

Litex development follows the humble [worse is better](https://www.dreamsongs.com/RiseOfWorseIsBetter.html) philosophy. Think about it: JavaScript made every mistake in its design as a programming language while it did everything right to make itself one of the most influential programming languages in the world by serving its users' most urgent needs: the language of the Internet. Litex is not perfect, but it is pragmatic enough.

It's hard to know how to implement Litex. It's even harder to know what to implement, how different language features work together with one another. Since Litex is so different, the creator of Litex has to try to implement it by trial-and-error instead of following any existing theories or just mimicking existing formal languages. Litex is rooted in its unique and simple (However, this simplicity is not easy to achieve.) ideas, not theories.

The creator of Litex wishes Litex to obtain adoption exponentially, like C++ and other programming languages did. It does not need a glorious beginning, but it needs a strong engine to grow. Compared with potential number of users of formal languages, all traditional formal languages are tiny. Litex wants to change that.

That is why Litex really needs YOUR help: to use it, to spread the word about it, to contribute to it, to improve it, to make it better.

