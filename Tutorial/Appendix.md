# Appendix

_Everything is a file._

_- Unix Philosophy_

## Language Tradeoffs

_Everything should be made as simple as possible, but not simpler._

__-- Albert Einstein__

*Simplicity over Generality*: Litex focuses more on simplicity of the language, so that more people can learn to use it. Currently, Litex has built-in support for naive set theory and first-order logic, which is enough for most daily math. If adding certain features (such as higher-order logic) would compromise Litex’s simplicity, we would rather leave them out. Just as Python gave up C’s manual memory management, and Markdown gave up LaTeX’s fine-grained pixel control, Litex gives up generality in exchange for simplicity.

*Simplicity is the single most important consideration in our design. It is more important than any other features like generality, elegance, efficiency, etc.*

__Given enough eyeballs, all bugs are shallow.__

__-- Linus Torvalds__

*Community-Driven Fast Development over Careful Design*: Litex follows the 'worse is better' development model, because this is the most effective way for software to gain impact. We care more about building the community and iterating quickly based on community feedback. No matter how good a feature is, if it cannot be implemented quickly or is not widely requested by the community, we won’t consider it.

*Bugs won't make a software obsolete. What truly kills a software is the lack of users and supporters.*

__We have some freedom in setting up our personal standards of beauty, but it is especially nice when the things we regard as beautiful are also regarded by other people as useful.__

__-- Donald Knuth__

*Pragmatic over Idealistic*: We would rather add features that are useful for daily math than features that are useful for theoretical math which is understood by only a few people on earth. That's why Litex is ended with tex: we want to make it a wide-spread pragmatic language which solves real problems just like tex.

*We are not aiming for a perfect language, but a language that is good enough for most use cases. We also want it to evolve fast to satisfy the changing needs of the community.*

## Keywords: Everything Happens Around Them

The keywords in Litex are almost identical in meaning and usage to the commonly used ones in mathematics. This makes writing in Litex a very pleasant experience.

| Keyword | Meaning |
|---------|---------|
| `let` | Define an object without checking its existence. |
| `prop` | Define a proposition. The verbs of logic. |
| `know` | Establish a fact |
| `forall` | Universal quantification |
| `exist` | Existential quantification |
| `have` | Introduce an object with checking its existence. |
| `exist_prop` | Existential quantification with a proposition |
| `or` | Disjunction |
| `not` | Negation |
| `fn` | Define a function without checking its existence |
| `fn_template` | Define a class of functions |
| `set` | set: a collection of objects |
| `in` | membership of an object in a set |
| `dom` | domain of a proposition, function, function template, etc. |
| `len`  | length of a set |
| `finite_set` | a set with a finite number of elements |
| `prove` | open a local environment to write some statements without affecting the global environment |
| `claim` | claim a factual statement, prove it here |
| `prove_by_contradiction` | prove by contradiction |
| `prove_in_each_case` | prove by case analysis |
| `prove_by_induction` | prove by mathematical induction |
| `prove_by_enum` | prove a universal statement by iterating over a finite set |
| `prove_in_range` | prove a universal statement by iterating over a range of integers |
| `import` | import a file or directory |
| `item_exists_in` | exist a object in a set |
| `set_defined_by_replacement` | define a set by a axiom of replacement |
| `obj_exist_as_preimage_of_prop` | exist a object as the preimage of a proposition |
| `obj_exist_as_preimage_of_fn` | exist a object as the preimage of a function |
| `N` `N_pos` `Z` `Q` `R` `C` `obj` | builtin sets: natural numbers, positive natural numbers, integers, rational numbers, real numbers, complex numbers, objects |
| `clear` | clear all facts |
| `set_product` | a product of sets |
| `proj` | a projection of a set product |
| `lift` | Point-wise lifting of an operator |

Although these keywords are rarely defined strictly in math textbooks, they are used everyday and everywhere. Litex creator can not find strict definition for keywords like `proposition`, `is`, `in` etc (actually, the word `definition` is also a vague word). He tried his best to make the meaning of these keywords as close to the meaning in our daily math expression, along with his own ideas and understanding, so that Litex is both intuitive and strict.

## Why Should You Learn Litex

_The only way to do great work is to love what you do._

_-- Steve Jobs_

Litex represents a fundamental shift in how we approach formal reasoning and mathematical thinking. Here are compelling reasons why you should consider learning Litex:

## 1. Master the Future of AI and Formal Reasoning

The AI landscape is rapidly evolving toward formal language-driven approaches. As traditional data-driven learning faces limitations, the industry is shifting to self-improving AI systems that use formal reasoning. Learning Litex positions you at the forefront of this transformation, giving you the tools to work with the next generation of AI systems that can reason, verify, and improve themselves.

## 2. Ensure Mathematical Rigor and Correctness

Mathematics demands absolute precision - a single error can invalidate entire proofs and lead to significant consequences. Litex provides a powerful framework for ensuring the correctness of any reasoning process. By learning Litex, you gain the ability to create bulletproof mathematical arguments and verify the work of others with complete confidence.

## 3. Scale Your Mathematical Collaboration

Traditional mathematical collaboration is limited by the need to manually verify every contribution. Litex changes this by providing automatic verification through its kernel, enabling unprecedented levels of collaboration. You can work with mathematicians worldwide, knowing that the system will certify the correctness of every contribution, dramatically expanding the scale of mathematical discovery and knowledge.

## 4. Transform Mathematics into Mathematical Engineering

Litex revolutionizes how we approach mathematical work by applying software engineering principles to mathematics. Through clear abstraction and composition, individual mathematical work becomes **mathematical engineering**. Writing mathematics in Litex can be as intuitive as writing code in Python, making complex formal reasoning accessible to a broader audience.

## 5. Join the Accessibility Revolution in Formal Reasoning

Unlike other formal languages that require extensive expertise, Litex is designed to be accessible to everyone - from children learning basic logic to experts working on cutting-edge research. By learning Litex, you become part of a movement that democratizes formal reasoning and enables more people to participate in rigorous mathematical thinking.

## 6. Build the Infrastructure for AI-Driven Discovery

Litex provides the perfect foundation for AI systems to learn and perform formal reasoning at scale. As AI becomes increasingly important in scientific discovery and problem-solving, understanding Litex gives you the ability to work with and contribute to AI systems that can reason formally, verify their own work, and discover new mathematical truths.


## The Time is Now

The convergence of AI advancement and the growing complexity of mathematics has created an unprecedented opportunity. Learning Litex today means positioning yourself at the intersection of two transformative forces: the AI revolution that's reshaping how we solve problems, and the formal reasoning revolution that's transforming how we think about mathematics and logic.

Whether you're a student, researcher, engineer, or simply someone fascinated by the power of rigorous thinking, Litex offers you the tools to participate in this exciting future. The question isn't whether formal reasoning will become central to our intellectual landscape - it's whether you'll be ready to contribute when it does.

---

## References

### AI and Formal Reasoning
- [DeepSeek-R1](https://arxiv.org/abs/2501.12948): DeepSeek-R1 uses formal language as value function for Reinforcement Learning, making their model extremely efficient and accurate.
- [AlphaProof](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/): AlphaProof uses formal language to formulate problems, solve them, and improve the model based on formal language interpreter output. It achieves silver medal level in IMO, which is super-human level in math.
- [AlphaGeometry](https://deepmind.google/discover/blog/alphageometry-an-olympiad-level-ai-system-for-geometry/): AlphaGeometry achieves gold medal level in IMO geometry problems, which is super-human level in math.
- [Safeguarded AI](https://www.aria.org.uk/opportunity-spaces/mathematics-for-safe-ai/safeguarded-ai/): One of the first AI safety organizations to focus on formal reasoning, with Turing award recipient Yoshua Bengio as Scientific Director.
- [Formal Mathematical Reasoning: A New Frontier in AI](https://arxiv.org/abs/2412.16075): This article argues AI-driven discovery in science, engineering, and beyond can be accelerated by the adoption of formal reasoning.

### Mathematics and Formal Methods
- [Machine Assisted Proof](https://terrytao.wordpress.com/wp-content/uploads/2024/03/machine-assisted-proof-notices.pdf): Fields Medalist Terence Tao forecasts the great potential of the combination of formal reasoning and machine learning in math.
- [Mathematics and the formal turn](https://arxiv.org/pdf/2311.00007): Lean advisory board member Jeremy Avigad argues that the formal turn in mathematics holds a lot of promise and the new technology will undoubtedly alter our conception of what it means to do mathematics.
- [Terrence Tao on Lex Fridman Podcast](https://www.youtube.com/watch?v=HUkBz-cdB-k&t=5400s): Fields Medalist Terence Tao discusses the potential of formal reasoning in math.

## Litex is Turing Complete Or Not?

_...an unlimited memory capacity obtained in the form of an infinite tape marked out into squares, on each of which a symbol could be printed. At any moment there is one symbol in the machine; it is called the scanned symbol. The machine can alter the scanned symbol, and its behavior is in part determined by that symbol, but the symbols on the tape elsewhere do not affect the behavior of the machine. However, the tape can be moved back and forth through the machine, this being one of the elementary operations of the machine. Any symbol on the tape may therefore eventually have an innings._

_-- Alan Turing_

One of the greatest joys of maintaining open-source software is being part of a passionate community. Often, people in the community know the language even better than its creator! Some community experts have tried to prove that Litex is Turing-complete from two different perspectives, and here are their code examples. Really thanks to their dedication. We wish more people can join us to make Litex better. Feel free to submit your interesting ideas on [zulip](https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/)!

Their proof is not fully verified. Feel free to point out anything about their proof!

1. Provided by Chenxuan Huang. He uses SKI combinator to prove the Turing completeness of Litex.

```litex
have Term nonempty_set
have I, S, K Term
fn app(a Term, b Term) Term

have Value nonempty_set
have I0, K0, S0 Value
fn K1(a Term) Value
fn S1(a Term) Value
fn S2(a Term, b Term) Value

have List nonempty_set
have Nil List
fn Cons(x Term, xs List) List

have Machine nonempty_set
fn M0(x Term, stk List) Machine
fn M1(x Value, stk List) Machine
fn M2(x Value) Machine

fn step(m Machine) Machine
know:
    # M0 steps down
    forall x, y Term, l List:
        step(M0(app(x, y), l)) = M0(x, Cons(y, l))
    forall l List:
        step(M0(I, l)) = M1(I0, l)
        step(M0(K, l)) = M1(K0, l)
        step(M0(S, l)) = M1(S0, l)

    # M1 perform the combinators' actions
    step(M1(I0, Nil)) = M2(I0)
    step(M1(K0, Nil)) = M2(K0)
    step(M1(S0, Nil)) = M2(S0)
    forall x Term, l List:
        step(M1(I0, Cons(x, l))) = M0(x, l)
        step(M1(K0, Cons(x, l))) = M1(K1(x), l)
        step(M1(S0, Cons(x, l))) = M1(S1(x), l)
        step(M1(K0(x), Nil)) = M2(K0(x))
        step(M1(S1(x), Nil)) = M2(S1(x))
    forall x, y Term, l List:
        step(M1(K0(x), Cons(y, l))) = M0(x, l)
        step(M1(S1(x), Cons(y, l))) = M1(S2(x, y), l)
        step(M1(S2(x, y), Nil)) = M2(S2(x, y))
    forall x, y, z Term, l List:
        step(M1(S2(x, y), Cons(z, l))) = M0(app(app(x, z), app(y, z)), l)

    # M2 ends the evaluation
    forall x Value:
        step(M2(x)) = M2(x)

fn evalm(m Machine) Machine
know:
    forall x Term, l List:
        evalm(M0(x, l)) = evalm(step(M0(x, l)))
    forall x Value, l List:
        evalm(M1(x, l)) = evalm(step(M1(x, l)))
    forall x Value:
        evalm(M2(x)) = M2(x)

have program0 Term
know:
    program0 = app(I, K)

# now to execute the program ...
step(M0(program0, Nil)) = M0(I, Cons(K, Nil))
evalm(M0(program0, Nil)) = evalm(M0(I, Cons(K, Nil)))
# add more steps as necessary...
```

2. Provided by Changyang Zhu. He uses the Y-combinator to prove the Turing completeness of Litex.

```litex
have Term nonempty_set
have I, S, K, C_, B, U Term
fn app(a Term, b Term) Term

# I = Lambda x.x
# S = lambda xyz.(xz)(yz)
# K = lambda xy.x
# C_ = lambda xyz.xzy
# B = lambda xyz.x(yz)
# U = lambda x.xx

have Value nonempty_set
have I0, K0, S0, C0, B0, U0 Value
fn K1(a Term) Value
fn S1(a Term) Value
fn S2(a Term, b Term) Value
fn C1(a Term) Value
fn C2(a Term, b Term) Value
fn B1(a Term) Value
fn B2(a Term, b Term) Value
fn U1(a Term) Value

have List nonempty_set
have Nil List
fn Cons(x Term, xs List) List

have Machine nonempty_set
fn M0(x Term, stk List) Machine
fn M1(x Value, stk List) Machine
fn M2(x Value) Machine

know:
    # M0 steps down
    forall x, y Term, l List:
        M0(app(x, y), l) = M0(x, Cons(y, l))
    forall l List:
        M0(I, l) = M1(I0, l)
        M0(K, l) = M1(K0, l)
        M0(S, l) = M1(S0, l)
        M0(C_, l) = M1(C0, l)
        M0(B, l) = M1(B0, l)
        M0(U, l) = M1(U0, l)

    # M1 perform the combinators' actions
    M1(I0, Nil) = M2(I0)
    M1(K0, Nil) = M2(K0)
    M1(S0, Nil) = M2(S0)
    M1(C0, Nil) = M2(C0)
    M1(B0, Nil) = M2(B0)
    M1(U0, Nil) = M2(U0)
    forall x Term, l List:
        M1(I0, Cons(x, l)) = M0(x, l)
        M1(U0, Cons(x, l)) = M0(app(x, x), l)
        M1(K0, Cons(x, l)) = M1(K1(x), l)
        M1(S0, Cons(x, l)) = M1(S1(x), l)
        M1(C0, Cons(x, l)) = M1(C1(x), l)
        M1(B0, Cons(x, l)) = M1(B1(x), l)
        M1(K0(x), Nil) = M2(K0(x))
        M1(S1(x), Nil) = M2(S1(x))
        M1(C1(x), Nil) = M2(C1(x))
        M1(B1(x), Nil) = M2(B1(x))
    forall x, y Term, l List:
        M1(K0(x), Cons(y, l)) = M0(x, l)
        M1(S1(x), Cons(y, l)) = M1(S2(x, y), l)
        M1(C1(x), Cons(y, l)) = M1(C2(x, y), l)
        M1(B1(x), Cons(y, l)) = M1(B2(x, y), l)
        M1(S2(x, y), Nil) = M2(S2(x, y))
        M1(C2(x, y), Nil) = M2(C2(x, y))
        M1(B2(x, y), Nil) = M2(B2(x, y))
    forall x, y, z Term, l List:
        M1(S2(x, y), Cons(z, l)) = M0(app(app(x, z), app(y, z)), l)
        M1(C2(x, y), Cons(z, l)) = M0(app(app(x, z), y), l)
        M1(B2(x, y), Cons(z, l)) = M0(app(x, app(y, z)), l)

have Y Term
know:
    Y = app(app(B, U), app(app(C_, B), U))

have F Term

have program Term
know:
    program = app(Y, F)

# Hereby we noticed that "step" and "evalm" are only symbols that require transitivity
# Thus we use "=" to simplify the program
# You can expand it to "step" and "evalm" if you want

know forall a, b Term: M0(a, Nil) = M0(b, Nil) => a = b
=:
    M0(program, Nil)
    M0(app(Y, F), Nil)
    M0(app(app(app(B, U), app(app(C_, B), U)), F), Nil)
    M0(app(app(B, U), app(app(C_, B), U)), Cons(F, Nil))
    M0(app(B, U), Cons(app(app(C_, B), U), Cons(F, Nil)))
    M0(B, Cons(U, Cons(app(app(C_, B), U), Cons(F, Nil))))
    M1(B0, Cons(U, Cons(app(app(C_, B), U), Cons(F, Nil))))
    M1(B1(U), Cons(app(app(C_, B), U), Cons(F, Nil)))
    M1(B2(U, app(app(C_, B), U)), Cons(F, Nil))
    M0(app(U, app(app(app(C_, B), U), F)), Nil)
    M0(U, Cons(app(app(app(C_, B), U), F), Nil))
    M1(U0, Cons(app(app(app(C_, B), U), F), Nil))
    M0(app(app(app(app(C_, B), U), F), app(app(app(C_, B), U), F)), Nil)

=:
    M0(app(app(app(C_, B), U), F), Nil)
    M0(app(app(C_, B), U), Cons(F, Nil))
    M0(app(C_, B), Cons(U, Cons(F, Nil)))
    M0(C_, Cons(B,Cons(U, Cons(F, Nil))))
    M1(C0, Cons(B,Cons(U, Cons(F, Nil))))
    M1(C1(B), Cons(U, Cons(F, Nil)))
    M1(C2(B, U), Cons(F, Nil))
    M0(app(app(B, F), U), Nil)

app(app(app(C_, B), U), F) = app(app(B, F), U)

=:
    M0(program, Nil)
    M0(app(app(app(app(C_, B), U), F), app(app(app(C_, B), U), F)), Nil)
    M0(app(app(app(B, F), U), app(app(B, F), U)), Nil)
    M0(app(app(B, F), U), Cons(app(app(B, F), U), Nil))
    M0(app(B, F), Cons(U, Cons(app(app(B, F), U), Nil)))
    M0(B, Cons(F, Cons(U, Cons(app(app(B, F), U), Nil))))
    M1(B0, Cons(F, Cons(U, Cons(app(app(B, F), U), Nil))))
    M1(B1(F), Cons(U, Cons(app(app(B, F), U), Nil)))
    M1(B2(F, U), Cons(app(app(B, F), U), Nil))
    M0(app(F, app(U, app(app(B, F), U))), Nil)

=:
    M0(app(U, app(app(B, F), U)), Nil)
    M0(U, Cons(app(app(B, F), U), Nil))
    M0(app(app(app(B, F), U), app(app(B, F), U)), Nil)
    M0(program, Nil)

app(U, app(app(B, F), U)) = program

=:
    M0(program, Nil)
    M0(app(F, app(U, app(app(B, F), U))), Nil)
    M0(app(F, program), Nil)

program = app(F, program)
app(Y, F) = app(F, app(Y, F))

# Thus, we've proved the property of Y-combinator
# Y F = F(Y F)
```

## Principles Behind Litex

_Everyday spent on Litex is another good day to explore new adventures._

_- Litex creator Jiachen Shen_

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

## Litex Kernel Implementation

2025.9.28 This file is under construction. There are many things to write about and I am still figuring out a systematic way to write about it. For now, there are just some notes here.

1. You can write forall under forall under forall, in other words, the depth of forall is limited to two levels. For example You can not write the following code:

```
# The domain fact is too deep: the maximum depth of the whole forall is 2 and thus the depth of the domain fact is 1
forall x R:
    forall y R:
        forall z R:
            x = y + z
    =>:
        x = y + z
```

The correct way to write it is:

```litex
forall x, y, z R:
    x = y + z
    =>:
        x = y + z
```

```
# The then fact is too deep: the maximum depth of the whole forall is 2 and thus the depth of the domain fact is 1
forall x R:
    forall y R:
        forall z R:
            x $in R
            y $in R
            z $in R
```

The correct way to write it is:
```litex
forall x, y, z R:
    x $in R
    y $in R
    z $in R
```

The reason why we must restrict the depth of forall is that proving a one-layer forall fact is computationally expensive: O(N). When the depth is two layers, the computational complexity is O(N^2). When the depth is three layers, the computational complexity is O(N^3). And so on. Therefore, we must restrict the depth of forall to two layers to avoid computational explosion.

To avoid too deep forall, you can put all the related parameters in the outmost layer of forall. For example:
```litex
forall x, y, z R:
    x $in R
    y $in R
    z $in R
```

instead of:
```litex
forall x R, y R:
    forall z R:
        x $in R
        y $in R
        z $in R
```

2. There is no infinite verification loop in Litex

For example, consider the following code:

```litex
prop p(x R)
prop q(x R)
know forall x R => $p(x) <=> $q(x)
$p(1)
```

Since Litex searches related facts using `match and substitution`, it finds that if we can prove $q(1) is true then $p(1) is true. So we prove $q(1). Then we find that if we can prove $p(1) is true then $q(1) is true. So we prove $p(1). This is a loop. It happens when two facts are equivalent.

This won't happen in Litex. Litex just searches 2 rounds of related `forall` facts. So even if we have a loop, it will end after 2 rounds. (Number 2 is equal to the depth of maximum `forall` depth, this is not a coincidence, it's by design.)

While Lean 4 is a powerful and rigorous proof assistant ideal, it requires months of training and years of experience to master. Litex takes a different approach: prioritizing accessibility and ease of use, enabling even beginners to formalize naive tasks like multivariate equations in minutes.

Since each Litex sentence corresponds directly to an expression in everyday mathematical language, and since it is supported by set theory (ZFC) and basic logic (not, forall, exist, or), Litex does not sacrifice any rigor. So please do not think about Litex using the mindset of traditional formal languages. Instead, imagine yourself as a college student or even a high school student who has a basic understanding of set theory — regardless of whether you like Litex or are skeptical of it.

*In summary, Litex is a piece of software that imitates the way people think when they verify mathematics in everyday reasoning, using a small number of straightforward rules.* For example, if it sees “24 * 25 = 600,” it knows that a calculation needs to be performed. If it sees statements like “Every person will die” and “Socrates is a person,” it uses pattern matching and substitution: it substitutes Socrates into the statement “Every person will die” and checks whether Socrates satisfies the condition “is a person.” If so, it concludes that Socrates will also die. Along with other extremely common rules, Litex can verify complex mathematical statements with ease.

