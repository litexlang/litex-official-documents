# Appendix

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
| `prove_over_finite_set` | prove a universal statement by iterating over a finite set |
| `import` | import a file or directory |
| `exist_in` | exist a object in a set |
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