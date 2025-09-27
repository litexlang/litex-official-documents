# When Formal Languages Meet the Everyday: Lean vs Litex

_Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex._

_-- The Zen of Python_

_What I cannot create, I do not understand._

_-- Richard Feynman_

Lean is a popular formal language, which has a 1 million LOC library and a vivid user community. The reason why people use Lean instead of Python to write math is that Lean is a programming language based on type theory, and type theory is one of the many ways of defining math. However, type theory is hard (even math PhD students do not understand it). After years of development, it is still extremely hard for an outsider, e.g. AI researchers who are not math PhD students but still hope to apply formal language to their work, to learn and use Lean.

On the other hand, Litex is all about formalization made simple. Litex, as a domain language, takes advantage of the difference between programming and verification, and is designed to be a simple and intuitive reasoning verifier. **If we want to build a successful formal language, it must be extremely simple—simple enough for ordinary people to understand. Only then can a formal language truly enter everyday life and have a real impact, rather than remaining an artwork admired only within expert circles.**

Next, I will show you how Litex is shaped by common sense, and why common sense is not so common in traditional formal languages. It must be noted that making Litex so common sense is a very uncommon thing, because it requires a deep understanding of both the nature of mathematics and the nature of programming.

I want to show you how Litex can be used to solve a simple linear equation. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex.

This example is about basic syllogism (三段论), which is the cornerstone of deductive reasoning.

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>have human nonempty_set, Jordan human</code> <br><br>
      <code>prop intelligent(x human)</code> <br><br>   
      <code>know forall x human => $intelligent(x)</code> <br> <br>
      <code>$intelligent(Jordan)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>def human := Type</code> <br><br>
      <code>def intelligent (x : human) : Prop := true</code> <br><br>
      <code>axiom intelligent_all :</code><br>
      <code>&nbsp;&nbsp;∀ (x : human), intelligent x</code> <br><br>
      <code>example (Jordan : human) : intelligent Jordan := intelligent_all Jordan</code>
    </td>
  </tr>
</table>

As you can see, in this very fundamental example, the Litex version is much more readable and intuitive than the Lean version. All keywords are very intuitive and easy to understand in the Litex version. But the syntax of Lean is much more complex.

This example means: Solve the equation 2x + 3y = 10 and 4x + 5y = 14. (本例是一个典型的多元线性方程组例子：解方程 2x + 3y = 10 和 4x + 5y = 14。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>let x R, y R:</code><br>
      <code>&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
      <code>&nbsp;&nbsp;4 * x + 5 * y = 14</code><br><br>
      <code>2 * (2 * x + 3 * y) = 2 * 10</code><br>
      <code>4* x + 6 * y = 2 * 10</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = 2 * 10 - 14</code><br>
      <code>(4*x + 6 * y) - (4*x + 5 * y) = y</code><br>
      <code>y = 6</code><br>
      <code>2 * x + 3 * 6 = 10</code><br>
      <code>2 * x + 18 - 18 = 10 - 18</code><br>
      <code>2 * x + 18 - 18 = -8</code><br>
      <code>(2 * x) / 2 = -8 / 2</code><br>
      <code>(2 * x) / 2 = x</code><br>
      <code>x = -4</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>import Mathlib.Tactic</code><br><br>
      <code>example (x y : ℝ) (h₁ : 2 * x + 3 * y = 10) (h₂ : 4 * x + 5 * y = 14) : x = -4 ∧ y = 6 := by</code><br>
      <code>&nbsp;&nbsp;have h₃ : 2 * (2 * x + 3 * y) = 2 * 10 := by rw [h₁]</code><br>
      <code>&nbsp;&nbsp;have h₄ : 4 * x + 6 * y = 20 := by linear_combination 2 * h₁</code><br>
      <code>&nbsp;&nbsp;have h₅ : (4 * x + 6 * y) - (4 * x + 5 * y) = 20 - 14 := by</code><br>
      <code>&nbsp;&nbsp;rw [h₄, h₂]</code><br>
      <code>&nbsp;&nbsp;have h₆ : (4 * x + 6 * y) - (4 * x + 5 * y) = y := by</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;have h₇ : 20 - 14 = 6 := by norm_num</code><br>
      <code>&nbsp;&nbsp;have h₈ : y = 6 := by</code><br>
      <code>&nbsp;&nbsp;rw [←h₆, h₅, h₇]</code><br>
      <code>&nbsp;&nbsp;have h₉ : 2 * x + 3 * 6 = 10 := by rw [h₈, h₁]</code><br>
      <code>&nbsp;&nbsp;have h₁₀ : 2 * x + 18 = 10 := by</code><br>
      <code>&nbsp;&nbsp;rw [mul_add] at h₉</code><br>
      <code>&nbsp;&nbsp;simp at h₉</code><br>
      <code>&nbsp;&nbsp;exact h₉</code><br>
      <code>&nbsp;&nbsp;have h₁₁ : 2 * x = -8 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₀ - 18</code><br>
      <code>&nbsp;&nbsp;have h₁₂ : x = -4 := by</code><br>
      <code>&nbsp;&nbsp;linear_combination h₁₁ / 2</code><br>
      <code>&nbsp;&nbsp;exact ⟨h₁₂, h₈⟩</code>
    </td>
  </tr>
</table>

I know Lean can use tactics to solve the same problem, and it is shorter. Litex will introduce similar features in the future. What I really want to show you here is that Litex is much more readable and intuitive than Lean in this case. Not every situation can be solved by tactics, and writing tactics itself in Lean is not easy. Litex spares you from remembering all these difficult things like `have`, `by`, `rw`, `simp`, `exact` and strange syntax etc. All you need is basic math knowledge, which significantly reduces the barrier to entry.

There is another way to write the same example in Litex, a bottom-up way.

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 40%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 60%;">Lean 4</th>
  </tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>claim:</code><br>
       <code>&nbsp;forall x, y R:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x = -4</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;y = 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 3 * y = 10</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * x + 5 * y = 14</code><br>
       <code>&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;10</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * -4 + 3 * 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 * x + 3 * y</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;=:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;14</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * -4 + 5 * 6</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;4 * x + 5 * y</code><br>
       <code></code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>example : ∀ x y : ℝ, x = -4 → y = 6 → (2 * x + 3 * y = 10 ∧ 4 * x + 5 * y = 14) :=</code><br>
       <code>by</code><br>
       <code>&nbsp;intro x y hx hy</code><br>
       <code>&nbsp;constructor</code><br>
       <code>&nbsp;· rw [hx, hy]</code><br>
       <code>&nbsp;&nbsp;calc</code><br>
       <code>&nbsp;&nbsp;&nbsp;2 * (-4) + 3 * 6 = (-8) + 18 := by rw [mul_neg, mul_one]</code><br>
       <code>&nbsp;&nbsp;&nbsp;_                = 10         := by rw [add_comm]</code><br>
       <code>&nbsp;· rw [hx, hy]</code><br>
       <code>&nbsp;&nbsp;calc</code><br>
       <code>&nbsp;&nbsp;&nbsp;4 * (-4) + 5 * 6 = (-16) + 30 := by rw [mul_neg, mul_one]</code><br>
       <code>&nbsp;&nbsp;&nbsp;_                = 14         := by rw [add_comm]</code><br>
       <code></code><br>
    </td>
  </tr>
</table>

It's very hard to prove `if x = 2 or x = -2, then x ^ 2 = 4` in Lean, because you have to remember so many strange tactic names like `rcases`, `rw`, `rfl`, `sorry` etc (The proof here is actually not complete, because `sorry` is used to avoid the proof of `-2 * -2 = 4`!!). In Litex, things are much more straightforward: it's a simple proof by cases.

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>claim:</code><br>
       <code>&nbsp;&nbsp;forall x R: or(x = 2, x = -2) => x ^ 2 = 4</code><br>
       <code>&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;prove_in_each_case:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;or(x = 2, x = -2)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = 4</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2 ^ 2 = 4</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;-2 ^ 2 = 4</code><br>
       <code></code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>&nbsp;theorem my_theorem (x : ℤ) (h : x = 2 ∨ x = -2) : x * x = 4 := by</code><br>
       <code>&nbsp;&nbsp;rcases h with ha | hb</code><br>
       <code>&nbsp;&nbsp;. rw [ha]</code><br>
       <code>&nbsp;&nbsp;&nbsp;rfl</code><br>
       <code>&nbsp;&nbsp;. have my_lemma : -2 * -2 = 4 := by sorry</code><br>
       <code>&nbsp;&nbsp;&nbsp;rw [hb] ; exact my_lemma</code><br>
       <code></code><br>
    </td>
  </tr>
</table>


Next we prove `sqrt(2) is irrational`. Since the standard library is not yet implemented, we have to define the log function ourselves for now. Note that how easy it is to define a new concept in Litex. You do not have to start from a very low level concept and build up to a higher level concept. You can define a new concept directly.

The Litex proof requires no extra knowledge except basic math knowledge, but the Lean proof requires a huge amount of knowledge about Lean tactics. Tactics are not easy to learn, not easy to remember, and very far from what we are truly thinking when we are doing math. On the other hand, any line of Litex code is very obvious to understand.

This example means: Prove `sqrt(2) is irrational`. (本例是一个典型的无理数证明例子：证明 `sqrt(2) 是无理数`。)


<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>fn logBase(x, y N) N:</code><br>
       <code>&nbsp;&nbsp;dom:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x != 0</code><br>
       <code>know forall x, y, z N => logBase(z, x^y) = y * logBase(z, x), logBase(z, x*y) = logBase(z, x) + logBase(z, y)</code><br>
       <code>know forall x N: x != 0 => logBase(x, x) = 1</code><br>
       <code></code><br>
       <code>claim:</code><br>
       <code>&nbsp;&nbsp;not sqrt(2) $in Q</code><br>
       <code>&nbsp;&nbsp;prove_by_contradiction:</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;sqrt(2) > 0</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;have x, y st $rational_positive_number_representation_in_fraction(sqrt(2))</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x = sqrt(2) * y</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = (sqrt(2) ^ 2) * (y ^ 2)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;sqrt(2) ^ 2 = 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;x ^ 2 = 2 * (y ^ 2)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, x ^ 2) = logBase(2, 2 * (y ^ 2))     </code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, x ^ 2) = 2 * logBase(2, x)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, y ^ 2) = 2 * logBase(2, y)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, 2 * (y ^ 2)) = logBase(2, 2) + logBase(2, y ^ 2)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, 2) = 1</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, 2 * (y ^ 2)) = 1 + logBase(2, y ^ 2)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;logBase(2, x ^ 2) = 1 + 2 * logBase(2, y)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * logBase(2, x) = 1 + 2 * logBase(2, y)</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = 2 * (2 * logBase(2, x)) % 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;2 * (2 * logBase(2, x)) % 2 = (1 + 2 * logBase(2, y)) % 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;(1 % 2 + (2 * logBase(2, y)) % 2) % 2 = (1 + 2 * logBase(2, y)) % 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;(1 + 2 * logBase(2, y)) % 2 = (1 % 2 + (2 * logBase(2, y)) % 2) % 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;(1 % 2 + (2 * logBase(2, y)) % 2) % 2 = (1 + 0) % 2</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;(1 + 0) % 2 = 1</code><br>
       <code>&nbsp;&nbsp;&nbsp;&nbsp;0 = 1</code><br>
       <code></code><br>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
       <code>def logBase (b n : Nat) : Nat :=</code><br>
       <code>&nbsp;if n = 0 then 0 else</code><br>
       <code>&nbsp;if n = 1 then 0 else</code><br>
       <code>&nbsp;if n % b = 0 then 1 + logBase b (n / b) else 0</code><br>
       <code></code><br>
       <code>theorem logBase_mul {b x y : Nat} (hx : x ≠ 0) (hy : y ≠ 0)</code><br>
       <code>&nbsp;(hdivx : x % b = 0) (hdivy : y % b = 0) :</code><br>
       <code>&nbsp;logBase b (x * y) = logBase b x + logBase b y := by</code><br>
       <code>&nbsp;admit</code><br>
       <code></code><br>
       <code>theorem logBase_pow2 {b x : Nat} (hx : x ≠ 0) (hdiv : x % b = 0) :</code><br>
       <code>&nbsp;logBase b (x ^ 2) = 2 * logBase b x := by</code><br>
       <code>&nbsp;admit</code><br>
       <code></code><br>
       <code>theorem logBase_two : logBase 2 2 = 1 := by</code><br>
       <code>&nbsp;simp [logBase]</code><br>
       <code>&nbsp;rfl</code><br>
       <code></code><br>
       <code>theorem sqrt2_irrational : ¬ ∃ (x y : Nat), y ≠ 0 ∧ x^2 = 2 * y^2 := by</code><br>
       <code>&nbsp;intro h</code><br>
       <code>&nbsp;obtain ⟨x, y, hy, eq⟩ := h</code><br>
       <code>&nbsp;have h1 : logBase 2 (x^2) = logBase 2 (2 * y^2) := by</code><br>
       <code>&nbsp;&nbsp;rw [eq]</code><br>
       <code>&nbsp;have lhs : logBase 2 (x^2) = 2 * logBase 2 x := by</code><br>
       <code>&nbsp;&nbsp;apply logBase_pow2</code><br>
       <code>&nbsp;&nbsp;exact Nat.pow_ne_zero 2 (Nat.zero_lt_succ _)</code><br>
       <code>&nbsp;&nbsp;admit</code><br>
       <code>&nbsp;have rhs : logBase 2 (2 * y^2) = 1 + 2 * logBase 2 y := by</code><br>
       <code>&nbsp;&nbsp;admit</code><br>
       <code>&nbsp;rw [lhs, rhs] at h1</code><br>
       <code>&nbsp;have : Even (2 * logBase 2 x) := by simp</code><br>
       <code>&nbsp;have : Odd (1 + 2 * logBase 2 y) := by simp</code><br>
       <code>&nbsp;contradiction</code><br>
       <code></code><br>
    </td>
  </tr>
</table>


Next I want to show you how Litex can be used to verify a simple group theory statement. It's clear that the Litex version can be read and understood by a 10-year-old, while the Lean version is much more complex. Look how easy it is to narrow the function type of `inverse` from `R` to `Z`.

This example means: Define a group, and prove `R` is a group. (本例是一个典型的群论例子：定义一个群，并证明 `R` 是一个群。)

<table style="border-collapse: collapse; width: 100%; font-size: 12px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):</code><br>
      <code>&nbsp;&nbsp;forall x s, y s, z s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(mul(x, y), z) = mul(x, mul(y, z))</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(x, inv(x)) = e</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(inv(x), x) = e</code><br><br>
      <code>fn inverse(x R)R:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;inverse(x) + x = 0</code><br><br>
      <code>forall x R:</code><br>
      <code>&nbsp;&nbsp;inverse(x) $in R</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = inverse(x) + x</code><br>
      <code>&nbsp;&nbsp;inverse(x) + x = 0</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = 0</code><br><br>
      <code>$is_group(R, +, inverse, 0)</code><br>
      <code>$is_group(Z, +, inverse, 0)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5">
      <code>structure MyGroup (G : Type) where</code><br>
      <code>&nbsp;&nbsp;add : G → G → G</code><br>
      <code>&nbsp;&nbsp;zero : G</code><br>
      <code>&nbsp;&nbsp;neg : G → G</code><br>
      <code>&nbsp;&nbsp;add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)</code><br>
      <code>&nbsp;&nbsp;zero_add : ∀ a : G, add zero a = a</code><br>
      <code>&nbsp;&nbsp;add_zero : ∀ a : G, add a zero = a</code><br>
      <code>&nbsp;&nbsp;add_left_neg : ∀ a : G, add (neg a) a = zero</code><br><br>
      <code>def intAddGroup : MyGroup Int where</code><br>
      <code>&nbsp;&nbsp;add := Int.add</code><br>
      <code>&nbsp;&nbsp;zero := 0</code><br>
      <code>&nbsp;&nbsp;neg := Int.neg</code><br>
      <code>&nbsp;&nbsp;add_assoc := by intros; apply Int.add_assoc</code><br>
      <code>&nbsp;&nbsp;zero_add := by intros; apply Int.zero_add</code><br>
      <code>&nbsp;&nbsp;add_zero := by intros; apply Int.add_zero</code><br>
      <code>&nbsp;&nbsp;add_left_neg := by intros; apply Int.neg_add_self</code><br><br>
      <code>-- R is not builtin in Lean, the user has to define it himself or rely on the library. We skip it.</code><br>
    </td>
  </tr>
</table>

In 2025, the number of mathematicians who use formal languages only takes less than 1 percent of the total number of mathematicians. The goal of Litex is not only to raise this proportion, but more importantly to enable non-mathematics practitioners — such as AI researchers, professionals in science and engineering, educators, and even children who are just beginning to explore mathematics — to experience the joy of math and logic through Litex, as well as the boundless potential that comes from combining reasoning with computing.

Litex is different from Lean. When defining concepts, Lean starts from the very bottom and gradually builds up to common mathematical notions. In contrast, Litex allows you to begin from any level of abstraction you care about. This means users can start doing mathematics in Litex right away without worrying about things they are not interested in. As a result, Litex is much easier for newcomers to pick up, and developing its standard library is also more straightforward.