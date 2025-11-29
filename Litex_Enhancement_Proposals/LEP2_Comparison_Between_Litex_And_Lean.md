# Comparison Between Litex and Lean

## Fundamental Differences in Design Philosophy

### Abstractness of Basic Elements

**Lean's Approach:**
Lean's basic elements (axioms and inference rules) are few and highly abstract. This design makes its kernel very small and allows it to express more general logics. For example, Lean is based on dependent type theory, which can express higher-order logic, and ZFC can be derived as a consequence within this framework.

**Litex's Approach:**
Litex's basic elements are less abstract and more concrete. Litex is built directly on ZFC (Zermelo-Fraenkel Set Theory with Choice), which is the foundation of modern mathematics. This means that ZFC axioms are the fundamental building blocks of Litex, rather than being derived from a more abstract system.

### Implications

1. **Learning Curve**: Because Litex is based on ZFC, which is closer to how mathematics is taught and understood in our middle school and university, it is more intuitive for mathematicians and students who are already familiar with set theory.

2. **Expressiveness**: While Lean's abstract foundation allows it to express a wider range of logical systems, Litex's concrete foundation based on ZFC makes it more straightforward for expressing standard mathematical concepts that most mathematicians work with.

3. **Entry Barrier**: Litex's less abstract foundation means users can start working with familiar mathematical concepts (sets, functions, relations) immediately, without needing to understand the deeper type-theoretic foundations that Lean requires.

It's worth noting that Lean also has its own advantages that Litex does not have:

- Mature ecosystem (Mathlib)
- Active community
- Powerful type system
- Broader logical expressiveness

## Code Examples Comparison

### Solving a System of Linear Equations

Solve the equation 2x + 3y = 10 and 4x + 5y = 14.

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

### Solving a Quadratic Equation

Solve the quadratic equation x² + 2ax + b = 0.

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
      <code>claim:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall a, b, x R:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x^2 + 2 * a * x + b = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;a^2 - b >= 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = -a + sqrt(a^2 - b) or x = -a - sqrt(a^2 - b)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;sqrt(a^2 - b) * sqrt(a^2 - b) = sqrt(a^2 - b) ^ 2 = a^2 - b</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(x + a - sqrt(a^2 - b)) * (x + a + sqrt(a^2 - b)) = x ^ 2 + 2 * a * x + a^2 - sqrt(a^2 - b) ^ 2 = x ^ 2 + 2 * a * x + a^2 - (a^2 - b) = x ^ 2 + 2 * a * x + b = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$product_is_0_then_at_least_one_factor_is_0(x + a - sqrt(a^2 - b), x + a + sqrt(a^2 - b))</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove_in_each_case:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x + a + sqrt(a^2 - b) = 0 or x + a - sqrt(a^2 - b) = 0</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = -a + sqrt(a^2 - b) or x = -a - sqrt(a^2 - b)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x + a + sqrt(a^2 - b) + (-a - sqrt(a^2 - b)) = 0 + (-a - sqrt(a^2 - b))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = 0 + (-a - sqrt(a^2 - b))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = -a - sqrt(a^2 - b)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x + a - sqrt(a^2 - b) + (-a + sqrt(a^2 - b)) = 0 + (-a + sqrt(a^2 - b))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = 0 + (-a + sqrt(a^2 - b))</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x = -a + sqrt(a^2 - b)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
      <code>theorem quadratic_formula (a b x : ℝ)</code><br>
      <code>&nbsp;&nbsp;(h : x^2 + 2 * a * x + b = 0)</code><br>
      <code>&nbsp;&nbsp;(h_nonneg : a^2 - b ≥ 0) :</code><br>
      <code>&nbsp;&nbsp;x = -a + Real.sqrt (a^2 - b) ∨ x = -a - Real.sqrt (a^2 - b) := by</code><br>
      <code>&nbsp;&nbsp;have h1 : Real.sqrt (a^2 - b) * Real.sqrt (a^2 - b) = a^2 - b := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [← Real.pow_two_sqrt h_nonneg]</code><br>
      <code>&nbsp;&nbsp;have h2 : (x + a - Real.sqrt (a^2 - b)) * (x + a + Real.sqrt (a^2 - b)) = 0 := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have : (x + a)^2 - (Real.sqrt (a^2 - b))^2 = x^2 + 2 * a * x + b := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;rw [Real.sq_sqrt h_nonneg]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;rw [← this, h]</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;ring</code><br>
      <code>&nbsp;&nbsp;rcases eq_zero_or_eq_zero_of_mul_eq_zero h2 with h3 | h4</code><br>
      <code>&nbsp;&nbsp;· right</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linarith</code><br>
      <code>&nbsp;&nbsp;· left</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;linarith</code>
    </td>
  </tr>
</table>

### Proving (Z, 0, +, negate) is a Group

<table style="border-collapse: collapse; width: 100%; font-size: 12px;">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
      <code>prop is_group(s set, mul fn(s, s)s, inv fn(s)s, e s):</code><br>
      <code>&nbsp;&nbsp;forall x s, y s, z s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(mul(x, y), z) = mul(x, mul(y, z))</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(x, inv(x)) = e</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(inv(x), x) = e</code><br>
      <code>&nbsp;&nbsp;forall x s:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(x, e) = x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;mul(e, x) = x</code><br>
      <code></code><br>
      <code>forall x Z: negate(x) = -x, -x $in Z, negate(x) $in Z</code><br>
      <code></code><br>
      <code>have fn inverse(x Z) Z = negate(x)</code><br>
      <code></code><br>
      <code>forall x Z:</code><br>
      <code>&nbsp;&nbsp;negate(x) = -x = inverse(x)</code><br>
      <code>&nbsp;&nbsp;x + inverse(x) = x + (-x) = 0</code><br>
      <code>&nbsp;&nbsp;inverse(x) $in Z</code><br>
      <code></code><br>
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
      <code>&nbsp;&nbsp;add_left_neg := by intros; apply Int.neg_add_self</code>
    </td>
  </tr>
</table>

### Inverse Function Definition

<table style="border-collapse: collapse; width: 100%; font-size: 12px">
  <tr>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Litex</th>
    <th style="border: 2px solid black; padding: 4px; text-align: left; width: 50%;">Lean 4</th>
  </tr>
  <tr>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
      <code>prop is_inverse_fn(X, Y set, f fn(X)Y, g fn(Y)X):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x X:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;g(f(x)) = x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall y Y:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(g(y)) = y</code><br>
      <code></code><br>
      <code>prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have fn f(x R) R = 2 * x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;have fn g(x R) R = x / 2</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x R: f(g(x)) = f(x / 2) = 2 * (x / 2) = x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall y R: g(f(y)) = g(2 * y) = (2 * y) / 2 = y</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$is_inverse_fn(R, R, f, g)</code><br>
      <code></code><br>
      <code>prop is_injective(X, Y set, f fn(X)Y):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall x1 X, x2 X:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(x1) = f(x2)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;x1 = x2</code><br>
      <code></code><br>
      <code>exist_prop x X st item_has_preimage(X, Y set, f fn(X)Y, y Y):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;f(x) = y</code><br>
      <code></code><br>
      <code>exist_prop g fn(Y)X st has_inverse_fn(X, Y set, f fn(X)Y):</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;$is_inverse_fn(X, Y, f, g)</code><br>
      <code></code><br>
      <code>claim:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;forall X, Y set, f fn(X)Y:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$is_injective(X, Y, f)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall y Y:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$item_has_preimage(X, Y, f, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;=>:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$has_inverse_fn(X, Y, f)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;have fn:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;g(y Y) X:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(g(y)) = y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;prove:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;have x st $item_has_preimage(X, Y, f, y)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(x) = y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;= x</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall y Y:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(g(y)) = y</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;forall x X:</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;f(g(f(x))) = f(x)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;g(f(x)) = x</code><br>
      <code></code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;$is_inverse_fn(X, Y, f, g)</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;exist g st $has_inverse_fn(X, Y, f)</code>
    </td>
    <td style="border: 2px solid black; padding: 2px; line-height: 1.5;">
      <code>def f (x : ℝ) : ℝ := 2 * x</code><br>
      <code>def g (x : ℝ) : ℝ := x / 2</code><br>
      <code></code><br>
      <code>theorem f_g_id : ∀ x : ℝ, f (g x) = x := by</code><br>
      <code>&nbsp;&nbsp;intro x</code><br>
      <code>&nbsp;&nbsp;unfold f g</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code></code><br>
      <code>theorem g_f_id : ∀ y : ℝ, g (f y) = y := by</code><br>
      <code>&nbsp;&nbsp;intro y</code><br>
      <code>&nbsp;&nbsp;unfold f g</code><br>
      <code>&nbsp;&nbsp;ring</code><br>
      <code></code><br>
      <code>def is_inverse_fn (X Y : Type) (f : X → Y) (g : Y → X) : Prop :=</code><br>
      <code>&nbsp;&nbsp;(∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)</code><br>
      <code></code><br>
      <code>theorem f_g_are_inverse : is_inverse_fn ℝ ℝ f g :=</code><br>
      <code>&nbsp;&nbsp;⟨f_g_id, g_f_id⟩</code><br>
      <code></code><br>
      <code>def is_injective {X Y : Type} (f : X → Y) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂</code><br>
      <code></code><br>
      <code>def has_preimage {X Y : Type} (f : X → Y) (y : Y) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∃ x : X, f x = y</code><br>
      <code></code><br>
      <code>def has_inverse_fn {X Y : Type} (f : X → Y) : Prop :=</code><br>
      <code>&nbsp;&nbsp;∃ g : Y → X, (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)</code><br>
      <code></code><br>
      <code>theorem injective_surjective_has_inverse {X Y : Type} (f : X → Y)</code><br>
      <code>&nbsp;&nbsp;(hinj : is_injective f)</code><br>
      <code>&nbsp;&nbsp;(hsurj : ∀ y : Y, has_preimage f y) :</code><br>
      <code>&nbsp;&nbsp;has_inverse_fn f := by</code><br>
      <code>&nbsp;&nbsp;have : ∀ y : Y, ∃! x : X, f x = y := by</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;intro y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;obtain ⟨x, hx⟩ := hsurj y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;use x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· exact hx</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;· intro x' hx'</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;exact hinj x x' (hx.trans hx'.symm)</code><br>
      <code>&nbsp;&nbsp;choose g hg using this</code><br>
      <code>&nbsp;&nbsp;use g</code><br>
      <code>&nbsp;&nbsp;constructor</code><br>
      <code>&nbsp;&nbsp;· intro x</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;exact (hg (f x)).left</code><br>
      <code>&nbsp;&nbsp;· intro y</code><br>
      <code>&nbsp;&nbsp;&nbsp;&nbsp;exact (hg y).left</code>
    </td>
  </tr>
</table>

