import Mathlib.Algebra.Polynomial.Eval.Defs
import UndergradKB.Precalculus.RationalExponents

/-!
# Algebraic functions and their sign diagrams (Stitz-Zeager, Precalculus, §5.3)

The book calls *algebraic* the functions obtained by combining radical functions with polynomial and rational
functions (§5.3, p. 411; its footnote adds `|x| = √(x²)`), and gives a sign-diagram procedure for them: radical
functions are continuous on their domains, so the Intermediate Value Theorem applies. The book gives no formal
definition. Here an algebraic function is the value of an *algebraic expression* in one variable, built from `x` and
real constants by sums, negatives, products, quotients and principal `n`-th roots (`principalRoot`, the book's
radical; Definition 5.4). Its natural domain `AlgebraicExpr.domain` is the book's: no zero denominator, and no even
root of a negative number.

Proved here:
* `AlgebraicExpr.continuousOn_domain`: every algebraic function is continuous on its natural domain;
* `sign_diagram_algebraicExpr`: the book's box "Steps for Constructing a Sign Diagram for an Algebraic Function": on
  an interval of the domain without zeros, the sign is constant, so one test value per interval suffices;
* `algebraicExpr_ivt`: the Intermediate Value Theorem for algebraic functions on an interval of the domain;
* polynomials, rational functions (`AlgebraicExpr.ofPolynomial`, `AlgebraicExpr.ofRational`) and the absolute value
  (`AlgebraicExpr.absX`) are algebraic, with the expected domains;
* Example 5.3.1(2): `√(2 - √(4x+3))` has domain `[-3/4, 1/4]` (`domain_example_5_3_1_2`).

This closes a recorded loose end (the wave-4 theorem `sign_diagram_algebraic` took continuity as a hypothesis).
-/

namespace UndergradKB.Precalculus

open Set

/-- Algebraic expressions in one real variable (§5.3): the variable `x`, real constants, sums, negatives, products,
quotients and principal `n`-th roots. -/
inductive AlgebraicExpr : Type
  | var : AlgebraicExpr
  | const (c : ℝ) : AlgebraicExpr
  | add (e f : AlgebraicExpr) : AlgebraicExpr
  | neg (e : AlgebraicExpr) : AlgebraicExpr
  | mul (e f : AlgebraicExpr) : AlgebraicExpr
  | div (e f : AlgebraicExpr) : AlgebraicExpr
  | root (n : ℕ) (e : AlgebraicExpr) : AlgebraicExpr

namespace AlgebraicExpr

/-- The function defined by an algebraic expression; `root n e` is the principal root `ⁿ√(e x)`. -/
noncomputable def eval : AlgebraicExpr → ℝ → ℝ
  | var => fun x => x
  | const c => fun _ => c
  | add e f => fun x => eval e x + eval f x
  | neg e => fun x => -eval e x
  | mul e f => fun x => eval e x * eval f x
  | div e f => fun x => eval e x / eval f x
  | root n e => fun x => principalRoot n (eval e x)

/-- The natural domain of an algebraic expression, as in the book: every denominator is nonzero, and every radical
`ⁿ√(e x)` has index `n ≥ 1` and is real (`n` odd, or `e x ≥ 0`). -/
def domain : AlgebraicExpr → Set ℝ
  | var => univ
  | const _ => univ
  | add e f => domain e ∩ domain f
  | neg e => domain e
  | mul e f => domain e ∩ domain f
  | div e f => domain e ∩ domain f ∩ {x | eval f x ≠ 0}
  | root n e => domain e ∩ {x | n ≠ 0 ∧ (Odd n ∨ 0 ≤ eval e x)}

/-- Difference of two algebraic expressions. -/
def sub (e f : AlgebraicExpr) : AlgebraicExpr := add e (neg f)

/-- Natural power of an algebraic expression. -/
def pow (e : AlgebraicExpr) : ℕ → AlgebraicExpr
  | 0 => const 1
  | k + 1 => mul (pow e k) e

@[simp] lemma eval_sub (e f : AlgebraicExpr) (x : ℝ) : (sub e f).eval x = e.eval x - f.eval x := by
  simp [sub, eval, sub_eq_add_neg]

@[simp] lemma domain_sub (e f : AlgebraicExpr) : (sub e f).domain = e.domain ∩ f.domain := rfl

@[simp] lemma eval_pow (e : AlgebraicExpr) (k : ℕ) (x : ℝ) : (pow e k).eval x = e.eval x ^ k := by
  induction k with
  | zero => simp [pow, eval]
  | succ k ih => simp [pow, eval, ih, pow_succ]

lemma domain_pow (e : AlgebraicExpr) (k : ℕ) (hk : k ≠ 0) : (pow e k).domain = e.domain := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp [pow, domain]
    · simp [pow, domain, ih hk'.ne']

/-- Radical functions are continuous on their domains, so every algebraic function is continuous on its natural
domain (§5.3, p. 411; the book leaves this to calculus). -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem continuousOn_domain : ∀ e : AlgebraicExpr, ContinuousOn e.eval e.domain
  | var => continuous_id.continuousOn
  | const _ => continuous_const.continuousOn
  | add e f => by
    have he := (continuousOn_domain e).mono (inter_subset_left (t := f.domain))
    have hf := (continuousOn_domain f).mono (inter_subset_right (s := e.domain))
    exact he.add hf
  | neg e => (continuousOn_domain e).neg
  | mul e f => by
    have he := (continuousOn_domain e).mono (inter_subset_left (t := f.domain))
    have hf := (continuousOn_domain f).mono (inter_subset_right (s := e.domain))
    exact he.mul hf
  | div e f => by
    have he := (continuousOn_domain e).mono fun x (hx : x ∈ (div e f).domain) => hx.1.1
    have hf := (continuousOn_domain f).mono fun x (hx : x ∈ (div e f).domain) => hx.1.2
    exact he.div hf fun x hx => hx.2
  | root n e => by
    have he := (continuousOn_domain e).mono fun x (hx : x ∈ (root n e).domain) => hx.1
    by_cases hn : Odd n
    · exact (principalRoot_continuous_odd hn).comp_continuousOn he
    · refine (principalRoot_continuousOn_even n).comp he ?_
      intro x hx
      exact hx.2.2.resolve_left hn

/-- Steps for constructing a sign diagram for an algebraic function (§5.3, p. 411): on an interval contained in the
domain and free of zeros, an algebraic function has one constant sign, so the excluded values and the zeros cut the
line into intervals on each of which one test value gives the sign. -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem sign_diagram_algebraicExpr (e : AlgebraicExpr) {I : Set ℝ} (hI : I.OrdConnected) (hsub : I ⊆ e.domain)
    (hz : ∀ x ∈ I, e.eval x ≠ 0) {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    SignType.sign (e.eval x) = SignType.sign (e.eval t) :=
  sign_diagram_algebraic hI ((continuousOn_domain e).mono hsub) hz hx ht

/-- The Intermediate Value Theorem applies to algebraic functions (§5.3, p. 411): if `[a, b]` lies in the domain and
`e(a)`, `e(b)` have opposite signs (weakly), then `e` has a zero in `[a, b]`. -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem algebraicExpr_ivt (e : AlgebraicExpr) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ e.domain)
    (hsign : e.eval a ≤ 0 ∧ 0 ≤ e.eval b ∨ 0 ≤ e.eval a ∧ e.eval b ≤ 0) :
    ∃ c ∈ Icc a b, e.eval c = 0 := by
  have hc := (continuousOn_domain e).mono hsub
  rcases hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Icc hab hc ⟨ha, hb⟩
  · exact intermediate_value_Icc' hab hc ⟨hb, ha⟩

/-- Every polynomial function is algebraic, with domain all of `ℝ`. -/
lemma exists_polynomial (p : Polynomial ℝ) :
    ∃ e : AlgebraicExpr, (∀ x, e.eval x = p.eval x) ∧ e.domain = univ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨e, he, hed⟩ := hp
    obtain ⟨f, hf, hfd⟩ := hq
    exact ⟨add e f, fun x => by simp [eval, he, hf], by simp [domain, hed, hfd]⟩
  | monomial k c =>
    refine ⟨mul (const c) (pow var k), fun x => by simp [eval], ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [domain, pow]
    · simp [domain, domain_pow _ _ hk.ne']

/-- An algebraic expression for a polynomial. -/
noncomputable def ofPolynomial (p : Polynomial ℝ) : AlgebraicExpr := (exists_polynomial p).choose

@[simp] lemma eval_ofPolynomial (p : Polynomial ℝ) (x : ℝ) : (ofPolynomial p).eval x = p.eval x :=
  (exists_polynomial p).choose_spec.1 x

@[simp] lemma domain_ofPolynomial (p : Polynomial ℝ) : (ofPolynomial p).domain = univ :=
  (exists_polynomial p).choose_spec.2

/-- A rational function `p/q` as an algebraic expression. -/
noncomputable def ofRational (p q : Polynomial ℝ) : AlgebraicExpr := div (ofPolynomial p) (ofPolynomial q)

@[simp] lemma eval_ofRational (p q : Polynomial ℝ) (x : ℝ) :
    (ofRational p q).eval x = p.eval x / q.eval x := by
  simp [ofRational, eval]

/-- The domain of a rational function `p/q` is where `q` does not vanish (§4.1). -/
@[simp] lemma domain_ofRational (p q : Polynomial ℝ) :
    (ofRational p q).domain = {x | q.eval x ≠ 0} := by
  ext x; simp [ofRational, domain]

/-- The absolute value as the algebraic expression `√(x²)` (the book's footnote in §5.3). -/
noncomputable def absX : AlgebraicExpr := root 2 (mul var var)

/-- `√(x²) = |x|` (§2.2, recalled in §5.3), so the absolute value is algebraic, with domain `ℝ`. -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem eval_absX (x : ℝ) : absX.eval x = |x| ∧ x ∈ absX.domain := by
  have hsq : 0 ≤ x * x := mul_self_nonneg x
  refine ⟨?_, ?_⟩
  · simp only [absX, eval]
    exact (principalRoot_unique two_ne_zero (Or.inr hsq) (Or.inr (abs_nonneg x))
      (by rw [sq_abs, sq])).symm
  · simp only [absX, domain, mem_inter_iff, mem_univ, mem_ofPred_eq, true_and]
    exact ⟨two_ne_zero, Or.inr hsq⟩

/-- The expression `√(2 - √(4x + 3))` of Example 5.3.1(2). -/
noncomputable def example_5_3_1_2 : AlgebraicExpr :=
  root 2 (sub (const 2) (root 2 (add (mul (const 4) var) (const 3))))

/-- Example 5.3.1(2): the natural domain of `g(x) = √(2 - √(4x + 3))` is `[-3/4, 1/4]`. -/
@[kb "stitzzeager2013" "Example 5.3.1, p. 411"]
theorem domain_example_5_3_1_2 : example_5_3_1_2.domain = Icc (-3 / 4) (1 / 4) := by
  ext x
  simp only [example_5_3_1_2, domain, eval, eval_sub, domain_sub, mem_inter_iff, mem_univ, mem_ofPred_eq,
    true_and, mem_Icc]
  have h2 : ¬ Odd 2 := by decide
  simp only [h2, false_or, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and]
  constructor
  · rintro ⟨h1, h2'⟩
    refine ⟨by linarith, ?_⟩
    have hr : principalRoot 2 (4 * x + 3) ≤ 2 := by linarith
    have hp := principalRoot_pow (n := 2) (x := 4 * x + 3) two_ne_zero (Or.inr h1)
    have hn := principalRoot_nonneg (n := 2) h1
    nlinarith
  · rintro ⟨h1, h2'⟩
    have h0 : 0 ≤ 4 * x + 3 := by linarith
    refine ⟨h0, ?_⟩
    have hp := principalRoot_pow (n := 2) (x := 4 * x + 3) two_ne_zero (Or.inr h0)
    have hn := principalRoot_nonneg (n := 2) h0
    nlinarith

end AlgebraicExpr

end UndergradKB.Precalculus
