import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# Hypergeometric terms and similarity (Petkovsek–Wilf–Zeilberger, "A = B", Sections 5.6, 8.2)

Sequences `ℕ → K` over a field `K` of characteristic zero, considered up to equality for all large
`n` (the book's "almost everywhere").  A hypergeometric term is a sequence that is not eventually
zero and satisfies `p(n) t(n+1) + q(n) t(n) = 0` for large `n`, for nonzero polynomials `p, q`.
Two terms are similar if their ratio is a rational function of `n`.
-/

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### Polynomials in `n` -/

/-- A nonzero polynomial does not vanish at all large natural numbers. -/
theorem eventually_eval_ne_zero {p : K[X]} (hp : p ≠ 0) :
    ∀ᶠ n : ℕ in atTop, p.eval (n : K) ≠ 0 := by
  classical
  have hfin : {n : ℕ | p.eval (n : K) = 0}.Finite := by
    refine (p.roots.toFinset.finite_toSet.preimage Nat.cast_injective.injOn).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp [Set.mem_preimage, Multiset.mem_toFinset, mem_roots hp, hn]
  rw [← Nat.cofinite_eq_atTop]
  exact hfin.eventually_cofinite_notMem

/-- A polynomial vanishing at all large natural numbers is zero. -/
theorem eq_zero_of_eventually_eval_eq_zero {p : K[X]}
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : K) = 0) : p = 0 := by
  by_contra hp
  obtain ⟨n, h1, h2⟩ := (h.and (eventually_eval_ne_zero hp)).exists
  exact h2 h1

/-! ### Hypergeometric terms -/

/-- CO-383. A sequence `t : ℕ → K` is hypergeometric if it is not eventually zero and there are
nonzero polynomials `p, q` with `p(n) t(n+1) + q(n) t(n) = 0` for all large `n`
(in the book's notation `p N t + q t = 0`, equality "almost everywhere"). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
def IsHypergeometric (t : ℕ → K) : Prop :=
  ¬ (∀ᶠ n : ℕ in atTop, t n = 0) ∧ ∃ p q : K[X], p ≠ 0 ∧ q ≠ 0 ∧
    ∀ᶠ n : ℕ in atTop, p.eval (n : K) * t (n + 1) + q.eval (n : K) * t n = 0

/-- Hypergeometric sequences are units, i.e. eventually nonzero (Corollary 8.2.1). -/
theorem IsHypergeometric.eventually_ne_zero {t : ℕ → K} (ht : IsHypergeometric t) :
    ∀ᶠ n : ℕ in atTop, t n ≠ 0 := by
  obtain ⟨hnz, p, q, hp, hq, h⟩ := ht
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((h.and (eventually_eval_ne_zero hp)).and (eventually_eval_ne_zero hq))
  by_contra hcon
  have : ∃ m ≥ N, t m = 0 := by
    by_contra hno
    push Not at hno
    exact hcon (eventually_atTop.2 ⟨N, fun n hn => hno n hn⟩)
  obtain ⟨m, hm, hm0⟩ := this
  apply hnz
  refine eventually_atTop.2 ⟨m, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base => exact hm0
  | succ n hn ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := hN n (hm.trans hn)
    rw [ih, mul_zero, add_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2

/-- CO-383 (equivalent form). A sequence is hypergeometric iff it is eventually nonzero and the
cross-multiplied ratio relation `q(n) t(n+1) = p(n) t(n)` holds for large `n`, for nonzero
polynomials `p, q`. -/
theorem isHypergeometric_iff {t : ℕ → K} :
    IsHypergeometric t ↔ (∀ᶠ n : ℕ in atTop, t n ≠ 0) ∧ ∃ p q : K[X], p ≠ 0 ∧ q ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, q.eval (n : K) * t (n + 1) = p.eval (n : K) * t n := by
  constructor
  · intro ht
    refine ⟨ht.eventually_ne_zero, ?_⟩
    obtain ⟨-, p, q, hp, hq, h⟩ := ht
    exact ⟨-q, p, neg_ne_zero.2 hq, hp, h.mono fun n e => by
      simp only [eval_neg]; linear_combination e⟩
  · rintro ⟨hnz, p, q, hp, hq, h⟩
    refine ⟨fun h0 => ?_, q, -p, hq, neg_ne_zero.2 hp, h.mono fun n e => by
      simp only [eval_neg]; linear_combination e⟩
    obtain ⟨n, h1, h2⟩ := (h0.and hnz).exists
    exact h2 h1

/-- CO-383 (ratio form). A sequence is hypergeometric iff it is eventually nonzero and its
consecutive ratio `t(n+1)/t(n)` is eventually a quotient `p(n)/q(n)` of nonzero polynomials. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.2.1, p. 158"]
theorem isHypergeometric_iff_ratio {t : ℕ → K} :
    IsHypergeometric t ↔ (∀ᶠ n : ℕ in atTop, t n ≠ 0) ∧ ∃ p q : K[X], p ≠ 0 ∧ q ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, t (n + 1) / t n = p.eval (n : K) / q.eval (n : K) := by
  rw [isHypergeometric_iff]
  constructor <;> rintro ⟨hnz, p, q, hp, hq, h⟩ <;> refine ⟨hnz, p, q, hp, hq, ?_⟩ <;>
    filter_upwards [h, hnz, eventually_eval_ne_zero hq] with n e h2 h3
  · rw [div_eq_div_iff h2 h3]; linear_combination e
  · rw [div_eq_div_iff h2 h3] at e; linear_combination e

/-! ### Similarity -/

/-- CO-412. Two sequences are similar if their ratio is a rational function of `n`:
`s(n)/t(n) = p(n)/q(n)` for large `n`, with `p, q` nonzero polynomials (written without
division). On hypergeometric terms this is Definition 5.6.1. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 5.6.1, p. 102"]
def IsSimilar (s t : ℕ → K) : Prop :=
  ∃ p q : K[X], p ≠ 0 ∧ q ≠ 0 ∧
    ∀ᶠ n : ℕ in atTop, q.eval (n : K) * s n = p.eval (n : K) * t n

/-- Similarity of a sequence to an eventually nonzero one means that the ratio is rational. -/
theorem isSimilar_iff_ratio {s t : ℕ → K} (ht : ∀ᶠ n : ℕ in atTop, t n ≠ 0) :
    IsSimilar s t ↔ ∃ p q : K[X], p ≠ 0 ∧ q ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, s n / t n = p.eval (n : K) / q.eval (n : K) := by
  constructor <;> rintro ⟨p, q, hp, hq, h⟩ <;> refine ⟨p, q, hp, hq, ?_⟩ <;>
    filter_upwards [h, ht, eventually_eval_ne_zero hq] with n e h2 h3
  · rw [div_eq_div_iff h2 h3]; linear_combination e
  · rw [div_eq_div_iff h2 h3] at e; linear_combination e

theorem IsSimilar.refl (s : ℕ → K) : IsSimilar s s :=
  ⟨1, 1, one_ne_zero, one_ne_zero, Eventually.of_forall fun n => by simp⟩

omit [CharZero K] in
theorem IsSimilar.symm{s t : ℕ → K} (h : IsSimilar s t) : IsSimilar t s := by
  obtain ⟨p, q, hp, hq, h⟩ := h
  exact ⟨q, p, hq, hp, h.mono fun n hn => hn.symm⟩

omit [CharZero K] in
theorem IsSimilar.trans{s t u : ℕ → K} (h : IsSimilar s t) (h' : IsSimilar t u) :
    IsSimilar s u := by
  obtain ⟨p₁, q₁, hp₁, hq₁, e₁⟩ := h
  obtain ⟨p₂, q₂, hp₂, hq₂, e₂⟩ := h'
  refine ⟨p₁ * p₂, q₁ * q₂, mul_ne_zero hp₁ hp₂, mul_ne_zero hq₁ hq₂, ?_⟩
  filter_upwards [e₁, e₂] with n a b
  simp only [eval_mul]
  linear_combination q₂.eval (n : K) * a + p₁.eval (n : K) * b

/-- CO-412. Similarity is an equivalence relation. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 5.6.1, p. 102"]
theorem isSimilar_equivalence : Equivalence (IsSimilar (K := K)) :=
  ⟨IsSimilar.refl, IsSimilar.symm, IsSimilar.trans⟩

/-- A sequence similar to a hypergeometric term is hypergeometric. -/
theorem IsSimilar.isHypergeometric {s t : ℕ → K} (hst : IsSimilar s t)
    (ht : IsHypergeometric t) : IsHypergeometric s := by
  have hte := ht.eventually_ne_zero
  obtain ⟨p, q, hp, hq, hrel⟩ := hst
  obtain ⟨-, P, Q, hP, hQ, hC⟩ := ht
  have hrel' : ∀ᶠ n : ℕ in atTop, q.eval ((n + 1 : ℕ) : K) * s (n + 1)
      = p.eval ((n + 1 : ℕ) : K) * t (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually hrel
  have hs0 : ∀ᶠ n : ℕ in atTop, s n ≠ 0 := by
    filter_upwards [hrel, hte, eventually_eval_ne_zero hp] with n e h1 h2 h0
    rw [h0, mul_zero] at e
    exact mul_ne_zero h2 h1 e.symm
  have hX : (X + 1 : K[X]) = X + C 1 := by simp
  have hcq : q.comp (X + 1) ≠ 0 := by rw [hX]; exact comp_X_add_C_ne_zero_iff.2 hq
  have hcp : p.comp (X + 1) ≠ 0 := by rw [hX]; exact comp_X_add_C_ne_zero_iff.2 hp
  refine ⟨fun h0 => ?_, P * (q.comp (X + 1)) * p, Q * q * p.comp (X + 1),
    mul_ne_zero (mul_ne_zero hP hcq) hp, mul_ne_zero (mul_ne_zero hQ hq) hcp, ?_⟩
  · obtain ⟨n, h1, h2⟩ := (h0.and hs0).exists
    exact h2 h1
  · filter_upwards [hrel, hrel', hC] with n A B C
    have e : ∀ r : K[X], (r.comp (X + 1)).eval (n : K) = r.eval ((n + 1 : ℕ) : K) := by
      intro r; simp [eval_comp]
    simp only [eval_mul, e]
    linear_combination (P.eval (n : K) * p.eval (n : K)) * B +
      (Q.eval (n : K) * p.eval ((n + 1 : ℕ) : K)) * A +
      (p.eval (n : K) * p.eval ((n + 1 : ℕ) : K)) * C

/-- Terms with equal consecutive ratio are similar (the ratio is a constant). -/
theorem isSimilar_of_ratio_eq {s t : ℕ → K} (hs : ∀ᶠ n : ℕ in atTop, s n ≠ 0)
    (ht : ∀ᶠ n : ℕ in atTop, t n ≠ 0)
    (h : ∀ᶠ n : ℕ in atTop, s (n + 1) * t n = s n * t (n + 1)) : IsSimilar s t := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hs.and ht).and h)
  have key : ∀ n, N ≤ n → s n * t N = s N * t n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      obtain ⟨⟨_, htn⟩, hW⟩ := hN n hn
      apply mul_left_cancel₀ htn
      linear_combination t N * hW + t (n + 1) * ih
  have hsN := (hN N le_rfl).1.1
  have htN := (hN N le_rfl).1.2
  refine ⟨C (s N), C (t N), by simpa using hsN, by simpa using htN, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [eval_C]
  linear_combination key n hn

/-! ### Propositions of Section 5.6 -/

/-- CO-413. If `s` is a hypergeometric term which is not eventually constant, then
`s(n+1) - s(n)` is a hypergeometric term similar to `s`.  (The book's "non-constant" is read as
"not eventually constant": in the book sequences are only considered for large `n`.) -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.1, p. 102"]
theorem isHypergeometric_sub_succ {s : ℕ → K} (hs : IsHypergeometric s)
    (hnc : ¬ ∀ᶠ n : ℕ in atTop, s (n + 1) = s n) :
    IsHypergeometric (fun n => s (n + 1) - s n) ∧ IsSimilar (fun n => s (n + 1) - s n) s := by
  obtain ⟨-, P, Q, hP, hQ, h⟩ := id hs
  have hne : P + Q ≠ 0 := by
    intro h0
    apply hnc
    filter_upwards [h, eventually_eval_ne_zero hP] with n e hP'
    have hq : P.eval (n : K) + Q.eval (n : K) = 0 := by
      simpa using congrArg (eval (n : K)) h0
    have : P.eval (n : K) * (s (n + 1) - s n) = 0 := by linear_combination e - s n * hq
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hP')
  have hsim : IsSimilar (fun n => s (n + 1) - s n) s :=
    ⟨-(P + Q), P, neg_ne_zero.2 hne, hP, h.mono fun n e => by
      simp only [eval_neg, eval_add]; linear_combination e⟩
  exact ⟨hsim.isHypergeometric hs, hsim⟩

/-- CO-414. For hypergeometric `s, t` with `s + t` not eventually zero, `s + t` is hypergeometric
iff `s` and `t` are similar. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.2, p. 102"]
theorem isHypergeometric_add_iff {s t : ℕ → K} (hs : IsHypergeometric s)
    (ht : IsHypergeometric t) (hst : ¬ ∀ᶠ n : ℕ in atTop, s n + t n = 0) :
    IsHypergeometric (fun n => s n + t n) ↔ IsSimilar s t := by
  constructor
  · intro hu
    have hs0 := hs.eventually_ne_zero
    have ht0 := ht.eventually_ne_zero
    obtain ⟨-, P1, Q1, hP1, hQ1, h1⟩ := hs
    obtain ⟨-, P2, Q2, hP2, hQ2, h2⟩ := ht
    obtain ⟨-, P3, Q3, hP3, hQ3, h3⟩ := hu
    set XP : K[X] := Q1 * P3 - Q3 * P1 with hXP
    set YP : K[X] := Q3 * P2 - Q2 * P3 with hYP
    have key : ∀ᶠ n : ℕ in atTop, XP.eval (n : K) * P2.eval (n : K) * s n
        = YP.eval (n : K) * P1.eval (n : K) * t n := by
      filter_upwards [h1, h2, h3] with n e1 e2 e3
      simp only [hXP, hYP, eval_mul, eval_sub]
      linear_combination (-(P1.eval (n : K) * P2.eval (n : K))) * e3 +
        (P2.eval (n : K) * P3.eval (n : K)) * e1 + (P1.eval (n : K) * P3.eval (n : K)) * e2
    by_cases hX0 : XP = 0
    · have hY0 : YP = 0 := by
        apply eq_zero_of_eventually_eval_eq_zero
        filter_upwards [key, ht0, eventually_eval_ne_zero hP1] with n k b c
        have : YP.eval (n : K) * P1.eval (n : K) * t n = 0 := by rw [← k, hX0]; simp
        exact ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right b)).resolve_right c)
      have hX0' : Q1 * P3 - Q3 * P1 = 0 := hX0
      have hY0' : Q3 * P2 - Q2 * P3 = 0 := hY0
      have h4 : (Q1 * P2 - Q2 * P1) * P3 = 0 := by linear_combination P2 * hX0' + P1 * hY0'
      have hQ : Q1 * P2 - Q2 * P1 = 0 := (mul_eq_zero.1 h4).resolve_right hP3
      have W : ∀ᶠ n : ℕ in atTop, s (n + 1) * t n = s n * t (n + 1) := by
        filter_upwards [h1, h2, hs0, ht0, eventually_eval_ne_zero hP1,
          eventually_eval_ne_zero hP2] with n e1 e2 a b c d
        have hq : Q1.eval (n : K) * P2.eval (n : K) = Q2.eval (n : K) * P1.eval (n : K) := by
          have := congrArg (eval (n : K)) hQ
          simp only [eval_sub, eval_mul, eval_zero] at this
          linear_combination this
        apply mul_left_cancel₀ (mul_ne_zero c d)
        linear_combination (P2.eval (n : K) * t n) * e1 - (P1.eval (n : K) * s n) * e2
          - (s n * t n) * hq
      exact isSimilar_of_ratio_eq hs0 ht0 W
    · have hY0 : YP ≠ 0 := by
        intro hY
        apply hX0
        apply eq_zero_of_eventually_eval_eq_zero
        filter_upwards [key, hs0, eventually_eval_ne_zero hP2] with n k a c
        have : XP.eval (n : K) * P2.eval (n : K) * s n = 0 := by rw [k, hY]; simp
        exact ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right a)).resolve_right c)
      refine ⟨YP * P1, XP * P2, mul_ne_zero hY0 hP1, mul_ne_zero hX0 hP2, ?_⟩
      filter_upwards [key] with n k
      simp only [eval_mul]
      exact k
  · intro hsim
    obtain ⟨p, q, hp, hq, h⟩ := hsim
    have hne : p + q ≠ 0 := by
      intro h0
      apply hst
      filter_upwards [h, eventually_eval_ne_zero hq] with n e hq'
      have hp0 : p.eval (n : K) + q.eval (n : K) = 0 := by
        simpa using congrArg (eval (n : K)) h0
      have : q.eval (n : K) * (s n + t n) = 0 := by linear_combination e + t n * hp0
      exact (mul_eq_zero.1 this).resolve_left hq'
    have hsim' : IsSimilar (fun n => s n + t n) s :=
      ⟨p + q, p, hne, hp, h.mono fun n e => by
        simp only [eval_add]; linear_combination (-1 : K) * e⟩
    exact hsim'.isHypergeometric hs

/-- For two hypergeometric terms whose consecutive ratios are not eventually equal, the term
`(r_a(n) - r_i(n)) t_i(n)` is similar to `t_i`, where `r_x(n) = t_x(n+1)/t_x(n)`. -/
theorem isSimilar_ratio_diff {ta ti : ℕ → K} (ha : IsHypergeometric ta)
    (hi : IsHypergeometric ti)
    (hne : ¬ ∀ᶠ n : ℕ in atTop, ta (n + 1) / ta n = ti (n + 1) / ti n) :
    IsSimilar (fun n => (ta (n + 1) / ta n - ti (n + 1) / ti n) * ti n) ti := by
  have ha0 := ha.eventually_ne_zero
  have hi0 := hi.eventually_ne_zero
  obtain ⟨-, Pa, Qa, hPa, hQa, ea⟩ := ha
  obtain ⟨-, Pi, Qi, hPi, hQi, ei⟩ := hi
  have hZ : Qi * Pa - Qa * Pi ≠ 0 := by
    intro hZ
    apply hne
    filter_upwards [ea, ei, ha0, hi0, eventually_eval_ne_zero hPa,
      eventually_eval_ne_zero hPi] with n a b c d e f
    have hz : Qi.eval (n : K) * Pa.eval (n : K) - Qa.eval (n : K) * Pi.eval (n : K) = 0 := by
      simpa using congrArg (eval (n : K)) hZ
    rw [div_eq_div_iff c d]
    apply mul_left_cancel₀ (mul_ne_zero e f)
    linear_combination (Pi.eval (n : K) * ti n) * a - (Pa.eval (n : K) * ta n) * b
      + (ta n * ti n) * hz
  refine ⟨Qi * Pa - Qa * Pi, Pa * Pi, hZ, mul_ne_zero hPa hPi, ?_⟩
  filter_upwards [ea, ei, ha0, hi0, eventually_eval_ne_zero hPa,
    eventually_eval_ne_zero hPi] with n a b c d e f
  have ra : ta (n + 1) / ta n = -(Qa.eval (n : K)) / Pa.eval (n : K) := by
    rw [div_eq_div_iff c e]; linear_combination a
  have ri : ti (n + 1) / ti n = -(Qi.eval (n : K)) / Pi.eval (n : K) := by
    rw [div_eq_div_iff d f]; linear_combination b
  simp only [eval_mul, eval_sub]
  rw [ra, ri]
  field_simp
  ring

/-- CO-415. If a (nonempty) finite sum of hypergeometric terms is zero (for large `n`), then two
of the terms, with different indices, are similar. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.1, p. 103"]
theorem exists_similar_of_sum_eq_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hne : s.Nonempty) (t : ι → ℕ → K) (ht : ∀ i ∈ s, IsHypergeometric (t i))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ IsSimilar (t i) (t j) := by
  induction s using Finset.induction_on generalizing t with
  | empty => exact absurd hne (by simp)
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · exfalso
      have hta := (ht a (by simp)).eventually_ne_zero
      obtain ⟨n, h1, h2⟩ := (hsum.and hta).exists
      simp at h1
      exact h2 h1
    · have hne_all : ∀ᶠ n : ℕ in atTop, ∀ i ∈ insert a s, t i n ≠ 0 :=
        (Filter.eventually_all_finset _).2 fun i hi => (ht i hi).eventually_ne_zero
      have hsum' : ∀ᶠ n : ℕ in atTop, ∑ i ∈ insert a s, t i (n + 1) = 0 :=
        (tendsto_add_atTop_nat 1).eventually hsum
      by_cases hcase : ∃ i ∈ s, ∀ᶠ n : ℕ in atTop, t a (n + 1) / t a n = t i (n + 1) / t i n
      · obtain ⟨i, hi, hr⟩ := hcase
        refine ⟨a, Finset.mem_insert_self _ _, i, Finset.mem_insert_of_mem hi,
          fun h => ha (h ▸ hi), ?_⟩
        refine isSimilar_of_ratio_eq (ht a (Finset.mem_insert_self _ _)).eventually_ne_zero
          (ht i (Finset.mem_insert_of_mem hi)).eventually_ne_zero ?_
        filter_upwards [hr, hne_all] with n e hn
        have h1 := hn a (Finset.mem_insert_self _ _)
        have h2 := hn i (Finset.mem_insert_of_mem hi)
        rw [div_eq_div_iff h1 h2] at e
        linear_combination e
      · have hcase' : ∀ i ∈ s, ¬ ∀ᶠ n : ℕ in atTop,
            t a (n + 1) / t a n = t i (n + 1) / t i n := fun i hi h => hcase ⟨i, hi, h⟩
        obtain ⟨u, hu_def⟩ : ∃ u : ι → ℕ → K, ∀ i n,
            u i n = (t a (n + 1) / t a n - t i (n + 1) / t i n) * t i n := ⟨_, fun _ _ => rfl⟩
        have hsim : ∀ i ∈ s, IsSimilar (u i) (t i) := by
          intro i hi
          have : u i = fun n => (t a (n + 1) / t a n - t i (n + 1) / t i n) * t i n :=
            funext (hu_def i)
          rw [this]
          exact isSimilar_ratio_diff (ht a (Finset.mem_insert_self _ _))
            (ht i (Finset.mem_insert_of_mem hi)) (hcase' i hi)
        have hu : ∀ i ∈ s, IsHypergeometric (u i) := fun i hi =>
          (hsim i hi).isHypergeometric (ht i (Finset.mem_insert_of_mem hi))
        have hsum_u : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, u i n = 0 := by
          filter_upwards [hsum, hsum', hne_all] with n h1 h2 hn
          have hr : ∀ i ∈ insert a s, t i (n + 1) / t i n * t i n = t i (n + 1) :=
            fun i hi => div_mul_cancel₀ _ (hn i hi)
          have hcalc : ∑ i ∈ insert a s, u i n = 0 := by
            calc ∑ i ∈ insert a s, u i n
                = t a (n + 1) / t a n * ∑ i ∈ insert a s, t i n
                  - ∑ i ∈ insert a s, t i (n + 1) / t i n * t i n := by
                  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                  exact Finset.sum_congr rfl fun i _ => by rw [hu_def]; ring
              _ = 0 := by rw [h1, Finset.sum_congr rfl hr, h2]; simp
          rw [Finset.sum_insert ha, hu_def, sub_self, zero_mul, zero_add] at hcalc
          exact hcalc
        obtain ⟨i, hi, j, hj, hij, hs_ij⟩ := ih hsne u hu hsum_u
        exact ⟨i, Finset.mem_insert_of_mem hi, j, Finset.mem_insert_of_mem hj, hij,
          ((hsim i hi).symm.trans hs_ij).trans (hsim j hj)⟩

/-- CO-416. Every sum of finitely many hypergeometric terms equals (for large `n`) a sum of
pairwise dissimilar hypergeometric terms, indexed by a subset `J` of the original index set
(so at most as many terms as before). -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.3, p. 103"]
theorem exists_dissimilar_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℕ → K)
    (ht : ∀ i ∈ s, IsHypergeometric (t i)) :
    ∃ (J : Finset ι) (u : ι → ℕ → K), J ⊆ s ∧ (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = ∑ j ∈ J, u j n := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, t, by simp, by simp, by simp, Eventually.of_forall fun n => by simp⟩
  | insert a s ha ih =>
    obtain ⟨J, u, hJs, hJh, hJd, hJsum⟩ := ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
    have hta := ht a (Finset.mem_insert_self a s)
    have haJ : a ∉ J := fun h => ha (hJs h)
    by_cases hcase : ∃ j ∈ J, IsSimilar (t a) (u j)
    · obtain ⟨j, hj, hsim⟩ := hcase
      have e : ∀ n : ℕ, ∑ x ∈ J, u x n = u j n + ∑ x ∈ J.erase j, u x n :=
        fun n => (Finset.add_sum_erase J (fun x => u x n) hj).symm
      by_cases hw : ∀ᶠ n : ℕ in atTop, u j n + t a n = 0
      · refine ⟨J.erase j, u,
          (Finset.erase_subset _ _).trans (hJs.trans (Finset.subset_insert _ _)),
          fun i hi => hJh i (Finset.mem_of_mem_erase hi),
          fun i hi k hk => hJd i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk), ?_⟩
        filter_upwards [hJsum, hw] with n h1 h2
        rw [Finset.sum_insert ha, h1, e n]
        linear_combination h2
      · obtain ⟨p, q, hp, hq, h⟩ := hsim
        have hne : p + q ≠ 0 := by
          intro h0
          apply hw
          filter_upwards [h, eventually_eval_ne_zero hq] with n en hq'
          have hp0 : p.eval (n : K) + q.eval (n : K) = 0 := by
            simpa using congrArg (eval (n : K)) h0
          have : q.eval (n : K) * (u j n + t a n) = 0 := by
            linear_combination en + u j n * hp0
          exact (mul_eq_zero.1 this).resolve_left hq'
        have hsim' : IsSimilar (fun n => u j n + t a n) (u j) :=
          ⟨p + q, q, hne, hq, h.mono fun n en => by
            simp only [eval_add]; linear_combination en⟩
        have hwh : IsHypergeometric (fun n => u j n + t a n) := hsim'.isHypergeometric (hJh j hj)
        refine ⟨J, Function.update u j (fun n => u j n + t a n),
          hJs.trans (Finset.subset_insert _ _), ?_, ?_, ?_⟩
        · intro i hi
          by_cases hij : i = j
          · subst hij; rw [Function.update_self]; exact hwh
          · rw [Function.update_of_ne hij]; exact hJh i hi
        · intro i hi k hk hik
          by_cases hij : i = j
          · subst hij
            have hkj : k ≠ i := fun h => hik h.symm
            rw [Function.update_self, Function.update_of_ne hkj]
            intro hs'
            exact hJd i hi k hk hik (hsim'.symm.trans hs')
          · by_cases hkj : k = j
            · subst hkj
              rw [Function.update_self, Function.update_of_ne hij]
              intro hs'
              exact hJd i hi k hk hik (hs'.trans hsim')
            · rw [Function.update_of_ne hij, Function.update_of_ne hkj]
              exact hJd i hi k hk hik
        · filter_upwards [hJsum] with n h1
          rw [Finset.sum_insert ha, h1, e n]
          have e2 : ∑ x ∈ J, Function.update u j (fun n => u j n + t a n) x n
              = (u j n + t a n) + ∑ x ∈ J.erase j, u x n := by
            rw [← Finset.add_sum_erase J _ hj, Function.update_self]
            congr 1
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
          rw [e2]; ring
    · have hcase' : ∀ j ∈ J, ¬ IsSimilar (t a) (u j) := fun j hj h => hcase ⟨j, hj, h⟩
      refine ⟨insert a J, Function.update u a (t a), Finset.insert_subset_insert a hJs, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hta
        · rw [Function.update_of_ne hia]
          exact hJh i ((Finset.mem_insert.1 hi).resolve_left hia)
      · intro i hi k hk hik
        by_cases hia : i = a
        · subst hia
          have hka : k ≠ i := fun h => hik h.symm
          rw [Function.update_self, Function.update_of_ne hka]
          exact hcase' k ((Finset.mem_insert.1 hk).resolve_left hka)
        · by_cases hka : k = a
          · subst hka
            rw [Function.update_self, Function.update_of_ne hia]
            intro hs'
            exact hcase' i ((Finset.mem_insert.1 hi).resolve_left hia) hs'.symm
          · rw [Function.update_of_ne hia, Function.update_of_ne hka]
            exact hJd i ((Finset.mem_insert.1 hi).resolve_left hia) k
              ((Finset.mem_insert.1 hk).resolve_left hka) hik
      · filter_upwards [hJsum] with n h1
        rw [Finset.sum_insert ha, Finset.sum_insert haJ, h1, Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Function.update_of_ne (fun h => haJ (by rwa [h] at hx))]

end UndergradKB.Combinatorics.AeqB
