import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm2
import UndergradKB.Combinatorics.AeqB.GosperForm
import UndergradKB.Combinatorics.AeqB.Hyper
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 5: course wrappers of results proved in this library (wave 3)
-/

open Finset Polynomial Filter
open UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.Course.AeqB.Ch05b

section

variable {K : Type*} [Field K] [CharZero K]

/-- CO-398. If `gcd (a(n), b(n+h)) = 1` for all `h ∈ ℕ`, any rational solution `f/g` (in lowest
terms) of `a(n) x(n+1) - b(n-1) x(n) = c(n)` is a polynomial. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.2.1, p. 86"]
theorem thm_5_2_1_gosper_rational_solution_is_polynomial (a b c f g : K[X])
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hfg : IsCoprime f g) (hg : g ≠ 0)
    (h : a * f.comp (X + 1) * g - b.comp (X - 1) * f * g.comp (X + 1)
      = c * g * g.comp (X + 1)) :
    g.natDegree = 0 ∧ ∃ p : K[X], f = p * g :=
  gosper_rational_solution_is_polynomial a b c f g hab hfg hg h

/-- CO-399. Hypergeometric solutions of `z_{n+1} - z_n = t_n` correspond to polynomial solutions
`x` of `a(n) x(n+1) - b(n-1) x(n) = c(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 87"]
theorem text_p87_isGosperSummable_iff_polynomial_solution {t : ℕ → K} {a b c : K[X]}
    (ht : IsHypergeometric t) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hrel : ∀ᶠ n : ℕ in atTop, (b * c).eval (n : K) * t (n + 1)
      = (a * c.comp (X + 1)).eval (n : K) * t n) :
    IsGosperSummable t ↔ ∃ x : K[X], a * x.comp (X + 1) - b.comp (X - 1) * x = c :=
  isGosperSummable_iff_polynomial_solution ht hb hc hab hrel

/-- CO-400. Gosper's algorithm: it finds the Gosper form of the term ratio, and returns a
hypergeometric antidifference when `t` is Gosper-summable, and the partial sum otherwise. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (outline), p. 87"]
theorem text_p87_gosper_algorithm {t : ℕ → K} (ht : IsHypergeometric t) :
    ∃ a b c : K[X], a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) ∧
      (∀ᶠ n : ℕ in atTop,
        (b * c).eval (n : K) * t (n + 1) = (a * c.comp (X + 1)).eval (n : K) * t n) ∧
      (IsGosperSummable t ↔ ∃ x, GosperEq a b c x) ∧
      (IsGosperSummable t →
        IsHypergeometric (gosperOutput t a b c) ∧
        ∀ᶠ n : ℕ in atTop, gosperOutput t a b c (n + 1) - gosperOutput t a b c n = t n) ∧
      (¬ IsGosperSummable t → gosperOutput t a b c = fun n => ∑ k ∈ Finset.range n, t k) :=
  gosper_algorithm ht

/-- CO-401. For nonzero `f` or `g`, `Res_n(f(n), g(n+α)) = 0` iff `f(n)` and `g(n+α)` have a
common factor; so `f(n)` and `g(n+h)` are coprime for all `h ∈ ℕ` iff the resultant never vanishes
at a nonnegative integer. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 89"]
theorem text_p89_resultant_shift {f g : K[X]} (hfg : f ≠ 0 ∨ g ≠ 0) :
    (∀ α : K, resultant f (g.comp (X + C α)) = 0 ↔ ¬ IsCoprime f (g.comp (X + C α))) ∧
    ((∀ h : ℕ, IsCoprime f (g.comp (X + C (h : K)))) ↔
      ∀ h : ℕ, resultant f (g.comp (X + C (h : K))) ≠ 0) :=
  ⟨fun α => resultant_shift_eq_zero_iff hfg α, forall_isCoprime_shift_iff hfg⟩

/-- CO-402. Step 2 of Gosper's algorithm: if the nonnegative integer zeros of the resultant are
among `hs 0, …, hs (N-1)`, the staged gcd cancellation yields `a, b, c` with `f b c = g a c(n+1)`
(up to the constant `Z`), `gcd (a, b(n+h)) = 1` for all `h`, and `c` monic. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 2), p. 90"]
theorem text_p90_gosper_step2_spec {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hs : ℕ → ℕ)
    (N : ℕ) (Z : K) (hZ : Z ≠ 0)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k) :
    C Z * f * ((gosperStage f g hs N).2 * gosperStep2C f g hs N)
      = g * ((C Z * (gosperStage f g hs N).1) * (gosperStep2C f g hs N).comp (X + 1)) ∧
    (∀ h : ℕ, IsCoprime (C Z * (gosperStage f g hs N).1)
      ((gosperStage f g hs N).2.comp (X + C (h : K)))) ∧
    (gosperStep2C f g hs N).Monic ∧ (g.Monic → (gosperStage f g hs N).2.Monic) :=
  gosper_step2_spec hf hg hs N Z hZ hS

/-- CO-403. In Step 2, `gcd (p_i(n), q_j(n+h)) = 1` for `k ≤ i, j ≤ N` and `h < h_{k+1}`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.3.1, p. 91"]
theorem prop_5_3_1_gosper_stage_coprime {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hs : ℕ → ℕ)
    (N : ℕ) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k)
    {k i j h : ℕ} (hkN : k ≤ N) (hki : k ≤ i) (hiN : i ≤ N) (hkj : k ≤ j) (hjN : j ≤ N)
    (hh : k < N → h < hs k) :
    IsCoprime (gosperStage f g hs i).1 ((gosperStage f g hs j).2.comp (X + C (h : K))) :=
  gosper_prop_5_3_1 hf hg hs N hmono hS hkN hki hiN hkj hjN hh

/-- CO-404. Every nonzero rational function `f/g` over a field of characteristic `0` has a Gosper
form `f (b c) = g (a c(n+1))` with `b, c` monic, `gcd (a, b(n+h)) = 1` for all `h`,
`gcd (a, c) = 1` and `gcd (b, c(n+1)) = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.3.1, p. 92"]
theorem thm_5_3_1_exists_gosper_form (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ a b c : K[X], a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      f * (b * c) = g * (a * c.comp (X + 1)) ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) :=
  exists_gosper_form f g hf hg

/-- CO-405. If two Gosper-type factorizations of the same rational function satisfy the gcd
conditions (one in canonical shape), then `c(n)` divides `C(n)`. -/
@[kb "petkovsekwilfzeilberger1996" "Lemma 5.3.1, p. 92"]
theorem lem_5_3_1_dvd_of_gosper_forms_eq {a b c a' b' c' : K[X]} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (ha : IsCoprime a c) (hb : IsCoprime b (c.comp (X + 1)))
    (hab' : ∀ h : ℕ, IsCoprime a' (b'.comp (X + C (h : K))))
    (h : a' * b * c * c'.comp (X + 1) = a * b' * c' * c.comp (X + 1)) : c ∣ c' :=
  dvd_of_gosper_forms_eq hc hc' ha hb hab' h

/-- CO-406. The canonical Gosper factorization is unique. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 5.3.1, p. 93"]
theorem cor_5_3_1_gosper_form_unique {a b c a' b' c' : K[X]} (hbm : b.Monic) (hcm : c.Monic)
    (hbm' : b'.Monic) (hcm' : c'.Monic)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) (hac : IsCoprime a c)
    (hbc : IsCoprime b (c.comp (X + 1)))
    (hab' : ∀ h : ℕ, IsCoprime a' (b'.comp (X + C (h : K)))) (hac' : IsCoprime a' c')
    (hbc' : IsCoprime b' (c'.comp (X + 1)))
    (h : a * c.comp (X + 1) * b' * c' = a' * c'.comp (X + 1) * b * c) :
    a = a' ∧ b = b' ∧ c = c' :=
  gosper_form_unique hbm hcm hbm' hcm' hab hac hbc hab' hac' hbc' h

/-- CO-407. Among all triples satisfying the Gosper-form relations, the Step 2 output has `c` of
least degree (it divides every other admissible `C₀`). -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 5.3.2, p. 93"]
theorem cor_5_3_2_gosper_step2_c_minimal {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hs : ℕ → ℕ)
    (N : ℕ) (Z : K) (hZ : Z ≠ 0) (hmono : StrictMono hs)
    (hS : ∀ k : ℕ, resultant f (g.comp (X + C (k : K))) = 0 → ∃ m < N, hs m = k)
    {A B C0 : K[X]} (hC0 : C0 ≠ 0) (hAB : ∀ h : ℕ, IsCoprime A (B.comp (X + C (h : K))))
    (h2 : C Z * f * (B * C0) = g * (A * C0.comp (X + 1))) :
    gosperStep2C f g hs N ∣ C0 ∧ (gosperStep2C f g hs N).natDegree ≤ C0.natDegree :=
  gosper_step2_c_minimal hf hg hs N Z hZ hmono hS hC0 hAB h2

/-- CO-408. If `v(n) = u(n-h)` for monic `u` of degree `d ≥ 1`, then `v` is monic of degree `d` and
`h = (u_{d-1} - v_{d-1})/d` from the subleading coefficients (equation 5.3.8). -/
@[kb "petkovsekwilfzeilberger1996" "text (5.3.8), p. 94"]
theorem text_p94_shift_eq_of_subleading {u v : K[X]} {d : ℕ} (hd : 1 ≤ d) (hu : u.Monic)
    (hdeg : u.natDegree = d) (h : K) (huv : v = u.comp (X + C (-h))) :
    v.Monic ∧ v.natDegree = d ∧ h = (u.coeff (d - 1) - v.coeff (d - 1)) / d :=
  shift_eq_of_subleading hd hu hdeg h huv

/-- CO-409. Degrees of a polynomial solution `x` of `a x(n+1) - b(n-1) x = c`: case 1 (leading
terms of `a` and `b` do not cancel) gives `deg c = deg x + max (deg a, deg b)`; case 2 (equal
degree and leading coefficient) gives `deg c + 1 = deg a + deg x` or an explicit value of `deg x`. -/
@[kb "petkovsekwilfzeilberger1996" "text, Cases 1, 2a, 2b, p. 94"]
theorem text_p94_solution_degree_cases {a b c x : K[X]} (ha : a ≠ 0) (hx : x ≠ 0)
    (h : a * x.comp (X + 1) - b.comp (X - 1) * x = c) :
    (b ≠ 0 → (a.natDegree ≠ b.natDegree ∨ a.leadingCoeff ≠ b.leadingCoeff) →
      c ≠ 0 ∧ c.natDegree = x.natDegree + max a.natDegree b.natDegree) ∧
    (a.natDegree = b.natDegree → a.leadingCoeff = b.leadingCoeff → 1 ≤ a.natDegree →
      c.natDegree + 1 = a.natDegree + x.natDegree ∨
        (x.natDegree : K) = ((b.comp (X - 1)).coeff (a.natDegree - 1) - a.coeff (a.natDegree - 1))
          / a.leadingCoeff) :=
  ⟨fun hb hne => natDegree_solution_case1 ha hb hx hne h,
    fun hdeg hlc hk => natDegree_solution_case2 ha hx hdeg hlc hk h⟩

/-- CO-410. Step 3 of Gosper's algorithm: the degree of a nonzero polynomial solution lies in the
candidate degree set and is at most the bound `d`; a solution exists iff the linear system for
coefficients of degree `≤ d` is solvable. -/
@[kb "petkovsekwilfzeilberger1996" "Gosper's Algorithm (Step 3.1), p. 96"]
theorem text_p96_gosper_step3 {a b c : K[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x : K[X], x ≠ 0 → GosperEq a b c x → x.natDegree ∈ gosperDegreeSet a b c) ∧
    (∀ x : K[X], x ≠ 0 → GosperEq a b c x → x.natDegree ≤ gosperDegreeBound a b c) ∧
    ((∃ x, x ≠ 0 ∧ GosperEq a b c x) ↔
      ∃ y : degreeLT K (gosperDegreeBound a b c + 1), (y : K[X]) ≠ 0 ∧
        ((gosperOpLT a b (gosperDegreeBound a b c) y :
          degreeLT K (gosperDegreeBound a b c + max a.natDegree b.natDegree + 1)) : K[X]) = c) :=
  ⟨fun _ hx h => natDegree_mem_gosperDegreeSet ha hb hx h,
    fun _ hx h => natDegree_le_gosperDegreeBound ha hb hx h,
    exists_solution_iff_linear_system ha hb⟩

/-- CO-411. The partial sum of `k!` is not a hypergeometric term plus a constant, i.e. `k!` is not
Gosper-summable. -/
@[kb "petkovsekwilfzeilberger1996" "Example 5.5.1, p. 96"]
theorem ex_5_5_1_not_isGosperSummable_factorial :
    ¬ IsGosperSummable (fun n : ℕ => (n.factorial : K)) :=
  not_isGosperSummable_factorial

/-- CO-412. Similarity of hypergeometric terms (their ratio is a rational function of `n`) is an
equivalence relation. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 5.6.1, p. 102"]
theorem def_5_6_1_isSimilar_equivalence : Equivalence (IsSimilar (K := K)) :=
  isSimilar_equivalence

/-- CO-413. For non-constant hypergeometric `s_n`, the difference `s_{n+1} - s_n` is hypergeometric
and similar to `s_n`. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.1, p. 102"]
theorem prop_5_6_1_isHypergeometric_sub_succ {s : ℕ → K} (hs : IsHypergeometric s)
    (hnc : ¬ ∀ᶠ n : ℕ in atTop, s (n + 1) = s n) :
    IsHypergeometric (fun n => s (n + 1) - s n) ∧ IsSimilar (fun n => s (n + 1) - s n) s :=
  isHypergeometric_sub_succ hs hnc

/-- CO-414. For hypergeometric `s, t` with `s + t` not eventually zero, `s + t` is hypergeometric
iff `s` and `t` are similar. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.2, p. 102"]
theorem prop_5_6_2_isHypergeometric_add_iff {s t : ℕ → K} (hs : IsHypergeometric s)
    (ht : IsHypergeometric t) (hst : ¬ ∀ᶠ n : ℕ in atTop, s n + t n = 0) :
    IsHypergeometric (fun n => s n + t n) ↔ IsSimilar s t :=
  isHypergeometric_add_iff hs ht hst

/-- CO-415. If a finite sum of hypergeometric terms is (eventually) zero, two of the terms are
similar. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.1, p. 103"]
theorem thm_5_6_1_exists_similar_of_sum_eq_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hne : s.Nonempty) (t : ι → ℕ → K) (ht : ∀ i ∈ s, IsHypergeometric (t i))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ IsSimilar (t i) (t j) :=
  exists_similar_of_sum_eq_zero s hne t ht hsum

/-- CO-416. A sum of finitely many hypergeometric terms can be rewritten as a sum of pairwise
dissimilar hypergeometric terms. -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 5.6.3, p. 103"]
theorem prop_5_6_3_exists_dissimilar_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (t : ι → ℕ → K) (ht : ∀ i ∈ s, IsHypergeometric (t i)) :
    ∃ (J : Finset ι) (u : ι → ℕ → K), J ⊆ s ∧ (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = ∑ j ∈ J, u j n :=
  exists_dissimilar_sum s t ht

/-- CO-417. Deciding rationality: from canonical factorizations of the term ratio and of `B/A`,
a hypergeometric `t_n` is similar to `1` (rational) iff `A` is monic and `a = b = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.2, p. 103"]
theorem thm_5_6_2_isRational_iff_canonical_forms {t : ℕ → K} {A B Z a b c : K[X]}
    (ht : IsHypergeometric t)
    (hBm : B.Monic) (hZm : Z.Monic) (hAB : ∀ h : ℕ, IsCoprime A (B.comp (X + C (h : K))))
    (hAZ : IsCoprime A Z) (hBZ : IsCoprime B (Z.comp (X + 1)))
    (hrel : ∀ᶠ n : ℕ in atTop,
      (B * Z).eval (n : K) * t (n + 1) = (A * Z.comp (X + 1)).eval (n : K) * t n)
    (hbm : b.Monic) (hcm : c.Monic) (hab : ∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K))))
    (hac : IsCoprime a c) (hbc : IsCoprime b (c.comp (X + 1)))
    (hcan : B * (b * c) = A * (a * c.comp (X + 1))) :
    IsSimilar t (fun _ => (1 : K)) ↔ A.Monic ∧ a = 1 ∧ b = 1 :=
  isRational_iff_canonical_forms ht hBm hZm hAB hAZ hBZ hrel hbm hcm hab hac hbc hcan

/-- CO-418. If Gosper's algorithm fails on `t_n`, the partial sum is not a fixed-length linear
combination of hypergeometric terms. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.6.3, p. 104"]
theorem thm_5_6_3_not_closed_form_of_not_isGosperSummable {t : ℕ → K} (ht : IsHypergeometric t)
    (hns : ¬ IsGosperSummable t) {m : ℕ} (s : Fin m → ℕ → K) (α : Fin m → K)
    (hs : ∀ i, IsHypergeometric (s i)) :
    ¬ ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range n, t k = ∑ i, α i * s i n :=
  not_closed_form_of_not_isGosperSummable ht hns s α hs

/-- CO-419. (partial) Extended Gosper algorithm: a finite sum of hypergeometric terms is rewritten
as a sum of pairwise dissimilar terms, Gosper's algorithm is applied to each, and the antidifferences
of the summable ones are hypergeometric (the algorithm itself is not formalized). -/
@[kb "petkovsekwilfzeilberger1996" "Extended Gosper's Algorithm, p. 105"]
theorem text_p105_extended_gosper {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℕ → K)
    (ht : ∀ i ∈ s, IsHypergeometric (t i)) :
    ∃ (J : Finset ι) (u : ι → ℕ → K), J ⊆ s ∧ (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = ∑ j ∈ J, u j n) ∧
      (∀ j ∈ J, IsGosperSummable (u j) → IsHypergeometric (gosperAntidiff (u j))) ∧
      ∀ᶠ n : ℕ in atTop, ∑ j ∈ J, gosperAntidiff (u j) (n + 1) - ∑ j ∈ J, gosperAntidiff (u j) n
        = ∑ i ∈ s, t i n :=
  extended_gosper s t ht

/-- CO-422. A sum recurrence of order one gives `f(n+1)/f(n) = -a₀/a₁`, so `f` is hypergeometric and
`f(n) = f(0) ∏_{j<n} (-a₀(j)/a₁(j))`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 113"]
theorem text_p113_order_one :
    (∀ (a₀ a₁ f : ℕ → K), (∀ n, a₁ n ≠ 0) → (∀ n, a₁ n * f (n + 1) + a₀ n * f n = 0) →
      ∀ n : ℕ, f n = f 0 * ∏ j ∈ Finset.range n, (-(a₀ j) / a₁ j)) ∧
    (∀ (a₀ a₁ : K[X]), a₀ ≠ 0 → a₁ ≠ 0 → ∀ f : ℕ → K, ¬ (∀ᶠ n : ℕ in atTop, f n = 0) →
      (∀ᶠ n : ℕ in atTop, a₁.eval (n : K) * f (n + 1) + a₀.eval (n : K) * f n = 0) →
      IsHypergeometric f ∧
        ∀ᶠ n : ℕ in atTop, f (n + 1) / f n = -(a₀.eval (n : K)) / a₁.eval (n : K)) :=
  ⟨fun a₀ a₁ f h₁ hf n => order_one_solution a₀ a₁ f h₁ hf n,
    fun a₀ a₁ h₀ h₁ f hf0 hf => isHypergeometric_of_order_one a₀ a₁ h₀ h₁ f hf0 hf⟩

end

/-- CO-049. The `s`-fold iterated partial sums of `C(2m,m)/4^m` have the closed form
`C(2n+2s,2s) C(2n,n) / (C(n+s,s) 4^n)`, proved by induction using Gosper's algorithm. -/
@[kb "petkovsekwilfzeilberger1996" "text (5.5.2), p. 99"]
theorem text_p99_iterCentral (s n : ℕ) :
    iterCentral s n = ((2 * n + 2 * s).choose (2 * s) : ℚ) * ((2 * n).choose n : ℚ)
      / (((n + s).choose s : ℚ) * 4 ^ n) :=
  iterCentral_eq s n

/-- CO-421. Summing a telescoped recurrence `∑_j a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` over `k`
(with finite supports) gives the `k`-free recurrence `∑_j a_j(n) f(n+j) = 0` for `f n = ∑_k F n k`. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.1.4), p. 113"]
theorem text_p113_finsum_recurrence {R : Type*} [Ring R] (J : ℕ) (a : ℕ → ℤ → R)
    (F G : ℤ → ℤ → R)
    (h : ∀ n k, ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = G n (k + 1) - G n k)
    (n : ℤ) (hF : ∀ j ≤ J, (Function.support (F (n + j))).Finite)
    (hG : (Function.support (G n)).Finite) :
    ∑ j ∈ Finset.range (J + 1), a j n * ∑ᶠ k, F (n + j) k = 0 :=
  finsum_recurrence J a F G h n hF hG

end UndergradKB.Combinatorics.Course.AeqB.Ch05b
