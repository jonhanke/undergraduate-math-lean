import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.SequenceRing
import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.SolutionSpace

/-!
# Recurrence operators: d'Alembertian sequences, bases of hypergeometric solutions,
factorization (Petkovsek–Wilf–Zeilberger, "A = B", §8.6, 8.7, 8.9, 8.10)
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace RecOp

/-! ### Basic facts on the action -/

/-- The action of an operator respects equality for large `n`. -/
theorem act_congr_eventually (L : RecOp K) {f g : ℕ → K} (h : ∀ᶠ n : ℕ in atTop, f n = g n) :
    ∀ᶠ n : ℕ in atTop, act L f n = act L g n := by
  have : ∀ᶠ n : ℕ in atTop, ∀ k ∈ L.support, f (n + k) = g (n + k) :=
    (Filter.eventually_all_finset _).2 fun k _ => (tendsto_add_atTop_nat k).eventually h
  filter_upwards [this] with n hn
  rw [act_def, act_def]
  exact Finset.sum_congr rfl fun k hk => by rw [hn k hk]

theorem act_one (y : ℕ → K) : act (1 : RecOp K) y = y := by
  have : (1 : RecOp K) = term 0 1 := rfl
  funext n
  rw [this, act_term]
  simp

theorem act_zero_seq (L : RecOp K) : act L (0 : ℕ → K) = 0 := by
  funext n
  simp [act_def]

/-- The first-order operator `p(n) N + q(n)`. -/
def firstOrder (p q : K[X]) : RecOp K := term 1 p + term 0 q

theorem act_firstOrder (p q : K[X]) (y : ℕ → K) (n : ℕ) :
    act (firstOrder p q) y n = p.eval (n : K) * y (n + 1) + q.eval (n : K) * y n := by
  rw [firstOrder, act_add, Pi.add_apply, act_term, act_term]
  simp

end RecOp

theorem IsHypergeometric.poly_mul {u : ℕ → K} (hu : IsHypergeometric u) {P : K[X]} (hP : P ≠ 0) :
    IsHypergeometric (fun n => P.eval (n : K) * u n) :=
  (show IsSimilar (fun n => P.eval (n : K) * u n) u from
    ⟨P, 1, hP, one_ne_zero, Eventually.of_forall fun n => by simp⟩).isHypergeometric hu

theorem IsHypergeometric.const_mul {u : ℕ → K} (hu : IsHypergeometric u) {c : K} (hc : c ≠ 0) :
    IsHypergeometric (fun n => c * u n) := by
  simpa using hu.poly_mul (P := C c) (by simpa using hc)

/-! ### CO-496: d'Alembertian sequences -/

/-- The sequence `a` is annihilated, for large `n`, by a product of `k` first-order operators
(with polynomial coefficients and nonzero leading coefficient); the operator applied first is
the one in the outer position of the recursion. -/
def IsChainAnnihilated : ℕ → (ℕ → K) → Prop
  | 0, a => ∀ᶠ n : ℕ in atTop, a n = 0
  | k + 1, a => ∃ p q : K[X], p ≠ 0 ∧
      IsChainAnnihilated k (fun n => p.eval (n : K) * a (n + 1) + q.eval (n : K) * a n)

theorem chain_congr : ∀ (k : ℕ) {a b : ℕ → K},
    (∀ᶠ n : ℕ in atTop, a n = b n) → IsChainAnnihilated k a → IsChainAnnihilated k b
  | 0, a, b, h, ha => by
    filter_upwards [h, ha] with n h1 h2
    rw [← h1, h2]
  | k + 1, a, b, h, ⟨p, q, hp, ha⟩ => by
    refine ⟨p, q, hp, chain_congr k ?_ ha⟩
    have h' : ∀ᶠ n : ℕ in atTop, a (n + 1) = b (n + 1) := (tendsto_add_atTop_nat 1).eventually h
    filter_upwards [h, h'] with n h1 h2
    rw [h1, h2]

/-- Multiplying a chain-annihilated sequence by a hypergeometric term keeps it chain-annihilated
(with the same number of factors): conjugating a first-order operator by a hypergeometric term
gives a first-order operator. -/
theorem IsChainAnnihilated.hyper_mul : ∀ (k : ℕ) {x u : ℕ → K}, IsChainAnnihilated k x →
    IsHypergeometric u → IsChainAnnihilated k (fun n => u n * x n)
  | 0, x, u, hx, _ => by
    filter_upwards [hx] with n h
    simp [h]
  | k + 1, x, u, ⟨p, q, hp, hx⟩, hu => by
    obtain ⟨-, P, Q, hP, hQ, hPQ⟩ := isHypergeometric_iff.1 hu
    refine ⟨p * Q, q * P, mul_ne_zero hp hQ, ?_⟩
    have h1 := IsChainAnnihilated.hyper_mul k hx (hu.poly_mul hP)
    refine chain_congr k ?_ h1
    filter_upwards [hPQ] with n e
    simp only [eval_mul]
    linear_combination (-(p.eval (n : K) * x (n + 1))) * e

/-- The (nested) definition: `a = h₁ Σ h₂ Σ ⋯ Σ h_k` with hypergeometric `h_i`, where `Σ x` is a
sequence `s` with `Δ s = x` (an indefinite sum). -/
@[kb "petkovsekwilfzeilberger1996" "text (d'Alembertian sequences), p. 167"]
inductive IsDAlembertian : (ℕ → K) → Prop
  | hyper {h : ℕ → K} : IsHypergeometric h → IsDAlembertian h
  | sum {x h s : ℕ → K} : IsDAlembertian x → IsHypergeometric h →
      (∀ᶠ n : ℕ in atTop, s (n + 1) - s n = x n) → IsDAlembertian (fun n => h n * s n)

/-- CO-496. A d'Alembertian sequence is annihilated by a product of first-order recurrence
operators (here with polynomial coefficients, `p ≠ 0`; clearing denominators this is the
book's rational coefficients). -/
theorem IsDAlembertian.exists_chain {a : ℕ → K} (ha : IsDAlembertian a) :
    ∃ k, IsChainAnnihilated k a := by
  induction ha with
  | hyper hh =>
    obtain ⟨-, p, q, hp, hq, h⟩ := hh
    exact ⟨1, p, q, hp, show ∀ᶠ n : ℕ in atTop, _ = 0 from h⟩
  | @sum x h s _ hh hs ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨-, P, Q, hP, hQ, hPQ⟩ := isHypergeometric_iff.1 hh
    refine ⟨k + 1, Q, -P, hQ, ?_⟩
    have := IsChainAnnihilated.hyper_mul k hk (hh.poly_mul hP)
    refine chain_congr k ?_ this
    filter_upwards [hPQ, hs] with n e1 e2
    simp only [eval_neg]
    rw [← e2]
    linear_combination (-(s (n + 1))) * e1

/-- CO-496. Equivalent operator form: a d'Alembertian sequence is annihilated (for large `n`) by a
product `L_k ⋯ L_1` of first-order operators `p_i(n) N + q_i(n)`, `p_i ≠ 0`, in the ring of
recurrence operators. -/
@[kb "petkovsekwilfzeilberger1996" "text (d'Alembertian sequences), p. 167"]
theorem IsDAlembertian.exists_firstOrder_product {a : ℕ → K} (ha : IsDAlembertian a) :
    ∃ ps : List (K[X] × K[X]), (∀ pq ∈ ps, pq.1 ≠ 0) ∧
      ∀ᶠ n : ℕ in atTop,
        RecOp.act (ps.map fun pq => RecOp.firstOrder pq.1 pq.2).prod a n = 0 := by
  obtain ⟨k, hk⟩ := ha.exists_chain
  clear ha
  induction k generalizing a with
  | zero =>
    refine ⟨[], by simp, ?_⟩
    simp only [List.map_nil, List.prod_nil, RecOp.act_one]
    exact hk
  | succ k ih =>
    obtain ⟨p, q, hp, hb⟩ := hk
    obtain ⟨ps, hps, hev⟩ := ih hb
    refine ⟨ps ++ [(p, q)], ?_, ?_⟩
    · intro pq hpq
      rcases List.mem_append.1 hpq with h | h
      · exact hps pq h
      · rw [List.mem_singleton.1 h]; exact hp
    · have e : RecOp.act (RecOp.firstOrder p q) a =
          fun n : ℕ => p.eval (n : K) * a (n + 1) + q.eval (n : K) * a n :=
        funext (RecOp.act_firstOrder p q a)
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, RecOp.act_mul, e]
      exact hev

/-! ### Dissimilar parts of a solution (for CO-476, CO-500) -/

/-- If a linear combination `∑ c_i h_i` of hypergeometric terms is killed by `L`, it can be
rewritten (for large `n`) as a sum of pairwise dissimilar hypergeometric terms, each of which
is killed by `L` (Proposition 5.6.3 and Theorem 8.7.1). -/
theorem exists_dissimilar_parts_kill (L : RecOp K) {r : ℕ} (c : Fin r → K) (h : Fin r → ℕ → K)
    (hh : ∀ i, IsHypergeometric (h i))
    (hL : ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => ∑ i, c i * h i m) n = 0) :
    ∃ (J : Finset (Fin r)) (u : Fin r → ℕ → K), (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in atTop, ∑ i, c i * h i n = ∑ j ∈ J, u j n) ∧
      ∀ j ∈ J, ∀ᶠ n : ℕ in atTop, RecOp.act L (u j) n = 0 := by
  classical
  set s : Finset (Fin r) := Finset.univ.filter (fun i => c i ≠ 0) with hs
  let t : Fin r → ℕ → K := fun i n => c i * h i n
  have ht : ∀ i ∈ s, IsHypergeometric (t i) := fun i hi =>
    (hh i).const_mul (Finset.mem_filter.1 hi).2
  obtain ⟨J, u, -, hJh, hJd, hJsum⟩ := exists_dissimilar_sum s t ht
  have hfs : ∀ n, ∑ i, c i * h i n = ∑ i ∈ s, t i n := by
    intro n
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hc : c i = 0 <;> simp [t, hc]
  have hev : ∀ᶠ n : ℕ in atTop, ∑ i, c i * h i n = ∑ j ∈ J, u j n :=
    hJsum.mono fun n hn => by rw [hfs n, hn]
  refine ⟨J, u, hJh, hJd, hev, ?_⟩
  have hLJ : ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => ∑ j ∈ J, u j m) n = 0 := by
    have := RecOp.act_congr_eventually L (f := fun m => ∑ i, c i * h i m)
      (g := fun m => ∑ j ∈ J, u j m) hev
    filter_upwards [this, hL] with n h1 h2
    rw [← h1]; exact h2
  exact RecOp.act_eq_zero_of_sum_dissimilar L J u hJh hJd hLJ

/-! ### CO-507: the right Euclidean algorithm -/

section Euclid

variable {F : Type*} [Field F] [MulSemiringAction (Multiplicative ℕ) F]

theorem skewOrder_lt_of_support {R : SkewPolynomial F} {n : ℕ} (hR : R ≠ 0)
    (h : ∀ k ∈ R.support, k < n) : skewOrder R < n := by
  have hne : R.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hR (SkewPolynomial.support_eq_empty.1 he)
  obtain ⟨j, hj⟩ := hne
  have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le j) (h j hj)
  exact (Finset.sup_lt_iff (by simpa using hpos)).2 h

theorem skew_gcrd_aux (m : ℕ) : ∀ L₁ L₂ : SkewPolynomial F, (L₂ = 0 ∨ skewOrder L₂ < m) →
    ∃ G A B : SkewPolynomial F, (∃ Q, L₁ = Q * G) ∧ (∃ Q, L₂ = Q * G) ∧ G = A * L₁ + B * L₂ := by
  induction m with
  | zero =>
    intro L₁ L₂ h
    have h0 : L₂ = 0 := h.resolve_right (by omega)
    exact ⟨L₁, 1, 0, ⟨1, by simp⟩, ⟨0, by simp [h0]⟩, by simp [h0]⟩
  | succ m ih =>
    intro L₁ L₂ h
    by_cases hL2 : L₂ = 0
    · exact ⟨L₁, 1, 0, ⟨1, by simp⟩, ⟨0, by simp [hL2]⟩, by simp [hL2]⟩
    · have hord : skewOrder L₂ < m + 1 := h.resolve_left hL2
      obtain ⟨Q, R, hQR, hRs⟩ := skew_right_division L₁ L₂ hL2
      have hR : R = 0 ∨ skewOrder R < m := by
        by_cases hR0 : R = 0
        · exact Or.inl hR0
        · exact Or.inr (by have := skewOrder_lt_of_support hR0 hRs; omega)
      obtain ⟨G, A, B, ⟨Q1, h1⟩, ⟨Q2, h2⟩, hG⟩ := ih L₂ R hR
      have hRe : R = L₁ - Q * L₂ := by rw [hQR]; abel
      refine ⟨G, B, A - B * Q, ⟨Q * Q1 + Q2, ?_⟩, ⟨Q1, h1⟩, ?_⟩
      · rw [hQR, add_mul, mul_assoc, ← h1, h2]
      · rw [hG, hRe]; noncomm_ring

/-- CO-507. The right-Euclidean algorithm: any two recurrence operators `L₁, L₂` (over a field
with the shift action) have a greatest common right divisor `G`: it right-divides both, and is a
left combination `G = A L₁ + B L₂`, so any common right divisor right-divides `G`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem skew_gcrd (L₁ L₂ : SkewPolynomial F) :
    ∃ G A B : SkewPolynomial F, (∃ Q, L₁ = Q * G) ∧ (∃ Q, L₂ = Q * G) ∧ G = A * L₁ + B * L₂ :=
  skew_gcrd_aux (skewOrder L₂ + 1) L₁ L₂ (Or.inr (Nat.lt_succ_self _))

/-- CO-507, book shape: greatest common right divisors of recurrence operators with rational
function coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem ratfunc_gcrd (L₁ L₂ : SkewPolynomial (RatFunc K)) :
    ∃ G A B : SkewPolynomial (RatFunc K), (∃ Q, L₁ = Q * G) ∧ (∃ Q, L₂ = Q * G) ∧
      G = A * L₁ + B * L₂ :=
  skew_gcrd L₁ L₂

end Euclid

namespace RecOp

/-! ### CO-509, CO-497: right factors and reduction of order -/

theorem act_of_factor (L L₁ M : RecOp K) (h : L = L₁ * M) (y : ℕ → K) :
    act L y = act L₁ (act M y) := by rw [h, act_mul]

/-- CO-509. If `L = L₁ (q N - p)` then every `y` with `q(n) y(n+1) = p(n) y(n)` (for large `n`;
for a hypergeometric `y` with ratio `p/q`) satisfies `L y = 0`.  This is the direction
"first-order right factor gives a hypergeometric solution" of the correspondence. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem solution_of_right_factor (L L₁ : RecOp K) (p q : K[X])
    (hL : L = L₁ * firstOrder q (-p)) (y : ℕ → K)
    (hy : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * y (n + 1) = p.eval (n : K) * y n) :
    ∀ᶠ n : ℕ in atTop, act L y n = 0 := by
  have h0 : ∀ᶠ n : ℕ in atTop, act (firstOrder q (-p)) y n = (0 : ℕ → K) n := by
    filter_upwards [hy] with n e
    rw [act_firstOrder]
    simp only [eval_neg, Pi.zero_apply]
    linear_combination e
  have := act_congr_eventually L₁ h0
  filter_upwards [this] with n hn
  rw [act_of_factor L L₁ _ hL, hn, act_zero_seq]
  rfl

/-- CO-509 (hypergeometric form). If `L = L₁ (q N - p)` with `p, q ≠ 0` and `y` is a
hypergeometric term with `q y(n+1) = p y(n)`, then `y` is a hypergeometric solution of `L y = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem hyper_solution_of_right_factor (L L₁ : RecOp K) (p q : K[X])
    (hL : L = L₁ * firstOrder q (-p)) (y : ℕ → K) (hy : IsHypergeometric y)
    (hr : ∀ᶠ n : ℕ in atTop, y (n + 1) / y n = p.eval (n : K) / q.eval (n : K))
    (hq : q ≠ 0) :
    IsHypergeometric y ∧ ∀ᶠ n : ℕ in atTop, act L y n = 0 := by
  refine ⟨hy, solution_of_right_factor L L₁ p q hL y ?_⟩
  filter_upwards [hr, hy.eventually_ne_zero, eventually_eval_ne_zero hq] with n e h1 h2
  rw [div_eq_div_iff h1 h2] at e
  linear_combination e

/-- CO-497. Reduction of order: if `L = L₁ M` and `y` solves `L y = 0`, then `z = M y` solves
`L₁ z = 0`; and conversely `L y = L₁ (M y)` for every `y`. -/
@[kb "petkovsekwilfzeilberger1996" "text (reduction of order), p. 167"]
theorem reduction_of_order (L L₁ M : RecOp K) (h : L = L₁ * M) (y : ℕ → K)
    (hy : ∀ᶠ n : ℕ in atTop, act L y n = 0) : ∀ᶠ n : ℕ in atTop, act L₁ (act M y) n = 0 := by
  rw [← act_of_factor L L₁ M h]; exact hy

/-- CO-497. Reduction of order along a hypergeometric solution `h` of `q N - p`: for
`y = h s`, `(q N - p) y (n) = q(n) h(n+1) (s(n+1) - s(n))`, so `L y = L₁ z` where `z` is
determined by the difference `Δ s` (to be closed up with Gosper's algorithm). -/
@[kb "petkovsekwilfzeilberger1996" "text (reduction of order), p. 167"]
theorem act_hyper_mul (L L₁ : RecOp K) (p q : K[X]) (hL : L = L₁ * firstOrder q (-p))
    (h : ℕ → K) (hh : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * h (n + 1) = p.eval (n : K) * h n)
    (s : ℕ → K) :
    ∀ᶠ n : ℕ in atTop, act L (fun m => h m * s m) n =
      act L₁ (fun m => q.eval (m : K) * h (m + 1) * (s (m + 1) - s m)) n := by
  have h0 : ∀ᶠ n : ℕ in atTop, act (firstOrder q (-p)) (fun m => h m * s m) n =
      q.eval (n : K) * h (n + 1) * (s (n + 1) - s n) := by
    filter_upwards [hh] with n e
    rw [act_firstOrder]
    simp only [eval_neg]
    linear_combination (s n) * e
  have := act_congr_eventually L₁ (h0.mono fun n hn => hn)
  filter_upwards [this] with n hn
  rw [act_of_factor L L₁ _ hL, hn]

/-! ### CO-504: inhomogeneous equations over the hypergeometric hull -/

/-- The operator `L_j = ∑ p_i (∏_{l<i} N s_l) N^i` of equation (8.9.3), for the shift ratio
`s(n) = f(n+1)/f(n)`, applied to `r`. -/
def conjOp (L : RecOp K) (s r : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ L.support, (L.coeff i).eval (n : K) * (∏ l ∈ Finset.range i, s (n + l)) * r (n + i)

theorem eventually_shift_prod {f s : ℕ → K}
    (hf : ∀ᶠ n : ℕ in atTop, f (n + 1) = s n * f n) (i : ℕ) :
    ∀ᶠ n : ℕ in atTop, f (n + i) = (∏ l ∈ Finset.range i, s (n + l)) * f n := by
  induction i with
  | zero => exact Eventually.of_forall fun n => by simp
  | succ i ih =>
    have h2 : ∀ᶠ n : ℕ in atTop, f (n + i + 1) = s (n + i) * f (n + i) :=
      (tendsto_add_atTop_nat i).eventually hf
    filter_upwards [ih, h2] with n a b
    rw [Finset.prod_range_succ, show n + (i + 1) = n + i + 1 from rfl, b, a]
    ring

/-- CO-504. Multiplying by `f` turns `L (r f)` into `L_j r`: if `f(n+1) = s(n) f(n)` for large
`n`, then `(L (r f))(n) = f(n) (L_j r)(n)`.  Hence `L a = f` for `a = r f` is equivalent to
`L_j r = 1` (for `f` eventually nonzero), the rational-solution problem (8.9.3). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 171"]
theorem act_mul_eq_conjOp (L : RecOp K) {f s : ℕ → K}
    (hf : ∀ᶠ n : ℕ in atTop, f (n + 1) = s n * f n) (r : ℕ → K) :
    ∀ᶠ n : ℕ in atTop, act L (fun m => r m * f m) n = f n * conjOp L s r n := by
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i ∈ L.support,
      f (n + i) = (∏ l ∈ Finset.range i, s (n + l)) * f n :=
    (Filter.eventually_all_finset _).2 fun i _ => eventually_shift_prod hf i
  filter_upwards [hall] with n hn
  rw [act_def, conjOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hn i hi]
  ring

/-- CO-504. Solving `L a = f_j` with `a = r f_j` (`f_j` eventually nonzero): `L a = f_j` holds iff
`L_j r = 1` for large `n`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 171"]
theorem act_mul_eq_self_iff (L : RecOp K) {f s : ℕ → K}
    (hf : ∀ᶠ n : ℕ in atTop, f (n + 1) = s n * f n) (hne : ∀ᶠ n : ℕ in atTop, f n ≠ 0)
    (r : ℕ → K) :
    (∀ᶠ n : ℕ in atTop, act L (fun m => r m * f m) n = f n) ↔
      ∀ᶠ n : ℕ in atTop, conjOp L s r n = 1 := by
  constructor <;> intro h <;>
    filter_upwards [h, act_mul_eq_conjOp L hf r, hne] with n h1 h2 h3
  · rw [h2] at h1
    exact mul_left_cancel₀ h3 (by rw [h1, mul_one])
  · rw [h2, h1, mul_one]

/-- CO-504. Superposition: if `L a_j = f_j` (for large `n`) for each `j` in a finite set, then
`L (∑ a_j + k) = ∑ f_j` for any `k` with `L k = 0` (a basis of `Ker L ∩ L(H_K)` supplying `k`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 171"]
theorem act_sum_particular {ι : Type*} (L : RecOp K) (s : Finset ι) (a f : ι → ℕ → K)
    (hs : ∀ j ∈ s, ∀ᶠ n : ℕ in atTop, act L (a j) n = f j n) (k : ℕ → K)
    (hk : ∀ᶠ n : ℕ in atTop, act L k n = 0) :
    ∀ᶠ n : ℕ in atTop, act L (fun m => ∑ j ∈ s, a j m + k m) n = ∑ j ∈ s, f j n := by
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j ∈ s, act L (a j) n = f j n :=
    (Filter.eventually_all_finset _).2 hs
  filter_upwards [hall, hk] with n h1 h2
  have e : (fun m => ∑ j ∈ s, a j m + k m) = (fun m => ∑ j ∈ s, a j m) + k := rfl
  rw [e, act_add_seq, Pi.add_apply, act_sum_seq, h2, add_zero]
  exact Finset.sum_congr rfl h1

/-! ### CO-511: the adjoint -/

/-- The operator `∑_{k ≤ d} c_k N^k`. -/
def ofCoeffs (d : ℕ) (c : ℕ → K[X]) : RecOp K := ∑ k ∈ Finset.range (d + 1), term k (c k)

theorem coeff_ofCoeffs (d : ℕ) (c : ℕ → K[X]) (j : ℕ) :
    (ofCoeffs d c).coeff j = if j ≤ d then c j else 0 := by
  induction d with
  | zero =>
    unfold ofCoeffs
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, SkewPolynomial.coeff_monomial]
    by_cases hj : j = 0
    · subst hj; simp
    · simp [Ne.symm hj, hj]
  | succ d ih =>
    have e : ofCoeffs (d + 1) c = ofCoeffs d c + term (d + 1) (c (d + 1)) := by
      unfold ofCoeffs; rw [Finset.sum_range_succ _ (d + 1)]
    rw [e, SkewPolynomial.coeff_add, ih, SkewPolynomial.coeff_monomial]
    by_cases h1 : j ≤ d
    · have : d + 1 ≠ j := by omega
      simp [h1, this, show j ≤ d + 1 by omega]
    · by_cases h2 : j = d + 1
      · subst h2; simp
      · have : ¬ j ≤ d + 1 := by omega
        simp [h1, Ne.symm h2, this]

theorem adjoint_eq_ofCoeffs (d : ℕ) (L : RecOp K) :
    adjoint d L = ofCoeffs d (fun k => (L.coeff (d - k)).comp (X + C (k : K))) := rfl

theorem eq_ofCoeffs_of_support (d : ℕ) (L : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d) :
    L = ofCoeffs d L.coeff := by
  unfold ofCoeffs
  have h1 : L = ∑ k ∈ L.support, term k (L.coeff k) :=
    (SkewPolynomial.sum_monomial L).symm.trans (SkewPolynomial.sum_def L _)
  conv_lhs => rw [h1]
  refine Finset.sum_subset (fun k hk => ?_) (fun k _ hk => ?_)
  · exact Finset.mem_range.2 (Nat.lt_succ_of_le (hL k hk))
  · rw [SkewPolynomial.notMem_support_iff.1 hk]; simp

theorem N_pow_eq (d : ℕ) : (N : RecOp K) ^ d = term d 1 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow_succ', ih]
    have h1 : (N : RecOp K) = term 1 1 := rfl
    rw [h1, term_mul_term]
    simp [add_comm]

/-- CO-511. The adjoint is an involution up to a shift: `L** = N^d L N^{-d}` for an operator `L`
of order at most `d`, here stated without `N^{-d}` as `L** N^d = N^d L`. -/
@[kb "petkovsekwilfzeilberger1996" "text (adjoint operator), p. 173"]
theorem adjoint_adjoint_mul (d : ℕ) (L : RecOp K) (hL : ∀ k ∈ L.support, k ≤ d) :
    adjoint d (adjoint d L) * N ^ d = N ^ d * L := by
  have hc : ∀ k ≤ d, ((adjoint d L).coeff (d - k)).comp (X + C (k : K)) =
      (L.coeff k).comp (X + C (d : K)) := by
    intro k hk
    rw [adjoint_eq_ofCoeffs, coeff_ofCoeffs, if_pos (Nat.sub_le d k), Nat.sub_sub_self hk,
      comp_shift_comp_shift]
    congr 3
    rw [← Nat.cast_add, Nat.sub_add_cancel hk]
  have hLL : adjoint d (adjoint d L) = ofCoeffs d (fun k => (L.coeff k).comp (X + C (d : K))) := by
    rw [adjoint_eq_ofCoeffs (L := adjoint d L)]
    unfold ofCoeffs
    refine Finset.sum_congr rfl fun k hk => ?_
    exact congrArg (term k) (hc k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  rw [hLL, N_pow_eq]
  conv_rhs => rw [eq_ofCoeffs_of_support d L hL]
  unfold ofCoeffs
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [term_mul_term, term_mul_term]
  simp [add_comm]

end RecOp

end UndergradKB.Combinatorics.AeqB

end
