import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-!
# WZ pairs and creative telescoping (Petkovsek–Wilf–Zeilberger, "A = B", Chapters 2, 6, 7)

Functions of two integer variables `F G : ℤ → ℤ → K`.  The WZ equation is
`F (n+1) k - F n k = G n (k+1) - G n k`.  Summing it over `k` and telescoping gives that
`∑_k F n k` does not depend on `n`, under finite support or limit hypotheses on `G`.
-/

namespace UndergradKB.Combinatorics.AeqB
open Filter Topology

section Telescoping

variable {E : Type*} [AddCommGroup E]

/-- Telescoping over an integer interval. -/
theorem sum_Ico_telescope (g : ℤ → E) {a b : ℤ} (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (g (j + 1) - g j) = g b - g a := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp), ih]; abel

/-- A finitely supported function on `ℤ` has telescoping sum `0` over all of `ℤ`. -/
theorem finsum_telescope {g : ℤ → E} (hg : (Function.support g).Finite) :
    ∑ᶠ k, (g (k + 1) - g k) = 0 := by
  have h1 : (Function.support fun k => g (k + 1)).Finite :=
    hg.preimage (Equiv.addRight (1 : ℤ)).injective.injOn
  rw [finsum_sub_distrib h1 hg]
  have := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := g)
  simp only [Equiv.coe_addRight] at this
  rw [this, sub_self]

/-- A function on `ℤ` that is invariant under `n ↦ n + 1` is constant. -/
theorem int_eq_of_succ_eq {α : Type*} {f : ℤ → α} (h : ∀ n, f (n + 1) = f n) (n m : ℤ) :
    f n = f m := by
  have key : ∀ n, f n = f 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [h, ih]
    | pred i ih =>
      have := h (-(i : ℤ) - 1)
      rw [sub_add_cancel] at this
      rw [← this]; exact ih
  rw [key n, key m]

/-- A function on `ℤ` with `f (n+1) = f n` for all `n ≥ 0` is constant on `n ≥ 0`. -/
theorem int_eq_of_succ_eq_of_nonneg {α : Type*} {f : ℤ → α} (h : ∀ n, 0 ≤ n → f (n + 1) = f n)
    (n : ℤ) (hn : 0 ≤ n) : f n = f 0 := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    have := h (k : ℤ) (by positivity)
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, this]
    exact ih (by positivity)

end Telescoping

/-! ### Definitions -/

section Defs

variable {K : Type*}

/-- CO-443. The WZ equation `F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` for all integers `n, k`
(equation (7.1.2) of the book). -/
def WZEq [Sub K] (F G : ℤ → ℤ → K) : Prop :=
  ∀ n k : ℤ, F (n + 1) k - F n k = G n (k + 1) - G n k

/-- A function of two integer variables is hypergeometric in both variables (polynomial model):
both consecutive-term ratios are given by quotients of polynomials in `(n, k)` with nonzero
denominator polynomial. -/
def IsHypergeometric₂ [CommRing K] (F : ℤ → ℤ → K) : Prop :=
  ∃ p₁ q₁ p₂ q₂ : MvPolynomial (Fin 2) K, q₁ ≠ 0 ∧ q₂ ≠ 0 ∧
    ∀ n k : ℤ,
      q₁.eval ![(n : K), (k : K)] * F (n + 1) k = p₁.eval ![(n : K), (k : K)] * F n k ∧
      q₂.eval ![(n : K), (k : K)] * F n (k + 1) = p₂.eval ![(n : K), (k : K)] * F n k

/-- CO-443. A WZ pair: a pair `(F, G)` of functions hypergeometric in `n` and `k` satisfying the
WZ equation. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (7.1.2), p. 132"]
structure IsWZPair [CommRing K] (F G : ℤ → ℤ → K) : Prop where
  hyper_left : IsHypergeometric₂ F
  hyper_right : IsHypergeometric₂ G
  eq : WZEq F G

end Defs

/-! ### Part 1: constancy of the sum -/

section Const

variable {E : Type*} [AddCommGroup E] {F G : ℤ → ℤ → E}

/-- One step of the WZ argument for finitely supported summands. -/
theorem WZEq.finsum_succ (h : WZEq F G) (n : ℤ) (hF : (Function.support (F n)).Finite)
    (hF' : (Function.support (F (n + 1))).Finite) (hG : (Function.support (G n)).Finite) :
    ∑ᶠ k, F (n + 1) k = ∑ᶠ k, F n k := by
  have h1 : ∑ᶠ k, (F (n + 1) k - F n k) = 0 := by
    have : (fun k => F (n + 1) k - F n k) = fun k => G n (k + 1) - G n k := funext (h n)
    rw [this]; exact finsum_telescope hG
  rw [finsum_sub_distrib hF' hF, sub_eq_zero] at h1
  exact h1

/-- CO-440. If `(F, G)` satisfy the WZ equation and, for each `n`, `F n ·` and `G n ·` have
finite support in `k`, then `∑_k F n k` is independent of `n`.  (The book's text assumes finite
support of the summand and telescopes the right side to `0`; for this one needs `G n ·` to be
finitely supported as well -- finite support of `F` alone does not suffice, e.g.
`F n k = n` at `k = -1`, `G n k = [k ≥ 0]`.) -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 36"]
theorem WZEq.finsum_const (h : WZEq F G) (hF : ∀ n, (Function.support (F n)).Finite)
    (hG : ∀ n, (Function.support (G n)).Finite) (n m : ℤ) :
    ∑ᶠ k, F n k = ∑ᶠ k, F m k :=
  int_eq_of_succ_eq (f := fun n => ∑ᶠ k, F n k)
    (fun n => h.finsum_succ n (hF n) (hF (n + 1)) (hG n)) n m

section Limit

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]

/-- One step of the proof of Theorem 7.1.1: sum the WZ equation over `-L ≤ k < L`, let `L → ∞`. -/
theorem WZEq.tsum_succ (h : WZEq F G) (n : ℤ) (hF : Summable (F n))
    (hF' : Summable (F (n + 1))) (hGt : Tendsto (G n) atTop (𝓝 0))
    (hGb : Tendsto (G n) atBot (𝓝 0)) :
    ∑' k, F (n + 1) k = ∑' k, F n k := by
  have hD : HasSum (fun k => F (n + 1) k - F n k) (∑' k, F (n + 1) k - ∑' k, F n k) :=
    hF'.hasSum.sub hF.hasSum
  have hlim : Tendsto (fun L : ℕ => ∑ k ∈ Finset.Ico (-(L : ℤ)) L, (F (n + 1) k - F n k)) atTop
      (𝓝 (∑' k, F (n + 1) k - ∑' k, F n k)) :=
    (show Tendsto (fun S : Finset ℤ => ∑ k ∈ S, (F (n + 1) k - F n k)) atTop _ from hD).comp
      Finset.tendsto_Ico_neg
  have hlim2 : Tendsto (fun L : ℕ => ∑ k ∈ Finset.Ico (-(L : ℤ)) L, (F (n + 1) k - F n k)) atTop
      (𝓝 0) := by
    have e : ∀ L : ℕ, ∑ k ∈ Finset.Ico (-(L : ℤ)) L, (F (n + 1) k - F n k)
        = G n L - G n (-(L : ℤ)) := by
      intro L
      have : ∀ k ∈ Finset.Ico (-(L : ℤ)) L, F (n + 1) k - F n k = G n (k + 1) - G n k :=
        fun k _ => h n k
      rw [Finset.sum_congr rfl this, sum_Ico_telescope (G n) (by omega)]
    simp_rw [e]
    have t1 : Tendsto (fun L : ℕ => G n (L : ℤ)) atTop (𝓝 0) :=
      hGt.comp tendsto_natCast_atTop_atTop
    have t2 : Tendsto (fun L : ℕ => G n (-(L : ℤ))) atTop (𝓝 0) :=
      hGb.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa using t1.sub t2
  have := tendsto_nhds_unique hlim hlim2
  exact sub_eq_zero.1 this

/-- CO-446. Wilf–Zeilberger theorem, first half (Theorem 7.1.1): if `(F, G)` satisfy the WZ
equation, `F n ·` is summable for `n ≥ 0`, and `G n k → 0` as `k → ±∞` for each `n ≥ 0`, then
`∑_k F n k` is independent of `n ≥ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 7.1.1, p. 134"]
theorem WZEq.tsum_const (h : WZEq F G) (hF : ∀ n, 0 ≤ n → Summable (F n))
    (hGt : ∀ n, 0 ≤ n → Tendsto (G n) atTop (𝓝 0))
    (hGb : ∀ n, 0 ≤ n → Tendsto (G n) atBot (𝓝 0)) (n : ℤ) (hn : 0 ≤ n) :
    ∑' k, F n k = ∑' k, F 0 k :=
  int_eq_of_succ_eq_of_nonneg (f := fun n => ∑' k, F n k)
    (fun n hn => h.tsum_succ n (hF n hn) (hF (n + 1) (by omega)) (hGt n hn) (hGb n hn)) n hn

/-- CO-447. Wilf–Zeilberger theorem, companion identity (second half of Theorem 7.1.1, (7.1.8)):
if `F n k → f k` as `n → ∞` for each `k`, the series `∑_{n ≥ 0} G n k` converge, and
`∑_{n ≥ 0} G n (-L) → 0` as `L → ∞`, then `∑_{n ≥ 0} G n k` is the limit, as `L → ∞`, of the
partial sums `∑_{-L ≤ j < k} (f j - F 0 j)`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 7.1.1, p. 134"]
theorem WZEq.companion (h : WZEq F G) (f : ℤ → E)
    (hF1 : ∀ k, Tendsto (fun n : ℕ => F n k) atTop (𝓝 (f k)))
    (hGs : ∀ k, Summable (fun n : ℕ => G n k))
    (hG2 : Tendsto (fun L : ℕ => ∑' n : ℕ, G n (-(L : ℤ))) atTop (𝓝 0)) (k : ℤ) :
    Tendsto (fun L : ℕ => ∑ j ∈ Finset.Ico (-(L : ℤ)) k, (f j - F 0 j)) atTop
      (𝓝 (∑' n : ℕ, G n k)) := by
  set g : ℤ → E := fun k => ∑' n : ℕ, G n k with hg
  -- the increment of `g`
  have step : ∀ j, g (j + 1) - g j = f j - F 0 j := by
    intro j
    have hS : HasSum (fun n : ℕ => G n (j + 1) - G n j) (g (j + 1) - g j) :=
      (hGs (j + 1)).hasSum.sub (hGs j).hasSum
    have t1 := hS.tendsto_sum_nat
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (G n (j + 1) - G n j) = F N j - F 0 j := by
      intro N
      have := Finset.sum_range_sub (fun i : ℕ => F (i : ℤ) j) N
      simp only [Nat.cast_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h (i : ℤ) j]; push_cast; rfl
    simp_rw [e] at t1
    have t2 : Tendsto (fun N : ℕ => F N j - F 0 j) atTop (𝓝 (f j - F 0 j)) :=
      (hF1 j).sub tendsto_const_nhds
    exact tendsto_nhds_unique t1 t2
  have t3 : Tendsto (fun L : ℕ => g k - g (-(L : ℤ))) atTop (𝓝 (g k - 0)) :=
    tendsto_const_nhds.sub hG2
  rw [sub_zero] at t3
  refine t3.congr' ?_
  filter_upwards [eventually_ge_atTop k.natAbs] with L hL
  have : ∀ j ∈ Finset.Ico (-(L : ℤ)) k, f j - F 0 j = g (j + 1) - g j :=
    fun j _ => (step j).symm
  rw [Finset.sum_congr rfl this, sum_Ico_telescope g (by omega)]

end Limit

end Const

/-! ### Creative telescoping: recurrences for the sum -/

section Recurrence

variable {R : Type*} [Ring R]

/-- CO-421. A telescoped recurrence `∑_{j ≤ J} a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` with the
`F (n+j) ·` and `G n ·` finitely supported gives the `k`-free recurrence
`∑_{j ≤ J} a_j(n) f(n+j) = 0` for `f n = ∑_k F n k`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 113"]
theorem finsum_recurrence (J : ℕ) (a : ℕ → ℤ → R) (F G : ℤ → ℤ → R)
    (h : ∀ n k, ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = G n (k + 1) - G n k)
    (n : ℤ) (hF : ∀ j ≤ J, (Function.support (F (n + j))).Finite)
    (hG : (Function.support (G n)).Finite) :
    ∑ j ∈ Finset.range (J + 1), a j n * ∑ᶠ k, F (n + j) k = 0 := by
  have h1 : ∑ᶠ k, ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = 0 := by
    have : (fun k => ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k)
        = fun k => G n (k + 1) - G n k := funext (h n)
    rw [this]; exact finsum_telescope hG
  rw [finsum_sum_comm _ _ (fun j hj => ?_)] at h1
  · rw [← h1]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mul_finsum' _ _ (hF j (by simpa [Nat.lt_succ_iff] using hj))]
  · refine (hF j (by simpa [Nat.lt_succ_iff] using hj)).subset ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h0; exact hk (by rw [h0, mul_zero])

/-- CO-432. Operator form with limits: if `∑_j a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)`, the series
`∑_k F(n+j,k)` converge, and `G n k → 0` as `k → ±∞`, then `a(n) = ∑_k F(n,k)` satisfies
`∑_j a_j(n) a(n+j) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 187"]
theorem tsum_recurrence [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (J : ℕ) (a : ℕ → ℤ → R) (F G : ℤ → ℤ → R)
    (h : ∀ n k, ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = G n (k + 1) - G n k)
    (n : ℤ) (hF : ∀ j ≤ J, Summable (F (n + j)))
    (hGt : Tendsto (G n) atTop (𝓝 0)) (hGb : Tendsto (G n) atBot (𝓝 0)) :
    ∑ j ∈ Finset.range (J + 1), a j n * ∑' k, F (n + j) k = 0 := by
  have hs : ∀ j ∈ Finset.range (J + 1), HasSum (fun k => a j n * F (n + j) k)
      (a j n * ∑' k, F (n + j) k) := fun j hj =>
    ((hF j (by simpa [Nat.lt_succ_iff] using hj)).hasSum).mul_left (a j n)
  have hD : HasSum (fun k => ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k)
      (∑ j ∈ Finset.range (J + 1), a j n * ∑' k, F (n + j) k) := hasSum_sum hs
  have hlim : Tendsto (fun L : ℕ => ∑ k ∈ Finset.Ico (-(L : ℤ)) L,
      ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k) atTop
      (𝓝 (∑ j ∈ Finset.range (J + 1), a j n * ∑' k, F (n + j) k)) :=
    (show Tendsto (fun S : Finset ℤ => ∑ k ∈ S, ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k)
      atTop _ from hD).comp Finset.tendsto_Ico_neg
  have hlim2 : Tendsto (fun L : ℕ => ∑ k ∈ Finset.Ico (-(L : ℤ)) L,
      ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k) atTop (𝓝 0) := by
    have e : ∀ L : ℕ, ∑ k ∈ Finset.Ico (-(L : ℤ)) L,
        ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = G n L - G n (-(L : ℤ)) := by
      intro L
      have : ∀ k ∈ Finset.Ico (-(L : ℤ)) L,
          ∑ j ∈ Finset.range (J + 1), a j n * F (n + j) k = G n (k + 1) - G n k :=
        fun k _ => h n k
      rw [Finset.sum_congr rfl this, sum_Ico_telescope (G n) (by omega)]
    simp_rw [e]
    have t1 : Tendsto (fun L : ℕ => G n (L : ℤ)) atTop (𝓝 0) :=
      hGt.comp tendsto_natCast_atTop_atTop
    have t2 : Tendsto (fun L : ℕ => G n (-(L : ℤ))) atTop (𝓝 0) :=
      hGb.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa using t1.sub t2
  exact tendsto_nhds_unique hlim hlim2

/-- CO-435. If `F n k = - F n (n + α - k)` for an integer `α` (the reflection `k ↦ n + α - k`
reverses the sign of the summand), then `∑_k F n k = 0`.  The proof needs no finiteness
assumption on the support, and works whenever `2 ≠ 0` in a ring without zero divisors. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 198"]
theorem finsum_eq_zero_of_reflect [NoZeroDivisors R] [CharZero R] (F : ℤ → ℤ → R) (α : ℤ)
    (h : ∀ n k, F n k = - F n (n + α - k)) (n : ℤ) : ∑ᶠ k, F n k = 0 := by
  have e := finsum_comp_equiv (Equiv.subLeft (n + α)) (f := F n)
  simp only [Equiv.subLeft_apply] at e
  have : ∑ᶠ k, F n k = - ∑ᶠ k, F n k := by
    calc ∑ᶠ k, F n k = ∑ᶠ k, -F n (n + α - k) := finsum_congr (fun k => h n k)
      _ = - ∑ᶠ k, F n (n + α - k) := finsum_neg_distrib _
      _ = - ∑ᶠ k, F n k := by rw [e]
  have h2 : (2 : R) * ∑ᶠ k, F n k = 0 := by
    rw [two_mul]; nth_rewrite 2 [this]; exact add_neg_cancel _
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

end Recurrence

/-! ### Symmetries of WZ pairs -/

section Symmetry

variable {K : Type*} [AddCommGroup K] {F G : ℤ → ℤ → K}

/-- CO-459. The map `(F(n,k), G(n,k)) ↦ (G(-k-1,-n), F(-k,-n-1))` sends WZ pairs to WZ pairs. -/
@[kb "petkovsekwilfzeilberger1996" "(7.3.7), p. 142"]
theorem WZEq.dual (h : WZEq F G) :
    WZEq (fun n k => G (-k - 1) (-n)) (fun n k => F (-k) (-n - 1)) := by
  intro n k
  have := h (-k - 1) (-n - 1)
  have e1 : -k - 1 + 1 = -k := by ring
  have e2 : -n - 1 + 1 = -n := by ring
  rw [e1, e2] at this
  have e5 : -(n + 1) = -n - 1 := by ring
  have e4 : -(k + 1) = -k - 1 := by ring
  simp only [e4, e5]
  linear_combination (norm := abel) this

/-- CO-465 (first sentence). Transposition: if `(F, G)` is a WZ pair then so is
`(G(k,n), F(k,n))`, i.e. `(fun n k => G k n, fun n k => F k n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 145"]
theorem WZEq.transpose (h : WZEq F G) : WZEq (fun n k => G k n) (fun n k => F k n) := by
  intro n k
  have := h k n
  simp only
  rw [eq_comm]
  exact this

/-- CO-465 (item 4). Shifts: `(F(n+α,k+β), G(n+α,k+β))` is a WZ pair. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 145"]
theorem WZEq.shift (h : WZEq F G) (α β : ℤ) :
    WZEq (fun n k => F (n + α) (k + β)) (fun n k => G (n + α) (k + β)) := by
  intro n k
  have := h (n + α) (k + β)
  have e1 : n + 1 + α = n + α + 1 := by ring
  have e2 : k + 1 + β = k + β + 1 := by ring
  simp only [e1, e2]
  exact this

/-- CO-465 (item 5, first part). `(F(-n,k), -G(-n-1,k))` is a WZ pair. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 145"]
theorem WZEq.neg_left (h : WZEq F G) :
    WZEq (fun n k => F (-n) k) (fun n k => -G (-n - 1) k) := by
  intro n k
  have := h (-n - 1) k
  have e1 : -n - 1 + 1 = -n := by ring
  have e2 : -(n + 1) = -n - 1 := by ring
  rw [e1] at this
  simp only [e2]
  linear_combination (norm := abel) -this

/-- CO-465 (item 5, second part). `(F(n,-k), -G(n,-k+1))` is a WZ pair. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 145"]
theorem WZEq.neg_right (h : WZEq F G) :
    WZEq (fun n k => F n (-k)) (fun n k => -G n (-k + 1)) := by
  intro n k
  have := h n (-k)
  have e : -(k + 1) + 1 = -k := by ring
  simp only [e]
  linear_combination (norm := abel) this

end Symmetry

end UndergradKB.Combinatorics.AeqB
