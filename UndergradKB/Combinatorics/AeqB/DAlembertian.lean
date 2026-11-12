import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.OperatorsMore
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm

/-!
# D'Alembertian sequences: converse, ring property, and closing up antidifferences with Gosper
(Petkovsek–Wilf–Zeilberger, "A = B", §8.6, p. 167)
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

universe u

variable {K : Type u} [Field K] [CharZero K]

/-! ### Small helpers -/

theorem ev_unshift {P : ℕ → Prop} (h : ∀ᶠ n : ℕ in atTop, P n) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ P (n - 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact eventually_atTop.2 ⟨N + 1, fun n hn => ⟨by omega, hN (n - 1) (by omega)⟩⟩

theorem eventually_const_of_diff_zero {f : ℕ → K}
    (h : ∀ᶠ n : ℕ in atTop, f (n + 1) - f n = 0) : ∃ c, ∀ᶠ n : ℕ in atTop, f n = c := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨f N, eventually_atTop.2 ⟨N, fun n hn => ?_⟩⟩
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have := hN n hn
    linear_combination this + ih

theorem isHypergeometric_one : IsHypergeometric (fun _ : ℕ => (1 : K)) :=
  isHypergeometric_iff.2 ⟨Eventually.of_forall fun _ => one_ne_zero, 1, 1, one_ne_zero,
    one_ne_zero, Eventually.of_forall fun n => by simp⟩

theorem isHypergeometric_poly {P : K[X]} (hP : P ≠ 0) :
    IsHypergeometric (fun n : ℕ => P.eval (n : K)) := by
  simpa using (isHypergeometric_one (K := K)).poly_mul hP

/-- Products of hypergeometric terms are hypergeometric. -/
theorem IsHypergeometric.mul_hyper {t u : ℕ → K} (ht : IsHypergeometric t)
    (hu : IsHypergeometric u) : IsHypergeometric (fun n => t n * u n) := by
  obtain ⟨h1, P, Q, hP, hQ, e1⟩ := isHypergeometric_iff.1 ht
  obtain ⟨h2, P', Q', hP', hQ', e2⟩ := isHypergeometric_iff.1 hu
  refine isHypergeometric_iff.2 ⟨?_, P * P', Q * Q', mul_ne_zero hP hP', mul_ne_zero hQ hQ', ?_⟩
  · filter_upwards [h1, h2] with n a b
    exact mul_ne_zero a b
  · filter_upwards [e1, e2] with n a b
    simp only [eval_mul]
    linear_combination (Q'.eval (n : K) * u (n + 1)) * a + (P.eval (n : K) * t n) * b

/-- Inverses of hypergeometric terms are hypergeometric. -/
theorem IsHypergeometric.inv_hyper {t : ℕ → K} (ht : IsHypergeometric t) :
    IsHypergeometric (fun n => (t n)⁻¹) := by
  obtain ⟨h1, P, Q, hP, hQ, e1⟩ := isHypergeometric_iff.1 ht
  refine isHypergeometric_iff.2 ⟨h1.mono fun n h => inv_ne_zero h, Q, P, hQ, hP, ?_⟩
  filter_upwards [e1, h1, (tendsto_add_atTop_nat 1).eventually h1] with n e a b
  field_simp
  first | linear_combination e | linear_combination -e

/-- The shift `n ↦ t(n+1)` of a hypergeometric term is hypergeometric. -/
theorem IsHypergeometric.shift_hyper {t : ℕ → K} (ht : IsHypergeometric t) :
    IsHypergeometric (fun n => t (n + 1)) := by
  obtain ⟨h1, P, Q, hP, hQ, e1⟩ := isHypergeometric_iff.1 ht
  refine isHypergeometric_iff.2 ⟨(tendsto_add_atTop_nat 1).eventually h1, P.comp (X + 1),
    Q.comp (X + 1), comp_X_add_one_ne_zero hP, comp_X_add_one_ne_zero hQ, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually e1] with n e
  simpa [eval_comp] using e

/-- The unshift `n ↦ t(n-1)` of a hypergeometric term is hypergeometric. -/
theorem IsHypergeometric.unshift_hyper {t : ℕ → K} (ht : IsHypergeometric t) :
    IsHypergeometric (fun n => t (n - 1)) := by
  obtain ⟨h1, P, Q, hP, hQ, e1⟩ := isHypergeometric_iff.1 ht
  refine isHypergeometric_iff.2 ⟨?_, P.comp (X - 1), Q.comp (X - 1), comp_X_sub_one_ne_zero hP,
    comp_X_sub_one_ne_zero hQ, ?_⟩
  · filter_upwards [ev_unshift h1] with n h
    exact h.2
  · filter_upwards [ev_unshift e1] with n h
    obtain ⟨hn, e⟩ := h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa [eval_comp] using e

/-- A hypergeometric term with prescribed (polynomial) ratio. -/
theorem exists_hyper_of_firstOrder_ratio {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ h : ℕ → K, IsHypergeometric h ∧
      ∀ᶠ n : ℕ in atTop, p.eval (n : K) * h (n + 1) + q.eval (n : K) * h n = 0 := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_eval_ne_zero hp).and (eventually_eval_ne_zero hq))
  let h : ℕ → K := fun n =>
    if n < N then 0 else ∏ i ∈ Finset.Ico N n, (-(q.eval (i : K) / p.eval (i : K)))
  have hstep : ∀ n, N ≤ n → h (n + 1) = (-(q.eval (n : K) / p.eval (n : K))) * h n := by
    intro n hn
    simp only [h, not_lt.2 hn, not_lt.2 (hn.trans (Nat.le_succ n)), ↓reduceIte]
    rw [Finset.prod_Ico_succ_top hn]
    ring
  have hne : ∀ n, N ≤ n → h n ≠ 0 := by
    intro n hn
    simp only [h, not_lt.2 hn, ↓reduceIte]
    refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
    have := hN i (Finset.mem_Ico.1 hi).1
    simp [this.1, this.2]
  have hrec : ∀ᶠ n : ℕ in atTop, p.eval (n : K) * h (n + 1) + q.eval (n : K) * h n = 0 := by
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have := (hN n hn).1
    rw [hstep n hn]
    field_simp
    ring
  refine ⟨h, isHypergeometric_iff.2 ⟨eventually_atTop.2 ⟨N, hne⟩, -q, p, neg_ne_zero.2 hq, hp,
    hrec.mono fun n e => ?_⟩, hrec⟩
  simp only [eval_neg]
  linear_combination e

/-! ### Chains of first-order operators -/

abbrev ChainAnn (k : ℕ) (a : ℕ → K) : Prop := IsChainAnnihilated k a

theorem chain_zero : ∀ k : ℕ, IsChainAnnihilated k (fun _ : ℕ => (0 : K))
  | 0 => Eventually.of_forall fun _ => rfl
  | k + 1 => ⟨1, 0, one_ne_zero,
      chain_congr k (Eventually.of_forall fun n => by simp) (chain_zero k)⟩

theorem chain_mono : ∀ (k : ℕ) {a : ℕ → K}, IsChainAnnihilated k a →
    IsChainAnnihilated (k + 1) a
  | 0, a, h => by
    have h0 : ∀ᶠ n : ℕ in atTop, a n = 0 := h
    have h1 : ∀ᶠ n : ℕ in atTop, a (n + 1) = 0 := (tendsto_add_atTop_nat 1).eventually h0
    refine ⟨1, 0, one_ne_zero, ?_⟩
    show ∀ᶠ n : ℕ in atTop, (1 : K[X]).eval (n : K) * a (n + 1) + (0 : K[X]).eval (n : K) * a n = 0
    filter_upwards [h1] with n e
    simp [e]
  | k + 1, a, ⟨p, q, hp, h⟩ => ⟨p, q, hp, chain_mono k h⟩

theorem chain_poly_mul (k : ℕ) {a : ℕ → K} (ha : IsChainAnnihilated k a) (P : K[X]) :
    IsChainAnnihilated k (fun n => P.eval (n : K) * a n) := by
  by_cases hP : P = 0
  · subst hP
    exact chain_congr k (Eventually.of_forall fun n => by simp) (chain_zero k)
  · exact IsChainAnnihilated.hyper_mul k ha (isHypergeometric_poly hP)

theorem chain_ratmul (k : ℕ) {a : ℕ → K} (ha : IsChainAnnihilated k a) (α p : K[X])
    (hp : p ≠ 0) :
    IsChainAnnihilated k (fun n => α.eval (n : K) / p.eval (n : K) * a n) := by
  by_cases hα : α = 0
  · subst hα
    exact chain_congr k (Eventually.of_forall fun n => by simp) (chain_zero k)
  · have hu : IsHypergeometric (fun n : ℕ => α.eval (n : K) / p.eval (n : K)) := by
      refine IsSimilar.isHypergeometric ⟨α, p, hα, hp, ?_⟩ isHypergeometric_one
      filter_upwards [eventually_eval_ne_zero hp] with n h
      field_simp
    exact IsChainAnnihilated.hyper_mul k ha hu

/-- The shift `p(n) ↦ p(n+1)` of a polynomial. -/
def shP (p : K[X]) : K[X] := p.comp (X + 1)

theorem eval_shP (p : K[X]) (n : ℕ) : (shP p).eval (n : K) = p.eval ((n + 1 : ℕ) : K) := by
  simp [shP, eval_comp]

/-- The class of chain-annihilated sequences is stable under applying any first-order operator
(Ore condition: `K' K = K̃ L₁` for first-order `K, L₁`). -/
theorem chain_firstOrder : ∀ (k : ℕ) (α β : K[X]) {b : ℕ → K}, IsChainAnnihilated k b →
    IsChainAnnihilated k (fun n => α.eval (n : K) * b (n + 1) + β.eval (n : K) * b n)
  | 0, α, β, b, hb => by
    have hb0 : ∀ᶠ n : ℕ in atTop, b n = 0 := hb
    have h1 : ∀ᶠ n : ℕ in atTop, b (n + 1) = 0 := (tendsto_add_atTop_nat 1).eventually hb0
    show ∀ᶠ n : ℕ in atTop, α.eval (n : K) * b (n + 1) + β.eval (n : K) * b n = 0
    filter_upwards [hb0, h1] with n e1 e2
    rw [e1, e2]
    simp
  | k + 1, α, β, b, ⟨p, q, hp, hb⟩ => by
    by_cases hD : q * α - β * p = 0
    · have hz : ∀ n : ℕ, p.eval (n : K) * (α.eval (n : K) * b (n + 1) + β.eval (n : K) * b n) =
          α.eval (n : K) * (p.eval (n : K) * b (n + 1) + q.eval (n : K) * b n) := by
        intro n
        have := congrArg (eval (n : K)) hD
        simp only [eval_sub, eval_mul, eval_zero] at this
        linear_combination (-(b n)) * this
      refine chain_mono k (chain_congr k ?_ (chain_ratmul k hb α p hp))
      filter_upwards [eventually_eval_ne_zero hp] with n hn
      rw [div_mul_eq_mul_div, div_eq_iff hn]
      linear_combination -(hz n)
    · obtain ⟨D, hDdef⟩ : ∃ D : K[X], D = q * α - β * p := ⟨_, rfl⟩
      have hDe : ∀ x : K, D.eval x = q.eval x * α.eval x - β.eval x * p.eval x := by
        intro x
        rw [hDdef]
        simp
      have hD' : D ≠ 0 := by rw [hDdef]; exact hD
      refine ⟨D * shP p, q * shP D, mul_ne_zero hD' (comp_X_add_one_ne_zero hp), ?_⟩
      refine chain_congr k ?_ (chain_firstOrder k (D * shP α) (β * shP D) hb)
      refine Eventually.of_forall fun n => ?_
      beta_reduce
      simp only [eval_mul, eval_shP, hDe]
      ring

theorem chain_add : ∀ (j : ℕ) {a b : ℕ → K} (k : ℕ), IsChainAnnihilated j a →
    IsChainAnnihilated k b → IsChainAnnihilated (j + k) (fun n => a n + b n)
  | 0, a, b, k, ha, hb => by
    rw [Nat.zero_add]
    refine chain_congr k ?_ hb
    have ha0 : ∀ᶠ n : ℕ in atTop, a n = 0 := ha
    filter_upwards [ha0] with n e
    simp [e]
  | j + 1, a, b, k, ⟨p, q, hp, ha⟩, hb => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    refine ⟨p, q, hp, ?_⟩
    refine chain_congr (j + k) ?_ (chain_add j k ha (chain_firstOrder k p q hb))
    exact Eventually.of_forall fun n => by simp only []; ring

theorem chain_mul_exists : ∀ (s j k : ℕ), j + k ≤ s →
    ∃ m : ℕ, ∀ a b : ℕ → K, IsChainAnnihilated j a → IsChainAnnihilated k b →
      IsChainAnnihilated m (fun n => a n * b n) := by
  intro s
  induction s with
  | zero =>
    intro j k h
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ k = 0 := by omega
    refine ⟨0, fun a b ha _ => ?_⟩
    have ha0 : ∀ᶠ n : ℕ in atTop, a n = 0 := ha
    show ∀ᶠ n : ℕ in atTop, a n * b n = 0
    filter_upwards [ha0] with n e
    simp [e]
  | succ s ih =>
    intro j k hjk
    rcases j with _ | j
    · refine ⟨0, fun a b ha _ => ?_⟩
      have ha0 : ∀ᶠ n : ℕ in atTop, a n = 0 := ha
      show ∀ᶠ n : ℕ in atTop, a n * b n = 0
      filter_upwards [ha0] with n e
      simp [e]
    rcases k with _ | k
    · refine ⟨0, fun a b _ hb => ?_⟩
      have hb0 : ∀ᶠ n : ℕ in atTop, b n = 0 := hb
      show ∀ᶠ n : ℕ in atTop, a n * b n = 0
      filter_upwards [hb0] with n e
      simp [e]
    obtain ⟨m1, h1⟩ := ih j k (by omega)
    obtain ⟨m2, h2⟩ := ih j (k + 1) (by omega)
    obtain ⟨m3, h3⟩ := ih (j + 1) k (by omega)
    refine ⟨m1 + m2 + m3 + 1, fun a b ha hb => ?_⟩
    have ha1 := ha
    have hb1 := hb
    obtain ⟨p, q, hp, ha'⟩ := ha
    obtain ⟨p', q', hp', hb'⟩ := hb
    have e1 := h1 _ _ ha' hb'
    have e2 := chain_poly_mul m2 (h2 _ b ha' hb1) (-q')
    have e3 := chain_poly_mul m3 (h3 a _ ha1 hb') (-q)
    have hsum := chain_add (m1 + m2) m3 (chain_add m1 m2 e1 e2) e3
    refine ⟨p * p', -(q * q'), mul_ne_zero hp hp', ?_⟩
    refine chain_congr (m1 + m2 + m3) ?_ hsum
    exact Eventually.of_forall fun n => by
      simp only [eval_mul, eval_neg]
      ring

/-! ### CO-496: the converse and the ring property -/

/-- A sequence is d'Alembertian up to finitely many terms (and the zero sequence): it is
eventually zero, or eventually equal to a d'Alembertian sequence. -/
def IsDAlembertianEv (a : ℕ → K) : Prop :=
  (∀ᶠ n : ℕ in atTop, a n = 0) ∨ ∃ d, IsDAlembertian d ∧ ∀ᶠ n : ℕ in atTop, a n = d n

theorem IsDAlembertianEv.congr {a b : ℕ → K} (h : ∀ᶠ n : ℕ in atTop, a n = b n)
    (hb : IsDAlembertianEv b) : IsDAlembertianEv a := by
  rcases hb with hb | ⟨d, hd, hbd⟩
  · exact Or.inl (by filter_upwards [h, hb] with n e1 e2; rw [e1, e2])
  · exact Or.inr ⟨d, hd, by filter_upwards [h, hbd] with n e1 e2; rw [e1, e2]⟩

theorem IsDAlembertian.hyper_mul {d u : ℕ → K} (hd : IsDAlembertian d)
    (hu : IsHypergeometric u) : IsDAlembertian (fun n => u n * d n) := by
  induction hd with
  | hyper hh => exact IsDAlembertian.hyper (hu.mul_hyper hh)
  | @sum x h s hx hh hs ih =>
    have e : (fun n => u n * (h n * s n)) = fun n => (u n * h n) * s n :=
      funext fun n => (mul_assoc _ _ _).symm
    rw [e]
    exact IsDAlembertian.sum hx (hu.mul_hyper hh) hs

theorem IsDAlembertian.unshift {d : ℕ → K} (hd : IsDAlembertian d) :
    IsDAlembertian (fun n => d (n - 1)) := by
  induction hd with
  | hyper hh => exact IsDAlembertian.hyper hh.unshift_hyper
  | @sum x h s hx hh hs ih =>
    refine IsDAlembertian.sum (x := fun n => x (n - 1)) (h := fun n => h (n - 1))
      (s := fun n => s (n - 1)) ih hh.unshift_hyper ?_
    filter_upwards [ev_unshift hs] with n hn
    obtain ⟨hn, e⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa using e

theorem IsDAlembertianEv.hyper_mul {a u : ℕ → K} (ha : IsDAlembertianEv a)
    (hu : IsHypergeometric u) : IsDAlembertianEv (fun n => u n * a n) := by
  rcases ha with ha | ⟨d, hd, had⟩
  · exact Or.inl (by filter_upwards [ha] with n e; rw [e, mul_zero])
  · exact Or.inr ⟨_, hd.hyper_mul hu, by filter_upwards [had] with n e; rw [e]⟩

theorem IsDAlembertianEv.unshift {a : ℕ → K} (ha : IsDAlembertianEv a) :
    IsDAlembertianEv (fun n => a (n - 1)) := by
  rcases ha with ha | ⟨d, hd, had⟩
  · exact Or.inl (by filter_upwards [ev_unshift ha] with n e; exact e.2)
  · exact Or.inr ⟨_, hd.unshift, by filter_upwards [ev_unshift had] with n e; exact e.2⟩

/-- The recursive step of the definition, for sequences d'Alembertian up to finitely many terms:
if `x` is, `h` is hypergeometric and `Δ s = x` for large `n`, then `h s` is. -/
theorem IsDAlembertianEv.sum_hyper {x h s : ℕ → K} (hx : IsDAlembertianEv x)
    (hh : IsHypergeometric h) (hs : ∀ᶠ n : ℕ in atTop, s (n + 1) - s n = x n) :
    IsDAlembertianEv (fun n => h n * s n) := by
  rcases hx with hx | ⟨d, hd, hxd⟩
  · obtain ⟨c, hc⟩ := eventually_const_of_diff_zero
      (show ∀ᶠ n : ℕ in atTop, s (n + 1) - s n = 0 by
        filter_upwards [hs, hx] with n e1 e2; rw [e1, e2])
    by_cases hc0 : c = 0
    · exact Or.inl (by filter_upwards [hc] with n e; rw [e, hc0, mul_zero])
    · exact Or.inr ⟨_, IsDAlembertian.hyper (hh.const_mul hc0), by
        filter_upwards [hc] with n e; rw [e]; ring⟩
  · exact Or.inr ⟨_, IsDAlembertian.sum hd hh (by
      filter_upwards [hs, hxd] with n e1 e2; rw [e1, e2]), Eventually.of_forall fun _ => rfl⟩

/-- CO-496 (converse of `IsDAlembertian.exists_chain`). A sequence annihilated (for large `n`) by a
product of `k` first-order operators with polynomial coefficients, nonzero leading coefficients,
is d'Alembertian up to finitely many terms (or eventually zero; the zero sequence and finite
modifications are excluded from `IsDAlembertian`, which asks for an exact nested-sum form). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem isDAlembertianEv_of_chain : ∀ (k : ℕ) {a : ℕ → K}, IsChainAnnihilated k a →
    IsDAlembertianEv a
  | 0, a, ha => Or.inl ha
  | k + 1, a, ⟨p, q, hp, hb⟩ => by
    have ihb := isDAlembertianEv_of_chain k hb
    by_cases hq : q = 0
    · subst hq
      have hu : IsHypergeometric (fun n : ℕ => (p.eval (n : K))⁻¹) :=
        (isHypergeometric_poly hp).inv_hyper
      have hunsh := (ihb.hyper_mul hu).unshift
      refine hunsh.congr ?_
      filter_upwards [ev_unshift (eventually_eval_ne_zero hp)] with n hn
      obtain ⟨h1, hpn⟩ := hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, eval_zero, zero_mul, add_zero] at hpn ⊢
      rw [← mul_assoc, inv_mul_cancel₀ hpn, one_mul]
    · obtain ⟨h, hh, hrec⟩ := exists_hyper_of_firstOrder_ratio hp hq
      have hh0 := hh.eventually_ne_zero
      have hv : IsHypergeometric (fun n : ℕ => (p.eval (n : K) * h (n + 1))⁻¹) :=
        ((isHypergeometric_poly hp).mul_hyper hh.shift_hyper).inv_hyper
      have hx := ihb.hyper_mul hv
      have has : ∀ᶠ n : ℕ in atTop, a n = h n * (a n / h n) := by
        filter_upwards [hh0] with n e
        field_simp
      have hds : ∀ᶠ n : ℕ in atTop, a (n + 1) / h (n + 1) - a n / h n =
          (p.eval (n : K) * h (n + 1))⁻¹ *
            (p.eval (n : K) * a (n + 1) + q.eval (n : K) * a n) := by
        filter_upwards [hrec, hh0, (tendsto_add_atTop_nat 1).eventually hh0,
          eventually_eval_ne_zero hp] with n e h0 h1 hpn
        have hq' : q.eval (n : K) = -(p.eval (n : K) * h (n + 1)) / h n := by
          field_simp
          linear_combination e
        rw [hq']
        field_simp
        ring
      exact (hx.sum_hyper hh hds).congr has

/-- CO-496 (the characterization). A sequence is d'Alembertian (up to finitely many terms, or
eventually zero) if and only if it is annihilated by a product of first-order recurrence
operators with polynomial (equivalently, rational) coefficients and nonzero leading coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem isDAlembertianEv_iff_chain {a : ℕ → K} :
    IsDAlembertianEv a ↔ ∃ k, IsChainAnnihilated k a := by
  constructor
  · rintro (ha | ⟨d, hd, had⟩)
    · exact ⟨0, ha⟩
    · obtain ⟨k, hk⟩ := hd.exists_chain
      exact ⟨k, chain_congr k (had.mono fun n h => h.symm) hk⟩
  · rintro ⟨k, hk⟩
    exact isDAlembertianEv_of_chain k hk

theorem chain_of_firstOrder_product (ps : List (K[X] × K[X])) (hps : ∀ pq ∈ ps, pq.1 ≠ 0) :
    ∀ a : ℕ → K, (∀ᶠ n : ℕ in atTop,
      RecOp.act (ps.map fun pq => RecOp.firstOrder pq.1 pq.2).prod a n = 0) →
      IsChainAnnihilated ps.length a := by
  induction ps using List.reverseRecOn with
  | nil =>
    intro a h
    show ∀ᶠ n : ℕ in atTop, a n = 0
    simpa [RecOp.act_one] using h
  | append_singleton ps x ih =>
    intro a h
    obtain ⟨p, q⟩ := x
    have hp : p ≠ 0 := hps (p, q) (by simp)
    have hps' : ∀ pq ∈ ps, pq.1 ≠ 0 := fun pq hpq => hps pq (by simp [hpq])
    have e : RecOp.act (RecOp.firstOrder p q) a =
        fun n : ℕ => p.eval (n : K) * a (n + 1) + q.eval (n : K) * a n :=
      funext (RecOp.act_firstOrder p q a)
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, RecOp.act_mul, e] at h
    rw [show (ps ++ [(p, q)]).length = ps.length + 1 by simp]
    exact ⟨p, q, hp, ih hps' _ h⟩

theorem chain_to_firstOrder_product : ∀ (k : ℕ) {a : ℕ → K}, IsChainAnnihilated k a →
    ∃ ps : List (K[X] × K[X]), (∀ pq ∈ ps, pq.1 ≠ 0) ∧ ∀ᶠ n : ℕ in atTop,
      RecOp.act (ps.map fun pq => RecOp.firstOrder pq.1 pq.2).prod a n = 0
  | 0, a, hk => by
    refine ⟨[], by simp, ?_⟩
    simp only [List.map_nil, List.prod_nil, RecOp.act_one]
    exact hk
  | k + 1, a, ⟨p, q, hp, hb⟩ => by
    obtain ⟨ps, hps, hev⟩ := chain_to_firstOrder_product k hb
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

/-- CO-496 (operator form of the characterization). A sequence is d'Alembertian (up to finitely
many terms, or eventually zero) if and only if it is annihilated, for large `n`, by a product
`L_k ⋯ L_1` of first-order operators `p_i(n) N + q_i(n)` with `p_i ≠ 0`, in the ring of
recurrence operators. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem isDAlembertianEv_iff_firstOrder_product {a : ℕ → K} :
    IsDAlembertianEv a ↔ ∃ ps : List (K[X] × K[X]), (∀ pq ∈ ps, pq.1 ≠ 0) ∧
      ∀ᶠ n : ℕ in atTop,
        RecOp.act (ps.map fun pq => RecOp.firstOrder pq.1 pq.2).prod a n = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := isDAlembertianEv_iff_chain.1 h
    exact chain_to_firstOrder_product k hk
  · rintro ⟨ps, hps, h⟩
    exact isDAlembertianEv_of_chain _ (chain_of_firstOrder_product ps hps a h)

/-- CO-496 (ring property, sums). Sums of d'Alembertian sequences are d'Alembertian (in the sense
of `IsDAlembertianEv`; a sum of two d'Alembertian sequences can vanish identically). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem IsDAlembertianEv.add {a b : ℕ → K} (ha : IsDAlembertianEv a) (hb : IsDAlembertianEv b) :
    IsDAlembertianEv (fun n => a n + b n) := by
  obtain ⟨j, hj⟩ := isDAlembertianEv_iff_chain.1 ha
  obtain ⟨k, hk⟩ := isDAlembertianEv_iff_chain.1 hb
  exact isDAlembertianEv_iff_chain.2 ⟨j + k, chain_add j k hj hk⟩

/-- CO-496 (ring property, products). Products of d'Alembertian sequences are d'Alembertian. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem IsDAlembertianEv.mul {a b : ℕ → K} (ha : IsDAlembertianEv a) (hb : IsDAlembertianEv b) :
    IsDAlembertianEv (fun n => a n * b n) := by
  obtain ⟨j, hj⟩ := isDAlembertianEv_iff_chain.1 ha
  obtain ⟨k, hk⟩ := isDAlembertianEv_iff_chain.1 hb
  obtain ⟨m, hm⟩ := chain_mul_exists (K := K) (j + k) j k le_rfl
  exact isDAlembertianEv_iff_chain.2 ⟨m, hm a b hj hk⟩

/-- CO-496 (ring property, negatives). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem IsDAlembertianEv.neg {a : ℕ → K} (ha : IsDAlembertianEv a) :
    IsDAlembertianEv (fun n => -a n) := by
  obtain ⟨j, hj⟩ := isDAlembertianEv_iff_chain.1 ha
  exact isDAlembertianEv_iff_chain.2 ⟨j, chain_congr j
    (Eventually.of_forall fun n => by simp) (chain_poly_mul j hj (-1))⟩

/-- CO-496 (ring property, constants and hypergeometric terms). -/
theorem IsDAlembertianEv.of_hyper {a : ℕ → K} (ha : IsHypergeometric a) :
    IsDAlembertianEv a :=
  Or.inr ⟨a, IsDAlembertian.hyper ha, Eventually.of_forall fun _ => rfl⟩

/-! ### CO-497: all closed-form solutions by reduction of order and Gosper's algorithm -/

/-- CO-497. One round of the method of the book (p. 167). Let `L = L₁ (q N - p)` and let `h` be a
hypergeometric solution of `q N - p` (that is, `q(n) h(n+1) = p(n) h(n)`).  Every other candidate
solution is `y = h s`; by reduction of order `L y = L₁ z`, where `z(n) = q(n) h(n+1) (s(n+1) - s(n))`.
If `z` is a solution of the reduced operator `L₁` which is itself d'Alembertian (found recursively),
then `y = h s` is a solution of `L`, and it is again d'Alembertian: `s` is an indefinite sum of the
d'Alembertian sequence `z / (q h(n+1))`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem reduced_solution_dalembertian {L L₁ : RecOp K} {p q : K[X]}
    (hL : L = L₁ * RecOp.firstOrder q (-p)) (hq : q ≠ 0) {h : ℕ → K} (hh : IsHypergeometric h)
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * h (n + 1) = p.eval (n : K) * h n)
    {z s : ℕ → K} (hz : IsDAlembertianEv z)
    (hLz : ∀ᶠ n : ℕ in atTop, RecOp.act L₁ z n = 0)
    (hs : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * h (n + 1) * (s (n + 1) - s n) = z n) :
    (∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => h m * s m) n = 0) ∧
      IsDAlembertianEv (fun n => h n * s n) := by
  constructor
  · have h1 := RecOp.act_hyper_mul L L₁ p q hL h hrel s
    have h2 := RecOp.act_congr_eventually L₁
      (f := fun m => q.eval (m : K) * h (m + 1) * (s (m + 1) - s m)) (g := z) hs
    filter_upwards [h1, h2, hLz] with n e1 e2 e3
    rw [e1, e2, e3]
  · have hv : IsHypergeometric (fun n : ℕ => (q.eval (n : K) * h (n + 1))⁻¹) :=
      ((isHypergeometric_poly hq).mul_hyper hh.shift_hyper).inv_hyper
    refine (hz.hyper_mul hv).sum_hyper hh ?_
    filter_upwards [hs, eventually_eval_ne_zero hq, (tendsto_add_atTop_nat 1).eventually
      hh.eventually_ne_zero] with n e h1 h2
    rw [← e]
    field_simp

/-- CO-497. The closing step of the method (page 167), for a hypergeometric solution `z` of the
reduced operator: `y = h s` with `s` an antidifference (`Δ s = x`, `x = z / (q h(n+1))`
hypergeometric) is closed up with Gosper's algorithm.  Gosper's algorithm, run on `x`, produces data
`a, b, c` and a sequence `g = gosperOutput x a b c` with `Δ g = x` for large `n`, so that
`s = g + c₀` for a constant `c₀` (and `y = h g + c₀ h`).  If `x` is Gosper-summable, `g` is
hypergeometric, so `h g` is hypergeometric and `y` is a sum of two hypergeometric terms (an
antidifference in closed form); if it is not, `g` is the partial sum `∑_{k<n} x k` (and `y` is the
d'Alembertian term `h · ∑ x`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 167"]
theorem reduced_solution_gosper {L L₁ : RecOp K} {p q : K[X]}
    (hL : L = L₁ * RecOp.firstOrder q (-p)) (hq : q ≠ 0) {h : ℕ → K} (hh : IsHypergeometric h)
    (hrel : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * h (n + 1) = p.eval (n : K) * h n)
    {z s : ℕ → K} (hz : IsHypergeometric z)
    (hLz : ∀ᶠ n : ℕ in atTop, RecOp.act L₁ z n = 0)
    (hs : ∀ᶠ n : ℕ in atTop, q.eval (n : K) * h (n + 1) * (s (n + 1) - s n) = z n) :
    (∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => h m * s m) n = 0) ∧
    ∃ (a b c : K[X]) (c₀ : K),
      IsHypergeometric (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) ∧
      (∀ᶠ n : ℕ in atTop, s n =
        gosperOutput (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) a b c n + c₀) ∧
      (∀ᶠ n : ℕ in atTop, h n * s n =
        h n * gosperOutput (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) a b c n + c₀ * h n) ∧
      (IsGosperSummable (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) →
        IsHypergeometric (gosperOutput (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) a b c) ∧
        IsHypergeometric (fun n =>
          h n * gosperOutput (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) a b c n)) ∧
      (¬ IsGosperSummable (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) →
        gosperOutput (fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n) a b c =
          fun n => ∑ k ∈ Finset.range n, (q.eval (k : K) * h (k + 1))⁻¹ * z k) := by
  refine ⟨(reduced_solution_dalembertian hL hq hh hrel (IsDAlembertianEv.of_hyper hz) hLz hs).1,
    ?_⟩
  set x : ℕ → K := fun n => (q.eval (n : K) * h (n + 1))⁻¹ * z n with hx_def
  have hv : IsHypergeometric (fun n : ℕ => (q.eval (n : K) * h (n + 1))⁻¹) :=
    ((isHypergeometric_poly hq).mul_hyper hh.shift_hyper).inv_hyper
  have hx : IsHypergeometric x := hv.mul_hyper hz
  have hds : ∀ᶠ n : ℕ in atTop, s (n + 1) - s n = x n := by
    filter_upwards [hs, eventually_eval_ne_zero hq, (tendsto_add_atTop_nat 1).eventually
      hh.eventually_ne_zero] with n e h1 h2
    rw [hx_def]
    simp only []
    rw [← e]
    field_simp
  obtain ⟨a, b, c, -, -, -, -, -, -, -, -, hsum, hnon⟩ := gosper_algorithm hx
  have hg : ∀ᶠ n : ℕ in atTop, gosperOutput x a b c (n + 1) - gosperOutput x a b c n = x n := by
    by_cases hS : IsGosperSummable x
    · exact (hsum hS).2
    · refine Eventually.of_forall fun n => ?_
      rw [hnon hS]
      simp only [Finset.sum_range_succ]
      ring
  obtain ⟨c₀, hc₀⟩ := eventually_const_of_diff_zero
    (f := fun n => s n - gosperOutput x a b c n)
    (by filter_upwards [hds, hg] with n e1 e2; linear_combination e1 - e2)
  have hsg : ∀ᶠ n : ℕ in atTop, s n = gosperOutput x a b c n + c₀ := by
    filter_upwards [hc₀] with n e
    linear_combination e
  refine ⟨a, b, c, c₀, hx, hsg, ?_, fun hS => ⟨(hsum hS).1, hh.mul_hyper (hsum hS).1⟩, hnon⟩
  filter_upwards [hsg] with n e
  rw [e]
  ring

end UndergradKB.Combinatorics.AeqB

end
