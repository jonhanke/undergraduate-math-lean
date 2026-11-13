import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr

/-!
# Small results of Lebl, chapters 0-7, not covered elsewhere

Harmonic partial sums (Remark 2.4.6), the tail of the geometric series, the alternating `p`-series, the nested
intervals of Example 7.2.7, `x y / (x² + y²)`, the discrete metric, critical points and strict extrema,
infinite sets and proper subsets, and step functions. Source: J. Lebl, *Basic Analysis I* (`lebl2026`).
-/

open Filter Topology Set

namespace UndergradKB.RealAnalysis

/-! ## Remark 2.4.6: harmonic partial sums -/

/-- The harmonic partial sums `x n = 1 + 1/2 + ... + 1/n`. -/
noncomputable def harmonicPartial (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

/-- Remark 2.4.6: for each fixed `j`, `x (n + j) - x n → 0`, yet the harmonic partial sums are not Cauchy. -/
@[kb "lebl2026" "Remark 2.4.6, p. 85"]
theorem harmonic_diff_tendsto_zero_not_cauchy :
    (∀ j : ℕ, Tendsto (fun n => harmonicPartial (n + j) - harmonicPartial n) atTop (𝓝 0)) ∧
      ¬ CauchySeq harmonicPartial := by
  refine ⟨fun j => ?_, fun hc => ?_⟩
  · have hid : ∀ n : ℕ, harmonicPartial (n + j) - harmonicPartial n
        = ∑ k ∈ Finset.range j, 1 / (((n + k : ℕ) : ℝ) + 1) := by
      intro n
      unfold harmonicPartial
      rw [Finset.sum_range_add]
      ring
    have hup : Tendsto (fun n : ℕ => (j : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (j : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
    · rw [hid]
      exact Finset.sum_nonneg (fun k _ => by positivity)
    · rw [hid]
      calc ∑ k ∈ Finset.range j, 1 / (((n + k : ℕ) : ℝ) + 1)
          ≤ ∑ k ∈ Finset.range j, 1 / ((n : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro k _
            apply one_div_le_one_div_of_le (by positivity)
            push_cast
            linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        _ = (j : ℝ) * (1 / ((n : ℝ) + 1)) := by simp
  · obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    exact not_tendsto_atTop_of_tendsto_nhds hL Real.tendsto_sum_range_one_div_nat_succ_atTop

/-! ## Section 2.5: the tail of the geometric series -/

/-- For `|r| < 1`: `∑_{n ≥ i} r ^ n = r ^ i / (1 - r)`. -/
@[kb "lebl2026" "Section 2.5 (tail of the geometric series), p. 91"]
theorem hasSum_geometric_tail {r : ℝ} (hr : |r| < 1) (i : ℕ) :
    HasSum (fun n : ℕ => r ^ (n + i)) (r ^ i / (1 - r)) := by
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_right (r ^ i)
  simpa [pow_add, div_eq_mul_inv, mul_comm] using h

/-! ## Section 2.6: the alternating `p`-series -/

/-- For every `p > 0`, `∑ (-1)^n / (n+1)^p` converges; for `0 < p ≤ 1` it is not absolutely convergent. -/
@[kb "lebl2026" "Section 2.6 (alternating p-series), p. 102"]
theorem alternating_p_series {p : ℝ} (hp : 0 < p) :
    (∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ p) atTop (𝓝 L)) ∧
      (p ≤ 1 → ¬ Summable (fun n : ℕ => |(-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ p|)) := by
  constructor
  · have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) := by
      intro m n hmn
      have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) p)
        (Real.rpow_le_rpow (by positivity) this hp.le)
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ p) atTop atTop :=
        (tendsto_rpow_atTop hp).comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      exact h1.inv_tendsto_atTop.congr (fun n => by simp [one_div])
    obtain ⟨L, hL⟩ := hanti.tendsto_alternating_series_of_tendsto_zero h0
    refine ⟨L, ?_⟩
    simpa [div_eq_mul_inv, mul_comm] using hL
  · intro hp1 hs
    have h2 : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ p) := by
      refine hs.congr (fun n => ?_)
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (Real.rpow_nonneg (by positivity) p),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have := (Real.summable_one_div_nat_add_rpow 1 p).1 h2
    linarith

/-! ## Example 7.2.7: an intersection of open sets that is not open -/

/-- `⋂ₙ (-1/(n+1), 1/(n+1)) = {0}`, and `{0}` is not open in `ℝ`. -/
@[kb "lebl2026" "Example 7.2.7, p. 266"]
theorem iInter_Ioo_eq_singleton_not_isOpen :
    (⋂ n : ℕ, Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) = {0} ∧
      ¬ IsOpen (⋂ n : ℕ, Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) := by
  have h : (⋂ n : ℕ, Set.Ioo (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) = {0} := by
    ext x
    simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 hne)
      have := hx n
      have h3 := abs_lt.2 this
      linarith
    · rintro rfl n
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      constructor <;> linarith
  exact ⟨h, by rw [h]; exact not_isOpen_singleton _⟩

/-! ## Section 7.5: separately continuous but not continuous -/

/-- `f (x, y) = x y / (x² + y²)`; in Lean it is `0` at the origin by division by zero. -/
noncomputable def sepCont (p : ℝ × ℝ) : ℝ := p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)

/-- Section 7.5: `f (x, y) = x y / (x² + y²)` (with `f 0 = 0`, which Lean's `x / 0 = 0` provides) is continuous in
each variable separately, but is not continuous at `(0, 0)`. -/
@[kb "lebl2026" "Section 7.5 (separate continuity), p. 288"]
theorem sepCont_separately_continuous_not_continuous :
    (∀ y₀ : ℝ, Continuous fun x : ℝ => sepCont (x, y₀)) ∧
      (∀ x₀ : ℝ, Continuous fun y : ℝ => sepCont (x₀, y)) ∧
      ¬ ContinuousAt sepCont (0, 0) := by
  refine ⟨fun y₀ => ?_, fun x₀ => ?_, fun hc => ?_⟩
  · by_cases h : y₀ = 0
    · subst h
      simp [sepCont]
      exact continuous_const
    · show Continuous fun x : ℝ => x * y₀ / (x ^ 2 + y₀ ^ 2)
      have h2 : ∀ x : ℝ, x ^ 2 + y₀ ^ 2 ≠ 0 := fun x => by positivity
      exact (continuous_id.mul continuous_const).div ((continuous_id.pow 2).add continuous_const) h2
  · by_cases h : x₀ = 0
    · subst h
      simp [sepCont]
      exact continuous_const
    · show Continuous fun y : ℝ => x₀ * y / (x₀ ^ 2 + y ^ 2)
      have h2 : ∀ y : ℝ, x₀ ^ 2 + y ^ 2 ≠ 0 := fun y => by positivity
      exact (continuous_const.mul continuous_id).div (continuous_const.add (continuous_id.pow 2)) h2
  · have hdiag : ContinuousAt (fun t : ℝ => sepCont (t, t)) 0 :=
      ContinuousAt.comp (g := sepCont) (f := fun t : ℝ => (t, t)) (x := 0) hc (by fun_prop)
    have h1 : Tendsto (fun t : ℝ => sepCont (t, t)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      unfold sepCont
      field_simp
      ring
    have h2 : Tendsto (fun t : ℝ => sepCont (t, t)) (𝓝[≠] 0) (𝓝 (sepCont (0, 0))) :=
      hdiag.tendsto.mono_left nhdsWithin_le_nhds
    have h3 := tendsto_nhds_unique h1 h2
    simp [sepCont] at h3

/-! ## Example 7.1.7: the discrete metric -/

/-- The discrete distance: `0` if the points are equal, `1` otherwise. -/
noncomputable def discreteDist {X : Type*} (x y : X) : ℝ := by
  classical
  exact if x = y then 0 else 1

/-- The discrete distance vanishes exactly on equal points. -/
@[kb "lebl2026" "Example 7.1.7, p. 259"]
theorem discreteDist_eq_zero_iff {X : Type*} (x y : X) : discreteDist x y = 0 ↔ x = y := by
  unfold discreteDist
  by_cases h : x = y <;> simp [h]

/-- The discrete distance is nonnegative. -/
@[kb "lebl2026" "Example 7.1.7, p. 259"]
theorem discreteDist_nonneg {X : Type*} (x y : X) : 0 ≤ discreteDist x y := by
  unfold discreteDist
  by_cases h : x = y <;> simp [h]

/-- The discrete distance is symmetric. -/
@[kb "lebl2026" "Example 7.1.7, p. 259"]
theorem discreteDist_comm {X : Type*} (x y : X) : discreteDist x y = discreteDist y x := by
  unfold discreteDist
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The discrete distance satisfies the triangle inequality. -/
@[kb "lebl2026" "Example 7.1.7, p. 259"]
theorem discreteDist_triangle {X : Type*} (x y z : X) :
    discreteDist x z ≤ discreteDist x y + discreteDist y z := by
  unfold discreteDist
  by_cases h1 : x = y <;> by_cases h2 : y = z
  · subst h1; subst h2; simp
  · subst h1; simp [h2]
  · subst h2; simp [h1]
  · simp only [h1, h2, ite_false]
    split_ifs <;> norm_num

/-! ## Critical points and strict relative extrema -/

/-- A critical point of `f`: `f` is differentiable at `c` with derivative `0`. -/
@[kb "lebl2026" "Definition (critical point), p. 163"]
def IsCriticalPoint (f : ℝ → ℝ) (c : ℝ) : Prop := HasDerivAt f 0 c

/-- Strict relative minimum at `c`: `f c < f x` for all `x ≠ c` near `c`. -/
@[kb "lebl2026" "Definition (strict relative extremum), p. 174"]
def IsStrictLocalMin (f : ℝ → ℝ) (c : ℝ) : Prop := ∀ᶠ x in 𝓝[≠] c, f c < f x

/-- Strict relative maximum at `c`: `f x < f c` for all `x ≠ c` near `c`. -/
@[kb "lebl2026" "Definition (strict relative extremum), p. 174"]
def IsStrictLocalMax (f : ℝ → ℝ) (c : ℝ) : Prop := ∀ᶠ x in 𝓝[≠] c, f x < f c

/-- A strict relative minimum is a relative minimum. -/
@[kb "lebl2026" "Definition (strict relative extremum), p. 174"]
theorem IsStrictLocalMin.isLocalMin {f : ℝ → ℝ} {c : ℝ} (h : IsStrictLocalMin f c) : IsLocalMin f c := by
  filter_upwards [eventually_nhdsWithin_iff.1 h] with x hx
  by_cases hxc : x = c
  · rw [hxc]
  · exact (hx hxc).le

/-- A strict relative maximum is a relative maximum. -/
@[kb "lebl2026" "Definition (strict relative extremum), p. 174"]
theorem IsStrictLocalMax.isLocalMax {f : ℝ → ℝ} {c : ℝ} (h : IsStrictLocalMax f c) : IsLocalMax f c := by
  filter_upwards [eventually_nhdsWithin_iff.1 h] with x hx
  by_cases hxc : x = c
  · rw [hxc]
  · exact (hx hxc).le

/-- Fermat's theorem: a differentiable relative minimum is a critical point. -/
@[kb "lebl2026" "Definition (critical point), p. 163"]
theorem isCriticalPoint_of_isLocalMin {f : ℝ → ℝ} {c : ℝ} (hd : DifferentiableAt ℝ f c)
    (h : IsLocalMin f c) : IsCriticalPoint f c := by
  have := h.hasDerivAt_eq_zero hd.hasDerivAt
  unfold IsCriticalPoint
  rw [← this]
  exact hd.hasDerivAt

/-- Fermat's theorem: a differentiable relative maximum is a critical point. -/
@[kb "lebl2026" "Definition (critical point), p. 163"]
theorem isCriticalPoint_of_isLocalMax {f : ℝ → ℝ} {c : ℝ} (hd : DifferentiableAt ℝ f c)
    (h : IsLocalMax f c) : IsCriticalPoint f c := by
  have := h.hasDerivAt_eq_zero hd.hasDerivAt
  unfold IsCriticalPoint
  rw [← this]
  exact hd.hasDerivAt

/-! ## Section 0.3.5: infinite sets and proper subsets -/

/-- A set is infinite iff it is in bijection with a proper subset of itself. -/
@[kb "lebl2026" "Section 0.3.5, p. 18"]
theorem infinite_iff_exists_ssubset_equiv {α : Type*} (S : Set α) :
    S.Infinite ↔ ∃ T ⊂ S, Nonempty (S ≃ T) := by
  constructor
  · intro hS
    have : Infinite S := hS.to_subtype
    obtain ⟨a⟩ : Nonempty S := (Infinite.nonempty S)
    have hinf : Infinite (({a}ᶜ : Set S)) := by
      have : (({a} : Set S)ᶜ).Infinite := Set.Infinite.sdiff Set.infinite_univ (Set.finite_singleton a) |>.mono
        (by intro x hx; simpa using hx)
      exact this.to_subtype
    have hc : Cardinal.mk (({a}ᶜ : Set S)) = Cardinal.mk S := by
      have h1 := Cardinal.mk_sum_compl ({a} : Set S)
      have h2 : Cardinal.mk (({a} : Set S)) = 1 := Cardinal.mk_singleton a
      rw [h2, add_comm] at h1
      rw [← h1]
      exact (Cardinal.add_one_eq (Cardinal.aleph0_le_mk _)).symm
    obtain ⟨e1⟩ := Cardinal.eq.1 hc.symm
    refine ⟨Subtype.val '' ({a}ᶜ : Set S), ?_, ⟨e1.trans (Equiv.Set.image _ _ Subtype.val_injective)⟩⟩
    rw [Set.ssubset_iff_of_subset (Subtype.coe_image_subset _ _)]
    refine ⟨a.1, a.2, ?_⟩
    rintro ⟨y, hy, hya⟩
    exact hy (Subtype.ext hya)
  · rintro ⟨T, hT, ⟨e⟩⟩ hfin
    have hTfin : T.Finite := hfin.subset hT.subset
    have hcard : T.ncard = S.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact (Nat.card_congr e).symm
    exact hT.ne (Set.eq_of_subset_of_ncard_le hT.subset hcard.ge hfin)

/-! ## Section 5.2: step functions -/

/-- A step function on `[a, b]`: a finite linear combination of indicators of subintervals `[l i, r i] ⊆ [a, b]`. -/
def IsStepFunction (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℝ) (l r : Fin n → ℝ), (∀ i, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b) ∧
    f = fun x => ∑ i, c i * (Set.Icc (l i) (r i)).indicator 1 x

/-- A step function is interval integrable on `[a, b]`. -/
@[kb "lebl2026" "Section 5.2 (step functions), p. 198"]
theorem IsStepFunction.intervalIntegrable {a b : ℝ} {f : ℝ → ℝ} (hf : IsStepFunction a b f) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  obtain ⟨n, c, l, r, -, rfl⟩ := hf
  have h : ∀ i : Fin n, IntervalIntegrable (fun x => c i * (Set.Icc (l i) (r i)).indicator (1 : ℝ → ℝ) x)
      MeasureTheory.volume a b := by
    intro i
    refine IntervalIntegrable.const_mul ?_ (c i)
    refine MeasureTheory.Integrable.intervalIntegrable ?_
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).2
      (MeasureTheory.integrableOn_const (by simp))
  have := IntervalIntegrable.sum Finset.univ (fun i _ => h i)
  convert this using 1
  ext x
  simp [Finset.sum_apply]

end UndergradKB.RealAnalysis
