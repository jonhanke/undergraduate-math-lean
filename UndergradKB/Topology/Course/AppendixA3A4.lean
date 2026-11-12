import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Appendices 3-4 (chaos, Hausdorff dimension)

Thin wrappers of Mathlib results in the terms of Morris, *Topology Without Tears*.
-/

namespace UndergradKB.Topology.Course

open Set MeasureTheory Measure
open scoped NNReal ENNReal

/-- Morris, Topology Without Tears, Definition A3.1.1 (TP-432). The iterate satisfies
`f^{n+1} = f ∘ f^n`. -/
@[kb "morris2024" "Definition A3.1.1, p. 438"]
theorem morris_A3_1_1 {α : Type*} (f : α → α) (n : ℕ) :
    f^[n + 1] = f ∘ f^[n] :=
  Function.iterate_succ' f n

/-- Morris, Topology Without Tears, Definition A3.1.3 (TP-434). A fixed point of `f` is a point
`a` with `f a = a`. -/
@[kb "morris2024" "Definition A3.1.3, p. 439"]
theorem morris_A3_1_3 {α : Type*} (f : α → α) (a : α) :
    Function.IsFixedPt f a ↔ f a = a :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition A3.2.2 (TP-436). A point is periodic with period
`p ≥ 1` when `f^p x = x`; its prime period is the least such `p`. -/
@[kb "morris2024" "Definition A3.2.2, p. 441"]
theorem morris_A3_2_2 {α : Type*} (f : α → α) (x : α) {p : ℕ} (hp : 0 < p)
    (h : f^[p] x = x) :
    f^[Function.minimalPeriod f x] x = x ∧ 0 < Function.minimalPeriod f x ∧
      Function.minimalPeriod f x ≤ p :=
  ⟨Function.isPeriodicPt_minimalPeriod f x,
    Function.IsPeriodicPt.minimalPeriod_pos hp h,
    Function.IsPeriodicPt.minimalPeriod_le hp h⟩

/-- Morris, Topology Without Tears, Definition A4.1.1 (TP-456). The diameter of a nonempty bounded
subset of a metric space is the supremum of the distances between its points. -/
@[kb "morris2024" "Definition A4.1.1, p. 471"]
theorem morris_A4_1_1 {X : Type*} [PseudoMetricSpace X] {Y : Set X} (hne : Y.Nonempty)
    (hb : Bornology.IsBounded Y) :
    IsLUB {r : ℝ | ∃ x ∈ Y, ∃ y ∈ Y, r = dist x y} (Metric.diam Y) := by
  refine ⟨?_, ?_⟩
  · rintro r ⟨x, hx, y, hy, rfl⟩
    exact Metric.dist_le_diam_of_mem hb hx hy
  · intro C hC
    obtain ⟨x, hx⟩ := hne
    have h0 : 0 ≤ C := by simpa using hC ⟨x, hx, x, hx, rfl⟩
    exact Metric.diam_le_of_forall_dist_le h0 fun a ha b hb' => hC ⟨a, ha, b, hb', rfl⟩

/-- Morris, Topology Without Tears, Definition A4.1.4 (TP-459). The `s`-dimensional Hausdorff outer
measure is the supremum over `ε > 0` of the infimum of `∑ (diam Uᵢ)^s` over countable covers by
sets of diameter at most `ε`. -/
@[kb "morris2024" "Definition A4.1.4, p. 473"]
theorem morris_A4_1_4 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (Y : Set X) :
    μH[s] Y =
      ⨆ (r : ℝ≥0∞) (_ : 0 < r),
        ⨅ (t : ℕ → Set X) (_ : Y ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
          ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s :=
  hausdorffMeasure_apply s Y

/-- Morris, Topology Without Tears, Proposition A4.1.8 (TP-461). If `s < t` and `H^s(Y) < ∞`
then `H^t(Y) = 0`. -/
@[kb "morris2024" "Proposition A4.1.8, p. 474"]
theorem morris_A4_1_8_a {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s t : ℝ} (hst : s < t) (Y : Set X) (h : μH[s] Y < ∞) : μH[t] Y = 0 :=
  (hausdorffMeasure_zero_or_top hst Y).resolve_right h.ne

/-- Morris, Topology Without Tears, Proposition A4.1.8 (TP-461). If `s < t` and
`0 ≠ H^t(Y) < ∞` then `H^s(Y) = ∞`. -/
@[kb "morris2024" "Proposition A4.1.8, p. 474"]
theorem morris_A4_1_8_b {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s t : ℝ} (hst : s < t) (Y : Set X) (h0 : μH[t] Y ≠ 0) (_h : μH[t] Y < ∞) :
    μH[s] Y = ∞ :=
  (hausdorffMeasure_zero_or_top hst Y).resolve_left h0

/-- Morris, Topology Without Tears, Definition A4.1.10 (TP-462). The Hausdorff dimension is the
infimum of the exponents `s` with `H^s(Y) = 0`. -/
@[kb "morris2024" "Definition A4.1.10, p. 474"]
theorem morris_A4_1_10 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Y : Set X) :
    dimH Y = ⨅ (s : ℝ≥0) (_ : μH[s] Y = 0), (s : ℝ≥0∞) :=
  dimH_eq_iInf Y

/-- Morris, Topology Without Tears, Proposition A4.1.11 (TP-463). The Hausdorff dimension is the
supremum of the `s` with `H^s(Y) = ∞`. -/
@[kb "morris2024" "Proposition A4.1.11, p. 475"]
theorem morris_A4_1_11_a {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Y : Set X) :
    dimH Y = ⨆ (s : ℝ≥0) (_ : μH[s] Y = ∞), (s : ℝ≥0∞) :=
  dimH_def Y

/-- Morris, Topology Without Tears, Proposition A4.1.11 (TP-463). `H^s(Y) = 0` for `s > dim_H Y`
and `H^s(Y) = ∞` for `s < dim_H Y`. -/
@[kb "morris2024" "Proposition A4.1.11, p. 475"]
theorem morris_A4_1_11_b {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Y : Set X) (s : ℝ≥0) :
    (dimH Y < s → μH[s] Y = 0) ∧ ((s : ℝ≥0∞) < dimH Y → μH[s] Y = ∞) :=
  ⟨hausdorffMeasure_of_dimH_lt, hausdorffMeasure_of_lt_dimH⟩

/-- Morris, Topology Without Tears, Exercise A4.1.12 (TP-464). A finite subset of a metric space
has Hausdorff dimension zero. -/
@[kb "morris2024" "Exercise A4.1.12, p. 475"]
theorem morris_A4_1_12 {X : Type*} [EMetricSpace X] {Y : Set X} (hY : Y.Finite) :
    dimH Y = 0 :=
  dimH_finite hY

/-- Morris, Topology Without Tears, Proposition A4.1.13 (TP-465). Isometric metric spaces have
the same Hausdorff dimension. -/
@[kb "morris2024" "Proposition A4.1.13, p. 475"]
theorem morris_A4_1_13 {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] (e : X ≃ᵢ Y) :
    dimH (univ : Set X) = dimH (univ : Set Y) :=
  e.dimH_univ

/-- Morris, Topology Without Tears, Proposition A4.1.14 (TP-466). Hausdorff dimension is monotone
under inclusion. -/
@[kb "morris2024" "Proposition A4.1.14, p. 476"]
theorem morris_A4_1_14 {X : Type*} [EMetricSpace X] {Z Y : Set X} (h : Z ⊆ Y) :
    dimH Z ≤ dimH Y :=
  dimH_mono h

/-- Morris, Topology Without Tears, Lemma A4.1.15 (TP-467). Countable subadditivity of the
Hausdorff outer measure. -/
@[kb "morris2024" "Lemma A4.1.15, p. 476"]
theorem morris_A4_1_15 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {ι : Type*} [Countable ι] (s : ℝ) (Y : ι → Set X) :
    μH[s] (⋃ i, Y i) ≤ ∑' i, μH[s] (Y i) :=
  measure_iUnion_le Y

/-- Morris, Topology Without Tears, Proposition A4.1.16 (TP-468). The dimension of a countable
union is the supremum of the dimensions of the pieces. -/
@[kb "morris2024" "Proposition A4.1.16, p. 476"]
theorem morris_A4_1_16 {X : Type*} [EMetricSpace X] {ι : Type*} [Countable ι] (Y : ι → Set X) :
    dimH (⋃ i, Y i) = ⨆ i, dimH (Y i) :=
  dimH_iUnion Y

/-- Morris, Topology Without Tears, Proposition A4.1.17 (TP-469). A countable subset of a metric
space has Hausdorff dimension zero. -/
@[kb "morris2024" "Proposition A4.1.17, p. 477"]
theorem morris_A4_1_17 {X : Type*} [EMetricSpace X] {Y : Set X} (hY : Y.Countable) :
    dimH Y = 0 :=
  dimH_countable hY

/-- Morris, Topology Without Tears, Proposition A4.1.19 (TP-470). A surjection `f` between metric
spaces with `a d(x,y) ≤ d(f x, f y) ≤ b d(x,y)` preserves Hausdorff dimension. -/
@[kb "morris2024" "Proposition A4.1.19, p. 477"]
theorem morris_A4_1_19 {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] {f : X → Y}
    {a b : ℝ≥0} (hb : LipschitzWith b f) (ha : AntilipschitzWith a f)
    (hf : Function.Surjective f) :
    dimH (univ : Set X) = dimH (univ : Set Y) := by
  apply le_antisymm
  · simpa [image_univ, hf.range_eq] using ha.le_dimH_image univ
  · simpa [image_univ, hf.range_eq] using hb.dimH_image_le univ

/-- Morris, Topology Without Tears, Proposition A4.1.24 (TP-473). `H^1([0,1]) = 1`, hence
`dim_H [0,1] = 1`. -/
@[kb "morris2024" "Proposition A4.1.24, p. 479"]
theorem morris_A4_1_24 : μH[1] (Icc (0 : ℝ) 1) = 1 ∧ dimH (Icc (0 : ℝ) 1) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [hausdorffMeasure_real]
    simp
  · have h := Real.dimH_of_nonempty_interior (E := ℝ) (s := Icc (0 : ℝ) 1)
      (by simp)
    simpa using h

/-- Morris, Topology Without Tears, Corollary A4.1.25 (TP-474). Every subset of `ℝ` has dimension
at most one, and any set containing a nontrivial interval has dimension exactly one. -/
@[kb "morris2024" "Corollary A4.1.25, p. 479"]
theorem morris_A4_1_25 :
    dimH (univ : Set ℝ) = 1 ∧ (∀ Y : Set ℝ, dimH Y ≤ 1) ∧
      ∀ (Y : Set ℝ) (c d : ℝ), c < d → Icc c d ⊆ Y → dimH Y = 1 := by
  refine ⟨Real.dimH_univ, fun Y => ?_, fun Y c d hcd hY => ?_⟩
  · exact (dimH_mono (subset_univ Y)).trans Real.dimH_univ.le
  · apply le_antisymm
    · exact (dimH_mono (subset_univ Y)).trans Real.dimH_univ.le
    · have h := Real.dimH_of_nonempty_interior (E := ℝ) (s := Icc c d)
        (by simpa using hcd)
      have h1 : dimH (Icc c d) = 1 := by simpa using h
      exact h1.symm.le.trans (dimH_mono hY)

/-- Morris, Topology Without Tears, Remark A4.1.26 (TP-475). `dim_H ℝⁿ = n`. -/
@[kb "morris2024" "Remark A4.1.26, p. 479"]
theorem morris_A4_1_26 (n : ℕ) : dimH (univ : Set (Fin n → ℝ)) = n :=
  Real.dimH_univ_pi_fin n

end UndergradKB.Topology.Course
