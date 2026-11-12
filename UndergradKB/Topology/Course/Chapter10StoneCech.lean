import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Pow
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Chapters 10.4 and 12.1 (Stone-Cech, Weierstrass preliminaries)

Thin wrappers of Mathlib results in the terms of Morris, *Topology Without Tears*.
-/

open Filter Function
open scoped Topology unitInterval

namespace UndergradKB.Topology.Course

universe u v

/-- Morris, Topology Without Tears, Definition 10.4.1 (TP-315). The Stone-Cech compactification
of `X` is compact Hausdorff, receives a continuous map from `X`, and every continuous map from `X`
to a compact Hausdorff space factors through it uniquely by a continuous map. -/
@[kb "morris2024" "Definition 10.4.1, p. 327"]
theorem morris_10_4_1 (X : Type u) [TopologicalSpace X] :
    CompactSpace (StoneCech X) ∧ T2Space (StoneCech X) ∧ Continuous (stoneCechUnit : X → StoneCech X) ∧
      ∀ (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (g : X → Y), Continuous g →
        ∃! h : StoneCech X → Y, Continuous h ∧ h ∘ stoneCechUnit = g := by
  refine ⟨inferInstance, inferInstance, continuous_stoneCechUnit, ?_⟩
  intro Y _ _ _ g hg
  refine ⟨stoneCechExtend hg, ⟨continuous_stoneCechExtend hg, stoneCechExtend_extends hg⟩, ?_⟩
  rintro h ⟨hc, hh⟩
  exact stoneCech_hom_ext hc (continuous_stoneCechExtend hg) (hh.trans (stoneCechExtend_extends hg).symm)

/-- Morris, Topology Without Tears, Lemma 10.4.4 (TP-317). Two continuous maps into a Hausdorff
space that agree on a dense subset are equal. -/
@[kb "morris2024" "Lemma 10.4.4, p. 329"]
theorem morris_10_4_4 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {D : Set X} (hD : Dense D) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ D, f x = g x) : f = g :=
  hf.ext_on hD hg h

/-- Morris, Topology Without Tears, Proposition 10.4.5 (TP-318). For a Tychonoff space `X`, the
canonical map into its Stone-Cech compactification is a (dense) embedding, and a space is
Tychonoff exactly when it embeds this way. -/
@[kb "morris2024" "Proposition 10.4.5, p. 330"]
theorem morris_10_4_5 (X : Type u) [TopologicalSpace X] [T35Space X] :
    _root_.Topology.IsEmbedding (stoneCechUnit : X → StoneCech X) ∧
      DenseRange (stoneCechUnit : X → StoneCech X) :=
  ⟨isEmbedding_stoneCechUnit, denseRange_stoneCechUnit⟩

/-- Morris, Topology Without Tears, Proposition 10.4.5 (TP-318), converse part. -/
@[kb "morris2024" "Proposition 10.4.5, p. 330"]
theorem morris_10_4_5_b (X : Type u) [TopologicalSpace X] :
    T35Space X ↔ _root_.Topology.IsEmbedding (stoneCechUnit : X → StoneCech X) :=
  t35Space_iff_isEmbedding_stoneCechUnit

/-- Morris, Topology Without Tears, Proposition 12.1.1 (TP-329). Bernoulli's inequality
`(1 + x)^n ≥ 1 + n x` for real `x ≥ -1` and natural `n`. -/
@[kb "morris2024" "Proposition 12.1.1, p. 356"]
theorem morris_12_1_1 (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- Morris, Topology Without Tears, Definition 12.1.2 (TP-330). A complex sequence tends to `b`
iff for every `ε > 0` all terms from some index on lie within `ε` of `b`. -/
@[kb "morris2024" "Definition 12.1.2, p. 357"]
theorem morris_12_1_2 (u : ℕ → ℂ) (b : ℂ) :
    Tendsto u atTop (𝓝 b) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖u n - b‖ < ε := by
  simp [Metric.tendsto_atTop, dist_eq_norm]

/-- Morris, Topology Without Tears, Remark 12.1.6 (TP-333). The Bernstein polynomials of a
continuous real function on `[0,1]` converge uniformly to it. -/
@[kb "morris2024" "Remark 12.1.6, p. 364"]
theorem morris_12_1_6 (f : C(unitInterval, ℝ)) :
    TendstoUniformly (fun n (x : unitInterval) => bernsteinApproximation n f x) f atTop :=
  ContinuousMap.tendsto_iff_tendstoUniformly.mp (bernsteinApproximation_uniform f)

/-- Morris, Topology Without Tears, Definition 12.1.10 (TP-336). Pointwise convergence of a
sequence of functions on a set `S`: convergence at each point of `S`. -/
@[kb "morris2024" "Definition 12.1.10, p. 366"]
theorem morris_12_1_10 {X : Type*} (S : Set X) (f : ℕ → X → ℂ) (g : X → ℂ) :
    Tendsto (fun n (x : S) => f n x) atTop (𝓝 fun x : S => g x) ↔
      ∀ x ∈ S, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  rw [tendsto_pi_nhds]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

/-- Morris, Topology Without Tears, Definition 12.1.11 (TP-337). Uniform convergence of a
sequence of functions on a set `S`: one index works for all points of `S`. -/
@[kb "morris2024" "Definition 12.1.11, p. 366"]
theorem morris_12_1_11 {X : Type*} (S : Set X) (f : ℕ → X → ℂ) (g : X → ℂ) :
    TendstoUniformlyOn f g atTop S ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ S, ‖f n x - g x‖ < ε := by
  rw [Metric.tendstoUniformlyOn_iff]
  simp only [gt_iff_lt, eventually_atTop, ge_iff_le, dist_eq_norm]
  refine forall₂_congr fun ε _ => exists_congr fun N => forall₂_congr fun n _ => forall₂_congr fun x _ => ?_
  rw [← norm_neg, neg_sub]

/-- Morris, Topology Without Tears, Proposition 12.1.19 (TP-341). The derivative of a map
`ℝⁿ → ℝᵐ` at a point is unique: two linear maps that both approximate `f` to first order agree. -/
@[kb "morris2024" "Proposition 12.1.19, p. 369"]
theorem morris_12_1_19 {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)}
    {A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hA : HasFDerivAt f A x) (hB : HasFDerivAt f B x) : A = B :=
  hA.unique hB

end UndergradKB.Topology.Course
