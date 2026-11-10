import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import UndergradKB.Geometry.HyperbolicDisc
import UndergradKB.Common.Attr

/-! # The h-plane as a metric space (Petrunin, Chapter 12)

The h-plane of the conformal disc model (p. 92-93): the points of the open unit disc of `ℂ` with
the h-distance `hdist` (wave 1, `HyperbolicDisc.lean`). We make it a type `HPoint` with its own
`MetricSpace` instance (Claims 12.12-12.14), so that the book's metric notions (lines as subsets
isometric to `ℝ`, motions) apply to it. (Mathlib's `Complex.UnitDisc` carries the Euclidean metric
of `ℂ`, so a separate type is needed.) -/

namespace UndergradKB.Geometry

/-- A point of the h-plane: a complex number in the open unit disc (p. 92). -/
@[ext]
structure HPoint where
  /-- The complex coordinate of the point. -/
  z : ℂ
  norm_lt : ‖z‖ < 1

namespace HPoint

/-- **The h-plane is a metric space (Claims 12.12-12.14, pp. 97-98)**: the h-distance is
nonnegative, vanishes exactly on the diagonal, is symmetric and satisfies the triangle inequality. -/
@[kb "petrunin2025" "Claims 12.12-12.14, pp. 97-98"]
noncomputable instance : MetricSpace HPoint where
  dist P Q := hdist P.z Q.z
  dist_self P := (hdist_eq_zero_iff P.norm_lt P.norm_lt).2 rfl
  dist_comm P Q := hdist_comm _ _
  dist_triangle P Q R := hdist_triangle P.norm_lt Q.norm_lt R.norm_lt
  eq_of_dist_eq_zero {P Q} h := HPoint.ext ((hdist_eq_zero_iff P.norm_lt Q.norm_lt).1 h)

theorem dist_eq (P Q : HPoint) : dist P Q = hdist P.z Q.z := rfl

/-- The Euclidean distance is bounded by `sinh` of half the h-distance: `‖P - Q‖ ≤ sinh (PQ_h / 2)`. -/
theorem norm_sub_le_sinh (P Q : HPoint) : ‖P.z - Q.z‖ ≤ Real.sinh (dist P Q / 2) := by
  have hc := cosh_hdist P.norm_lt Q.norm_lt
  rw [← dist_eq] at hc
  set d := dist P Q
  have hd : 0 ≤ d := dist_nonneg
  have h2 : Real.cosh d = 1 + 2 * Real.sinh (d / 2) ^ 2 := by
    have := Real.cosh_two_mul (d / 2)
    rw [show 2 * (d / 2) = d by ring, Real.cosh_sq] at this
    linarith
  have hP := one_sub_sq_pos P.norm_lt
  have hQ := one_sub_sq_pos Q.norm_lt
  have hD : 0 < (1 - ‖P.z‖ ^ 2) * (1 - ‖Q.z‖ ^ 2) := mul_pos hP hQ
  have hD1 : (1 - ‖P.z‖ ^ 2) * (1 - ‖Q.z‖ ^ 2) ≤ 1 := by
    have := sq_nonneg ‖P.z‖
    have := sq_nonneg ‖Q.z‖
    nlinarith
  unfold hcosh at hc
  rw [h2] at hc
  have key : ‖P.z - Q.z‖ ^ 2 = Real.sinh (d / 2) ^ 2 * ((1 - ‖P.z‖ ^ 2) * (1 - ‖Q.z‖ ^ 2)) := by
    field_simp at hc
    linarith
  have hs : 0 ≤ Real.sinh (d / 2) := Real.sinh_nonneg_iff.2 (by linarith)
  have : ‖P.z - Q.z‖ ^ 2 ≤ Real.sinh (d / 2) ^ 2 := by
    rw [key]
    exact mul_le_of_le_one_right (sq_nonneg _) hD1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero).1 this

/-- The complex coordinate is continuous from the h-plane to `ℂ`. -/
theorem continuous_z : Continuous HPoint.z := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨2 * Real.arsinh ε, by have := Real.arsinh_pos_iff.2 hε; linarith, fun a ha => ?_⟩
  rw [Complex.dist_eq]
  calc ‖a.z - b.z‖ ≤ Real.sinh (dist a b / 2) := norm_sub_le_sinh a b
    _ < Real.sinh (Real.arsinh ε) := Real.sinh_lt_sinh.2 (by linarith)
    _ = ε := Real.sinh_arsinh ε

/-- The centre of the absolute. -/
def center : HPoint := ⟨0, by simp⟩

end HPoint

end UndergradKB.Geometry
