import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Sphere.Basic
import UndergradKB.Geometry.ClassicalProblems
import UndergradKB.Common.Attr

/-! # Problem of Apollonius: which configurations have a solution (Petrunin, Problem 19.2, p. 157)

The book asks for a circle tangent to three given circles, without hypotheses, but the problem has
no solution in some configurations.  `ClassicalProblems.lean` proves existence for three pairwise
exterior circles.  Here:

* `apollonius_nested`: two exterior circles both strictly inside a third circle;
* `apollonius_obstruction`: if one circle separates the other two (one strictly inside it, the
  other outside its closed disc) no circle is tangent to all three; this holds in any metric space;
* `apollonius_concentric`: three concentric circles with distinct radii have no common tangent circle;
* `apollonius_exists_iff`: for three pairwise disjoint circles, a tangent circle exists iff no one of
  the circles separates the other two.

Tangency is `CirclesTangent` (external or internal). -/

namespace UndergradKB.Geometry

open EuclideanGeometry

section ApolloniusNested

namespace Apollonius

theorem det_fail {d21 d22 d31 d32 r1 r2 r3 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3)
    (h : ∀ t2 t3 : ℝ, (t2 = r2 ∨ t2 = -r2) → (t3 = r3 ∨ t3 = -r3) →
      lorentzDet d21 d22 d31 d32 (t2 - r1) (t3 - r1) = 0) :
    d31 ^ 2 + d32 ^ 2 = 0 := by
  have hpp := h r2 r3 (Or.inl rfl) (Or.inl rfl)
  have hmp := h (-r2) r3 (Or.inr rfl) (Or.inl rfl)
  have hpm := h r2 (-r3) (Or.inl rfl) (Or.inr rfl)
  have hmm := h (-r2) (-r3) (Or.inr rfl) (Or.inr rfl)
  simp only [lorentzDet] at hpp hmp hpm hmm
  have k1 : r2 * (r1 * (d31 ^ 2 + d32 ^ 2) + (r3 - r1) * (d21 * d31 + d22 * d32)) = 0 := by
    linear_combination (1 / 4) * (hpp - hmp)
  have k2 : r2 * (r1 * (d31 ^ 2 + d32 ^ 2) + (-r3 - r1) * (d21 * d31 + d22 * d32)) = 0 := by
    linear_combination (1 / 4) * (hpm - hmm)
  have k1' := (mul_eq_zero.mp k1).resolve_left hr2.ne'
  have k2' := (mul_eq_zero.mp k2).resolve_left hr2.ne'
  have hC : d21 * d31 + d22 * d32 = 0 := by
    have : r3 * (d21 * d31 + d22 * d32) = 0 := by linear_combination (1 / 2) * (k1' - k2')
    exact (mul_eq_zero.mp this).resolve_left hr3.ne'
  rw [hC] at k1'
  have : r1 * (d31 ^ 2 + d32 ^ 2) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hr1.ne'

theorem exists_pattern_gen {d21 d22 d31 d32 r1 r2 r3 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hr3 : 0 < r3) (hA : 0 < d21 ^ 2 + d22 ^ 2) :
    ∃ t2 t3 : ℝ, (t2 = r2 ∨ t2 = -r2) ∧ (t3 = r3 ∨ t3 = -r3) ∧
      lorentzDet d21 d22 d31 d32 (t2 - r1) (t3 - r1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hA' := det_fail (d21 := d31) (d22 := d32) (d31 := d21) (d32 := d22) hr1 hr3 hr2
    (fun t3 t2 h3 h2 => by
      have := hcon t2 t3 h2 h3
      unfold lorentzDet at this ⊢
      linear_combination this)
  linarith

theorem apollonius_pattern_gen {d21 d22 d31 d32 r1 t2 t3 : ℝ}
    (hQ : 0 ≤ (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) * (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) *
      ((d21 - d31) ^ 2 + (d22 - d32) ^ 2 - (t2 - t3) ^ 2))
    (hdet : lorentzDet d21 d22 d31 d32 (t2 - r1) (t3 - r1) ≠ 0) :
    ∃ x y σ : ℝ, x ^ 2 + y ^ 2 = (σ - r1) ^ 2 ∧ (x - d21) ^ 2 + (y - d22) ^ 2 = (σ - t2) ^ 2 ∧
      (x - d31) ^ 2 + (y - d32) ^ 2 = (σ - t3) ^ 2 := by
  obtain ⟨x, y, z, e1, e2, e3⟩ := lorentz_exists
    (u1 := d21) (u2 := d22) (u3 := t2 - r1) (v1 := d31) (v2 := d32) (v3 := t3 - r1)
    (m := (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) (n := (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2)
    (g1 := d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) (g2 := d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2)
    (g12 := d21 * d31 + d22 * d32 - (t2 - r1) * (t3 - r1)) rfl rfl rfl hdet (by
      have : (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) * ((d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) ^ 2 -
          2 * (d21 * d31 + d22 * d32 - (t2 - r1) * (t3 - r1)) *
            ((d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) * ((d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2) +
          (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) * ((d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2) ^ 2 =
          (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) * (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) *
            ((d21 - d31) ^ 2 + (d22 - d32) ^ 2 - (t2 - t3) ^ 2) / 4 := by ring
      rw [this]
      linarith)
  refine ⟨x, y, z + r1, by linear_combination e3, ?_, ?_⟩
  · linear_combination e3 - 2 * e1
  · linear_combination e3 - 2 * e2

end Apollonius

open Apollonius

/-- **Problem of Apollonius, nested case** (Petrunin, Problem 19.2, p. 157), in the Euclidean
plane.  Covered configuration: two circles `(O₁, r₁)`, `(O₂, r₂)` that are exterior to each other
(`r₁ + r₂ < |O₁O₂|`) and both strictly inside the third circle `(O₃, r₃)`
(`|O_iO₃| + r_i < r₃`).  Then some circle of positive radius is tangent (externally or internally)
to all three.  Together with `apollonius_exists` (three pairwise exterior circles) this covers all
pairwise disjoint configurations without separation; see `apollonius_exists_iff`. -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_nested (O₁ O₂ O₃ : EuclideanSpace ℝ (Fin 2)) {r₁ r₂ r₃ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (h12 : r₁ + r₂ < dist O₁ O₂)
    (h13 : dist O₁ O₃ + r₁ < r₃) (h23 : dist O₂ O₃ + r₂ < r₃) :
    ∃ Γ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)), 0 < Γ.radius ∧
      CirclesTangent Γ ⟨O₁, r₁⟩ ∧ CirclesTangent Γ ⟨O₂, r₂⟩ ∧ CirclesTangent Γ ⟨O₃, r₃⟩ := by
  have s12 : (r₁ + r₂) ^ 2 < (O₂ 0 - O₁ 0) ^ 2 + (O₂ 1 - O₁ 1) ^ 2 := by
    have := pow_lt_pow_left₀ h12 (by positivity) (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  have s13 : (O₃ 0 - O₁ 0) ^ 2 + (O₃ 1 - O₁ 1) ^ 2 < (r₃ - r₁) ^ 2 := by
    have := pow_lt_pow_left₀ (show dist O₁ O₃ < r₃ - r₁ by linarith) dist_nonneg (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  have s23 : ((O₂ 0 - O₁ 0) - (O₃ 0 - O₁ 0)) ^ 2 + ((O₂ 1 - O₁ 1) - (O₃ 1 - O₁ 1)) ^ 2 <
      (r₃ - r₂) ^ 2 := by
    have := pow_lt_pow_left₀ (show dist O₂ O₃ < r₃ - r₂ by linarith) dist_nonneg (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  obtain ⟨t2, t3, h2, h3, hdet⟩ := exists_pattern_gen (d21 := O₂ 0 - O₁ 0) (d22 := O₂ 1 - O₁ 1)
    (d31 := O₃ 0 - O₁ 0) (d32 := O₃ 1 - O₁ 1) hr₁ hr₂ hr₃ (by nlinarith [mul_pos hr₁ hr₂])
  have ga' : (t2 - r₁) ^ 2 ≤ (r₁ + r₂) ^ 2 := by
    rcases h2 with rfl | rfl <;> nlinarith [mul_pos hr₁ hr₂]
  have gb' : (r₃ - r₁) ^ 2 ≤ (t3 - r₁) ^ 2 := by
    rcases h3 with rfl | rfl <;> nlinarith [mul_pos hr₁ hr₃]
  have gc' : (r₃ - r₂) ^ 2 ≤ (t2 - t3) ^ 2 := by
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> nlinarith [mul_pos hr₂ hr₃]
  have ga : 0 < (O₂ 0 - O₁ 0) ^ 2 + (O₂ 1 - O₁ 1) ^ 2 - (t2 - r₁) ^ 2 := by linarith
  have gb : (O₃ 0 - O₁ 0) ^ 2 + (O₃ 1 - O₁ 1) ^ 2 - (t3 - r₁) ^ 2 < 0 := by linarith
  have gc : ((O₂ 0 - O₁ 0) - (O₃ 0 - O₁ 0)) ^ 2 + ((O₂ 1 - O₁ 1) - (O₃ 1 - O₁ 1)) ^ 2 -
      (t2 - t3) ^ 2 < 0 := by linarith
  have hQ := mul_pos (mul_pos ga (neg_pos.mpr gb)) (neg_pos.mpr gc)
  obtain ⟨x, y, σ, e1, e2, e3⟩ := apollonius_pattern_gen (r1 := r₁) (t2 := t2) (t3 := t3)
    (by linarith [hQ]) hdet
  set X : EuclideanSpace ℝ (Fin 2) := !₂[O₁ 0 + x, O₁ 1 + y] with hX
  have hX0 : X 0 = O₁ 0 + x := by simp [hX]
  have hX1 : X 1 = O₁ 1 + y := by simp [hX]
  have d1 : dist X O₁ = |σ - r₁| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e1
  have d2 : dist X O₂ = |σ - t2| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e2
  have d3 : dist X O₃ = |σ - t3| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e3
  have a1 : |t2| = r₂ := abs_of_pm hr₂ h2
  have a2 : |t3| = r₃ := abs_of_pm hr₃ h3
  have hσ : σ ≠ 0 := by
    intro h0
    have := dist_triangle O₁ X O₂
    rw [dist_comm O₁ X, d1, d2, h0, zero_sub, abs_neg, abs_of_pos hr₁, zero_sub, abs_neg, a1] at this
    linarith
  have hpos : 0 < |σ| := abs_pos.mpr hσ
  have ine : ∀ (O : EuclideanSpace ℝ (Fin 2)) (t r : ℝ), dist X O = |σ - t| → |t| = r →
      dist X O ≤ |σ| + r :=
    fun O t r hd ht => by
      rw [hd, ← ht]; exact abs_sub σ t
  refine ⟨⟨X, |σ|⟩, hpos, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hc : X = O₁ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₁ := congrArg EuclideanGeometry.Sphere.radius h
    have := ine O₂ t2 r₂ d2 a1
    rw [hc, hr] at this
    linarith
  · exact (tangent_abs hr₁ (Or.inl rfl) |>.imp (fun h => d1.trans h) (fun h => d1.trans h))
  · intro h
    have hc : X = O₂ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₂ := congrArg EuclideanGeometry.Sphere.radius h
    have := ine O₁ r₁ r₁ (by rw [d1]) (abs_of_pos hr₁)
    rw [hc, hr, dist_comm] at this
    linarith
  · exact (tangent_abs hr₂ h2 |>.imp (fun h => d2.trans h) (fun h => d2.trans h))
  · intro h
    have hc : X = O₃ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₃ := congrArg EuclideanGeometry.Sphere.radius h
    have := abs_sub_abs_le_abs_sub σ r₁
    rw [← d1, hc, hr, abs_of_pos hr₁, dist_comm] at this
    linarith
  · exact (tangent_abs hr₃ h3 |>.imp (fun h => d3.trans h) (fun h => d3.trans h))

end ApolloniusNested

section Obstruction

/-- **Problem of Apollonius, obstruction** (Petrunin, Problem 19.2, p. 157): the problem can have
no solution.  Covered configuration (in any metric space): `Ω₂` separates `Ω₁` and `Ω₃`, i.e. `Ω₁`
lies strictly inside the disc of `Ω₂` (`|O₁O₂| + r₁ < r₂`) and `Ω₃` lies outside the closed disc of
`Ω₂`, either exterior to it (`r₂ + r₃ < |O₂O₃|`) or enclosing it (`|O₂O₃| + r₂ < r₃`).  Then no
circle of nonnegative radius is tangent to all three.  (A circle tangent to `Ω₂` stays on one side
of it, while it must touch both `Ω₁` and `Ω₃`.) -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_obstruction {P : Type*} [MetricSpace P] (Ω₁ Ω₂ Ω₃ : EuclideanGeometry.Sphere P)
    (hr₁ : 0 < Ω₁.radius) (hr₃ : 0 < Ω₃.radius)
    (hin : dist Ω₁.center Ω₂.center + Ω₁.radius < Ω₂.radius)
    (hout : Ω₂.radius + Ω₃.radius < dist Ω₂.center Ω₃.center ∨
      dist Ω₂.center Ω₃.center + Ω₂.radius < Ω₃.radius) :
    ¬ ∃ Γ : EuclideanGeometry.Sphere P, 0 ≤ Γ.radius ∧ CirclesTangent Γ Ω₁ ∧
      CirclesTangent Γ Ω₂ ∧ CirclesTangent Γ Ω₃ := by
  rintro ⟨Γ, hρ, ⟨-, ha⟩, ⟨-, hb⟩, ⟨-, hc⟩⟩
  obtain ⟨X, ρ⟩ := Γ
  obtain ⟨O₁, r₁⟩ := Ω₁
  obtain ⟨O₂, r₂⟩ := Ω₂
  obtain ⟨O₃, r₃⟩ := Ω₃
  simp only at *
  have t1 := dist_triangle X O₁ O₂
  have t2 := dist_triangle X O₂ O₁
  have t3 := dist_triangle O₂ X O₃
  have t4 := dist_triangle X O₂ O₃
  rw [dist_comm O₂ X] at t3
  rw [dist_comm O₂ O₁] at t2
  have ha_le : dist X O₁ ≤ ρ + r₁ := by
    rcases ha with h | h
    · linarith
    · rw [h]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  have ha_ge : ρ - r₁ ≤ dist X O₁ := by
    rcases ha with h | h
    · linarith
    · rw [h]; exact le_abs_self _
  have hc_le : dist X O₃ ≤ ρ + r₃ := by
    rcases hc with h | h
    · linarith
    · rw [h]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc_ge : r₃ - ρ ≤ dist X O₃ := by
    rcases hc with h | h
    · linarith
    · rw [h]; exact le_abs.mpr (Or.inr (by linarith))
  rcases hb with hb | hb
  · linarith
  · rcases le_total r₂ ρ with h | h
    · rw [abs_of_nonneg (by linarith)] at hb
      linarith
    · rw [abs_of_nonpos (by linarith)] at hb
      rcases hout with ho | ho <;> linarith

/-- **Three concentric circles** (special case of `apollonius_obstruction`): if
`0 < r₁ < r₂ < r₃`, no circle of nonnegative radius is tangent to the three concentric circles of
radii `r₁, r₂, r₃` about a common centre (the middle one separates the other two). -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_concentric {P : Type*} [MetricSpace P] (O : P) {r₁ r₂ r₃ : ℝ} (hr₁ : 0 < r₁)
    (h12 : r₁ < r₂) (h23 : r₂ < r₃) :
    ¬ ∃ Γ : EuclideanGeometry.Sphere P, 0 ≤ Γ.radius ∧ CirclesTangent Γ ⟨O, r₁⟩ ∧
      CirclesTangent Γ ⟨O, r₂⟩ ∧ CirclesTangent Γ ⟨O, r₃⟩ :=
  apollonius_obstruction ⟨O, r₁⟩ ⟨O, r₂⟩ ⟨O, r₃⟩ hr₁ (by simp only; linarith)
    (by simp only [dist_self]; linarith) (Or.inr (by simp only [dist_self]; linarith))

end Obstruction

section Crossing

namespace Apollonius

theorem sign_prod {ga gb gc : ℝ}
    (h : (0 < ga ∧ 0 < gb ∧ 0 < gc) ∨ (0 < ga ∧ gb < 0 ∧ gc < 0) ∨
      (ga < 0 ∧ 0 < gb ∧ gc < 0) ∨ (ga < 0 ∧ gb < 0 ∧ 0 < gc)) : 0 ≤ ga * gb * gc := by
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact (mul_pos (mul_pos a b) c).le
  · exact (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg a b) c).le
  · exact (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos a b) c).le
  · exact (mul_pos (mul_pos_of_neg_of_neg a b) c).le

end Apollonius

open Apollonius

/-- **Problem of Apollonius, three pairwise crossing circles** (Petrunin, Problem 19.2, p. 157), in
the Euclidean plane.  Covered configuration: three circles of positive radii, any two of which meet
in exactly two points (`|r_i - r_j| < |O_iO_j| < r_i + r_j`), and which have no point in common.
Then some circle of positive radius is tangent (externally or internally) to all three.  The
hypothesis of no common point cannot be dropped: three circles of a pencil through two points have
no tangent circle of positive radius (inversion turns them into three concurrent lines).
The case of three circles through exactly one common point (non-collinear centres) is not covered. -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_crossing (O₁ O₂ O₃ : EuclideanSpace ℝ (Fin 2)) {r₁ r₂ r₃ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (h12 : |r₁ - r₂| < dist O₁ O₂) (h12' : dist O₁ O₂ < r₁ + r₂)
    (h13 : |r₁ - r₃| < dist O₁ O₃) (h13' : dist O₁ O₃ < r₁ + r₃)
    (h23 : |r₂ - r₃| < dist O₂ O₃) (h23' : dist O₂ O₃ < r₂ + r₃)
    (hcommon : ¬ ∃ P : EuclideanSpace ℝ (Fin 2),
      dist P O₁ = r₁ ∧ dist P O₂ = r₂ ∧ dist P O₃ = r₃) :
    ∃ Γ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)), 0 < Γ.radius ∧
      CirclesTangent Γ ⟨O₁, r₁⟩ ∧ CirclesTangent Γ ⟨O₂, r₂⟩ ∧ CirclesTangent Γ ⟨O₃, r₃⟩ := by
  have lo : ∀ a b d : ℝ, |a - b| < d → (a - b) ^ 2 < d ^ 2 := fun a b d h => by
    have := pow_lt_pow_left₀ h (abs_nonneg _) (two_ne_zero)
    rwa [sq_abs] at this
  have hi : ∀ a b d : ℝ, 0 < a → 0 < b → d < a + b → 0 ≤ d → d ^ 2 < (a + b) ^ 2 :=
    fun a b d ha hb h hd => pow_lt_pow_left₀ h hd (two_ne_zero)
  have s12 := lo _ _ _ h12
  have s13 := lo _ _ _ h13
  have s23 := lo _ _ _ h23
  have u12 := hi _ _ _ hr₁ hr₂ h12' dist_nonneg
  have u13 := hi _ _ _ hr₁ hr₃ h13' dist_nonneg
  have u23 := hi _ _ _ hr₂ hr₃ h23' dist_nonneg
  rw [dist_sq_coords] at s12 s13 s23 u12 u13 u23
  have hA : 0 < (O₂ 0 - O₁ 0) ^ 2 + (O₂ 1 - O₁ 1) ^ 2 := by nlinarith [sq_nonneg (r₁ - r₂)]
  obtain ⟨t2, t3, h2, h3, hdet⟩ := exists_pattern_gen (d21 := O₂ 0 - O₁ 0) (d22 := O₂ 1 - O₁ 1)
    (d31 := O₃ 0 - O₁ 0) (d32 := O₃ 1 - O₁ 1) hr₁ hr₂ hr₃ hA
  have hQ : 0 ≤ ((O₂ 0 - O₁ 0) ^ 2 + (O₂ 1 - O₁ 1) ^ 2 - (t2 - r₁) ^ 2) *
      ((O₃ 0 - O₁ 0) ^ 2 + (O₃ 1 - O₁ 1) ^ 2 - (t3 - r₁) ^ 2) *
      (((O₂ 0 - O₁ 0) - (O₃ 0 - O₁ 0)) ^ 2 + ((O₂ 1 - O₁ 1) - (O₃ 1 - O₁ 1)) ^ 2 -
        (t2 - t3) ^ 2) := by
    apply sign_prod
    rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl
    · left; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · right; right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith
    · right; right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith
  obtain ⟨x, y, σ, e1, e2, e3⟩ := apollonius_pattern_gen (r1 := r₁) (t2 := t2) (t3 := t3) hQ hdet
  set X : EuclideanSpace ℝ (Fin 2) := !₂[O₁ 0 + x, O₁ 1 + y] with hX
  have hX0 : X 0 = O₁ 0 + x := by simp [hX]
  have hX1 : X 1 = O₁ 1 + y := by simp [hX]
  have d1 : dist X O₁ = |σ - r₁| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e1
  have d2 : dist X O₂ = |σ - t2| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e2
  have d3 : dist X O₃ = |σ - t3| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e3
  have a1 : |t2| = r₂ := abs_of_pm hr₂ h2
  have a2 : |t3| = r₃ := abs_of_pm hr₃ h3
  have hσ : σ ≠ 0 := by
    intro h0
    refine hcommon ⟨X, ?_, ?_, ?_⟩
    · rw [d1, h0, zero_sub, abs_neg, abs_of_pos hr₁]
    · rw [d2, h0, zero_sub, abs_neg, a1]
    · rw [d3, h0, zero_sub, abs_neg, a2]
  have hpos : 0 < |σ| := abs_pos.mpr hσ
  have tg1 := tangent_abs (σ := σ) hr₁ (Or.inl rfl : r₁ = r₁ ∨ r₁ = -r₁)
  have tg2 := tangent_abs (σ := σ) hr₂ h2
  have tg3 := tangent_abs (σ := σ) hr₃ h3
  refine ⟨⟨X, |σ|⟩, hpos, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hc : X = O₁ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₁ := congrArg EuclideanGeometry.Sphere.radius h
    have e : dist O₁ O₂ = |σ - t2| := by rw [← hc]; exact d2
    rcases tg2 with t | t <;> rw [t, hr] at e <;> linarith
  · exact (tg1.imp (fun h => d1.trans h) (fun h => d1.trans h))
  · intro h
    have hc : X = O₂ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₂ := congrArg EuclideanGeometry.Sphere.radius h
    have e : dist O₂ O₁ = |σ - r₁| := by rw [← hc]; exact d1
    have := dist_comm O₁ O₂
    have := abs_sub_comm r₁ r₂
    rcases tg1 with t | t <;> rw [t, hr] at e <;> linarith
  · exact (tg2.imp (fun h => d2.trans h) (fun h => d2.trans h))
  · intro h
    have hc : X = O₃ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₃ := congrArg EuclideanGeometry.Sphere.radius h
    have e : dist O₃ O₁ = |σ - r₁| := by rw [← hc]; exact d1
    have := dist_comm O₁ O₃
    have := abs_sub_comm r₁ r₃
    rcases tg1 with t | t <;> rw [t, hr] at e <;> linarith
  · exact (tg3.imp (fun h => d3.trans h) (fun h => d3.trans h))

end Crossing

section Classification

namespace Apollonius

abbrev Circ := EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))

/-- The circle `Ω` is exterior to `Ω'`: the two discs are disjoint. -/
def CircExt (Ω Ω' : Circ) : Prop :=
  Ω.radius + Ω'.radius < dist Ω.center Ω'.center

/-- The circle `Ω` lies strictly inside the open disc of `Ω'`. -/
def CircInside (Ω Ω' : Circ) : Prop :=
  dist Ω.center Ω'.center + Ω.radius < Ω'.radius

/-- Two circles are disjoint (as sets, for positive radii): exterior, or one inside the other. -/
def CircDisjoint (Ω Ω' : Circ) : Prop :=
  CircExt Ω Ω' ∨ CircInside Ω Ω' ∨ CircInside Ω' Ω

/-- `Ω₂` separates `Ω₁` from `Ω₃`: one of them is strictly inside the disc of `Ω₂`, the other lies
outside its closed disc (exterior to it, or enclosing it). -/
def CircSeparates (Ω₂ Ω₁ Ω₃ : Circ) : Prop :=
  (CircInside Ω₁ Ω₂ ∧ (CircExt Ω₂ Ω₃ ∨ CircInside Ω₂ Ω₃)) ∨
    (CircInside Ω₃ Ω₂ ∧ (CircExt Ω₂ Ω₁ ∨ CircInside Ω₂ Ω₁))

theorem circExt_symm {Ω Ω' : Circ} (h : CircExt Ω Ω') : CircExt Ω' Ω := by
  unfold CircExt at *; rw [dist_comm]; linarith

theorem ex_ext (Ω₁ Ω₂ Ω₃ : Circ) (h₁ : 0 < Ω₁.radius) (h₂ : 0 < Ω₂.radius) (h₃ : 0 < Ω₃.radius)
    (e12 : CircExt Ω₁ Ω₂) (e13 : CircExt Ω₁ Ω₃) (e23 : CircExt Ω₂ Ω₃) :
    ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₂ ∧
      CirclesTangent Γ Ω₃ :=
  apollonius_exists Ω₁.center Ω₂.center Ω₃.center h₁ h₂ h₃ e12 e13 e23

theorem ex_nest (Ω₁ Ω₂ Ω₃ : Circ) (h₁ : 0 < Ω₁.radius) (h₂ : 0 < Ω₂.radius) (h₃ : 0 < Ω₃.radius)
    (e12 : CircExt Ω₁ Ω₂) (i13 : CircInside Ω₁ Ω₃) (i23 : CircInside Ω₂ Ω₃) :
    ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₂ ∧
      CirclesTangent Γ Ω₃ :=
  apollonius_nested Ω₁.center Ω₂.center Ω₃.center h₁ h₂ h₃ e12 i13 i23

theorem ex_perm_a {Ω₁ Ω₂ Ω₃ : Circ}
    (h : ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₃ ∧
      CirclesTangent Γ Ω₂) :
    ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₂ ∧
      CirclesTangent Γ Ω₃ := by
  obtain ⟨Γ, h, a, b, c⟩ := h
  exact ⟨Γ, h, a, c, b⟩

theorem ex_perm_b {Ω₁ Ω₂ Ω₃ : Circ}
    (h : ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₂ ∧ CirclesTangent Γ Ω₃ ∧
      CirclesTangent Γ Ω₁) :
    ∃ Γ : Circ, 0 < Γ.radius ∧ CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₂ ∧
      CirclesTangent Γ Ω₃ := by
  obtain ⟨Γ, h, a, b, c⟩ := h
  exact ⟨Γ, h, c, a, b⟩

end Apollonius

open Apollonius

/-- **Problem of Apollonius, complete answer for disjoint circles** (Petrunin, Problem 19.2,
p. 157), in the Euclidean plane.  Covered configuration: three circles of positive radii that are
pairwise disjoint (each pair exterior, or one strictly inside the other).  Then a circle tangent
(externally or internally) to all three exists iff none of the three circles separates the other
two.  The `←` direction combines `apollonius_exists` and `apollonius_nested` (the only
non-separating disjoint configurations are three exterior circles, or two exterior circles inside
the third); the `→` direction is `apollonius_obstruction`. -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_exists_iff (Ω₁ Ω₂ Ω₃ : Circ)
    (h₁ : 0 < Ω₁.radius) (h₂ : 0 < Ω₂.radius) (h₃ : 0 < Ω₃.radius)
    (d12 : CircDisjoint Ω₁ Ω₂) (d13 : CircDisjoint Ω₁ Ω₃) (d23 : CircDisjoint Ω₂ Ω₃) :
    (∃ Γ : Circ, 0 < Γ.radius ∧
      CirclesTangent Γ Ω₁ ∧ CirclesTangent Γ Ω₂ ∧ CirclesTangent Γ Ω₃) ↔
    ¬ (CircSeparates Ω₁ Ω₂ Ω₃ ∨ CircSeparates Ω₂ Ω₁ Ω₃ ∨ CircSeparates Ω₃ Ω₁ Ω₂) := by
  constructor
  · rintro ⟨Γ, hρ, a, b, c⟩ hsep
    rcases hsep with hs | hs | hs
    · rcases hs with ⟨i, o⟩ | ⟨i, o⟩
      · exact apollonius_obstruction Ω₂ Ω₁ Ω₃ h₂ h₃ i o ⟨Γ, hρ.le, b, a, c⟩
      · exact apollonius_obstruction Ω₃ Ω₁ Ω₂ h₃ h₂ i o ⟨Γ, hρ.le, c, a, b⟩
    · rcases hs with ⟨i, o⟩ | ⟨i, o⟩
      · exact apollonius_obstruction Ω₁ Ω₂ Ω₃ h₁ h₃ i o ⟨Γ, hρ.le, a, b, c⟩
      · exact apollonius_obstruction Ω₃ Ω₂ Ω₁ h₃ h₁ i o ⟨Γ, hρ.le, c, b, a⟩
    · rcases hs with ⟨i, o⟩ | ⟨i, o⟩
      · exact apollonius_obstruction Ω₁ Ω₃ Ω₂ h₁ h₂ i o ⟨Γ, hρ.le, a, c, b⟩
      · exact apollonius_obstruction Ω₂ Ω₃ Ω₁ h₂ h₁ i o ⟨Γ, hρ.le, b, c, a⟩
  · intro hns
    have t12 := dist_triangle Ω₁.center Ω₂.center Ω₃.center
    have t13 := dist_triangle Ω₁.center Ω₃.center Ω₂.center
    have t23 := dist_triangle Ω₂.center Ω₁.center Ω₃.center
    have c12 := dist_comm Ω₁.center Ω₂.center
    have c13 := dist_comm Ω₁.center Ω₃.center
    have c23 := dist_comm Ω₂.center Ω₃.center
    have s12 := @circExt_symm Ω₁ Ω₂
    have s13 := @circExt_symm Ω₁ Ω₃
    have s23 := @circExt_symm Ω₂ Ω₃
    have s21 := @circExt_symm Ω₂ Ω₁
    have s31 := @circExt_symm Ω₃ Ω₁
    have s32 := @circExt_symm Ω₃ Ω₂
    unfold CircDisjoint at d12 d13 d23
    rcases d12 with e12 | i12 | j12 <;> rcases d13 with e13 | i13 | j13 <;>
      rcases d23 with e23 | i23 | j23 <;>
      first
      | (refine ex_ext Ω₁ Ω₂ Ω₃ h₁ h₂ h₃ ?_ ?_ ?_ <;> assumption)
      | (refine ex_nest Ω₁ Ω₂ Ω₃ h₁ h₂ h₃ ?_ ?_ ?_ <;> assumption)
      | (refine ex_perm_a (ex_nest Ω₁ Ω₃ Ω₂ h₁ h₃ h₂ ?_ ?_ ?_) <;> assumption)
      | (refine ex_perm_b (ex_nest Ω₂ Ω₃ Ω₁ h₂ h₃ h₁ ?_ ?_ ?_) <;> assumption)
      | (exfalso; first
          | (clear hns s12 s13 s23 s21 s31 s32; simp only [CircExt, CircInside] at *; linarith)
          | (clear t12 t13 t23 c12 c13 c23 h₁ h₂ h₃; apply hns; clear hns; simp [CircSeparates, *]))

end Classification

end UndergradKB.Geometry
