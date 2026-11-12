import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.KleinModel2
import UndergradKB.Geometry.HypAngles
import UndergradKB.Geometry.ProjectivePlane2
import UndergradKB.Geometry.FractionalLinear
import UndergradKB.Geometry.InversiveClassification
import Mathlib.Analysis.Complex.Isometry

/-! # The projective model, continued (Petrunin, Remark p. 143 and chapter 13C, pp. 105-107)

* Every h-motion `z ↦ u · (z - a)/(1 - ā z)` of the conformal model acts on the projective model
  `P ↦ P̂` by a real fractional-linear map of the plane, i.e. a projective transformation given by an
  invertible `3 × 3` real matrix (Remark p. 143).
* Equidistants of an arbitrary h-line `hline α c` (pp. 105-107): the h-points at h-distance `r` from the
  h-line form the part in the disc of two Euclidean circles through its ideal points. -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-! ### Fractional-linear maps of the plane -/

section FracLin

/-- The projective transformation of the affine plane `ℂ ≅ ℝ²` given by a `3 × 3` real matrix:
`(x, y) ↦ ((M₀₀x + M₀₁y + M₀₂)/(M₂₀x + M₂₁y + M₂₂), (M₁₀x + M₁₁y + M₁₂)/(M₂₀x + M₂₁y + M₂₂))`. -/
noncomputable def fracLin (M : Matrix (Fin 3) (Fin 3) ℝ) (X : ℂ) : ℂ :=
  ⟨(M 0 0 * X.re + M 0 1 * X.im + M 0 2) / (M 2 0 * X.re + M 2 1 * X.im + M 2 2),
    (M 1 0 * X.re + M 1 1 * X.im + M 1 2) / (M 2 0 * X.re + M 2 1 * X.im + M 2 2)⟩

/-- The denominator of `fracLin M` at `X`. -/
def fracDen (M : Matrix (Fin 3) (Fin 3) ℝ) (X : ℂ) : ℝ := M 2 0 * X.re + M 2 1 * X.im + M 2 2

theorem row_div (P0 P1 P2 n0 n1 d : ℝ) (hd : d ≠ 0) :
    P0 * (n0 / d) + P1 * (n1 / d) + P2 = (P0 * n0 + P1 * n1 + P2 * d) / d := by
  field_simp

theorem fracLin_mul(M N : Matrix (Fin 3) (Fin 3) ℝ) (X : ℂ) (hN : fracDen N X ≠ 0) :
    fracLin M (fracLin N X) = fracLin (M * N) X ∧
      fracDen (M * N) X = fracDen M (fracLin N X) * fracDen N X := by
  unfold fracDen at hN
  constructor
  · apply Complex.ext
    · simp only [fracLin, Matrix.mul_apply, Fin.sum_univ_three]
      rw [row_div _ _ _ _ _ _ hN, row_div _ _ _ _ _ _ hN, div_div_div_cancel_right₀ hN]
      congr 1 <;> ring
    · simp only [fracLin, Matrix.mul_apply, Fin.sum_univ_three]
      rw [row_div _ _ _ _ _ _ hN, row_div _ _ _ _ _ _ hN, div_div_div_cancel_right₀ hN]
      congr 1 <;> ring
  · simp only [fracDen, fracLin, Matrix.mul_apply, Fin.sum_univ_three]
    rw [row_div _ _ _ _ _ _ hN]
    field_simp
    ring

/-- The rotation by the unit complex number `u`, as a matrix. -/
def rotMat (u : ℂ) : Matrix (Fin 3) (Fin 3) ℝ := !![u.re, -u.im, 0; u.im, u.re, 0; 0, 0, 1]

theorem fracLin_rotMat (u X : ℂ) : fracLin (rotMat u) X = u * X := by
  apply Complex.ext <;> simp [fracLin, rotMat, Complex.mul_re, Complex.mul_im] <;> ring

theorem fracDen_rotMat (u X : ℂ) : fracDen (rotMat u) X = 1 := by simp [fracDen, rotMat]

theorem det_rotMat {u : ℂ} (hu : ‖u‖ = 1) : (rotMat u).det ≠ 0 := by
  have := sq_norm_eq u
  rw [hu] at this
  rw [Matrix.det_fin_three]
  simp [rotMat]
  nlinarith

/-- The matrix of the boost `projBoost a`. -/
noncomputable def boostMat (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, -(2 * a / (1 + a ^ 2)); 0, (1 - a ^ 2) / (1 + a ^ 2), 0; -(2 * a / (1 + a ^ 2)), 0, 1]

theorem fracLin_boostMat (a : ℝ) (X : ℂ) : fracLin (boostMat a) X = projBoost a X := by
  apply Complex.ext <;> simp [fracLin, boostMat, projBoost] <;> ring_nf

theorem fracDen_boostMat (a : ℝ) (X : ℂ) :
    fracDen (boostMat a) X = 1 - 2 * a / (1 + a ^ 2) * X.re := by
  simp [fracDen, boostMat]; ring

theorem det_boostMat {a : ℝ} (ha : |a| < 1) : (boostMat a).det ≠ 0 := by
  have ha2 : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).mpr ha
  have hp : 0 < 1 + a ^ 2 := by positivity
  rw [Matrix.det_fin_three]
  simp [boostMat]
  have h1 : (1 - a ^ 2) / (1 + a ^ 2) ≠ 0 := (div_pos (by linarith) hp).ne'
  have h2 : 1 - (2 * a / (1 + a ^ 2)) ^ 2 ≠ 0 := by
    have : 1 - (2 * a / (1 + a ^ 2)) ^ 2 = ((1 - a ^ 2) / (1 + a ^ 2)) ^ 2 := by
      field_simp; ring
    rw [this]; exact pow_ne_zero 2 h1
  intro h
  apply mul_ne_zero h1 h2
  linear_combination h

theorem mobius_polar {a w z : ℂ} {r : ℝ} (hw : ‖w‖ = 1) (har : a = (r : ℂ) * w) (ha : ‖a‖ < 1)
    (hz : ‖z‖ < 1) : mobius a z = w * mobius (r : ℂ) (conj w * z) := by
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; simp
  have hden : 1 - conj a * z ≠ 0 := mobius_den_ne ha hz
  have hc : conj a = (r : ℂ) * conj w := by rw [har]; simp
  unfold mobius
  rw [Complex.conj_ofReal]
  have hd2 : 1 - (r : ℂ) * (conj w * z) ≠ 0 := by
    rw [← mul_assoc, ← hc]; exact hden
  rw [hc] at hden ⊢
  rw [← mul_div_assoc, div_eq_div_iff hden hd2, har]
  linear_combination (-z * (1 - (r : ℂ) * (conj w * z))) * hww

end FracLin

/-! ### Motions in the projective model (Remark p. 143) -/

section Motions

/-- Remark p. 143: every h-motion `z ↦ u · (z - a)/(1 - ā z)` of the conformal model (`‖u‖ = 1`,
`‖a‖ < 1`) is, in the projective model `P ↦ P̂`, a projective transformation: there is an invertible
real `3 × 3` matrix `M` with `(u · mobius a z)^ = fracLin M (ẑ)` for every point `z` of the h-plane.
(`KleinModel2` has the case of a real `a`; the general case composes it with rotations.) -/
@[kb "petrunin2025" "Section 17B, Motions, p. 143"]
theorem kleinMap_motion_projective {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ z : ℂ, ‖z‖ < 1 → fracDen M (kleinMap z) ≠ 0 ∧
        kleinMap (u * mobius a z) = fracLin M (kleinMap z) := by
  obtain ⟨w, hw, har⟩ : ∃ w : ℂ, ‖w‖ = 1 ∧ a = (‖a‖ : ℂ) * w := by
    by_cases h0 : a = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · refine ⟨a / (‖a‖ : ℂ), ?_, ?_⟩
      · rw [norm_div]; simp [h0]
      · have : (‖a‖ : ℂ) ≠ 0 := by simpa using h0
        field_simp
  set r := ‖a‖ with hr
  have hr1 : |r| < 1 := by rw [abs_of_nonneg (norm_nonneg a)]; exact ha
  have hcw : ‖conj w‖ = 1 := by rw [Complex.norm_conj, hw]
  have huw : ‖u * w‖ = 1 := by rw [norm_mul, hu, hw, one_mul]
  refine ⟨rotMat (u * w) * (boostMat r * rotMat (conj w)), ?_, fun z hz => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (det_rotMat huw) (mul_ne_zero (det_boostMat hr1) (det_rotMat hcw))
  · have hz' : ‖conj w * z‖ < 1 := by rw [norm_mul, hcw, one_mul]; exact hz
    have h1 : kleinMap (u * mobius a z) = (u * w) * projBoost r (conj w * kleinMap z) := by
      rw [mobius_polar hw har ha hz, ← mul_assoc, kleinMap_rotation huw,
        kleinMap_mobius_real hr1 hz', kleinMap_rotation hcw]
    have hX : ‖conj w * kleinMap z‖ < 1 := by
      rw [norm_mul, hcw, one_mul]; exact norm_kleinMap_lt_one hz
    have hd1 : fracDen (rotMat (conj w)) (kleinMap z) ≠ 0 := by rw [fracDen_rotMat]; exact one_ne_zero
    obtain ⟨e1, d1⟩ := fracLin_mul (boostMat r) (rotMat (conj w)) (kleinMap z) hd1
    have hd2 : fracDen (boostMat r * rotMat (conj w)) (kleinMap z) ≠ 0 := by
      rw [d1, fracDen_rotMat, mul_one, fracDen_boostMat, fracLin_rotMat]
      have hre : |(conj w * kleinMap z).re| < 1 :=
        lt_of_le_of_lt (Complex.abs_re_le_norm _) hX
      have hv : |2 * r / (1 + r ^ 2)| < 1 := by
        have hp : 0 < 1 + r ^ 2 := by positivity
        rw [abs_div, abs_of_pos hp, div_lt_one hp, abs_mul]
        have := sq_nonneg (|r| - 1)
        have h2 : (|r|) ^ 2 = r ^ 2 := sq_abs r
        rw [abs_two]; nlinarith [abs_nonneg r]
      have : |2 * r / (1 + r ^ 2) * (conj w * kleinMap z).re| < 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (2 * r / (1 + r ^ 2)), abs_nonneg (conj w * kleinMap z).re]
      rw [abs_lt] at this; linarith [this.2]
    obtain ⟨e2, d2⟩ := fracLin_mul (rotMat (u * w)) (boostMat r * rotMat (conj w)) (kleinMap z) hd2
    refine ⟨by rw [d2, fracDen_rotMat, one_mul]; exact hd2, ?_⟩
    rw [h1, ← e2, ← e1, fracLin_rotMat, fracLin_boostMat, fracLin_rotMat]

/-! #### The link with `IsProjectiveTransformation` -/

/-- The vector `(x, y, 1)` of the space model representing the affine point `x + i y`. -/
noncomputable def affVec (X : ℂ) : Space3 := !₂[X.re, X.im, 1]

theorem affVec_ne_zero (X : ℂ) : affVec X ≠ 0 := by
  intro h
  have := congrArg (fun v : Space3 => v 2) h
  simp [affVec] at this

/-- The point of the projective plane (space model) corresponding to the affine point `X`. -/
noncomputable def affPt (X : ℂ) : ProjPoint := ProjPoint.mk' (affVec X) (affVec_ne_zero X)

/-- The projective transformation induced by an invertible matrix acts on the affine points `[x, y, 1]`
as the fractional-linear map `fracLin M`, whenever the denominator is nonzero. -/
theorem map_affPt (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0) (X : ℂ)
    (hd : fracDen M X ≠ 0) :
    ProjPoint.map (glOfMatrix M h) (affPt X) = affPt (fracLin M X) := by
  unfold affPt
  rw [ProjPoint.map_mk', ProjPoint.mk'_eq_iff]
  refine ⟨(fracDen M X)⁻¹, ?_⟩
  unfold fracDen at hd ⊢
  ext i
  fin_cases i
  · simp [glOfMatrix_apply, affVec, fracLin]
    field_simp
  · simp [glOfMatrix_apply, affVec, fracLin]
    field_simp
  · simp [glOfMatrix_apply, affVec, fracLin]
    field_simp

/-- Remark p. 143 (motions of the projective model are projective transformations): every h-motion
`z ↦ u · (z - a)/(1 - ā z)` of the conformal model acts, via `P ↦ P̂` and the embedding
`X ↦ [X.re, X.im, 1]` of the plane in the projective plane, as the restriction of a projective
transformation `IsProjectiveTransformation` of the whole projective plane. -/
@[kb "petrunin2025" "Section 17B, Motions, p. 143"]
theorem kleinMap_motion_isProjective {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) :
    ∃ (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0),
      IsProjectiveTransformation (ProjPoint.map (glOfMatrix M h)) ∧
        ∀ z : ℂ, ‖z‖ < 1 →
          ProjPoint.map (glOfMatrix M h) (affPt (kleinMap z)) = affPt (kleinMap (u * mobius a z)) := by
  obtain ⟨M, hM, hz⟩ := kleinMap_motion_projective ha hu
  refine ⟨M, hM, isProjectiveTransformation_map _, fun z hz1 => ?_⟩
  obtain ⟨hd, he⟩ := hz z hz1
  rw [map_affPt M hM _ hd, he]

end Motions

/-! ### Equidistants of an arbitrary h-line (chapter 13C, pp. 105-107) -/

section Equidistant

/-- Real-algebra core: the lower bound `cosh² d ≥ 1 + (x-α)²/(Q m)` for the distance from a point
(with Klein coordinates `x, y` in the frame of the chord) to a point of the chord at height `s`. -/
theorem equid_core {N α x y m s K2 : ℝ} (hN : 0 < N) (hQ : 0 < N - α ^ 2) (hm : 0 < m)
    (hs : s ^ 2 < N - α ^ 2) (hy : N * (1 - m) = x ^ 2 + y ^ 2)
    (hK : K2 * (N * m * (N - α ^ 2 - s ^ 2)) = (N - α * x - s * y) ^ 2) :
    1 + (x - α) ^ 2 / ((N - α ^ 2) * m) ≤ K2 := by
  have e3 : (N - α * x) ^ 2 - (N - α ^ 2) * y ^ 2 = N * ((x - α) ^ 2 + (N - α ^ 2) * m) := by
    linear_combination (N - α ^ 2) * hy
  have hs' : 0 < N - α ^ 2 - s ^ 2 := by linarith
  have hQm : 0 < (N - α ^ 2) * m := mul_pos hQ hm
  have e0 : 1 + (x - α) ^ 2 / ((N - α ^ 2) * m) = ((x - α) ^ 2 + (N - α ^ 2) * m) / ((N - α ^ 2) * m) := by
    field_simp
    ring
  rw [e0, div_le_iff₀ hQm]
  refine le_of_mul_le_mul_right ?_ (mul_pos hN hs')
  have : K2 * ((N - α ^ 2) * m) * (N * (N - α ^ 2 - s ^ 2)) =
      ((x - α) ^ 2 + (N - α ^ 2) * m) * (N * (N - α ^ 2 - s ^ 2)) +
        ((N - α * x) * s - (N - α ^ 2) * y) ^ 2 := by
    linear_combination (N - α ^ 2) * hK + (N - α ^ 2 - s ^ 2) * e3
  rw [this]
  nlinarith [sq_nonneg (((N - α * x) * s - (N - α ^ 2) * y))]

theorem equid_B_pos {N α x y m : ℝ} (hN : 0 < N) (hQ : 0 < N - α ^ 2) (hm : 0 < m)
    (hy : N * (1 - m) = x ^ 2 + y ^ 2) : 0 < N - α * x := by
  have hx2 : x ^ 2 < N := by nlinarith [sq_nonneg y]
  have h1 : (α * x) ^ 2 < N ^ 2 := by
    have : α ^ 2 * x ^ 2 ≤ α ^ 2 * N := mul_le_mul_of_nonneg_left hx2.le (sq_nonneg α)
    nlinarith [sq_nonneg α]
  have := abs_lt_of_sq_lt_sq h1 hN.le
  rw [abs_lt] at this
  linarith [this.2]

theorem equid_eq {N α x y m s K2 : ℝ} (hN : 0 < N) (hQ : 0 < N - α ^ 2) (hm : 0 < m)
    (hy : N * (1 - m) = x ^ 2 + y ^ 2) (hs : s = (N - α ^ 2) * y / (N - α * x))
    (hK : K2 * (N * m * (N - α ^ 2 - s ^ 2)) = (N - α * x - s * y) ^ 2) :
    K2 = 1 + (x - α) ^ 2 / ((N - α ^ 2) * m) := by
  have hB := equid_B_pos hN hQ hm hy
  have e3 : (N - α * x) ^ 2 - (N - α ^ 2) * y ^ 2 = N * ((x - α) ^ 2 + (N - α ^ 2) * m) := by
    linear_combination (N - α ^ 2) * hy
  set B := N - α * x with hBdef
  set Q := N - α ^ 2 with hQdef
  have hΔ : 0 < B ^ 2 - Q * y ^ 2 := by
    rw [e3]; have := sq_nonneg (x - α); positivity
  have h1 : B - s * y = (B ^ 2 - Q * y ^ 2) / B := by rw [hs]; field_simp
  have h2 : Q - s ^ 2 = Q * (B ^ 2 - Q * y ^ 2) / B ^ 2 := by rw [hs]; field_simp
  have hΔ' : 0 < B ^ 2 - Q * y ^ 2 := hΔ
  have hK' : K2 * (N * m * (Q * (B ^ 2 - Q * y ^ 2) / B ^ 2)) = ((B ^ 2 - Q * y ^ 2) / B) ^ 2 := by
    rw [← h2, ← h1]; exact hK
  have : K2 = (B ^ 2 - Q * y ^ 2) / (N * m * Q) := by
    field_simp at hK' ⊢
    have hne := hΔ'.ne'
    apply mul_left_cancel₀ hne
    nlinarith [hK']
  rw [this, e3]
  field_simp
  ring

/-- The Klein-model computation of the chord form of `kcosh`: for `Y` in the chord
`Re (c̄ Y) = α`, writing `s = Im (c̄ Y)`,
`kcosh² · N (1-‖X‖²) (N - α² - s²) = (N - α Re (c̄X) - s Im (c̄X))²` with `N = ‖c‖²`. -/
theorem kcosh_sq_chord {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) {α : ℝ} {c : ℂ} (hc : c ≠ 0)
    (hre : (conj c * Y).re = α) :
    kcosh X Y ^ 2 * (‖c‖ ^ 2 * (1 - ‖X‖ ^ 2) * (‖c‖ ^ 2 - α ^ 2 - (conj c * Y).im ^ 2)) =
      (‖c‖ ^ 2 - α * (conj c * X).re - (conj c * Y).im * (conj c * X).im) ^ 2 := by
  have hm := one_sub_sq_pos hX
  have hu := one_sub_sq_pos hY
  have hN : 0 < ‖c‖ ^ 2 := by have := norm_pos_iff.mpr hc; positivity
  have h1 : ‖c‖ ^ 2 - α ^ 2 - (conj c * Y).im ^ 2 = ‖c‖ ^ 2 * (1 - ‖Y‖ ^ 2) := by
    have := normsq_dot c Y
    rw [hre] at this; linarith
  have h2 : ‖c‖ ^ 2 - α * (conj c * X).re - (conj c * Y).im * (conj c * X).im =
      ‖c‖ ^ 2 * (1 - (conj X * Y).re) := by
    have := dot_identity c X Y
    rw [hre] at this; linarith
  unfold kcosh
  rw [div_pow, Real.sq_sqrt (mul_pos hm hu).le, h1, h2]
  field_simp

theorem exists_foot {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ F ∈ hline α c, IsLeast (hdist z '' hline α c) (hdist z F) ∧
      Real.sinh (hdist z F) ^ 2 =
        ((conj c * kleinMap z).re - α) ^ 2 /
          ((‖c‖ ^ 2 - α ^ 2) * (1 - ‖kleinMap z‖ ^ 2)) := by
  have hc : c ≠ 0 := c_ne_zero h
  set X := kleinMap z with hXdef
  have hX : ‖X‖ < 1 := norm_kleinMap_lt_one hz
  set N := ‖c‖ ^ 2 with hNdef
  have hN : 0 < N := by have := norm_pos_iff.mpr hc; positivity
  have hQ : 0 < N - α ^ 2 := by linarith
  set m := 1 - ‖X‖ ^ 2 with hmdef
  have hm : 0 < m := one_sub_sq_pos hX
  set x := (conj c * X).re with hx
  set y := (conj c * X).im with hy
  have hy' : N * (1 - m) = x ^ 2 + y ^ 2 := by
    have := normsq_dot c X
    rw [hmdef]; linear_combination this
  have hB := equid_B_pos hN hQ hm hy'
  set s0 := (N - α ^ 2) * y / (N - α * x) with hs0
  have e3 : (N - α * x) ^ 2 - (N - α ^ 2) * y ^ 2 = N * ((x - α) ^ 2 + (N - α ^ 2) * m) := by
    linear_combination (N - α ^ 2) * hy'
  have hs0lt : s0 ^ 2 < N - α ^ 2 := by
    rw [hs0, div_pow, div_lt_iff₀ (by positivity)]
    have : 0 < N * ((x - α) ^ 2 + (N - α ^ 2) * m) := by
      have := sq_nonneg (x - α); positivity
    nlinarith [e3]
  -- the foot
  set Y : ℂ := c * (((α : ℂ) + (s0 : ℂ) * Complex.I) / ((‖c‖ : ℂ) ^ 2)) with hY
  have hcY : conj c * Y = (α : ℂ) + (s0 : ℂ) * Complex.I := by
    have hcc : conj c * c = ((‖c‖ : ℂ) ^ 2) := by
      rw [Complex.conj_mul']
    have hne : ((‖c‖ : ℂ) ^ 2) ≠ 0 := by
      have : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
      exact pow_ne_zero 2 this
    rw [hY, ← mul_assoc, hcc, mul_div_assoc', mul_div_cancel_left₀ _ hne]
  have hYre : (conj c * Y).re = α := by rw [hcY]; simp
  have hYim : (conj c * Y).im = s0 := by rw [hcY]; simp
  have hYn : ‖Y‖ < 1 := by
    have := normsq_dot c Y
    rw [hYre, hYim, ← hNdef] at this
    by_contra hge
    rw [not_lt] at hge
    have h1 : 1 ≤ ‖Y‖ ^ 2 := by nlinarith [norm_nonneg Y]
    nlinarith [mul_le_mul_of_nonneg_left h1 hN.le]
  have hYchord : Y ∈ chord α c := ⟨hYn, hYre⟩
  rw [← kleinMap_image_hline] at hYchord
  obtain ⟨F, hF, hFY⟩ := hYchord
  have hFn : ‖F‖ < 1 := hF.1
  -- cosh² along the line
  have hcosh_sq : ∀ w ∈ hline α c, 1 + (x - α) ^ 2 / ((N - α ^ 2) * m) ≤ Real.cosh (hdist z w) ^ 2 := by
    intro w hw
    have hwn : ‖w‖ < 1 := hw.1
    have hYw : ‖kleinMap w‖ < 1 := norm_kleinMap_lt_one hwn
    have hre := re_conj_mul_kleinMap_of_hline hw
    have key := kcosh_sq_chord hX hYw hc hre
    have hsq : (conj c * kleinMap w).im ^ 2 < N - α ^ 2 := by
      have := normsq_dot c (kleinMap w)
      rw [hre] at this
      have h1 : ‖kleinMap w‖ ^ 2 < 1 := by nlinarith [norm_nonneg (kleinMap w)]
      nlinarith [hN]
    rw [cosh_hdist hz hwn, hcosh_eq_kcosh z w hz hwn]
    exact equid_core hN hQ hm hsq hy' key
  have hcosh_F : Real.cosh (hdist z F) ^ 2 = 1 + (x - α) ^ 2 / ((N - α ^ 2) * m) := by
    have key := kcosh_sq_chord hX hYn hc hYre
    rw [hYim] at key
    rw [cosh_hdist hz hFn, hcosh_eq_kcosh z F hz hFn, hFY]
    exact equid_eq hN hQ hm hy' hs0 key
  refine ⟨F, hF, ⟨⟨F, hF, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have h1 := cosh_hdist hz hFn
    have h2 := cosh_hdist hz hw.1
    have hle : Real.cosh (hdist z F) ≤ Real.cosh (hdist z w) := by
      exact (sq_le_sq₀ (Real.cosh_pos _).le (Real.cosh_pos _).le).mp
        (by rw [hcosh_F]; exact hcosh_sq w hw)
    have := Real.cosh_le_cosh.mp hle
    rwa [abs_of_nonneg (hdist_nonneg hz hFn), abs_of_nonneg (hdist_nonneg hz hw.1)] at this
  · have := Real.cosh_sq (hdist z F)
    rw [hcosh_F] at this
    linarith

/-- Section 13C (Equidistants), an arbitrary h-line `hline α c`: for a point `z` of the h-plane, `r`
is the h-distance from `z` to the h-line (the least h-distance to its points) iff
`sinh r · √(‖c‖² - α²) · (1 - ‖z‖²) = |α (‖z‖² + 1) - 2 Re (c̄ z)|`.  (For `α = 0`, `c = i` this is
`isLeast_hdist_diameter_iff`.) -/
theorem isLeast_hdist_hline_iff {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) {z : ℂ} (hz : ‖z‖ < 1)
    (r : ℝ) :
    IsLeast (hdist z '' hline α c) r ↔
      Real.sinh r * (Real.sqrt (‖c‖ ^ 2 - α ^ 2) * (1 - ‖z‖ ^ 2)) =
        |α * (‖z‖ ^ 2 + 1) - 2 * (conj c * z).re| := by
  obtain ⟨F, hF, hleast, hs⟩ := exists_foot h hz
  have hFn : ‖F‖ < 1 := hF.1
  have hQ : 0 < ‖c‖ ^ 2 - α ^ 2 := by linarith
  have hp := one_sub_sq_pos hz
  have hsq : 0 < Real.sqrt (‖c‖ ^ 2 - α ^ 2) := Real.sqrt_pos.mpr hQ
  have hd : 0 < Real.sqrt (‖c‖ ^ 2 - α ^ 2) * (1 - ‖z‖ ^ 2) := mul_pos hsq hp
  have h1p : (1 + ‖z‖ ^ 2) ≠ 0 := by positivity
  have hx : (conj c * kleinMap z).re = 2 / (1 + ‖z‖ ^ 2) * (conj c * z).re :=
    re_conj_mul_kleinMap c z
  have hform : Real.sinh (hdist z F) =
      |α * (‖z‖ ^ 2 + 1) - 2 * (conj c * z).re| /
        (Real.sqrt (‖c‖ ^ 2 - α ^ 2) * (1 - ‖z‖ ^ 2)) := by
    have h0 : 0 ≤ Real.sinh (hdist z F) := Real.sinh_nonneg_iff.mpr (hdist_nonneg hz hFn)
    refine (sq_eq_sq₀ h0 (by positivity)).mp ?_
    rw [hs, hx, one_sub_norm_kleinMap_sq, div_pow, mul_pow, Real.sq_sqrt hQ.le, sq_abs]
    field_simp
    ring
  constructor
  · intro hr
    have := hleast.unique hr
    rw [← this, hform]
    field_simp
  · intro hr
    have : Real.sinh r = Real.sinh (hdist z F) := by
      rw [hform, eq_div_iff hd.ne']; exact hr
    rw [Real.sinh_injective this]
    exact hleast

/-- Section 13C (Equidistants), pp. 105-107, general h-line.  Let `ℓ = hline α c` be an h-line (with
ideal points `A, B`, the points of the absolute with `Re (c̄ A) = α`) and `r > 0`.  The h-points `z`
at h-distance `r` from `ℓ` are exactly the points of the open disc lying on one of the two
circlines `(α + κ)‖z‖² + (α - κ) = 2 Re (c̄ z)` or `(α - κ)‖z‖² + (α + κ) = 2 Re (c̄ z)`, where
`κ = sinh r · √(‖c‖² - α²)`, one for each side of `ℓ`.  Both pass through all the ideal points of `ℓ`
(`equidistant_circle_through_ideal`), so they are the circular arcs (Euclidean circles, or the
chord when `α = ±κ`) through `A` and `B`.  This generalizes `equidistant_diameter` (`α = 0`, `c = i`,
where it reads `‖z ± i/sinh r‖² = 1 + 1/sinh² r`). -/
@[kb "petrunin2025" "Equidistants of an arbitrary h-line, p. 106"]
theorem equidistant_hline {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) {z : ℂ} (hz : ‖z‖ < 1) {r : ℝ}
    (hr : 0 < r) :
    IsLeast (hdist z '' hline α c) r ↔
      (α + Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2)) * ‖z‖ ^ 2 +
          (α - Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2)) = 2 * (conj c * z).re ∨
      (α - Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2)) * ‖z‖ ^ 2 +
          (α + Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2)) = 2 * (conj c * z).re := by
  rw [isLeast_hdist_hline_iff h hz]
  have hQ : 0 < ‖c‖ ^ 2 - α ^ 2 := by linarith
  have hp := one_sub_sq_pos hz
  have hκ : 0 < Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2) :=
    mul_pos (Real.sinh_pos_iff.mpr hr) (Real.sqrt_pos.mpr hQ)
  rw [← mul_assoc]
  generalize Real.sinh r * Real.sqrt (‖c‖ ^ 2 - α ^ 2) = κ at hκ ⊢
  have hpos : 0 < κ * (1 - ‖z‖ ^ 2) := mul_pos hκ hp
  constructor
  · intro hT
    rcases (abs_eq hpos.le).mp hT.symm with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h1 | h1)
    · symm; rw [abs_eq hpos.le]; left; linarith
    · symm; rw [abs_eq hpos.le]; right; linarith

/-- Both circlines of `equidistant_hline` pass through every ideal point of the h-line. -/
theorem equidistant_circle_through_ideal {α : ℝ} {c A : ℂ} (hA : A ∈ idealPts α c) (κ : ℝ) :
    (α + κ) * ‖A‖ ^ 2 + (α - κ) = 2 * (conj c * A).re ∧
      (α - κ) * ‖A‖ ^ 2 + (α + κ) = 2 * (conj c * A).re := by
  rw [hA.1, hA.2]; constructor <;> ring

end Equidistant

/-! ### Motions are inversive transformations (conformal model half of Remark p. 143) -/

section Inversive

open OnePoint

instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

/-- A map of the inversive plane `OnePoint ℂ` that is (as a function) an inversive transformation. -/
def IsInvMap (f : Function.End (OnePoint ℂ)) : Prop :=
  ∃ σ : Equiv.Perm (OnePoint ℂ), IsInversiveTransformation ℂ σ ∧ ∀ x, σ x = f x

theorem isInvMap_translate (w : ℂ) : IsInvMap (FractionalLinear.translate w) := by
  refine ⟨extendEquiv (AffineIsometryEquiv.constVAdd ℝ ℂ w),
    isInversiveTransformation_extendEquiv _, fun x => ?_⟩
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    show ((w +ᵥ z : ℂ) : OnePoint ℂ) = _
    simp [FractionalLinear.translate, add_comm]

theorem isInvMap_scale {a : ℂ} (ha : a ≠ 0) : IsInvMap (FractionalLinear.scale a) := by
  have hk : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖a / (‖a‖ : ℂ)‖ = 1 := by
    rw [norm_div]; simp [ha]
  have hmem : a / (‖a‖ : ℂ) ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.mpr hu
  let rotE : ℂ ≃ᵃⁱ[ℝ] ℂ :=
    (rotation ⟨a / (‖a‖ : ℂ), hmem⟩).toAffineIsometryEquiv
  refine ⟨((inversionEquiv (0 : ℂ) 1 one_ne_zero).trans
      (inversionEquiv (0 : ℂ) (Real.sqrt ‖a‖) (Real.sqrt_pos.mpr hk).ne')).trans (extendEquiv rotE),
    ((isInversiveTransformation_inversionEquiv one_pos).trans
      (isInversiveTransformation_inversionEquiv (Real.sqrt_pos.mpr hk))).trans
      (isInversiveTransformation_extendEquiv _), fun x => ?_⟩
  show extendOP rotE (inversionOP 0 (Real.sqrt ‖a‖) (inversionOP 0 1 x)) = _
  rw [inversionOP_homothety 0 hk]
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    show ((rotE (‖a‖ • (z - 0) + 0) : ℂ) : OnePoint ℂ) = _
    simp only [FractionalLinear.scale]
    show _ = (((a * z : ℂ)) : OnePoint ℂ)
    congr 1
    have : rotE (‖a‖ • (z - 0) + 0) = (a / (‖a‖ : ℂ)) * (‖a‖ * z) := by
      show (rotation _ : ℂ ≃ₗᵢ[ℝ] ℂ) _ = _
      rw [sub_zero, add_zero]
      refine (rotation_apply _ _).trans ?_
      simp [Complex.real_smul]
    rw [this]
    have : (‖a‖ : ℂ) ≠ 0 := by simpa using ha
    field_simp

theorem isInvMap_inv : IsInvMap FractionalLinear.inv := by
  refine ⟨(inversionEquiv (0 : ℂ) 1 one_ne_zero).trans
      (extendEquiv Complex.conjLIE.toAffineIsometryEquiv),
    (isInversiveTransformation_inversionEquiv one_pos).trans
      (isInversiveTransformation_extendEquiv _), fun x => ?_⟩
  show extendOP _ (inversionOP 0 1 x) = _
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp [FractionalLinear.inv_coe, extendOP]
    · rw [inversionOP_coe_of_ne hz, FractionalLinear.inv_coe, if_neg hz]
      show ((Complex.conjLIE (EuclideanGeometry.inversion 0 1 z) : ℂ) : OnePoint ℂ) = _
      congr 1
      rw [Complex.inv_def]
      simp [EuclideanGeometry.inversion, Complex.real_smul, dist_zero_right, Complex.normSq_eq_norm_sq]
      ring

theorem isInvMap_of_mem_closure {f : Function.End (OnePoint ℂ)}
    (hf : f ∈ Submonoid.closure FractionalLinear.elementary) : IsInvMap f := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    rcases hf with ⟨w, rfl⟩ | ⟨a, ha, rfl⟩ | rfl
    · exact isInvMap_translate w
    · exact isInvMap_scale ha
    · exact isInvMap_inv
  | one => exact ⟨Equiv.refl _, IsInversiveTransformation.refl, fun x => rfl⟩
  | mul f g _ _ hf hg =>
    obtain ⟨σ, hσ, hσf⟩ := hf
    obtain ⟨τ, hτ, hτg⟩ := hg
    exact ⟨τ.trans σ, hτ.trans hσ, fun x => by
      show σ (τ x) = f (g x)
      rw [hτg, hσf]⟩

/-- Fractional-linear maps of the Riemann sphere `OnePoint ℂ` are inversive transformations. -/
theorem isInvMap_of_isFractionalLinear {f : Function.End (OnePoint ℂ)}
    (hf : FractionalLinear.IsFractionalLinear f) : IsInvMap f :=
  isInvMap_of_mem_closure ((FractionalLinear.isFractionalLinear_iff_mem_closure f).mp hf)

/-- The open unit disc inside the inversive plane. -/
def discOP : Set (OnePoint ℂ) := {x | ∃ z : ℂ, ‖z‖ < 1 ∧ x = (z : OnePoint ℂ)}

/-- Remark p. 143, conformal model: every h-motion `z ↦ u · (z - a)/(1 - ā z)` (`‖u‖ = 1`,
`‖a‖ < 1`) is the restriction to the open disc of an inversive transformation of the inversive
plane `OnePoint ℂ` (a fractional-linear map of the Riemann sphere), which maps the disc onto itself. -/
@[kb "petrunin2025" "Section 17B, Motions, p. 143"]
theorem motion_isInversive {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) :
    ∃ σ : Equiv.Perm (OnePoint ℂ), IsInversiveTransformation ℂ σ ∧
      (∀ z : ℂ, ‖z‖ < 1 → σ (z : OnePoint ℂ) = ((u * mobius a z : ℂ) : OnePoint ℂ)) ∧
      σ '' discOP = discOP := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hdet : u * 1 - (-(u * a)) * (-(conj a)) ≠ 0 := by
    have h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj']; push_cast; rfl
    have h2 : u * 1 - (-(u * a)) * (-(conj a)) = u * (1 - ((‖a‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← h1]; ring
    rw [h2]
    refine mul_ne_zero hu0 ?_
    have : (‖a‖ ^ 2 : ℝ) < 1 := by nlinarith [norm_nonneg a]
    intro h
    have h3 : ((‖a‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination -h
    have h4 : (‖a‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h3
    linarith
  have hden : ∀ z : ℂ, ‖z‖ < 1 → -conj a * z + 1 ≠ 0 := by
    intro z hz h
    exact mobius_den_ne ha hz (by linear_combination h)
  obtain ⟨σ, hσ, hσg⟩ := isInvMap_of_isFractionalLinear
    (f := fun x => (FractionalLinear.glOf u (-(u * a)) (-(conj a)) 1 hdet) • x)
    ⟨FractionalLinear.glOf u (-(u * a)) (-(conj a)) 1 hdet, fun x => rfl⟩
  have hval : ∀ z : ℂ, ‖z‖ < 1 → σ (z : OnePoint ℂ) = ((u * mobius a z : ℂ) : OnePoint ℂ) := by
    intro z hz
    rw [hσg]
    show FractionalLinear.glOf u (-(u * a)) (-(conj a)) 1 hdet • (z : OnePoint ℂ) = _
    rw [FractionalLinear.glOf_smul_coe, if_neg (hden z hz)]
    congr 1
    rw [show -conj a * z + 1 = 1 - conj a * z by ring]
    unfold mobius
    ring
  refine ⟨σ, hσ, hval, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨u * mobius a z, by rw [norm_mul, hu, one_mul]; exact norm_mobius_lt_one ha hz,
      hval z hz⟩
  · rintro ⟨w, hw, rfl⟩
    have hy : ‖conj u * w‖ < 1 := by rw [norm_mul, Complex.norm_conj, hu, one_mul]; exact hw
    have ha' : ‖-a‖ < 1 := by simpa using ha
    have hz := norm_mobius_lt_one ha' hy
    refine ⟨(mobius (-a) (conj u * w) : ℂ), ⟨_, hz, rfl⟩, ?_⟩
    rw [hval _ hz, mobius_mobius_neg ha hy]
    congr 1
    rw [← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, hu]
    simp

end Inversive

end UndergradKB.Geometry
