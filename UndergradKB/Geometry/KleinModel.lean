import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Between
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HyperbolicDisc2

/-! # The projective (Klein) model of the hyperbolic plane (Petrunin, chapter 17, and 13C)

The bijection `P ↦ P̂` of the open unit disc (stereographic lift to the upper half-sphere followed
by the vertical projection) is `P̂ = 2P/(1+‖P‖²)` (`kleinMap`).  Lemma 17.1 (the chord and the
cross-ratio formula), the projective model with `kdist`, Observation 17.5, Exercises 17.8, 17.9,
Bolyai's construction and Proposition 17.14, hyperbolic Pappus (Theorem 17.4) and motions, and
(chapter 13C) equidistants and horocycles. -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-! ### The bijection `P ↦ P̂` (Construction, p. 139) -/

/-- The bijection `P ↦ P̂` of section 17A: `P̂ = 2P/(1+‖P‖²)`, proved in `kleinMap_eq_footpoint`
to be the footpoint of the stereographic lift of `P` to the unit sphere. -/
noncomputable def kleinMap (P : ℂ) : ℂ := (2 / (1 + ‖P‖ ^ 2)) • P

/-- The inverse `Q ↦ Q/(1+√(1-‖Q‖²))` of `kleinMap` on the open disc. -/
noncomputable def kleinInv (Q : ℂ) : ℂ := (1 / (1 + Real.sqrt (1 - ‖Q‖ ^ 2))) • Q

section Klein

variable {P Q : ℂ}

theorem norm_smul_sq (s : ℝ) (P : ℂ) : ‖s • P‖ ^ 2 = s ^ 2 * ‖P‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem kleinMap_re (P : ℂ) : (kleinMap P).re = 2 / (1 + ‖P‖ ^ 2) * P.re := by
  rw [kleinMap, Complex.smul_re, smul_eq_mul]

theorem kleinMap_im (P : ℂ) : (kleinMap P).im = 2 / (1 + ‖P‖ ^ 2) * P.im := by
  rw [kleinMap, Complex.smul_im, smul_eq_mul]

theorem norm_kleinMap_sq (P : ℂ) : ‖kleinMap P‖ ^ 2 = 4 * ‖P‖ ^ 2 / (1 + ‖P‖ ^ 2) ^ 2 := by
  unfold kleinMap
  rw [norm_smul_sq]
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem one_sub_norm_kleinMap_sq (P : ℂ) :
    1 - ‖kleinMap P‖ ^ 2 = (1 - ‖P‖ ^ 2) ^ 2 / (1 + ‖P‖ ^ 2) ^ 2 := by
  rw [norm_kleinMap_sq]
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem norm_kleinMap_lt_one (hP : ‖P‖ < 1) : ‖kleinMap P‖ < 1 := by
  have h := one_sub_norm_kleinMap_sq P
  have h1 := one_sub_sq_pos hP
  have : 0 < (1 - ‖P‖ ^ 2) ^ 2 / (1 + ‖P‖ ^ 2) ^ 2 := by positivity
  nlinarith [norm_nonneg (kleinMap P)]

theorem kleinInv_kleinMap (hP : ‖P‖ < 1) : kleinInv (kleinMap P) = P := by
  have h1 := one_sub_sq_pos hP
  have hq : 1 - ‖kleinMap P‖ ^ 2 = ((1 - ‖P‖ ^ 2) / (1 + ‖P‖ ^ 2)) ^ 2 := by
    rw [one_sub_norm_kleinMap_sq, div_pow]
  have hs : Real.sqrt (1 - ‖kleinMap P‖ ^ 2) = (1 - ‖P‖ ^ 2) / (1 + ‖P‖ ^ 2) := by
    rw [hq]; exact Real.sqrt_sq (by positivity)
  unfold kleinInv
  rw [hs]
  unfold kleinMap
  rw [smul_smul]
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  have e : 1 / (1 + (1 - ‖P‖ ^ 2) / (1 + ‖P‖ ^ 2)) * (2 / (1 + ‖P‖ ^ 2)) = 1 := by
    field_simp; ring
  rw [e, one_smul]

theorem kleinMap_kleinInv (hQ : ‖Q‖ < 1) : kleinMap (kleinInv Q) = Q := by
  have h1 := one_sub_sq_pos hQ
  set r := Real.sqrt (1 - ‖Q‖ ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - ‖Q‖ ^ 2 := Real.sq_sqrt h1.le
  have hn : ‖kleinInv Q‖ ^ 2 = ‖Q‖ ^ 2 / (1 + r) ^ 2 := by
    unfold kleinInv
    rw [← hr, norm_smul_sq]
    field_simp
  unfold kleinMap
  rw [hn]
  unfold kleinInv
  rw [← hr, smul_smul]
  have h2 : (1 + r) ≠ 0 := by positivity
  have h3 : (1 + r) ^ 2 + ‖Q‖ ^ 2 = 2 * (1 + r) := by nlinarith
  have e : 2 / (1 + ‖Q‖ ^ 2 / (1 + r) ^ 2) * (1 / (1 + r)) = 1 := by
    have : 1 + ‖Q‖ ^ 2 / (1 + r) ^ 2 = 2 * (1 + r) / (1 + r) ^ 2 := by
      field_simp; linarith
    rw [this]
    field_simp
  rw [e, one_smul]

/-- Construction p. 139 (the bijection `P ↦ P̂`): it maps the open unit disc bijectively onto
itself. -/
@[kb "petrunin2025" "Section 17A, Construction, p. 139"]
theorem kleinMap_bijOn : Set.BijOn kleinMap (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
  refine Set.InvOn.bijOn (f' := kleinInv) ⟨fun P hP => kleinInv_kleinMap (by simpa using hP),
    fun Q hQ => kleinMap_kleinInv (by simpa using hQ)⟩ (fun P hP => ?_) (fun Q hQ => ?_)
  · simpa using norm_kleinMap_lt_one (by simpa using hP)
  · have hQ' : ‖Q‖ < 1 := by simpa using hQ
    have h := one_sub_sq_pos hQ'
    have hr0 := Real.sqrt_nonneg (1 - ‖Q‖ ^ 2)
    have hr1 : Real.sqrt (1 - ‖Q‖ ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]; nlinarith [norm_nonneg Q]
    have : 0 < 1 + Real.sqrt (1 - ‖Q‖ ^ 2) := by linarith
    simp only [kleinInv, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    rw [one_div, inv_mul_lt_iff₀ this]
    linarith

/-- The map `P ↦ P̂` fixes the centre. -/
theorem kleinMap_zero : kleinMap 0 = 0 := by simp [kleinMap]

/-- `P̂ = P` exactly for the centre and the points of the absolute (book p. 140). -/
@[kb "petrunin2025" "Section 17A, Construction, p. 139"]
theorem kleinMap_eq_self_iff : kleinMap P = P ↔ P = 0 ∨ ‖P‖ = 1 := by
  unfold kleinMap
  constructor
  · intro h
    by_cases hP : P = 0
    · exact Or.inl hP
    · right
      have h1 : ((2 / (1 + ‖P‖ ^ 2)) - 1) • P = 0 := by rw [sub_smul, h]; simp
      rcases smul_eq_zero.mp h1 with h2 | h2
      · have hp : 1 + ‖P‖ ^ 2 ≠ 0 := by positivity
        have : ‖P‖ ^ 2 = 1 := by field_simp at h2; linarith
        nlinarith [norm_nonneg P]
      · exact absurd h2 hP
  · rintro (rfl | h)
    · simp
    · rw [h]; norm_num

/-- The points of the absolute are fixed by `P ↦ P̂`. -/
theorem kleinMap_of_norm_eq_one (h : ‖P‖ = 1) : kleinMap P = P :=
  kleinMap_eq_self_iff.mpr (Or.inr h)

/-- The unit sphere `x² + y² + z² = 1` with `x + iy ∈ ℂ`, as a set in `ℂ × ℝ`. -/
def unitSphere : Set (ℂ × ℝ) := {w | ‖w.1‖ ^ 2 + w.2 ^ 2 = 1}

/-- The stereographic lift `P ↦ P'` of the plane `Π = {z = 0}` to the unit sphere from the south
pole `S = (0, 0, -1)`: the second intersection point of the line `SP` with the sphere. -/
noncomputable def stereoLift (P : ℂ) : ℂ × ℝ :=
  (0, -1) + (2 / (1 + ‖P‖ ^ 2)) • (((P, 0) : ℂ × ℝ) - (0, -1))

theorem stereoLift_eq (P : ℂ) :
    stereoLift P = (kleinMap P, (1 - ‖P‖ ^ 2) / (1 + ‖P‖ ^ 2)) := by
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  ext
  · simp [stereoLift, kleinMap]
  · simp only [stereoLift, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    field_simp
    ring

/-- Construction p. 139: the stereographic lift `P'` lies on the unit sphere, is the second point
of the line `SP` on the sphere, lies in the open northern half-sphere iff `P` is in the open disc,
and the footpoint `P̂` of `P'` on `Π` (the vertical projection, first coordinate) is `kleinMap P`. -/
@[kb "petrunin2025" "Section 17A, Construction, p. 139"]
theorem kleinMap_eq_footpoint (P : ℂ) :
    stereoLift P ∈ unitSphere ∧ (stereoLift P).1 = kleinMap P ∧
      (0 < (stereoLift P).2 ↔ ‖P‖ < 1) := by
  rw [stereoLift_eq]
  have hp : 0 < 1 + ‖P‖ ^ 2 := by positivity
  refine ⟨?_, rfl, ?_⟩
  · simp only [unitSphere, Set.mem_ofPred_eq]
    rw [norm_kleinMap_sq]
    field_simp
    ring
  · simp only
    rw [div_pos_iff_of_pos_right hp, sub_pos]
    constructor
    · intro h; nlinarith [norm_nonneg P]
    · intro h; nlinarith [norm_nonneg P]

end Klein

/-! ### Chords: Lemma 17.1 -/

section Chord

variable {α : ℝ} {c A B P Q z z' : ℂ}

theorem dot_identity (c A P : ℂ) :
    ‖c‖ ^ 2 * (conj A * P).re =
      (conj c * A).re * (conj c * P).re + (conj c * A).im * (conj c * P).im := by
  rw [sq_norm_eq]; simp [Complex.mul_re, Complex.mul_im]; ring

theorem normsq_dot (c P : ℂ) :
    ‖c‖ ^ 2 * ‖P‖ ^ 2 = (conj c * P).re ^ 2 + (conj c * P).im ^ 2 := by
  rw [← mul_pow, ← Complex.norm_conj c, ← norm_mul, sq_norm_eq]

theorem re_conj_mul_kleinMap (c P : ℂ) :
    (conj c * kleinMap P).re = 2 / (1 + ‖P‖ ^ 2) * (conj c * P).re := by
  unfold kleinMap; rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]

theorem im_conj_mul_kleinMap (c P : ℂ) :
    (conj c * kleinMap P).im = 2 / (1 + ‖P‖ ^ 2) * (conj c * P).im := by
  unfold kleinMap; rw [mul_smul_comm, Complex.smul_im, smul_eq_mul]

/-- The open chord `{z in the disc | Re (c̄ z) = α}` (the Euclidean line meets the open disc). -/
def chord (α : ℝ) (c : ℂ) : Set ℂ := {z | ‖z‖ < 1 ∧ (conj c * z).re = α}

theorem re_conj_mul_kleinMap_of_hline (hP : P ∈ hline α c) : (conj c * kleinMap P).re = α := by
  obtain ⟨_, h⟩ := hP
  rw [re_conj_mul_kleinMap]
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  field_simp
  linarith

/-- Section 17B, Lines: the image of the h-line `hline α c` under `P ↦ P̂` is the open chord
`{z : Re (c̄ z) = α}` of the unit circle, i.e. the chord through its ideal points (without them). -/
@[kb "petrunin2025" "Section 17B, Lines, p. 141"]
theorem kleinMap_image_hline : kleinMap '' hline α c = chord α c := by
  ext z
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨by simpa using kleinMap_bijOn.mapsTo (show P ∈ Metric.ball (0 : ℂ) 1 by simpa using hP.1),
      re_conj_mul_kleinMap_of_hline hP⟩
  · rintro ⟨hz, hre⟩
    obtain ⟨P, hP, rfl⟩ := kleinMap_bijOn.surjOn (show z ∈ Metric.ball (0 : ℂ) 1 by simpa using hz)
    refine ⟨P, ⟨by simpa using hP, ?_⟩, rfl⟩
    rw [re_conj_mul_kleinMap] at hre
    have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
    field_simp at hre
    linarith

theorem norm_sub_of_re_eq (h : (conj c * z).re = (conj c * z').re) :
    ‖c‖ * ‖z - z'‖ = |(conj c * z).im - (conj c * z').im| := by
  have e : conj c * (z - z') = (((conj c * z).im - (conj c * z').im : ℝ) : ℂ) * Complex.I := by
    rw [mul_sub]
    apply Complex.ext <;> simp [h]
  rw [← Complex.norm_conj c, ← norm_mul, e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem dist_of_re_eq (hc : c ≠ 0) (h : (conj c * z).re = (conj c * z').re) :
    dist z z' = |(conj c * z).im - (conj c * z').im| / ‖c‖ := by
  have hN : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [dist_eq_norm, eq_div_iff hN.ne', mul_comm, norm_sub_of_re_eq h]

theorem c_ne_zero (h : α ^ 2 < ‖c‖ ^ 2) : c ≠ 0 := by
  rintro rfl
  simp at h
  nlinarith [sq_nonneg α]

theorem ideal_im_sq (hA : A ∈ idealPts α c) :
    (conj c * A).im ^ 2 = ‖c‖ ^ 2 - α ^ 2 := by
  obtain ⟨h1, h2⟩ := hA
  have := normsq_dot c A
  rw [h1, h2] at this
  linarith

theorem ideal_im_neg (hc : c ≠ 0) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c) (hAB : A ≠ B) :
    (conj c * B).im = -(conj c * A).im := by
  have e : (conj c * B).im ^ 2 = (conj c * A).im ^ 2 := by rw [ideal_im_sq hA, ideal_im_sq hB]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp e with h | h
  · exfalso
    apply hAB
    have : conj c * A = conj c * B :=
      Complex.ext (by rw [hA.2, hB.2]) h.symm
    exact mul_left_cancel₀ (by simpa using hc) this
  · exact h

theorem chord_im_sq_lt (h : α ^ 2 < ‖c‖ ^ 2) (hz : ‖z‖ < 1) (hre : (conj c * z).re = α) :
    (conj c * z).im ^ 2 < ‖c‖ ^ 2 - α ^ 2 := by
  have := normsq_dot c z
  rw [hre] at this
  have h1 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have h2 : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
  nlinarith

theorem sign_facts {a x y : ℝ} (ha : a ≠ 0) (hx : |x| < |a|) (hy : |y| < |a|) :
    0 < (a - y) * (a + x) ∧ 0 < (a + y) * (a - x) ∧ |a - y| * |a + x| = (a - y) * (a + x) ∧
      |a + y| * |a - x| = (a + y) * (a - x) := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [abs_of_neg h] at hx hy
    have h1 : a - y < 0 := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
    have h2 : a + x < 0 := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
    have h3 : a + y < 0 := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
    have h4 : a - x < 0 := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
    refine ⟨mul_pos_of_neg_of_neg h1 h2, mul_pos_of_neg_of_neg h3 h4, ?_, ?_⟩
    · rw [← abs_mul, abs_of_pos (mul_pos_of_neg_of_neg h1 h2)]
    · rw [← abs_mul, abs_of_pos (mul_pos_of_neg_of_neg h3 h4)]
  · rw [abs_of_pos h] at hx hy
    have h1 : 0 < a - y := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
    have h2 : 0 < a + x := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
    have h3 : 0 < a + y := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
    have h4 : 0 < a - x := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
    refine ⟨mul_pos h1 h2, mul_pos h3 h4, ?_, ?_⟩
    · rw [← abs_mul, abs_of_pos (mul_pos h1 h2)]
    · rw [← abs_mul, abs_of_pos (mul_pos h3 h4)]

theorem half_log_aux {a x y : ℝ} (ha : a ≠ 0) (hx : |x| < |a|) (hy : |y| < |a|) :
    ∃ w : ℝ, 0 < w ∧ w ^ 2 = (a - y) * (a + x) / ((a + y) * (a - x)) ∧
      Real.cosh (Real.log w) = (a ^ 2 - x * y) / Real.sqrt ((a ^ 2 - x ^ 2) * (a ^ 2 - y ^ 2)) ∧
      (|a - x| ≤ |a - y| → 1 ≤ w) := by
  obtain ⟨hu, ht, -, -⟩ := sign_facts ha hx hy
  have hx2 : x ^ 2 < a ^ 2 := sq_lt_sq.mpr hx
  have hy2 : y ^ 2 < a ^ 2 := sq_lt_sq.mpr hy
  have hprod : 0 < (a ^ 2 - x ^ 2) * (a ^ 2 - y ^ 2) :=
    mul_pos (by linarith) (by linarith)
  set S := Real.sqrt ((a ^ 2 - x ^ 2) * (a ^ 2 - y ^ 2)) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr hprod
  have hS2 : S * S = (a - y) * (a + x) * ((a + y) * (a - x)) := by
    rw [hSdef, Real.mul_self_sqrt hprod.le]; ring
  refine ⟨(a - y) * (a + x) / S, div_pos hu hS, ?_, ?_, ?_⟩
  · rw [div_pow, div_eq_div_iff (by positivity) ht.ne']
    nlinarith [hS2]
  · rw [Real.cosh_log (div_pos hu hS), inv_div]
    have : S / ((a - y) * (a + x)) = (a + y) * (a - x) / S := by
      rw [div_eq_div_iff hu.ne' hS.ne']; linarith [hS2]
    rw [this, ← add_div, div_div]
    rw [div_eq_div_iff (by positivity) hS.ne']
    ring
  · intro hle
    have hle2 : (a + y) * (a - x) ≤ (a - y) * (a + x) := by
      rcases lt_or_gt_of_ne ha with h | h
      · rw [abs_of_neg h] at hx hy
        have h1 : a - x < 0 := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
        have h2 : a - y < 0 := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
        rw [abs_of_neg h1, abs_of_neg h2] at hle
        nlinarith
      · rw [abs_of_pos h] at hx hy
        have h1 : 0 < a - x := by rw [abs_lt] at hx; linarith [hx.1, hx.2]
        have h2 : 0 < a - y := by rw [abs_lt] at hy; linarith [hy.1, hy.2]
        rw [abs_of_pos h1, abs_of_pos h2] at hle
        nlinarith
    have hw2 : 1 ≤ ((a - y) * (a + x) / S) ^ 2 := by
      have : ((a - y) * (a + x) / S) ^ 2 = (a - y) * (a + x) / ((a + y) * (a - x)) := by
        rw [div_pow, div_eq_div_iff (by positivity) ht.ne']
        nlinarith [hS2]
      rw [this, one_le_div ht]
      exact hle2
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_one₀ (div_pos hu hS).le hlt (two_ne_zero)
    linarith

theorem norm_sub_sq' (P Q : ℂ) : ‖P - Q‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 - 2 * (conj P * Q).re := by
  rw [sq_norm_eq, sq_norm_eq, sq_norm_eq, re_conj_mul]; simp; ring

theorem re_conj_kleinMap (P Q : ℂ) :
    (conj (kleinMap P) * kleinMap Q).re =
      4 * (conj P * Q).re / ((1 + ‖P‖ ^ 2) * (1 + ‖Q‖ ^ 2)) := by
  rw [re_conj_mul, kleinMap_re, kleinMap_re, kleinMap_im, kleinMap_im, re_conj_mul]
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  have : (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem chord_sq (hP : P ∈ hline α c) :
    ‖c‖ ^ 2 - α ^ 2 - (conj c * kleinMap P).im ^ 2 = ‖c‖ ^ 2 * (1 - ‖kleinMap P‖ ^ 2) := by
  have := normsq_dot c (kleinMap P)
  rw [re_conj_mul_kleinMap_of_hline hP] at this
  linarith

theorem chord_mul (hP : P ∈ hline α c) (hQ : Q ∈ hline α c) :
    ‖c‖ ^ 2 - α ^ 2 - (conj c * kleinMap P).im * (conj c * kleinMap Q).im =
      ‖c‖ ^ 2 * (1 - (conj (kleinMap P) * kleinMap Q).re) := by
  have := dot_identity c (kleinMap P) (kleinMap Q)
  rw [re_conj_mul_kleinMap_of_hline hP, re_conj_mul_kleinMap_of_hline hQ] at this
  linarith

theorem hcosh_chord (h : α ^ 2 < ‖c‖ ^ 2) (hP : P ∈ hline α c) (hQ : Q ∈ hline α c) :
    hcosh P Q =
      (‖c‖ ^ 2 - α ^ 2 - (conj c * kleinMap P).im * (conj c * kleinMap Q).im) /
        Real.sqrt ((‖c‖ ^ 2 - α ^ 2 - (conj c * kleinMap P).im ^ 2) *
          (‖c‖ ^ 2 - α ^ 2 - (conj c * kleinMap Q).im ^ 2)) := by
  have hp := one_sub_sq_pos hP.1
  have hq := one_sub_sq_pos hQ.1
  have hN : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
  rw [chord_sq hP, chord_sq hQ, chord_mul hP hQ]
  have hsq : ‖c‖ ^ 2 * (1 - ‖kleinMap P‖ ^ 2) * (‖c‖ ^ 2 * (1 - ‖kleinMap Q‖ ^ 2)) =
      (‖c‖ ^ 2 * (1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2) / ((1 + ‖P‖ ^ 2) * (1 + ‖Q‖ ^ 2))) ^ 2 := by
    rw [one_sub_norm_kleinMap_sq, one_sub_norm_kleinMap_sq]
    have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
    have : (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg (mul_nonneg hN.le hp.le) hq.le) (by positivity))]
  unfold hcosh
  rw [re_conj_kleinMap, norm_sub_sq']
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  have : (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
  have := hp.ne'
  have := hq.ne'
  have : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr (c_ne_zero h)
  field_simp
  ring

theorem ideal_dist_sq (hA : A ∈ idealPts α c) (hP : P ∈ hline α c) :
    ‖c‖ ^ 2 * ‖A - P‖ ^ 2 = (1 + ‖P‖ ^ 2) * (conj c * A).im ^ 2 -
      2 * (conj c * A).im * (conj c * P).im := by
  have e1 := norm_sub_sq' A P
  rw [hA.1] at e1
  have eq2 := dot_identity c A P
  rw [hA.2] at eq2
  have eq3 := hP.2
  have eq4 := ideal_im_sq hA
  rw [e1]
  linear_combination (-2) * eq2 + (-(1 + ‖P‖ ^ 2)) * eq4 + α * eq3

theorem abs_cross {a x : ℝ} (ha : a ≠ 0) (hx : |x| < |a|) : |a - x| * (a + x) = |a + x| * (a - x) := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [abs_of_neg h, abs_lt] at hx
    rw [abs_of_neg (by linarith [hx.1, hx.2] : a - x < 0), abs_of_neg (by linarith [hx.1, hx.2] : a + x < 0)]
    ring
  · rw [abs_of_pos h, abs_lt] at hx
    rw [abs_of_pos (by linarith [hx.1, hx.2] : 0 < a - x), abs_of_pos (by linarith [hx.1, hx.2] : 0 < a + x)]
    ring

theorem ratio_klein (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hAB : A ≠ B) (hP : P ∈ hline α c) :
    ‖A - kleinMap P‖ * ‖B - P‖ ^ 2 = ‖B - kleinMap P‖ * ‖A - P‖ ^ 2 := by
  have hc := c_ne_zero h
  have hN : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hBn := ideal_im_neg hc hA hB hAB
  have hre := re_conj_mul_kleinMap_of_hline hP
  have hPc : kleinMap P ∈ chord α c := ⟨norm_kleinMap_lt_one hP.1, hre⟩
  have hx := chord_im_sq_lt h hPc.1 hPc.2
  rw [← ideal_im_sq hA] at hx
  have hxa : |(conj c * kleinMap P).im| < |(conj c * A).im| := sq_lt_sq.mp hx
  have ha : (conj c * A).im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hxa; exact absurd hxa (not_lt.mpr (abs_nonneg _))
  have e1 := norm_sub_of_re_eq (c := c) (z := A) (z' := kleinMap P) (by rw [hA.2, hre])
  have e2 := norm_sub_of_re_eq (c := c) (z := B) (z' := kleinMap P) (by rw [hB.2, hre])
  have d1 := ideal_dist_sq hA hP
  have d2 := ideal_dist_sq hB hP
  rw [hBn] at e2 d2
  rw [im_conj_mul_kleinMap] at e1 e2 hxa
  have hp : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  generalize (conj c * A).im = a at *
  generalize (conj c * P).im = v at *
  have hx' : |2 / (1 + ‖P‖ ^ 2) * v| < |a| := hxa
  have key := abs_cross ha hx'
  have d1' : ‖c‖ ^ 2 * ‖A - P‖ ^ 2 = (1 + ‖P‖ ^ 2) * a * (a - 2 / (1 + ‖P‖ ^ 2) * v) := by
    rw [d1]; field_simp
  have d2' : ‖c‖ ^ 2 * ‖B - P‖ ^ 2 = (1 + ‖P‖ ^ 2) * a * (a + 2 / (1 + ‖P‖ ^ 2) * v) := by
    rw [d2]; field_simp; ring
  have e2' : |-a - 2 / (1 + ‖P‖ ^ 2) * v| = |a + 2 / (1 + ‖P‖ ^ 2) * v| := by
    rw [show -a - 2 / (1 + ‖P‖ ^ 2) * v = -(a + 2 / (1 + ‖P‖ ^ 2) * v) by ring, abs_neg]
  rw [e2'] at e2
  apply mul_left_cancel₀ (pow_ne_zero 3 hN.ne')
  have L : ‖c‖ ^ 3 * (‖A - kleinMap P‖ * ‖B - P‖ ^ 2) =
      (‖c‖ * ‖A - kleinMap P‖) * (‖c‖ ^ 2 * ‖B - P‖ ^ 2) := by ring
  have R : ‖c‖ ^ 3 * (‖B - kleinMap P‖ * ‖A - P‖ ^ 2) =
      (‖c‖ * ‖B - kleinMap P‖) * (‖c‖ ^ 2 * ‖A - P‖ ^ 2) := by ring
  rw [L, R, e1, e2, d1', d2']
  linear_combination ((1 + ‖P‖ ^ 2) * a) * key

theorem sbtw_of_chord (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hAB : A ≠ B) (hz : z ∈ chord α c) : Sbtw ℝ A z B := by
  have hc := c_ne_zero h
  have hBn := ideal_im_neg hc hA hB hAB
  have hx := chord_im_sq_lt h hz.1 hz.2
  rw [← ideal_im_sq hA] at hx
  have hxa : |(conj c * z).im| < |(conj c * A).im| := sq_lt_sq.mp hx
  have ha : (conj c * A).im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hxa; exact absurd hxa (not_lt.mpr (abs_nonneg _))
  have hcc : conj c ≠ 0 := by simpa using hc
  generalize hnu : (conj c * z).im = ν at *
  generalize hna : (conj c * A).im = a at *
  have ht : 0 < (a - ν) / (2 * a) ∧ (a - ν) / (2 * a) < 1 := by
    rcases lt_or_gt_of_ne ha with h1 | h1
    · rw [abs_of_neg h1, abs_lt] at hxa
      constructor
      · apply div_pos_of_neg_of_neg <;> linarith [hxa.1, hxa.2]
      · rw [div_lt_one_of_neg (by linarith)]; linarith [hxa.1, hxa.2]
    · rw [abs_of_pos h1, abs_lt] at hxa
      constructor
      · apply div_pos <;> linarith [hxa.1, hxa.2]
      · rw [div_lt_one (by linarith)]; linarith [hxa.1, hxa.2]
  have hz_eq : z = A + (((a - ν) / (2 * a) : ℝ) : ℂ) * (B - A) := by
    apply mul_left_cancel₀ hcc
    have e : conj c * (A + (((a - ν) / (2 * a) : ℝ) : ℂ) * (B - A)) =
        conj c * A + (((a - ν) / (2 * a) : ℝ) : ℂ) * (conj c * B - conj c * A) := by ring
    rw [e]
    apply Complex.ext
    · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, hz.2, hA.2, hB.2]; ring
    · rw [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, hnu, hna, hBn]
      field_simp
      ring
  have hl : z = AffineMap.lineMap A B ((a - ν) / (2 * a)) := by
    rw [AffineMap.lineMap_apply, hz_eq]
    simp [Complex.real_smul, add_comm]
  rw [hl]
  exact sbtw_lineMap_iff.mpr ⟨hAB, ht⟩

/-- Lemma 17.1, first part: for an h-line `hline α c` with ideal points `A ≠ B` and a point `P` of
it, the point `P̂` lies strictly inside the chord `[AB]`. -/
@[kb "petrunin2025" "Lemma 17.1, p. 140"]
theorem kleinMap_sbtw (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hAB : A ≠ B) (hP : P ∈ hline α c) : Sbtw ℝ A (kleinMap P) B :=
  sbtw_of_chord h hA hB hAB ⟨norm_kleinMap_lt_one hP.1, re_conj_mul_kleinMap_of_hline hP⟩

theorem dist_ideal_conf_pos (hA : A ∈ idealPts α c) (hP : ‖P‖ < 1) : 0 < dist A P := by
  rw [dist_pos]; rintro rfl; have := hA.1; linarith

/-- Lemma 17.1, the identity ➊: `(AQ̂·BP̂)/(Q̂B·P̂A) = ((AQ·BP)/(QB·PA))²`. -/
@[kb "petrunin2025" "Lemma 17.1, p. 140"]
theorem crossRatio_kleinMap (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c)
    (hB : B ∈ idealPts α c) (hAB : A ≠ B) (hP : P ∈ hline α c) (hQ : Q ∈ hline α c) :
    dist A (kleinMap Q) * dist B (kleinMap P) / (dist (kleinMap Q) B * dist (kleinMap P) A) =
      (dist A Q * dist B P / (dist Q B * dist P A)) ^ 2 := by
  have rP := ratio_klein h hA hB hAB hP
  have rQ := ratio_klein h hA hB hAB hQ
  have pA := dist_ideal_conf_pos hA hP.1
  have pB := dist_ideal_conf_pos hB hP.1
  have qA := dist_ideal_conf_pos hA hQ.1
  have qB := dist_ideal_conf_pos hB hQ.1
  have pA' := dist_ideal_conf_pos hA (norm_kleinMap_lt_one hP.1)
  have pB' := dist_ideal_conf_pos hB (norm_kleinMap_lt_one hP.1)
  have qA' := dist_ideal_conf_pos hA (norm_kleinMap_lt_one hQ.1)
  have qB' := dist_ideal_conf_pos hB (norm_kleinMap_lt_one hQ.1)
  simp only [dist_eq_norm] at *
  rw [norm_sub_rev (kleinMap Q) B, norm_sub_rev (kleinMap P) A, norm_sub_rev Q B, norm_sub_rev P A]
  rw [norm_sub_rev] at pA qA pA' qA'
  have e1 : ‖A - kleinMap Q‖ = ‖B - kleinMap Q‖ * ‖A - Q‖ ^ 2 / ‖B - Q‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]; linarith
  have e2 : ‖A - kleinMap P‖ = ‖B - kleinMap P‖ * ‖A - P‖ ^ 2 / ‖B - P‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]; linarith
  rw [e1, e2]
  field_simp

theorem crossRatio_chord (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hAB : A ≠ B) (hP : P ∈ hline α c) (hQ : Q ∈ hline α c) :
    dist A (kleinMap Q) * dist B (kleinMap P) / (dist (kleinMap Q) B * dist (kleinMap P) A) =
      ((conj c * A).im - (conj c * kleinMap Q).im) * ((conj c * A).im + (conj c * kleinMap P).im) /
      (((conj c * A).im + (conj c * kleinMap Q).im) * ((conj c * A).im - (conj c * kleinMap P).im)) := by
  have hc := c_ne_zero h
  have hN : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hBn := ideal_im_neg hc hA hB hAB
  have hreP := re_conj_mul_kleinMap_of_hline hP
  have hreQ := re_conj_mul_kleinMap_of_hline hQ
  have hPc : kleinMap P ∈ chord α c := ⟨norm_kleinMap_lt_one hP.1, hreP⟩
  have hQc : kleinMap Q ∈ chord α c := ⟨norm_kleinMap_lt_one hQ.1, hreQ⟩
  have hx := chord_im_sq_lt h hPc.1 hPc.2
  have hy := chord_im_sq_lt h hQc.1 hQc.2
  rw [← ideal_im_sq hA] at hx hy
  have hxa : |(conj c * kleinMap P).im| < |(conj c * A).im| := sq_lt_sq.mp hx
  have hya : |(conj c * kleinMap Q).im| < |(conj c * A).im| := sq_lt_sq.mp hy
  have ha : (conj c * A).im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hxa; exact absurd hxa (not_lt.mpr (abs_nonneg _))
  obtain ⟨s1, s2, s3, s4⟩ := sign_facts ha hxa hya
  rw [dist_of_re_eq hc (by rw [hA.2, hreQ]), dist_of_re_eq hc (by rw [hB.2, hreP]),
    dist_of_re_eq hc (by rw [hreQ, hB.2]), dist_of_re_eq hc (by rw [hreP, hA.2]), hBn]
  have e1 : |-(conj c * A).im - (conj c * kleinMap P).im| = |(conj c * A).im + (conj c * kleinMap P).im| := by
    rw [show -(conj c * A).im - (conj c * kleinMap P).im = -((conj c * A).im + (conj c * kleinMap P).im) by ring, abs_neg]
  have e2 : |(conj c * kleinMap Q).im - -(conj c * A).im| = |(conj c * A).im + (conj c * kleinMap Q).im| := by
    rw [sub_neg_eq_add, add_comm]
  have e3 : |(conj c * kleinMap P).im - (conj c * A).im| = |(conj c * A).im - (conj c * kleinMap P).im| := abs_sub_comm _ _
  rw [e1, e2, e3]
  generalize (conj c * A).im = a at *
  generalize (conj c * kleinMap P).im = x at *
  generalize (conj c * kleinMap Q).im = y at *
  have : |a + y| * |a - x| ≠ 0 := by rw [s4]; exact s2.ne'
  have h5 : (a + y) * (a - x) ≠ 0 := s2.ne'
  have hNn := hN.ne'
  rw [div_mul_div_comm, div_mul_div_comm, div_div_div_cancel_right₀ (by positivity), ← abs_mul, ← abs_mul, abs_of_pos s1, abs_of_pos s2]

theorem chord_abs_lt (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c) (hP : P ∈ hline α c)
    (hQ : Q ∈ hline α c) :
    (conj c * A).im ≠ 0 ∧ |(conj c * kleinMap P).im| < |(conj c * A).im| ∧
      |(conj c * kleinMap Q).im| < |(conj c * A).im| := by
  have hx := chord_im_sq_lt h (norm_kleinMap_lt_one hP.1) (re_conj_mul_kleinMap_of_hline hP)
  have hy := chord_im_sq_lt h (norm_kleinMap_lt_one hQ.1) (re_conj_mul_kleinMap_of_hline hQ)
  rw [← ideal_im_sq hA] at hx hy
  have hxa : |(conj c * kleinMap P).im| < |(conj c * A).im| := sq_lt_sq.mp hx
  refine ⟨?_, hxa, sq_lt_sq.mp hy⟩
  intro h0; rw [h0, abs_zero] at hxa; exact absurd hxa (not_lt.mpr (abs_nonneg _))

/-- Lemma 17.1, the distance formula: if `A, P̂, Q̂, B` appear in this order on the chord (here
`AP̂ ≤ AQ̂`), then `PQ_h = ½ ln ((AQ̂·BP̂)/(Q̂B·P̂A))`. -/
@[kb "petrunin2025" "Lemma 17.1, p. 140"]
theorem hdist_eq_half_log_kleinMap (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c)
    (hB : B ∈ idealPts α c) (hAB : A ≠ B) (hP : P ∈ hline α c) (hQ : Q ∈ hline α c)
    (hord : dist A (kleinMap P) ≤ dist A (kleinMap Q)) :
    hdist P Q = 1 / 2 * Real.log
      (dist A (kleinMap Q) * dist B (kleinMap P) / (dist (kleinMap Q) B * dist (kleinMap P) A)) := by
  have hc := c_ne_zero h
  have hN : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨ha, hxa, hya⟩ := chord_abs_lt h hA hP hQ
  obtain ⟨w, hw0, hw2, hcw, hw1⟩ := half_log_aux ha hxa hya
  have hR := crossRatio_chord h hA hB hAB hP hQ
  have hord' : |(conj c * A).im - (conj c * kleinMap P).im| ≤ |(conj c * A).im - (conj c * kleinMap Q).im| := by
    rw [dist_of_re_eq hc (by rw [hA.2, re_conj_mul_kleinMap_of_hline hP]),
      dist_of_re_eq hc (by rw [hA.2, re_conj_mul_kleinMap_of_hline hQ])] at hord
    exact (div_le_div_iff_of_pos_right hN).mp hord
  have hw1' := hw1 hord'
  rw [hR, ← hw2, Real.log_pow]
  have hl : 0 ≤ Real.log w := Real.log_nonneg hw1'
  have hch : hcosh P Q = Real.cosh (Real.log w) := by
    rw [hcw, hcosh_chord h hP hQ, ← ideal_im_sq hA]
  unfold hdist
  rw [hch, Real.arcosh_cosh hl]
  push_cast
  ring

/-- Lemma 17.1 with the book's definition of the h-distance: for `A, P, Q, B` in this order,
`PQ_h = ln ((AQ·BP)/(QB·PA))` (in the conformal model, with the Euclidean distances of the
points themselves). -/
@[kb "petrunin2025" "Lemma 17.1, p. 140"]
theorem hdist_eq_log_crossRatio (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c)
    (hB : B ∈ idealPts α c) (hAB : A ≠ B) (hP : P ∈ hline α c) (hQ : Q ∈ hline α c)
    (hord : dist A (kleinMap P) ≤ dist A (kleinMap Q)) :
    hdist P Q = Real.log (dist A Q * dist B P / (dist Q B * dist P A)) := by
  rw [hdist_eq_half_log_kleinMap h hA hB hAB hP hQ hord, crossRatio_kleinMap h hA hB hAB hP hQ,
    Real.log_pow]
  push_cast
  ring

end Chord

/-! ### The projective model: `kdist` (Section 17B) -/

section Projective

/-- The parameter, along `X + t (Y - X)`, of the two points where the line `XY` meets the unit circle
(`σ = -1` the first, `σ = 1` the second). -/
noncomputable def kEndParam (X Y : ℂ) (σ : ℝ) : ℝ :=
  (-(conj X * (Y - X)).re + σ * Real.sqrt ((conj X * (Y - X)).re ^ 2 + ‖Y - X‖ ^ 2 * (1 - ‖X‖ ^ 2))) /
    ‖Y - X‖ ^ 2

/-- The two ideal points `A, B` of the line `XY` of the projective model: the intersections of the
Euclidean line `(XY)` with the absolute, ordered so that `A, X, Y, B` lie in this order. -/
noncomputable def kEnd (X Y : ℂ) (σ : ℝ) : ℂ := X + kEndParam X Y σ • (Y - X)

/-- The distance of the projective model (book ➍, p. 142): for `X ≠ Y` in the open disc and `A, B`
the intersections of the line `XY` with the absolute (ordered `A, X, Y, B`),
`XY_k = ½ ln (AY·BX / (YB·XA))`. -/
@[kb "petrunin2025" "Section 17B, Distance, p. 142"]
noncomputable def kdist (X Y : ℂ) : ℝ :=
  1 / 2 * Real.log (dist (kEnd X Y (-1)) Y * dist (kEnd X Y 1) X /
    (dist Y (kEnd X Y 1) * dist X (kEnd X Y (-1))))

/-- The auxiliary expression `(1 - ⟨X, Y⟩)/√((1-‖X‖²)(1-‖Y‖²))` (the `cosh` of the distance of the
projective model, proved in `kdist_eq_arcosh`). -/
noncomputable def kcosh (X Y : ℂ) : ℝ :=
  (1 - (conj X * Y).re) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2))

theorem hcosh_eq_kcosh (P Q : ℂ) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    hcosh P Q = kcosh (kleinMap P) (kleinMap Q) := by
  have hp := one_sub_sq_pos hP
  have hq := one_sub_sq_pos hQ
  unfold kcosh
  have hsq : (1 - ‖kleinMap P‖ ^ 2) * (1 - ‖kleinMap Q‖ ^ 2) =
      ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2) / ((1 + ‖P‖ ^ 2) * (1 + ‖Q‖ ^ 2))) ^ 2 := by
    rw [one_sub_norm_kleinMap_sq, one_sub_norm_kleinMap_sq]
    have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
    have : (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hsq, Real.sqrt_sq (div_nonneg (mul_nonneg hp.le hq.le) (by positivity))]
  unfold hcosh
  rw [re_conj_kleinMap, norm_sub_sq']
  have : (1 + ‖P‖ ^ 2) ≠ 0 := by positivity
  have : (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
  have := hp.ne'
  have := hq.ne'
  field_simp
  ring

theorem dist_param (X Y : ℂ) (t t' : ℝ) :
    dist (X + t • (Y - X)) (X + t' • (Y - X)) = |t - t'| * ‖Y - X‖ := by
  rw [dist_eq_norm]
  have : X + t • (Y - X) - (X + t' • (Y - X)) = (t - t') • (Y - X) := by
    rw [sub_smul]; abel
  rw [this, norm_smul, Real.norm_eq_abs]

theorem kdist_real {s u : ℝ} (hs : s < 0) (hu : 1 < u) :
    ∃ w : ℝ, 0 < w ∧ w ^ 2 = (1 - s) * u / ((u - 1) * -s) ∧ 1 ≤ w ∧
      Real.cosh (Real.log w) =
        (-s * u + (s + u) / 2) / Real.sqrt ((-s * u) * ((1 - s) * (u - 1))) := by
  have ha : (u - s) / 2 ≠ 0 := by intro h; linarith
  have hx : |(s + u) / 2| < |(u - s) / 2| := by
    rw [abs_of_pos (by linarith : 0 < (u - s) / 2), abs_lt]; constructor <;> linarith
  have hy : |(s + u) / 2 - 1| < |(u - s) / 2| := by
    rw [abs_of_pos (by linarith : 0 < (u - s) / 2), abs_lt]; constructor <;> linarith
  obtain ⟨w, hw0, hw2, hcw, hw1⟩ := half_log_aux ha hx hy
  refine ⟨w, hw0, ?_, ?_, ?_⟩
  · rw [hw2]
    congr 1 <;> ring
  · apply hw1
    rw [abs_of_pos (by linarith : 0 < (u - s) / 2 - (s + u) / 2),
      abs_of_pos (by linarith : 0 < (u - s) / 2 - ((s + u) / 2 - 1))]
    linarith
  · rw [hcw]
    have e1 : ((u - s) / 2) ^ 2 - (s + u) / 2 * ((s + u) / 2 - 1) = -s * u + (s + u) / 2 := by ring
    have e2 : (((u - s) / 2) ^ 2 - ((s + u) / 2) ^ 2) * (((u - s) / 2) ^ 2 - ((s + u) / 2 - 1) ^ 2) =
        (-s * u) * ((1 - s) * (u - 1)) := by ring
    rw [e1, e2]

theorem kcosh_aux {s u p q e d : ℝ} (hd : 0 < d) (hp : p < 1) (hq : q < 1)
    (hsu : s * u = -(1 - p) / d) (hss : s + u = -2 * e / d) (hq' : q = p + 2 * e + d) :
    (-s * u + (s + u) / 2) / Real.sqrt ((-s * u) * ((1 - s) * (u - 1))) =
      (1 - (p + e)) / Real.sqrt ((1 - p) * (1 - q)) := by
  have hM : 0 < (1 - p) * (1 - q) := mul_pos (by linarith) (by linarith)
  have h1 : -s * u + (s + u) / 2 = (1 - (p + e)) / d := by
    have : -s * u = (1 - p) / d := by rw [neg_mul, hsu]; ring
    rw [this, hss]; field_simp; ring
  have h2 : (-s * u) * ((1 - s) * (u - 1)) = (Real.sqrt ((1 - p) * (1 - q)) / d) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hM.le]
    have h3 : -s * u = (1 - p) / d := by rw [neg_mul, hsu]; ring
    have h4 : (1 - s) * (u - 1) = (1 - q) / d := by
      have : (1 - s) * (u - 1) = (s + u) - 1 - s * u := by ring
      rw [this, hss, hsu, hq']; field_simp; ring
    rw [h3, h4]; field_simp
  rw [h1, h2, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hd.le)]
  have : Real.sqrt ((1 - p) * (1 - q)) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  field_simp

theorem dist_param_Y (X Y : ℂ) (t : ℝ) : dist (X + t • (Y - X)) Y = |t - 1| * ‖Y - X‖ := by
  have := dist_param X Y t 1
  simpa using this

theorem dist_param_X (X Y : ℂ) (t : ℝ) : dist (X + t • (Y - X)) X = |t| * ‖Y - X‖ := by
  simp

theorem norm_sq_add_param (X Y : ℂ) :
    ‖Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y - X‖ ^ 2 + 2 * (conj X * (Y - X)).re := by
  rw [sq_norm_eq, sq_norm_eq, sq_norm_eq, re_conj_mul]; simp; ring

theorem re_conj_eq_param (X Y : ℂ) : (conj X * Y).re = ‖X‖ ^ 2 + (conj X * (Y - X)).re := by
  rw [sq_norm_eq, re_conj_mul, re_conj_mul]; simp; ring

theorem kcosh_self {X : ℂ} (hX : ‖X‖ < 1) : kcosh X X = 1 := by
  have h1 := one_sub_sq_pos hX
  unfold kcosh
  have : (conj X * X).re = ‖X‖ ^ 2 := by rw [sq_norm_eq, re_conj_mul]; ring
  rw [this, Real.sqrt_mul_self h1.le]
  exact div_self h1.ne'

/-- The projective distance is the `arcosh` of `kcosh`. -/
theorem kdist_eq_arcosh {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    kdist X Y = Real.arcosh (kcosh X Y) := by
  by_cases hXY : X = Y
  · subst hXY
    rw [kcosh_self hX, (Real.arcosh_eq_zero_iff le_rfl).mpr rfl]
    simp [kdist, kEnd]
  have hp := one_sub_sq_pos hX
  have hq := one_sub_sq_pos hY
  have hD : 0 < ‖Y - X‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hXY))
  have hd : 0 < ‖Y - X‖ ^ 2 := by positivity
  have hq' := norm_sq_add_param X Y
  have hdisc : 0 < (conj X * (Y - X)).re ^ 2 + ‖Y - X‖ ^ 2 * (1 - ‖X‖ ^ 2) := by
    have := mul_pos hd hp
    nlinarith [sq_nonneg (conj X * (Y - X)).re]
  have hr := Real.sqrt_pos.mpr hdisc
  have hr2 := Real.sq_sqrt hdisc.le
  have hkc : kcosh X Y = (1 - (‖X‖ ^ 2 + (conj X * (Y - X)).re)) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2)) := by
    unfold kcosh; rw [re_conj_eq_param]
  rw [hkc]
  unfold kdist kEnd kEndParam
  generalize Real.sqrt ((conj X * (Y - X)).re ^ 2 + ‖Y - X‖ ^ 2 * (1 - ‖X‖ ^ 2)) = r at hr hr2 ⊢
  generalize hsd : (-(conj X * (Y - X)).re + -1 * r) / ‖Y - X‖ ^ 2 = s
  generalize hud : (-(conj X * (Y - X)).re + 1 * r) / ‖Y - X‖ ^ 2 = u
  generalize hed : (conj X * (Y - X)).re = e at *
  generalize hdd : ‖Y - X‖ ^ 2 = d at *
  have hsu : s * u = -(1 - ‖X‖ ^ 2) / d := by
    rw [← hsd, ← hud, div_mul_div_comm, div_eq_div_iff (by positivity) hd.ne']
    linear_combination (-d) * hr2
  have hss : s + u = -2 * e / d := by
    rw [← hsd, ← hud]; field_simp; ring
  have hsu' : s < u := by
    rw [← hsd, ← hud]; apply div_lt_div_of_pos_right _ hd; linarith
  have hs0 : s < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    have : 0 < -(1 - ‖X‖ ^ 2) / d * -1 := by
      have : -(1 - ‖X‖ ^ 2) / d < 0 := div_neg_of_neg_of_pos (by linarith) hd
      linarith
    nlinarith
  have hu1 : 1 < u := by
    by_contra hcon
    rw [not_lt] at hcon
    have hq1 : (s - 1) * (u - 1) = -(1 - ‖Y‖ ^ 2) / d := by
      have : (s - 1) * (u - 1) = s * u - (s + u) + 1 := by ring
      rw [this, hsu, hss, show ‖Y‖ ^ 2 = ‖X‖ ^ 2 + d + 2 * e by linarith]
      field_simp; ring
    have : -(1 - ‖Y‖ ^ 2) / d < 0 := div_neg_of_neg_of_pos (by linarith) hd
    nlinarith
  obtain ⟨w, hw0, hw2, hw1, hcw⟩ := kdist_real hs0 hu1
  have hdist1 : dist (X + s • (Y - X)) Y = (1 - s) * ‖Y - X‖ := by
    rw [dist_param_Y, abs_of_neg (by linarith)]; ring
  have hdist2 : dist (X + u • (Y - X)) X = u * ‖Y - X‖ := by
    rw [dist_param_X, abs_of_pos (by linarith)]
  have hdist3 : dist Y (X + u • (Y - X)) = (u - 1) * ‖Y - X‖ := by
    rw [dist_comm, dist_param_Y, abs_of_pos (by linarith)]
  have hdist4 : dist X (X + s • (Y - X)) = -s * ‖Y - X‖ := by
    rw [dist_comm, dist_param_X, abs_of_neg hs0]
  rw [hdist1, hdist2, hdist3, hdist4]
  have hR : (1 - s) * ‖Y - X‖ * (u * ‖Y - X‖) / ((u - 1) * ‖Y - X‖ * (-s * ‖Y - X‖)) =
      w ^ 2 := by
    rw [hw2]
    have : ‖Y - X‖ ≠ 0 := hD.ne'
    have h3 : u - 1 ≠ 0 := by linarith
    have h4 : -s ≠ 0 := by linarith
    field_simp
  rw [hR, Real.log_pow]
  have hl : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hcc : (1 - (‖X‖ ^ 2 + e)) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2)) = Real.cosh (Real.log w) := by
    rw [hcw]
    exact (kcosh_aux hd (by linarith) (by linarith) hsu hss (by linarith)).symm
  rw [hcc, Real.arcosh_cosh hl]
  push_cast
  ring

/-- Section 17B (isometry): the map `P ↦ P̂` is an isometry from the conformal model
`(disc, hdist)` onto the projective model `(disc, kdist)`. -/
@[kb "petrunin2025" "Section 17B, Distance, p. 142"]
theorem hdist_eq_kdist {P Q : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    hdist P Q = kdist (kleinMap P) (kleinMap Q) := by
  rw [kdist_eq_arcosh (norm_kleinMap_lt_one hP) (norm_kleinMap_lt_one hQ),
    ← hcosh_eq_kcosh P Q hP hQ]
  rfl

theorem norm_param_sq (X Y : ℂ) (t : ℝ) :
    ‖X + t • (Y - X)‖ ^ 2 =
      ‖X‖ ^ 2 + 2 * t * (conj X * (Y - X)).re + t ^ 2 * ‖Y - X‖ ^ 2 := by
  rw [sq_norm_eq, sq_norm_eq, sq_norm_eq, re_conj_mul]; simp; ring

/-- The ideal points `kEnd X Y (±1)` of the line `XY` of the projective model are the two
points of the absolute on the chord through `X` and `Y`. -/
theorem kEnd_mem_idealPts {α : ℝ} {c X Y : ℂ} (hX : X ∈ chord α c) (hY : Y ∈ chord α c)
    (hXY : X ≠ Y) {σ : ℝ} (hσ : σ ^ 2 = 1) : kEnd X Y σ ∈ idealPts α c := by
  have hp := one_sub_sq_pos hX.1
  have hD : 0 < ‖Y - X‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hXY))
  have hd : 0 < ‖Y - X‖ ^ 2 := by positivity
  have hdisc : 0 < (conj X * (Y - X)).re ^ 2 + ‖Y - X‖ ^ 2 * (1 - ‖X‖ ^ 2) := by
    have := mul_pos hd hp
    nlinarith [sq_nonneg (conj X * (Y - X)).re]
  have hr2 := Real.sq_sqrt hdisc.le
  constructor
  · unfold kEnd kEndParam
    generalize Real.sqrt ((conj X * (Y - X)).re ^ 2 + ‖Y - X‖ ^ 2 * (1 - ‖X‖ ^ 2)) = r at hr2 ⊢
    have h1 := norm_param_sq X Y ((-(conj X * (Y - X)).re + σ * r) / ‖Y - X‖ ^ 2)
    generalize (conj X * (Y - X)).re = e at *
    generalize ‖Y - X‖ ^ 2 = d at *
    have : ‖X + ((-e + σ * r) / d) • (Y - X)‖ ^ 2 = 1 := by
      rw [h1]
      field_simp
      have : σ ^ 2 * r ^ 2 = r ^ 2 := by rw [hσ]; ring
      nlinarith [hr2, this]
    nlinarith [norm_nonneg (X + ((-e + σ * r) / d) • (Y - X))]
  · have e : conj c * kEnd X Y σ = conj c * X + (kEndParam X Y σ : ℂ) * (conj c * Y - conj c * X) := by
      unfold kEnd; rw [Complex.real_smul]; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, hX.2, hY.2]; ring

/-- Section 17B (Lines): for an h-line `hline α c` with ideal points `A ≠ B`, the image under
`P ↦ P̂` is the open chord `(AB)` of the absolute, that is the set of points of the open disc on
the Euclidean line through `A` and `B`. -/
@[kb "petrunin2025" "Section 17B, Lines, p. 141"]
theorem kleinMap_image_hline_eq_line {α : ℝ} {c A B : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hA : A ∈ idealPts α c)
    (hB : B ∈ idealPts α c) (hAB : A ≠ B) :
    kleinMap '' hline α c = {z | ‖z‖ < 1 ∧ z ∈ line[ℝ, A, B]} := by
  rw [kleinMap_image_hline]
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, (sbtw_of_chord h hA hB hAB hz).wbtw.mem_affineSpan⟩
  · rintro ⟨hz, hl⟩
    refine ⟨hz, ?_⟩
    obtain ⟨t, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hl
    rw [AffineMap.lineMap_apply]
    have e : conj c * (t • (B -ᵥ A) +ᵥ A) = conj c * A + (t : ℂ) * (conj c * B - conj c * A) := by
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, hA.2, hB.2]; ring

end Projective

/-! ### Observation 17.5: perpendicularity at an endpoint of a segment from the centre -/

section Perp

variable {A B : ℂ}

theorem klein_perp_expr (A B : ℂ) :
    (kleinMap A * conj (kleinMap B - kleinMap A)).re =
      4 * ((1 + ‖A‖ ^ 2) * (A.re * B.re + A.im * B.im) - ‖A‖ ^ 2 * (1 + ‖B‖ ^ 2)) /
        ((1 + ‖A‖ ^ 2) ^ 2 * (1 + ‖B‖ ^ 2)) := by
  have : (1 + ‖A‖ ^ 2) ≠ 0 := by positivity
  have : (1 + ‖B‖ ^ 2) ≠ 0 := by positivity
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    kleinMap_re, kleinMap_im]
  rw [sq_norm_eq A]
  field_simp
  rw [sq_norm_eq B]
  ring

theorem mobius_zero_conj (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    mobius A 0 * conj (mobius A B) =
      (-A * conj (B - A) * (1 - conj A * B)) / ((‖1 - conj A * B‖ ^ 2 : ℝ) : ℂ) := by
  have hden := mobius_den_ne hA hB
  have hden' : (1 - A * conj B) ≠ 0 := by
    intro h; apply hden
    have := congrArg conj h
    simpa [map_sub, map_mul, mul_comm] using this
  have hn : ((‖1 - conj A * B‖ ^ 2 : ℝ) : ℂ) = (1 - conj A * B) * (1 - A * conj B) := by
    push_cast
    rw [← Complex.mul_conj']
    simp [map_sub, map_mul, mul_comm]
  rw [hn]
  unfold mobius
  simp only [map_div₀, map_sub, map_one, map_mul, Complex.conj_conj, mul_zero, sub_zero, zero_sub]
  field_simp

theorem mobius_perp_expr (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    (mobius A 0 * conj (mobius A B)).re =
      -((1 + ‖A‖ ^ 2) * (A.re * B.re + A.im * B.im) - ‖A‖ ^ 2 * (1 + ‖B‖ ^ 2)) /
        ‖1 - conj A * B‖ ^ 2 := by
  rw [mobius_zero_conj hA hB, Complex.div_ofReal_re]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [sq_norm_eq A, sq_norm_eq B]
  ring

/-- Observation 17.5 (the right angle at `A`, via the h-motion `mobius A`): for `A', B'` in the
disc with images `A = Â'`, `B = B̂'` in the projective model, the Euclidean segments `OA` and `AB` are
perpendicular if and only if the h-segments `OA'` and `A'B'` are h-perpendicular, the right angle at
`A'` being expressed (as in Theorem 13.16) by the images of `O` and `B'` under the motion
`mobius A'` lying on perpendicular diameters. -/
@[kb "petrunin2025" "Observation 17.5, p. 143"]
theorem klein_perp_iff (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    (kleinMap A * conj (kleinMap B - kleinMap A)).re = 0 ↔
      (mobius A 0 * conj (mobius A B)).re = 0 := by
  rw [klein_perp_expr, mobius_perp_expr hA hB]
  have h1 : (0 : ℝ) < (1 + ‖A‖ ^ 2) ^ 2 * (1 + ‖B‖ ^ 2) := by positivity
  have h2 : 0 < ‖1 - conj A * B‖ ^ 2 := by have := norm_den_pos hA hB; positivity
  rw [div_eq_zero_iff, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · left; linarith
    · exact absurd h h1.ne'
  · rintro (h | h)
    · left; linarith
    · exact absurd h h2.ne'

theorem hcosh_pythag_diff (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    hcosh 0 B - hcosh 0 A * hcosh A B =
      4 * ((1 + ‖A‖ ^ 2) * (A.re * B.re + A.im * B.im) - ‖A‖ ^ 2 * (1 + ‖B‖ ^ 2)) /
        ((1 - ‖A‖ ^ 2) ^ 2 * (1 - ‖B‖ ^ 2)) := by
  have hp := one_sub_sq_pos hA
  have hq := one_sub_sq_pos hB
  rw [hcosh_zero_left hA, hcosh_zero_left hB]
  unfold hcosh
  rw [norm_sub_sq', re_conj_mul]
  have := hp.ne'
  have := hq.ne'
  field_simp
  ring

/-- Observation 17.5, Pythagorean form: in the projective model the Euclidean segments `OA` and `AB`
are perpendicular iff the h-triangle `O A' B'` satisfies the hyperbolic Pythagorean relation
`ch OB'_h = ch OA'_h · ch A'B'_h` (the converse of Theorem 13.16). -/
@[kb "petrunin2025" "Observation 17.5, p. 143"]
theorem klein_perp_iff_pythagoras (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    (kleinMap A * conj (kleinMap B - kleinMap A)).re = 0 ↔
      Real.cosh (hdist 0 B) = Real.cosh (hdist 0 A) * Real.cosh (hdist A B) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  rw [cosh_hdist h0 hB, cosh_hdist h0 hA, cosh_hdist hA hB, klein_perp_expr]
  have hd := hcosh_pythag_diff hA hB
  have hp := one_sub_sq_pos hA
  have hq := one_sub_sq_pos hB
  have h1 : (0 : ℝ) < (1 + ‖A‖ ^ 2) ^ 2 * (1 + ‖B‖ ^ 2) := by positivity
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    have h' : (1 + ‖A‖ ^ 2) * (A.re * B.re + A.im * B.im) - ‖A‖ ^ 2 * (1 + ‖B‖ ^ 2) = 0 := by
      rcases h with h | h
      · linarith
      · exact absurd h h1.ne'
    rw [h'] at hd
    simp at hd
    linarith
  · intro h
    have : hcosh 0 B - hcosh 0 A * hcosh A B = 0 := by linarith
    rw [this] at hd
    have h3 : 0 < (1 - ‖A‖ ^ 2) ^ 2 * (1 - ‖B‖ ^ 2) := by positivity
    have := (div_eq_zero_iff.mp hd.symm).resolve_right h3.ne'
    rw [div_eq_zero_iff]
    left; linarith

end Perp

/-! ### Exercises 17.8 and 17.9 -/

section Exercises

/-- The h-lines `hline α c` and `hline β d` are h-perpendicular at a common point `X`: their
tangent directions at `X` (perpendicular to the gradients `αX - c`, `βX - d` of the defining
equations) are perpendicular.  The conformal model preserves angles at the point, so this is the
h-perpendicularity (book chapter 12, p. 101). -/
def HPerpAt (α : ℝ) (c : ℂ) (β : ℝ) (d : ℂ) (X : ℂ) : Prop :=
  ((α • X - c) * conj (β • X - d)).re = 0

theorem hperp_iff {α β : ℝ} {c d X : ℂ} (hX : X ∈ hline α c) (hX' : X ∈ hline β d) :
    HPerpAt α c β d X ↔ (conj d * c).re = α * β := by
  have e1 := hX.2
  have e2 := hX'.2
  rw [sq_norm_eq, re_conj_mul] at e1 e2
  unfold HPerpAt
  have : ((α • X - c) * conj (β • X - d)).re = (conj d * c).re - α * β := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    linear_combination (α / 2) * e2 + (β / 2) * e1
  rw [this]
  constructor <;> intro h <;> linarith

theorem solve2 {u A B : ℂ} (hdet : A.re * B.im - A.im * B.re ≠ 0)
    (h1 : u.re * A.re + u.im * A.im = 0) (h2 : u.re * B.re + u.im * B.im = 0) : u = 0 := by
  apply Complex.ext
  · have : u.re * (A.re * B.im - A.im * B.re) = 0 := by linear_combination B.im * h1 - A.im * h2
    simpa [hdet] using this
  · have : u.im * (A.re * B.im - A.im * B.re) = 0 := by linear_combination A.re * h2 - B.re * h1
    simpa [hdet] using this

theorem ideal_indep {A B Z : ℂ} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hAB : A ≠ B)
    (hZA : (conj A * Z).re = 1) (hZB : (conj B * Z).re = 1) : A.re * B.im - A.im * B.re ≠ 0 := by
  intro hdet
  have a1 := sq_norm_eq A
  have b1 := sq_norm_eq B
  rw [hA] at a1
  rw [hB] at b1
  have hl : (A.re * B.re + A.im * B.im) ^ 2 = 1 := by
    nlinarith [hdet]
  rw [re_conj_mul] at hZA hZB
  have hm : (A.re * B.re + A.im * B.im - 1) * (A.re * B.re + A.im * B.im + 1) = 0 := by
    linarith [hl]
  rcases mul_eq_zero.mp hm with h | h
  · apply hAB
    have h1 : (A.re - B.re) ^ 2 + (A.im - B.im) ^ 2 = 0 := by nlinarith
    exact Complex.ext (by nlinarith [sq_nonneg (A.re - B.re), sq_nonneg (A.im - B.im)])
      (by nlinarith [sq_nonneg (A.re - B.re), sq_nonneg (A.im - B.im)])
  · have h1 : (A.re + B.re) ^ 2 + (A.im + B.im) ^ 2 = 0 := by nlinarith
    have h2 : A.re + B.re = 0 := by nlinarith [sq_nonneg (A.re + B.re), sq_nonneg (A.im + B.im)]
    have h3 : A.im + B.im = 0 := by nlinarith [sq_nonneg (A.re + B.re), sq_nonneg (A.im + B.im)]
    have e1 : B.re = -A.re := by linarith
    have e2 : B.im = -A.im := by linarith
    rw [e1, e2] at hZB
    linarith

/-- Exercise 17.8.  In the projective model let `ℓ` have the ideal points `A ≠ B` (it is the image
of `hline α c`), let `s`, `t` be the tangents `Re (Ā z) = 1`, `Re (B̄ z) = 1` of the absolute at
`A`, `B`, and let the line of `m` (the image of `hline β d`, the line `Re (d̄ z) = β`) pass through a
common point `Z` of `s` and `t`.  Then `ℓ ⊥ m` (h-perpendicular at every common point). -/
@[kb "petrunin2025" "Exercise 17.8, p. 143"]
theorem klein_exercise_17_8 {α β : ℝ} {c d A B Z X : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c) (hAB : A ≠ B)
    (hZA : (conj A * Z).re = 1) (hZB : (conj B * Z).re = 1) (hZm : (conj d * Z).re = β)
    (hX : X ∈ hline α c) (hX' : X ∈ hline β d) : HPerpAt α c β d X := by
  have hdet := ideal_indep hA.1 hB.1 hAB hZA hZB
  have hc := c_ne_zero h
  have hA2 := hA.2
  have hB2 := hB.2
  rw [re_conj_mul] at hA2 hB2 hZA hZB
  have hα : α ≠ 0 := by
    intro h0
    rw [h0] at hA2 hB2
    exact hc (solve2 hdet hA2 hB2)
  have hW : α • Z - c = 0 := by
    apply solve2 hdet
    · simp only [Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      linear_combination α * hZA - hA2
    · simp only [Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      linear_combination α * hZB - hB2
  have hcZ : c = α • Z := (sub_eq_zero.mp hW).symm
  rw [hperp_iff hX hX', hcZ, mul_smul_comm, Complex.smul_re, smul_eq_mul, hZm]

/-- Exercise 17.9: the angle of parallelism from the projective model.  For `0 < φ < π/2`, the
chord `Re z = cos φ` (the image of the h-line `hline (cos φ) 1`) is at Euclidean distance `cos φ`
from the centre `O` and has the ideal points `B = e^{iφ}`, `B' = e^{-iφ}`; the angle at `O`
between the radius `OB` (argument `φ`) and the perpendicular `O Q̂` to the chord is `φ`, which is
the h-angle since angles at the centre agree.  The foot `Q̂ = cos φ` is the image of a point `Q`
of the h-line and, by the distance formula of Lemma 17.1, `OQ_h = ½ ln ((1+cos φ)/(1-cos φ))`,
that is `cos φ = (e^{2h}-1)/(e^{2h}+1)` (Proposition 13.3). -/
@[kb "petrunin2025" "Exercise 17.9, p. 144"]
theorem angle_of_parallelism_klein {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    Complex.mk (Real.cos φ) (Real.sin φ) ∈ idealPts (Real.cos φ) 1 ∧
    Complex.mk (Real.cos φ) (-Real.sin φ) ∈ idealPts (Real.cos φ) 1 ∧
    Complex.arg (Complex.mk (Real.cos φ) (Real.sin φ)) = φ ∧
    ∃ Q : ℂ, ‖Q‖ < 1 ∧ Q ∈ hline (Real.cos φ) 1 ∧ kleinMap Q = (Real.cos φ : ℂ) ∧
      hdist 0 Q = 1 / 2 * Real.log ((1 + Real.cos φ) / (1 - Real.cos φ)) ∧
      Real.cos φ = (Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1) := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsc := Real.sin_sq_add_cos_sq φ
  have hc1 : Real.cos φ < 1 := by nlinarith
  have hnorm : ∀ t : ℝ, t ^ 2 = Real.sin φ ^ 2 → ‖Complex.mk (Real.cos φ) t‖ = 1 := by
    intro t ht
    have : ‖Complex.mk (Real.cos φ) t‖ ^ 2 = 1 := by rw [sq_norm_eq]; simp; nlinarith
    nlinarith [norm_nonneg (Complex.mk (Real.cos φ) t)]
  refine ⟨⟨hnorm _ rfl, by simp⟩, ⟨hnorm _ (by ring), by simp⟩, ?_, ?_⟩
  · have h2 := Complex.arg_cos_add_sin_mul_I (θ := φ) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h2
    convert h2 using 2
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · set x : ℝ := Real.cos φ with hx
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hc.le]; exact hc1
    have hmem : (x : ℂ) ∈ chord x 1 := ⟨hxn, by simp⟩
    rw [← kleinMap_image_hline] at hmem
    obtain ⟨Q, hQh, hQe⟩ := hmem
    have hQim : Q.im = 0 := by
      have h3 := kleinMap_im Q
      rw [hQe, Complex.ofReal_im] at h3
      have hne : 2 / (1 + ‖Q‖ ^ 2) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h3.symm).resolve_left hne
    have hQ0 : Q ∈ hline 0 Complex.I := ⟨hQh.1, by simp [hQim]⟩
    have hP0 : (0 : ℂ) ∈ hline 0 Complex.I := ⟨by simp, by simp⟩
    have hA1 : (-1 : ℂ) ∈ idealPts 0 Complex.I := ⟨by simp, by simp⟩
    have hB1 : (1 : ℂ) ∈ idealPts 0 Complex.I := ⟨by simp, by simp⟩
    have hd := hdist_eq_half_log_kleinMap (α := 0) (c := Complex.I) (by simp) hA1 hB1
      (by norm_num) hP0 hQ0 (by
        rw [kleinMap_zero, hQe, dist_eq_norm, dist_eq_norm]
        have e1 : (-1 : ℂ) - 0 = ((-1 : ℝ) : ℂ) := by simp
        have e2 : (-1 : ℂ) - (x : ℂ) = ((-1 - x : ℝ) : ℂ) := by push_cast; ring
        rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_neg (by linarith), abs_of_neg (by linarith)]
        linarith)
    rw [kleinMap_zero, hQe] at hd
    have e3 : dist (-1 : ℂ) (x : ℂ) = 1 + x := by
      rw [dist_eq_norm, show (-1 : ℂ) - (x : ℂ) = ((-1 - x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
    have e4 : dist (1 : ℂ) 0 = 1 := by simp
    have e5 : dist (x : ℂ) 1 = 1 - x := by
      rw [dist_eq_norm, show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
    have e6 : dist (0 : ℂ) (-1) = 1 := by simp
    rw [e3, e4, e5, e6] at hd
    have hpos : 0 < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
    refine ⟨Q, hQh.1, hQh, hQe, ?_, ?_⟩
    · rw [hd]; congr 2; field_simp
    · have h2 : Real.exp (2 * hdist 0 Q) = (1 + x) / (1 - x) := by
        rw [hd, show 2 * (1 / 2 * Real.log ((1 + x) * 1 / ((1 - x) * 1))) =
          Real.log ((1 + x) / (1 - x)) by ring_nf, Real.exp_log hpos]
      rw [h2]
      have : 1 - x ≠ 0 := by linarith
      field_simp
      ring


end Exercises

end UndergradKB.Geometry
