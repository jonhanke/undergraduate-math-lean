import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import UndergradKB.Common.Attr

/-! # The conformal disc model of the hyperbolic plane (Petrunin, chapters 12 and 13)

The h-plane is the open unit disc `{z : ℂ | ‖z‖ < 1}`.  The book defines the h-distance through the
cross-ratio of the two ideal points of the h-line through `P` and `Q`; here we use the equivalent
closed formula (book Exercise 12.25)
`cosh (PQ_h) = 1 + 2 ‖P - Q‖² / ((1 - ‖P‖²)(1 - ‖Q‖²))`
as definition (`hdist`), and prove the book's cross-ratio formula for the h-lines through the centre
(`hdist_zero_eq_log_crossRatio`, Lemma 12.8 in cross-ratio form).

Contents: Lemma 12.8 (distance from the centre), Claims 12.12-12.14 (metric axioms), Lemma 12.6 and
Observation 12.7 (Möbius motions preserve the h-distance), Lemma 12.10 (h-circles about the centre),
Proposition 13.3 (angle of parallelism, in the centred model), and the hyperbolic Pythagorean
theorem 13.16. -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-- `cosh` of the h-distance between two points of the unit disc (book Exercise 12.25). -/
noncomputable def hcosh (P Q : ℂ) : ℝ :=
  1 + 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2))

/-- The h-distance in the conformal disc model, `arcosh` of `hcosh`.  For `P, Q` in the open unit
disc it equals the book's `ln (AQ·PB / (QB·PA))`, `A, B` the ideal points of the h-line `PQ`
(book Exercise 12.25 and Definition p. 93; verified through the centre in
`hdist_zero_eq_log_crossRatio`). -/
noncomputable def hdist (P Q : ℂ) : ℝ := Real.arcosh (hcosh P Q)

section Basic

variable {P Q : ℂ}

theorem one_sub_sq_pos (h : ‖P‖ < 1) : 0 < 1 - ‖P‖ ^ 2 := by nlinarith [norm_nonneg P]

theorem one_le_hcosh (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) : 1 ≤ hcosh P Q := by
  unfold hcosh
  have := mul_pos (one_sub_sq_pos hP) (one_sub_sq_pos hQ)
  have : 0 ≤ 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) :=
    div_nonneg (by positivity) this.le
  linarith

theorem cosh_hdist (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) : Real.cosh (hdist P Q) = hcosh P Q :=
  Real.cosh_arcosh (one_le_hcosh hP hQ)

theorem hcosh_comm (P Q : ℂ) : hcosh P Q = hcosh Q P := by
  unfold hcosh; rw [norm_sub_rev, mul_comm (1 - ‖P‖ ^ 2)]

/-- Claim 12.12 (first half): `PQ_h ≥ 0`. -/
@[kb "petrunin2025" "Claim 12.12, p. 97"]
theorem hdist_nonneg (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) : 0 ≤ hdist P Q :=
  Real.arcosh_nonneg (one_le_hcosh hP hQ)

/-- Claim 12.12 (second half): `PQ_h = 0` iff `P = Q`. -/
@[kb "petrunin2025" "Claim 12.12, p. 97"]
theorem hdist_eq_zero_iff (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) : hdist P Q = 0 ↔ P = Q := by
  unfold hdist
  rw [Real.arcosh_eq_zero_iff (one_le_hcosh hP hQ)]
  have hd := mul_pos (one_sub_sq_pos hP) (one_sub_sq_pos hQ)
  unfold hcosh
  constructor
  · intro h
    have h1 : 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) = 0 := by linarith
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · have : ‖P - Q‖ ^ 2 = 0 := by linarith
      exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))
    · exact absurd h2 hd.ne'
  · rintro rfl; simp

/-- Claim 12.13: the h-distance is symmetric. -/
@[kb "petrunin2025" "Claim 12.13, p. 97"]
theorem hdist_comm (P Q : ℂ) : hdist P Q = hdist Q P := by
  unfold hdist; rw [hcosh_comm]

theorem hcosh_zero_left (hP : ‖P‖ < 1) : hcosh 0 P = (1 + ‖P‖ ^ 2) / (1 - ‖P‖ ^ 2) := by
  have h := one_sub_sq_pos hP
  unfold hcosh
  simp only [zero_sub, norm_neg, norm_zero]
  field_simp
  ring

/-- Lemma 12.8 (centred form): for `P` in the disc, `OP_h = ln ((1 + OP)/(1 - OP))`. -/
theorem hdist_zero_eq_log (hP : ‖P‖ < 1) : hdist 0 P = Real.log ((1 + ‖P‖) / (1 - ‖P‖)) := by
  have h1 : 0 < 1 - ‖P‖ := by linarith
  have h0 := norm_nonneg P
  have hr : 1 ≤ (1 + ‖P‖) / (1 - ‖P‖) := by
    rw [le_div_iff₀ h1]; linarith
  have hpos : 0 < (1 + ‖P‖) / (1 - ‖P‖) := by linarith
  have hc : hcosh 0 P = Real.cosh (Real.log ((1 + ‖P‖) / (1 - ‖P‖))) := by
    rw [Real.cosh_log hpos, hcosh_zero_left hP]
    have h2 : 1 + ‖P‖ ≠ 0 := by linarith
    have h3 : 1 - ‖P‖ ≠ 0 := h1.ne'
    have h4 : 1 - ‖P‖ ^ 2 ≠ 0 := (one_sub_sq_pos hP).ne'
    field_simp
    ring
  unfold hdist
  rw [hc]
  exact Real.arcosh_cosh (Real.log_nonneg hr)

/-- Lemma 12.8 (first half, p. 95): for `0 ≤ x < 1`, the h-distance from the centre to the point
`x` is `ln ((1 + x)/(1 - x))`. -/
@[kb "petrunin2025" "Lemma 12.8, p. 95"]
theorem hdist_zero_ofReal {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    hdist 0 (x : ℂ) = Real.log ((1 + x) / (1 - x)) := by
  have : ‖(x : ℂ)‖ = x := by simp [abs_of_nonneg h0]
  rw [hdist_zero_eq_log (by rw [this]; exact h1), this]

/-- Lemma 12.8 (second half, p. 95): conversely `x = (e^y - 1)/(e^y + 1)` where `y = OP_h`. -/
@[kb "petrunin2025" "Lemma 12.8, p. 95"]
theorem ofReal_eq_exp_div {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    x = (Real.exp (hdist 0 (x : ℂ)) - 1) / (Real.exp (hdist 0 (x : ℂ)) + 1) := by
  rw [hdist_zero_ofReal h0 h1]
  have h2 : 0 < 1 - x := by linarith
  rw [Real.exp_log (by positivity)]
  have h3 : (1 + x) / (1 - x) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Lemma 12.8 in the book's cross-ratio form: if `Q = x u` with `‖u‖ = 1`, `0 ≤ x < 1`, the
ideal points of the h-line `0Q` are `A = -u` and `B = u`, and
`OQ_h = ln (AQ · OB / (QB · OA))`. -/
@[kb "petrunin2025" "Lemma 12.8, p. 95"]
theorem hdist_zero_eq_log_crossRatio {x : ℝ} {u : ℂ} (hu : ‖u‖ = 1) (h0 : 0 ≤ x) (h1 : x < 1) :
    hdist 0 ((x : ℂ) * u) =
      Real.log (dist (-u) ((x : ℂ) * u) * dist 0 u / (dist ((x : ℂ) * u) u * dist 0 (-u))) := by
  have hn : ‖(x : ℂ) * u‖ = x := by simp [hu, abs_of_nonneg h0]
  rw [hdist_zero_eq_log (by rw [hn]; exact h1), hn]
  have e1 : dist (-u) ((x : ℂ) * u) = 1 + x := by
    rw [dist_eq_norm, show -u - (x : ℂ) * u = -(((1 + x : ℝ) : ℂ) * u) by push_cast; ring]
    rw [norm_neg, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e2 : dist ((x : ℂ) * u) u = 1 - x := by
    rw [dist_eq_norm, show (x : ℂ) * u - u = -(((1 - x : ℝ) : ℂ) * u) by push_cast; ring]
    rw [norm_neg, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [e1, e2]
  simp [hu]

/-! ### Möbius motions (Lemma 12.6, Observation 12.7) -/

/-- The h-motion `z ↦ (z - a)/(1 - ā z)` sending `a` to the centre `0`.  (In the book: the
inversion across the circle centred at `a/‖a‖²` perpendicular to the absolute, followed by a
reflection; Lemma 12.6.) -/
noncomputable def mobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

section Mobius

variable {a z w : ℂ}

theorem mobius_den_ne (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : 1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, norm_one] at h2
  nlinarith [norm_nonneg a, norm_nonneg z]

theorem norm_den_pos (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : 0 < ‖1 - conj a * z‖ :=
  norm_pos_iff.mpr (mobius_den_ne ha hz)

theorem normSq_den_sub (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem one_sub_norm_mobius_sq (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - ‖mobius a z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 := by
  have hD := norm_den_pos ha hz
  unfold mobius
  rw [norm_div, div_pow]
  have := normSq_den_sub a z
  have hne : ‖1 - conj a * z‖ ^ 2 ≠ 0 := by positivity
  rw [eq_div_iff hne, sub_mul, one_mul, div_mul_cancel₀ _ hne]
  linarith

/-- The Möbius motion preserves the open unit disc. -/
theorem norm_mobius_lt_one (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mobius a z‖ < 1 := by
  have h := one_sub_norm_mobius_sq ha hz
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - conj a * z‖ ^ 2 :=
    div_pos (mul_pos (one_sub_sq_pos ha) (one_sub_sq_pos hz)) (by have := norm_den_pos ha hz; positivity)
  by_contra hc
  rw [not_lt] at hc
  nlinarith [norm_nonneg (mobius a z)]

theorem mobius_self (_ha : ‖a‖ < 1) : mobius a a = 0 := by
  simp [mobius]

theorem mobius_sub (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    mobius a z - mobius a w =
      (z - w) * ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) / ((1 - conj a * z) * (1 - conj a * w)) := by
  have h1 := mobius_den_ne ha hz
  have h2 := mobius_den_ne ha hw
  have e : (‖a‖ : ℂ) ^ 2 = a * conj a := by
    have := Complex.mul_conj a
    rw [Complex.normSq_eq_norm_sq] at this
    rw [this]; push_cast; ring
  unfold mobius
  rw [div_sub_div _ _ h1 h2]
  congr 1
  push_cast
  rw [e]
  ring

theorem norm_mobius_sub (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖mobius a z - mobius a w‖ =
      ‖z - w‖ * (1 - ‖a‖ ^ 2) / (‖1 - conj a * z‖ * ‖1 - conj a * w‖) := by
  rw [mobius_sub ha hz hw, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (one_sub_sq_pos ha).le]

/-- Lemma 12.6 and Observation 12.7: the Möbius motion preserves `hcosh`. -/
theorem hcosh_mobius (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hcosh (mobius a z) (mobius a w) = hcosh z w := by
  have hk := one_sub_sq_pos ha
  have hz' := one_sub_sq_pos hz
  have hw' := one_sub_sq_pos hw
  have dz := norm_den_pos ha hz
  have dw := norm_den_pos ha hw
  unfold hcosh
  rw [norm_mobius_sub ha hz hw, one_sub_norm_mobius_sq ha hz, one_sub_norm_mobius_sq ha hw]
  generalize ‖1 - conj a * z‖ = Dz at dz ⊢
  generalize ‖1 - conj a * w‖ = Dw at dw ⊢
  have := hk.ne'
  have := hz'.ne'
  have := hw'.ne'
  have := dz.ne'
  have := dw.ne'
  field_simp

/-- Observation 12.7 (h-distance part): the Möbius motion `z ↦ (z - a)/(1 - ā z)`, which
moves `a` to the centre, preserves the h-distance. -/
@[kb "petrunin2025" "Observation 12.7, p. 94"]
theorem hdist_mobius (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hdist (mobius a z) (mobius a w) = hdist z w := by
  unfold hdist; rw [hcosh_mobius ha hz hw]

/-- Lemma 12.6: the motion `z ↦ (z - a)/(1 - ā z)` sends `a` to the centre and the disc to
itself. -/
@[kb "petrunin2025" "Lemma 12.6, p. 94"]
theorem mobius_aim (ha : ‖a‖ < 1) :
    mobius a a = 0 ∧ ∀ z : ℂ, ‖z‖ < 1 → ‖mobius a z‖ < 1 :=
  ⟨mobius_self ha, fun _ hz => norm_mobius_lt_one ha hz⟩

end Mobius

/-! ### Triangle inequality (Claim 12.14) -/

theorem sinh_hdist_zero (hP : ‖P‖ < 1) : Real.sinh (hdist 0 P) = 2 * ‖P‖ / (1 - ‖P‖ ^ 2) := by
  have h1 : 0 < 1 - ‖P‖ := by linarith
  have h0 := norm_nonneg P
  have hpos : 0 < (1 + ‖P‖) / (1 - ‖P‖) := by positivity
  rw [hdist_zero_eq_log hP, Real.sinh_log hpos]
  have h2 : 1 + ‖P‖ ≠ 0 := by linarith
  have h3 : 1 - ‖P‖ ≠ 0 := h1.ne'
  have h4 : 1 - ‖P‖ ^ 2 ≠ 0 := (one_sub_sq_pos hP).ne'
  field_simp
  ring

theorem hdist_triangle_zero (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    hdist P Q ≤ hdist P 0 + hdist 0 Q := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hP' := one_sub_sq_pos hP
  have hQ' := one_sub_sq_pos hQ
  have n1 := norm_nonneg P
  have n2 := norm_nonneg Q
  rw [hdist_comm P 0]
  have ha := hdist_nonneg h0 hP
  have hb := hdist_nonneg h0 hQ
  have hc := hdist_nonneg hP hQ
  have key : Real.cosh (hdist P Q) ≤ Real.cosh (hdist 0 P + hdist 0 Q) := by
    rw [cosh_hdist hP hQ, Real.cosh_add, cosh_hdist h0 hP, cosh_hdist h0 hQ,
      hcosh_zero_left hP, hcosh_zero_left hQ, sinh_hdist_zero hP, sinh_hdist_zero hQ]
    have hn : ‖P - Q‖ ^ 2 ≤ (‖P‖ + ‖Q‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le P Q) 2
    unfold hcosh
    rw [← sub_nonneg]
    have e : (1 + ‖P‖ ^ 2) / (1 - ‖P‖ ^ 2) * ((1 + ‖Q‖ ^ 2) / (1 - ‖Q‖ ^ 2)) +
        2 * ‖P‖ / (1 - ‖P‖ ^ 2) * (2 * ‖Q‖ / (1 - ‖Q‖ ^ 2)) -
        (1 + 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2))) =
        2 * ((‖P‖ + ‖Q‖) ^ 2 - ‖P - Q‖ ^ 2) / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) := by
      field_simp
      ring
    rw [e]
    exact div_nonneg (by linarith) (mul_pos hP' hQ').le
  have := Real.cosh_le_cosh.mp key
  rwa [abs_of_nonneg hc, abs_of_nonneg (add_nonneg ha hb)] at this

/-- Claim 12.14 (inequality part): the triangle inequality for the h-distance.  The equality case
(`P, Q, R` in this order on an h-line) is not formalized. -/
@[kb "petrunin2025" "Claim 12.14, p. 98"]
theorem hdist_triangle (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) {R : ℂ} (hR : ‖R‖ < 1) :
    hdist P R ≤ hdist P Q + hdist Q R := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have h := hdist_triangle_zero (norm_mobius_lt_one hQ hP) (norm_mobius_lt_one hQ hR)
  rw [hdist_mobius hQ hP hR, ← mobius_self hQ, hdist_mobius hQ hP hQ,
    hdist_mobius hQ hQ hR] at h
  exact h

/-! ### Hyperbolic Pythagorean theorem (Theorem 13.16) -/

theorem hcosh_perp (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (h : (P * conj Q).re = 0) :
    hcosh P Q = hcosh 0 P * hcosh 0 Q := by
  have e : ‖P - Q‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp at h ⊢
    nlinarith
  have h1 := one_sub_sq_pos hP
  have h2 := one_sub_sq_pos hQ
  rw [hcosh_zero_left hP, hcosh_zero_left hQ]
  unfold hcosh
  rw [e]
  field_simp
  ring

/-- Theorem 13.16, right angle at the centre: if the legs `OA`, `OB` lie on perpendicular
diameters (`A ⊥ B` as vectors of `ℂ`), then `ch AB_h = ch OA_h · ch OB_h`. -/
theorem cosh_hdist_pythagoras_zero (hA : ‖P‖ < 1) (hB : ‖Q‖ < 1) (h : (P * conj Q).re = 0) :
    Real.cosh (hdist P Q) = Real.cosh (hdist 0 P) * Real.cosh (hdist 0 Q) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  rw [cosh_hdist hA hB, cosh_hdist h0 hA, cosh_hdist h0 hB, hcosh_perp hA hB h]

/-- Theorem 13.16 (hyperbolic Pythagorean theorem), right angle at an arbitrary vertex `C`:
the right angle at `C` between `CA` and `CB` is expressed by saying that the images of `A` and `B`
under the h-motion `mobius C` taking `C` to the centre lie on perpendicular diameters
(`(φ_C A · conj (φ_C B)).re = 0`); then `ch AB_h = ch CA_h · ch CB_h`.  (H-angles themselves are
not formalized; this is the book's reduction to the centre, p. 111.) -/
@[kb "petrunin2025" "Theorem 13.16, p. 111"]
theorem cosh_hdist_pythagoras {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1)
    (h : (mobius C A * conj (mobius C B)).re = 0) :
    Real.cosh (hdist A B) = Real.cosh (hdist C A) * Real.cosh (hdist C B) := by
  have e1 : hdist C A = hdist 0 (mobius C A) := by
    rw [← hdist_mobius hC hC hA, mobius_self hC]
  have e2 : hdist C B = hdist 0 (mobius C B) := by
    rw [← hdist_mobius hC hC hB, mobius_self hC]
  rw [← hdist_mobius hC hA hB, e1, e2]
  exact cosh_hdist_pythagoras_zero (norm_mobius_lt_one hC hA) (norm_mobius_lt_one hC hB) h

/-! ### H-circles about the centre (Lemma 12.10, Proposition 13.14) -/

theorem tanh_half_eq (r : ℝ) : Real.tanh (r / 2) = (Real.exp r - 1) / (Real.exp r + 1) := by
  have h : Real.exp r = Real.exp (r / 2) * Real.exp (r / 2) := by
    rw [← Real.exp_add]; ring_nf
  have := Real.exp_pos (r / 2)
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, h]
  field_simp

/-- Lemma 12.10 (centred case, as used for Proposition 13.14): the h-circle about the centre `O`
of h-radius `r` is the Euclidean circle about `O` of radius `tanh (r/2)`. -/
@[kb "petrunin2025" "Lemma 12.10, p. 96"]
theorem hdist_zero_eq_iff {r : ℝ} (hP : ‖P‖ < 1) : hdist 0 P = r ↔ ‖P‖ = Real.tanh (r / 2) := by
  have h1 : 0 < 1 - ‖P‖ := by linarith
  have h0 := norm_nonneg P
  have hpos : 0 < (1 + ‖P‖) / (1 - ‖P‖) := by positivity
  constructor
  · intro h
    have hl := hdist_zero_eq_log hP
    rw [h] at hl
    have he : Real.exp r = (1 + ‖P‖) / (1 - ‖P‖) := by rw [hl, Real.exp_log hpos]
    rw [tanh_half_eq, he]
    have : (1 + ‖P‖) / (1 - ‖P‖) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · intro h
    rw [hdist_zero_eq_log hP, h, tanh_half_eq]
    have hp : 0 < Real.exp r + 1 := by positivity
    have e : (1 + (Real.exp r - 1) / (Real.exp r + 1)) / (1 - (Real.exp r - 1) / (Real.exp r + 1))
        = Real.exp r := by
      field_simp
      ring
    rw [e, Real.log_exp]

/-! ### Angle of parallelism (Proposition 13.3, centred model) -/

theorem angle_of_parallelism_aux {c s t : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ^ 2 + c ^ 2 = 1)
    (htan : t = s / c) :
    let Z : ℝ := 1 / c
    let Q : ℂ := (((1 - s) / c : ℝ) : ℂ)
    ‖Q‖ < 1 ∧ ‖Q - (Z : ℂ)‖ = t ∧
    ‖(Complex.mk c s) - (Z : ℂ)‖ = t ∧
    ‖(Complex.mk c (-s)) - (Z : ℂ)‖ = t ∧
    hdist 0 Q = (1 / 2) * Real.log ((1 + c) / (1 - c)) ∧
    c = (Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1) := by
  intro Z Q
  have hs1 : s < 1 := by nlinarith
  have hc1 : c < 1 := by nlinarith
  have hQ0 : 0 ≤ (1 - s) / c := div_nonneg (by linarith) hc.le
  have hQn : ‖Q‖ = (1 - s) / c := by
    simp only [Q, Complex.norm_real]
    exact Real.norm_of_nonneg hQ0
  have hQ1 : (1 - s) / c < 1 := by
    rw [div_lt_one hc]; nlinarith
  have hpos : 0 < c - 1 + s := by nlinarith
  have ht0 : 0 ≤ t := by rw [htan]; positivity
  have hnorm : 1 - (1 - s) / c = (c - 1 + s) / c := by field_simp; ring
  have e1 : (1 + (1 - s) / c) / (1 - (1 - s) / c) = (c + 1 - s) / (c - 1 + s) := by
    rw [hnorm]; field_simp; ring
  have hR : ((c + 1 - s) / (c - 1 + s)) ^ 2 = (1 + c) / (1 - c) := by
    rw [div_pow, div_eq_div_iff (by positivity) (by linarith)]
    linear_combination (-2 * c) * hsc
  have hh : hdist 0 Q = Real.log ((c + 1 - s) / (c - 1 + s)) := by
    rw [hdist_zero_eq_log (by rw [hQn]; exact hQ1), hQn, e1]
  have h2 : 2 * hdist 0 Q = Real.log ((1 + c) / (1 - c)) := by
    rw [hh, ← hR, Real.log_pow]; push_cast; ring
  refine ⟨by rw [hQn]; exact hQ1, ?_, ?_, ?_, by linarith, ?_⟩
  · rw [← Complex.ofReal_sub, Complex.norm_real, htan,
      show (1 - s) / c - Z = -(s / c) by simp only [Z]; field_simp; ring, norm_neg,
      Real.norm_of_nonneg (by positivity)]
  · rw [← sq_eq_sq₀ (norm_nonneg _) ht0, Complex.sq_norm, Complex.normSq_apply, htan]
    simp only [Z, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    linear_combination (c ^ 2 - 1) * hsc
  · rw [← sq_eq_sq₀ (norm_nonneg _) ht0, Complex.sq_norm, Complex.normSq_apply, htan]
    simp only [Z, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    linear_combination (c ^ 2 - 1) * hsc
  · rw [h2, Real.exp_log (by apply div_pos <;> linarith)]
    field_simp
    ring


/-- Proposition 13.3 in the centred model of the proof.  For `0 < φ < π/2`, the h-line `ℓ` has
ideal points `B = e^{iφ}` and `A = e^{-iφ}` and lies on the Euclidean circle `Γ` with centre
`Z = 1/cos φ` and radius `tan φ`; its closest point to the centre `P = 0` is the real point
`Q = (1 - sin φ)/cos φ`.  Then `Q` lies in the disc and on `Γ`, `B` and `A` lie on `Γ`, and
`h = PQ_h` satisfies `h = (1/2) ln ((1 + cos φ)/(1 - cos φ))` and
`cos φ = (e^{2h} - 1)/(e^{2h} + 1)`.  Here `φ` is the angle between the h-line `PQ` and `PB`,
that is, the angle of parallelism. -/
@[kb "petrunin2025" "Proposition 13.3, p. 104"]
theorem angle_of_parallelism {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    let Z : ℝ := 1 / Real.cos φ
    let Q : ℂ := (((1 - Real.sin φ) / Real.cos φ : ℝ) : ℂ)
    ‖Q‖ < 1 ∧ ‖Q - (Z : ℂ)‖ = Real.tan φ ∧
    ‖(Complex.mk (Real.cos φ) (Real.sin φ)) - (Z : ℂ)‖ = Real.tan φ ∧
    ‖(Complex.mk (Real.cos φ) (-Real.sin φ)) - (Z : ℂ)‖ = Real.tan φ ∧
    hdist 0 Q = (1 / 2) * Real.log ((1 + Real.cos φ) / (1 - Real.cos φ)) ∧
    Real.cos φ = (Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1) := by
  intro Z Q
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  exact angle_of_parallelism_aux hc hs (Real.sin_sq_add_cos_sq φ) (Real.tan_eq_sin_div_cos φ)

end Basic

end UndergradKB.Geometry
