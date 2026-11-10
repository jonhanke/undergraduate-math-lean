import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypAngles

/-! # Hyperbolic triangles (Petrunin, chapter 13)

The hyperbolic law of cosines (generalizing the Pythagorean theorem 13.16), the dual law of
cosines, Theorem 13.10 (positive defect, i.e. angle sum `< π`), Theorem 13.11 (AAA congruence) and
Proposition 13.14 (circumference `2π sinh r` as the integral of the conformal factor of
Lemma 13.13). -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-! ### The law of cosines -/

section LawCos

theorem hcosh_law_zero {u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    Real.cosh (hdist u v) = Real.cosh (hdist 0 u) * Real.cosh (hdist 0 v) -
      Real.sinh (hdist 0 u) * Real.sinh (hdist 0 v) *
        Real.cos (InnerProductGeometry.angle u v) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have n1 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have n2 : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have p1 := one_sub_sq_pos hu
  have p2 := one_sub_sq_pos hv
  rw [cosh_hdist hu hv, cosh_hdist h0 hu, cosh_hdist h0 hv, hcosh_zero_left hu,
    hcosh_zero_left hv, sinh_hdist_zero hu, sinh_hdist_zero hv, InnerProductGeometry.cos_angle]
  unfold hcosh
  have e := norm_sub_sq_real u v
  rw [e]
  field_simp
  ring

/-- The hyperbolic law of cosines (book Theorem 13.16 is the case of a right angle).  For distinct
points `A, B, C` of the disc, with `a = BC_h`, `b = AC_h`, `c = AB_h`,
`cosh a = cosh b cosh c - sinh b sinh c cos ∠_h BAC`. -/
@[kb "petrunin2025" "Theorem 13.16 (law of cosines generalization), p. 111"]
theorem hlaw_cosines {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) (hBA : B ≠ A)
    (hCA : C ≠ A) :
    Real.cosh (hdist B C) = Real.cosh (hdist A B) * Real.cosh (hdist A C) -
      Real.sinh (hdist A B) * Real.sinh (hdist A C) * Real.cos (hangle B A C) := by
  have := hcosh_law_zero (norm_mobius_lt_one hA hB) (norm_mobius_lt_one hA hC)
    (mobius_ne_zero hA hB hBA) (mobius_ne_zero hA hC hCA)
  rw [hdist_mobius hA hB hC, ← hdist_eq_mobius hA hB, ← hdist_eq_mobius hA hC] at this
  exact this

end LawCos

/-! ### The dual law of cosines -/

section Dual

/-- Pure algebra behind the dual law: squares of `sin α sinh b sinh c` and `sin β sinh a sinh c`
agree (both equal the Gram-type quantity `1 - ca² - cb² - cc² + 2 ca cb cc`). -/
theorem core_K {a b c x y p q : ℝ}
    (hp2 : p ^ 2 = 1 - x ^ 2) (hq2 : q ^ 2 = 1 - y ^ 2)
    (L1 : Real.cosh a = Real.cosh b * Real.cosh c - Real.sinh b * Real.sinh c * x)
    (L2 : Real.cosh b = Real.cosh a * Real.cosh c - Real.sinh a * Real.sinh c * y) :
    (p * Real.sinh b * Real.sinh c) ^ 2 =
        1 - Real.cosh a ^ 2 - Real.cosh b ^ 2 - Real.cosh c ^ 2 +
          2 * Real.cosh a * Real.cosh b * Real.cosh c ∧
    (q * Real.sinh a * Real.sinh c) ^ 2 =
        1 - Real.cosh a ^ 2 - Real.cosh b ^ 2 - Real.cosh c ^ 2 +
          2 * Real.cosh a * Real.cosh b * Real.cosh c := by
  have ea := Real.cosh_sq a
  have eb := Real.cosh_sq b
  have ec := Real.cosh_sq c
  set sa := Real.sinh a
  set sb := Real.sinh b
  set sc := Real.sinh c
  set ca := Real.cosh a
  set cb := Real.cosh b
  set cc := Real.cosh c
  have Lx : sb * sc * x = cb * cc - ca := by linarith
  have Ly : sa * sc * y = ca * cc - cb := by linarith
  constructor
  · have : (p * sb * sc) ^ 2 = sb ^ 2 * sc ^ 2 * p ^ 2 := by ring
    rw [this, hp2]
    have : sb ^ 2 * sc ^ 2 * (1 - x ^ 2) = sb ^ 2 * sc ^ 2 - (sb * sc * x) ^ 2 := by ring
    rw [this, Lx]
    linear_combination (-sc ^ 2) * eb + (-(cb ^ 2 - 1)) * ec
  · have : (q * sa * sc) ^ 2 = sa ^ 2 * sc ^ 2 * q ^ 2 := by ring
    rw [this, hq2]
    have : sa ^ 2 * sc ^ 2 * (1 - y ^ 2) = sa ^ 2 * sc ^ 2 - (sa * sc * y) ^ 2 := by ring
    rw [this, Ly]
    linear_combination (-sc ^ 2) * ea + (-(ca ^ 2 - 1)) * ec

/-- Pure algebra behind the dual law: from the three laws of cosines. -/
theorem dual_core {a b c x y z p q : ℝ} (ha : 0 < Real.sinh a) (hb : 0 < Real.sinh b)
    (hc : 0 < Real.sinh c) (hp : 0 ≤ p) (hq : 0 ≤ q) (hp2 : p ^ 2 = 1 - x ^ 2)
    (hq2 : q ^ 2 = 1 - y ^ 2)
    (L1 : Real.cosh a = Real.cosh b * Real.cosh c - Real.sinh b * Real.sinh c * x)
    (L2 : Real.cosh b = Real.cosh a * Real.cosh c - Real.sinh a * Real.sinh c * y)
    (L3 : Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * z) :
    z = -x * y + p * q * Real.cosh c := by
  obtain ⟨h1, h2⟩ := core_K hp2 hq2 L1 L2
  have ea := Real.cosh_sq a
  have eb := Real.cosh_sq b
  have ec := Real.cosh_sq c
  set sa := Real.sinh a
  set sb := Real.sinh b
  set sc := Real.sinh c
  set ca := Real.cosh a
  set cb := Real.cosh b
  set cc := Real.cosh c
  set K : ℝ := 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc with hK
  have Lx : sb * sc * x = cb * cc - ca := by linarith
  have Ly : sa * sc * y = ca * cc - cb := by linarith
  have Lz : sa * sb * z = ca * cb - cc := by linarith
  have h3 : p * sb * sc = q * sa * sc :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp (h1.trans h2.symm)
  have h4 : p * q * (sa * sb * sc ^ 2) = K := by
    rw [← h1]
    have : p * q * (sa * sb * sc ^ 2) = (p * sb * sc) * (q * sa * sc) := by ring
    rw [this, ← h3]; ring
  have hne : sa * sb * sc ^ 2 ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  have : (-x * y + p * q * cc) * (sa * sb * sc ^ 2) =
      -(sb * sc * x) * (sa * sc * y) + K * cc := by
    rw [← h4]; ring
  rw [this, Lx, Ly, hK]
  have : z * (sa * sb * sc ^ 2) = (sa * sb * z) * sc ^ 2 := by ring
  rw [this, Lz]
  linear_combination (-(ca * cb - cc)) * ec

theorem hangle_comm (P Q R : ℂ) : hangle P Q R = hangle R Q P :=
  InnerProductGeometry.angle_comm _ _

theorem sinh_hdist_pos {P Q : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (h : P ≠ Q) :
    0 < Real.sinh (hdist P Q) :=
  Real.sinh_pos_iff.mpr ((hdist_nonneg hP hQ).lt_of_ne' (fun e => h ((hdist_eq_zero_iff hP hQ).mp e)))

/-- The three laws of cosines of a triangle, in the normalization `a = BC_h`, `b = AC_h`,
`c = AB_h`, `α = ∠_h BAC`, `β = ∠_h ABC`, `γ = ∠_h ACB`. -/
theorem three_laws {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) (hAB : A ≠ B)
    (hAC : A ≠ C) (hBC : B ≠ C) :
    Real.cosh (hdist B C) = Real.cosh (hdist A C) * Real.cosh (hdist A B) -
        Real.sinh (hdist A C) * Real.sinh (hdist A B) * Real.cos (hangle B A C) ∧
    Real.cosh (hdist A C) = Real.cosh (hdist B C) * Real.cosh (hdist A B) -
        Real.sinh (hdist B C) * Real.sinh (hdist A B) * Real.cos (hangle A B C) ∧
    Real.cosh (hdist A B) = Real.cosh (hdist B C) * Real.cosh (hdist A C) -
        Real.sinh (hdist B C) * Real.sinh (hdist A C) * Real.cos (hangle A C B) := by
  have L1 := hlaw_cosines hA hB hC hAB.symm hAC.symm
  have L2 := hlaw_cosines hB hA hC hAB hBC.symm
  have L3 := hlaw_cosines hC hA hB hAC hBC
  rw [hdist_comm B A] at L2
  rw [hdist_comm C A, hdist_comm C B] at L3
  refine ⟨?_, ?_, ?_⟩
  · rw [L1]; ring
  · rw [L2]; ring
  · rw [L3]; ring

/-- The dual law of cosines: for distinct `A, B, C` in the disc, with `α = ∠_h BAC`, `β = ∠_h ABC`,
`γ = ∠_h ACB`: `cos γ = - cos α cos β + sin α sin β cosh (AB_h)`. -/
@[kb "petrunin2025" "Theorem 13.10, proof ingredient (dual law of cosines), p. 107"]
theorem hdual_law {A B C : ℂ} (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) (hAB : A ≠ B)
    (hAC : A ≠ C) (hBC : B ≠ C) :
    Real.cos (hangle A C B) = -Real.cos (hangle B A C) * Real.cos (hangle A B C) +
      Real.sin (hangle B A C) * Real.sin (hangle A B C) * Real.cosh (hdist A B) := by
  obtain ⟨L1, L2, L3⟩ := three_laws hA hB hC hAB hAC hBC
  refine dual_core (a := hdist B C) (b := hdist A C) (c := hdist A B) (sinh_hdist_pos hB hC hBC)
    (sinh_hdist_pos hA hC hAC) (sinh_hdist_pos hA hB hAB)
    (InnerProductGeometry.sin_angle_nonneg _ _)
    (InnerProductGeometry.sin_angle_nonneg _ _) ?_ ?_ L1 L2 L3
  · have := Real.sin_sq_add_cos_sq (hangle B A C); linarith
  · have := Real.sin_sq_add_cos_sq (hangle A B C); linarith

/-- If the angle at `X` of a triangle has positive sine, so does the angle at `Y`. -/
theorem sin_pos_next {X Y Z : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (hZ : ‖Z‖ < 1) (hXY : X ≠ Y)
    (hXZ : X ≠ Z) (hYZ : Y ≠ Z) (h : 0 < Real.sin (hangle Y X Z)) :
    0 < Real.sin (hangle X Y Z) := by
  obtain ⟨L1, L2, -⟩ := three_laws hX hY hZ hXY hXZ hYZ
  have hp2 : Real.sin (hangle Y X Z) ^ 2 = 1 - Real.cos (hangle Y X Z) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (hangle Y X Z); linarith
  have hq2 : Real.sin (hangle X Y Z) ^ 2 = 1 - Real.cos (hangle X Y Z) ^ 2 := by
    have := Real.sin_sq_add_cos_sq (hangle X Y Z); linarith
  obtain ⟨h1, h2⟩ := core_K hp2 hq2 L1 L2
  have ha := sinh_hdist_pos hY hZ hYZ
  have hb := sinh_hdist_pos hX hZ hXZ
  have hc := sinh_hdist_pos hX hY hXY
  have hq0 := InnerProductGeometry.sin_angle_nonneg (mobius Y X) (mobius Y Z)
  by_contra hcon
  have hq : Real.sin (hangle X Y Z) = 0 := le_antisymm (not_lt.mp hcon) hq0
  rw [hq] at h2
  have : (Real.sin (hangle Y X Z) * Real.sinh (hdist X Z) * Real.sinh (hdist X Y)) ^ 2 = 0 := by
    rw [h1, ← h2]; ring
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  have : 0 < Real.sin (hangle Y X Z) * Real.sinh (hdist X Z) * Real.sinh (hdist X Y) := by positivity
  linarith

end Dual

/-! ### Theorem 13.10: positive defect -/

section Defect

/-- Pure algebra: if `cos γ < 1` (no degenerate angle at `C`), then `cos α + cos β > 0`. -/
theorem cos_add_pos_core {a b c x y z : ℝ} (ha : 0 < Real.sinh a) (hb : 0 < Real.sinh b)
    (hc : 0 < Real.sinh c)
    (L1 : Real.cosh a = Real.cosh b * Real.cosh c - Real.sinh b * Real.sinh c * x)
    (L2 : Real.cosh b = Real.cosh a * Real.cosh c - Real.sinh a * Real.sinh c * y)
    (L3 : Real.cosh c = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * z)
    (hz : z < 1) : 0 < x + y := by
  have ea := Real.cosh_sq a
  have eb := Real.cosh_sq b
  set sa := Real.sinh a
  set sb := Real.sinh b
  set sc := Real.sinh c
  set ca := Real.cosh a
  set cb := Real.cosh b
  set cc := Real.cosh c
  have Lx : sb * sc * x = cb * cc - ca := by linarith
  have Ly : sa * sc * y = ca * cc - cb := by linarith
  have Lz : sa * sb * z = ca * cb - cc := by linarith
  have hca : 0 < ca := Real.cosh_pos _
  have hcb : 0 < cb := Real.cosh_pos _
  have key : sa * sb * sc * (x + y) = (sa * cb + sb * ca) * (sa * sb * (1 - z)) := by
    linear_combination sa * Lx + sb * Ly + (sa * cb + sb * ca) * Lz + (sa * ca) * eb +
      (sb * cb) * ea
  have hpos : 0 < (sa * cb + sb * ca) * (sa * sb * (1 - z)) := by
    have : 0 < 1 - z := by linarith
    positivity
  rw [← key] at hpos
  have : 0 < sa * sb * sc := by positivity
  exact pos_of_mul_pos_right hpos this.le

theorem lt_of_cos_lt {x y : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ π) (hy : 0 ≤ y) (hyπ : y ≤ π)
    (h : Real.cos y < Real.cos x) : x < y := by
  by_contra hle
  rw [not_lt] at hle
  have := Real.cos_le_cos_of_nonneg_of_le_pi hy hxπ hle
  linarith

/-- A nondegenerate h-triangle `ABC`: points of the disc with `B, C ≠ A` and not on one h-line.
The h-line through `A` and `B` is the image under `mobius (-A)` of the diameter through
`mobius A B` (h-lines through `A` are diameters in the picture of the h-motion `mobius A`), so
`C` lies on it iff `mobius A C` is a real multiple of `mobius A B`. -/
def HTriangleNondeg (A B C : ℂ) : Prop :=
  ‖A‖ < 1 ∧ ‖B‖ < 1 ∧ ‖C‖ < 1 ∧ B ≠ A ∧ C ≠ A ∧ ∀ t : ℝ, mobius A C ≠ (t : ℂ) * mobius A B

theorem HTriangleNondeg.angle_pos_lt {A B C : ℂ} (h : HTriangleNondeg A B C) :
    0 < hangle B A C ∧ hangle B A C < π := by
  obtain ⟨hA, hB, hC, hBA, hCA, hnc⟩ := h
  have h1 := mobius_ne_zero hA hB hBA
  unfold hangle
  refine ⟨lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _) (fun e => ?_),
    lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _) (fun e => ?_)⟩
  · obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_zero_iff.mp e.symm
    exact hnc r (by rw [hr, Complex.real_smul])
  · obtain ⟨-, r, -, hr⟩ := InnerProductGeometry.angle_eq_pi_iff.mp e
    exact hnc r (by rw [hr, Complex.real_smul])

theorem HTriangleNondeg.ne_bc {A B C : ℂ} (h : HTriangleNondeg A B C) : B ≠ C := by
  obtain ⟨-, -, -, -, -, hnc⟩ := h
  intro e
  exact hnc 1 (by rw [e]; simp)

/-- In a nondegenerate h-triangle all three angles have positive sine (are strictly between
`0` and `π`). -/
theorem HTriangleNondeg.sin_pos {A B C : ℂ} (h : HTriangleNondeg A B C) :
    0 < Real.sin (hangle B A C) ∧ 0 < Real.sin (hangle A B C) ∧ 0 < Real.sin (hangle A C B) := by
  have hbc := h.ne_bc
  obtain ⟨hl, hu⟩ := h.angle_pos_lt
  obtain ⟨hA, hB, hC, hBA, hCA, -⟩ := h
  have sa := Real.sin_pos_of_pos_of_lt_pi hl hu
  refine ⟨sa, sin_pos_next hA hB hC hBA.symm hCA.symm hbc sa, ?_⟩
  exact sin_pos_next hA hC hB hCA.symm hBA.symm hbc.symm (by rwa [hangle_comm])

/-- Theorem 13.10: every nondegenerate h-triangle has positive defect: the sum
`∠_h BAC + ∠_h ABC + ∠_h ACB` of its angles is `< π`. -/
@[kb "petrunin2025" "Theorem 13.10, p. 107"]
theorem hangle_sum_lt_pi {A B C : ℂ} (h : HTriangleNondeg A B C) :
    hangle B A C + hangle A B C + hangle A C B < π := by
  have hbc := h.ne_bc
  obtain ⟨sα, sβ, sγ⟩ := h.sin_pos
  obtain ⟨hA, hB, hC, hBA, hCA, -⟩ := h
  have hAB := hBA.symm
  have hAC := hCA.symm
  obtain ⟨L1, L2, L3⟩ := three_laws hA hB hC hAB hAC hbc
  have D := hdual_law hA hB hC hAB hAC hbc
  have nα := InnerProductGeometry.angle_nonneg (mobius A B) (mobius A C)
  have uα := InnerProductGeometry.angle_le_pi (mobius A B) (mobius A C)
  have nβ := InnerProductGeometry.angle_nonneg (mobius B A) (mobius B C)
  have uβ := InnerProductGeometry.angle_le_pi (mobius B A) (mobius B C)
  have nγ := InnerProductGeometry.angle_nonneg (mobius C A) (mobius C B)
  have uγ := InnerProductGeometry.angle_le_pi (mobius C A) (mobius C B)
  change 0 ≤ hangle B A C at nα
  change hangle B A C ≤ π at uα
  change 0 ≤ hangle A B C at nβ
  change hangle A B C ≤ π at uβ
  change 0 ≤ hangle A C B at nγ
  change hangle A C B ≤ π at uγ
  have hz : Real.cos (hangle A C B) < 1 := by
    have := Real.sin_sq_add_cos_sq (hangle A C B)
    nlinarith [Real.cos_le_one (hangle A C B)]
  have hs := cos_add_pos_core (sinh_hdist_pos hB hC hbc) (sinh_hdist_pos hA hC hAC)
    (sinh_hdist_pos hA hB hAB) L1 L2 L3 hz
  have h1 : hangle B A C < π - hangle A B C := by
    have : Real.cos (π - hangle A B C) < Real.cos (hangle B A C) := by
      rw [Real.cos_pi_sub]; linarith
    exact lt_of_cos_lt nα uα (by linarith) (by linarith) this
  have hcc : 1 < Real.cosh (hdist A B) :=
    Real.one_lt_cosh.mpr (Real.sinh_pos_iff.mp (sinh_hdist_pos hA hB hAB)).ne'
  have hpq := mul_pos sα sβ
  have h2 : Real.cos (π - (hangle B A C + hangle A B C)) < Real.cos (hangle A C B) := by
    rw [Real.cos_pi_sub, Real.cos_add]
    nlinarith
  have := lt_of_cos_lt nγ uγ (by linarith) (by linarith) h2
  linarith

end Defect

/-! ### Theorem 13.11: AAA congruence -/

section AAA

theorem eq_of_dual {x y z p q c c' : ℝ} (hpq : 0 < p * q) (d : z = -x * y + p * q * c)
    (d' : z = -x * y + p * q * c') : c = c' := by
  have : p * q * c = p * q * c' := by linarith
  exact mul_left_cancel₀ hpq.ne' this

theorem hdist_eq_of_cosh_eq {P Q P' Q' : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hP' : ‖P'‖ < 1)
    (hQ' : ‖Q'‖ < 1) (h : Real.cosh (hdist P Q) = Real.cosh (hdist P' Q')) :
    hdist P Q = hdist P' Q' := by
  rw [← Real.arcosh_cosh (hdist_nonneg hP hQ), h, Real.arcosh_cosh (hdist_nonneg hP' hQ')]

/-- Theorem 13.11 (AAA congruence condition).  Two nondegenerate h-triangles `ABC`, `A'B'C'`
whose corresponding angles are equal are congruent: all three pairs of corresponding sides have
equal h-length (from the dual law of cosines, which gives `cosh` of each side in terms of the
angles) and then there is an h-motion (composite of `mobius`, a rotation about the centre and
possibly `conj`) taking `A, B, C` to `A', B', C'` (by SAS, `hsas`).  The book allows the signed
angles to agree up to sign; the unsigned `hangle` is exactly that. -/
@[kb "petrunin2025" "Theorem 13.11, p. 108"]
theorem haaa {A B C A' B' C' : ℂ} (h : HTriangleNondeg A B C) (h' : HTriangleNondeg A' B' C')
    (e1 : hangle B A C = hangle B' A' C') (e2 : hangle A B C = hangle A' B' C')
    (e3 : hangle A C B = hangle A' C' B') :
    hdist A B = hdist A' B' ∧ hdist A C = hdist A' C' ∧ hdist B C = hdist B' C' ∧
      ∃ v : ℂ, ‖v‖ = 1 ∧
        ((hmotion A' v A A = A' ∧ hmotion A' v A B = B' ∧ hmotion A' v A C = C') ∨
         (hmotionConj A' v A A = A' ∧ hmotionConj A' v A B = B' ∧ hmotionConj A' v A C = C')) := by
  have hbc := h.ne_bc
  have hbc' := h'.ne_bc
  obtain ⟨sα, sβ, sγ⟩ := h.sin_pos
  obtain ⟨hA, hB, hC, hBA, hCA, -⟩ := h
  obtain ⟨hA', hB', hC', hBA', hCA', -⟩ := h'
  have hAB := hBA.symm
  have hAC := hCA.symm
  have hAB' := hBA'.symm
  have hAC' := hCA'.symm
  have D1 := hdual_law hA hB hC hAB hAC hbc
  have D1' := hdual_law hA' hB' hC' hAB' hAC' hbc'
  have D2 := hdual_law hA hC hB hAC hAB hbc.symm
  have D2' := hdual_law hA' hC' hB' hAC' hAB' hbc'.symm
  rw [hangle_comm C A B] at D2
  rw [hangle_comm C' A' B'] at D2'
  rw [← e1, ← e2, ← e3] at D1'
  rw [← e1, ← e2, ← e3] at D2'
  have c1 := eq_of_dual (mul_pos sα sβ) D1 D1'
  have c2 := eq_of_dual (mul_pos sα sγ) D2 D2'
  have d1 := hdist_eq_of_cosh_eq hA hB hA' hB' c1
  have d2 := hdist_eq_of_cosh_eq hA hC hA' hC' c2
  obtain ⟨d3, v, hv, hm⟩ := hsas hB hA hC hB' hA' hC' hBA hCA hBA' hCA'
    d1 d2 e1
  exact ⟨d1, d2, d3, v, hv, hm⟩

end AAA

/-! ### Proposition 13.14: circumference of an h-circle -/

section Circumference

/-- The h-length of the parametrized curve `γ : ℝ → ℂ` over `[a, b]` in the conformal disc model:
the integral of the conformal factor of Lemma 13.13 against the Euclidean speed,
`∫_a^b 2 ‖γ'(θ)‖ / (1 - ‖γ(θ)‖²) dθ`.  (Lemma 13.13, `tendsto_hdist_div_norm`, says that
`2/(1 - ‖P‖²)` is the infinitesimal ratio of h-distance to Euclidean distance at `P`.) -/
noncomputable def hlength (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ θ in a..b, 2 * ‖deriv γ θ‖ / (1 - ‖γ θ‖ ^ 2)

/-- The standard parametrization `θ ↦ ρ e^{iθ}` of the Euclidean circle of radius `ρ` about the
centre. -/
noncomputable def circleParam (ρ : ℝ) (θ : ℝ) : ℂ := (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem hasDerivAt_circleParam (ρ θ : ℝ) :
    HasDerivAt (circleParam ρ) ((ρ : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ := by
  have h1 : HasDerivAt (fun z : ℂ => (ρ : ℂ) * Complex.exp (z * Complex.I))
      ((ρ : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * (1 * Complex.I))) (θ : ℂ) :=
    (((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp).const_mul (ρ : ℂ)
  have := h1.comp_ofReal
  have e : circleParam ρ = fun y : ℝ => (ρ : ℂ) * Complex.exp ((y : ℂ) * Complex.I) := rfl
  rw [e]
  simpa using this

theorem norm_circleParam {ρ : ℝ} (h : 0 ≤ ρ) (θ : ℝ) : ‖circleParam ρ θ‖ = ρ := by
  simp [circleParam, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg h]

theorem norm_deriv_circleParam {ρ : ℝ} (h : 0 ≤ ρ) (θ : ℝ) : ‖deriv (circleParam ρ) θ‖ = ρ := by
  rw [(hasDerivAt_circleParam _ θ).deriv]
  simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg h]

/-- Proposition 13.14 (circumference of the h-circle).  Let `r ≥ 0` and `ρ = tanh (r/2)`.  The
curve `θ ↦ ρ e^{iθ}`, `θ ∈ [0, 2π]`, runs once around the h-circle `hcircle 0 r` of h-radius `r`
about the centre (Lemma 12.10), and its h-length, defined as the integral of the conformal factor
`2/(1 - ‖γ‖²)` (Lemma 13.13) against the Euclidean speed, is `2π sinh r`.  (The book defines the
circumference as the limit of perimeters of inscribed regular polygons and computes it through the
conformal factor; here the conformal-factor integral is taken as the length.  The general
circle follows by the motion invariance of the h-distance and is not formalized.) -/
@[kb "petrunin2025" "Proposition 13.14, p. 110"]
theorem circumference_hcircle {r : ℝ} (hr : 0 ≤ r) :
    (∀ θ : ℝ, circleParam (Real.tanh (r / 2)) θ ∈ hcircle 0 r) ∧
    hlength (circleParam (Real.tanh (r / 2))) 0 (2 * π) = 2 * π * Real.sinh r := by
  have h0 : 0 ≤ Real.tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le
  have h1 : Real.tanh (r / 2) < 1 := Real.tanh_lt_one _
  have hn := norm_circleParam h0
  refine ⟨fun θ => ?_, ?_⟩
  · rw [mem_hcircle_zero, hn]
    exact ⟨h1, rfl⟩
  · have hd := norm_deriv_circleParam h0
    unfold hlength
    simp_rw [hd, hn]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    rw [← circumference_identity r]
    ring

end Circumference

/-! ### Uniqueness of the h-line through an interior point and an ideal point (p. 103) -/

section Parallels

/-- Through a point `P` of the disc and a point `A` of the absolute there is only one h-line: if
`hline α c` and `hline α' c'` (with `α² < ‖c‖²`, `α'² < ‖c'‖²`) both contain `P` and have `A` as an
ideal point, they coincide. -/
theorem hline_eq_of_ideal_and_point {α α' : ℝ} {c c' A P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (h' : α' ^ 2 < ‖c'‖ ^ 2) (hA : A ∈ idealPts α c) (hA' : A ∈ idealPts α' c')
    (hP : P ∈ hline α c) (hP' : P ∈ hline α' c') : hline α c = hline α' c' := by
  obtain ⟨hAn, hAr⟩ := hA
  obtain ⟨-, hAr'⟩ := hA'
  obtain ⟨hPn, hPe⟩ := hP
  obtain ⟨-, hPe'⟩ := hP'
  have hA2 : A.re ^ 2 + A.im ^ 2 = 1 := by rw [← sq_norm_eq, hAn]; norm_num
  have hP2 : P.re ^ 2 + P.im ^ 2 < 1 := by rw [← sq_norm_eq]; nlinarith [norm_nonneg P]
  have hN : 0 < c.re ^ 2 + c.im ^ 2 := by rw [← sq_norm_eq]; nlinarith [sq_nonneg α]
  have hN' : 0 < c'.re ^ 2 + c'.im ^ 2 := by rw [← sq_norm_eq]; nlinarith [sq_nonneg α']
  rw [re_conj_mul] at hAr hAr' hPe hPe'
  rw [sq_norm_eq] at hPe hPe'
  set wr : ℝ := 2 * P.re - (P.re ^ 2 + P.im ^ 2 + 1) * A.re with hwr
  set wi : ℝ := 2 * P.im - (P.re ^ 2 + P.im ^ 2 + 1) * A.im with hwi
  have e1 : c.re * wr + c.im * wi = 0 := by
    rw [hwr, hwi]; linear_combination (-1 : ℝ) * hPe - (P.re ^ 2 + P.im ^ 2 + 1) * hAr
  have e2 : c'.re * wr + c'.im * wi = 0 := by
    rw [hwr, hwi]; linear_combination (-1 : ℝ) * hPe' - (P.re ^ 2 + P.im ^ 2 + 1) * hAr'
  have hw : wr ≠ 0 ∨ wi ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hwr] at h1
    rw [hwi] at h2
    have : 4 * (P.re ^ 2 + P.im ^ 2) = (P.re ^ 2 + P.im ^ 2 + 1) ^ 2 := by
      linear_combination (2 * P.re + (P.re ^ 2 + P.im ^ 2 + 1) * A.re) * h1 +
        (2 * P.im + (P.re ^ 2 + P.im ^ 2 + 1) * A.im) * h2 +
        (P.re ^ 2 + P.im ^ 2 + 1) ^ 2 * hA2
    nlinarith [sq_nonneg (P.re ^ 2 + P.im ^ 2 - 1)]
  have hx : c.re * c'.im - c.im * c'.re = 0 := by
    rcases hw with hv | hv
    · have : wr * (c.re * c'.im - c.im * c'.re) = 0 := by
        linear_combination c'.im * e1 - c.im * e2
      exact (mul_eq_zero.mp this).resolve_left hv
    · have : wi * (c.re * c'.im - c.im * c'.re) = 0 := by
        linear_combination c.re * e2 - c'.re * e1
      exact (mul_eq_zero.mp this).resolve_left hv
  set μ := (c.re * c'.re + c.im * c'.im) / (c.re ^ 2 + c.im ^ 2) with hμ
  have hc1 : c'.re = μ * c.re := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-c.im) * hx
  have hc2 : c'.im = μ * c.im := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination c.re * hx
  have hα : α' = μ * α := by
    rw [← hAr', hc1, hc2, ← hAr]; ring
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc1 hc2
    rw [hc1, hc2] at hN'
    simp at hN'
  exact (hline_eq_of_proportional hμ0 hc1 hc2 hα).symm

/-- Definition p. 103 and the claim that follows it ("exactly two"): through a point `P` of the
disc off the h-line `ℓ = hline α c` there pass two different asymptotically parallel h-lines to
`ℓ` (one through each ideal point), and every h-line through `P` asymptotically parallel to `ℓ`
coincides (as a set) with one of them. -/
@[kb "petrunin2025" "Definition (asymptotically parallel), p. 103"]
theorem exactly_two_asymParallel {α : ℝ} {c P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) :
    ∃ (α₁ : ℝ) (c₁ : ℂ) (α₂ : ℝ) (c₂ : ℂ), AsymParallel α c α₁ c₁ ∧ AsymParallel α c α₂ c₂ ∧
      P ∈ hline α₁ c₁ ∧ P ∈ hline α₂ c₂ ∧ idealPts α₁ c₁ ≠ idealPts α₂ c₂ ∧
      ∀ (α' : ℝ) (c' : ℂ), AsymParallel α c α' c' → P ∈ hline α' c' →
        hline α' c' = hline α₁ c₁ ∨ hline α' c' = hline α₂ c₂ := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_idealPts h
  obtain ⟨α₁, c₁, h1, hP1, hA1⟩ := exists_hline_through hA.1 hP
  obtain ⟨α₂, c₂, h2, hP2, hB2⟩ := exists_hline_through hB.1 hP
  have hall : ∀ z ∈ idealPts α c, z = A ∨ z = B := by
    have hS := idealPts_eq h
    intro z hz
    have hA' := hA
    have hB' := hB
    rw [hS] at hz hA' hB'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hA' hB'
    rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl <;> rcases hz with rfl | rfl <;>
      simp_all
  refine ⟨α₁, c₁, α₂, c₂, ⟨h, h1, ?_, A, hA, hA1⟩, ⟨h, h2, ?_, B, hB, hB2⟩, hP1, hP2, ?_, ?_⟩
  · intro e
    exact hPl (mem_hline_of_two_common h h1 hAB hA hB hA1 (by rw [← e]; exact hB) hP1)
  · intro e
    exact hPl (mem_hline_of_two_common h h2 hAB hA hB (by rw [← e]; exact hA) hB2 hP2)
  · intro e
    exact hPl (mem_hline_of_two_common h h1 hAB hA hB hA1 (by rw [e]; exact hB2) hP1)
  · rintro α' c' ⟨-, h', -, z, hz, hz'⟩ hPm
    rcases hall z hz with e | e
    · rw [e] at hz'
      left
      exact (hline_eq_of_ideal_and_point h1 h' hA1 hz' hP1 hPm).symm
    · rw [e] at hz'
      right
      exact (hline_eq_of_ideal_and_point h2 h' hB2 hz' hP2 hPm).symm

end Parallels

end UndergradKB.Geometry
