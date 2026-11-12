import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import UndergradKB.Geometry.HPlaneNeutral
import UndergradKB.Geometry.NeutralConditions
import UndergradKB.Geometry.HypInradius
import UndergradKB.Geometry.NeutralEuclidean
import UndergradKB.Geometry.Parallels
import UndergradKB.Geometry.Lines
import UndergradKB.Common.Attr

/-! # Theorem 11.16 on the two models (Petrunin, Chapter 11D, p. 88)

Petrunin's Theorem 11.16 (stated without proof in the book): a neutral plane is Euclidean iff one of
(a) there is a line and a point off it with exactly one parallel through the point,
(b) every nondegenerate triangle can be circumscribed,
(c) there are two distinct lines at bounded distance from each other,
(d) there are triangles of arbitrarily large inradius,
(e) there is a nondegenerate triangle of zero defect,
(f) there is a rectangle.

The abstract theorem needs the whole development of neutral geometry.  The conditions are stated for an arbitrary
`NeutralPlane` in `NeutralConditions`; here we verify the theorem on the two models of the repository: in the h-plane
(`hyperbolicNeutralPlane`) all of (a)-(f) fail, and in the Euclidean plane all of them hold. -/

namespace UndergradKB.Geometry

open Complex ComplexConjugate


/-! ## The h-plane: all six conditions fail -/

section HPlane

open HPoint

/-- (a) fails in the h-plane: Axiom h-V gives two parallels. -/
@[kb "petrunin2025" "Theorem 11.16 (a), p. 88"]
theorem hyperbolic_not_onlyOneParallel : ¬ hyperbolicNeutralPlane.OnlyOneParallel := by
  rintro ⟨ℓ, hℓ, Q, hQ, m, -, huniq⟩
  obtain ⟨m1, m2, hne, h1, h2⟩ := hyperbolicNeutralPlane_axiomHV ℓ hℓ Q hQ
  exact hne ((huniq m1 h1).trans (huniq m2 h2).symm)

/-- If `mobius A C` is a real multiple of `mobius A B` then `A, B, C` lie on one h-line. -/
theorem degenerate_of_mobius_smul {A B C : HPoint} (hAB : A ≠ B) {t : ℝ}
    (h : mobius A.z C.z = (t : ℂ) * mobius A.z B.z) : IsTriangle.Degenerate A B C := by
  have hne : A.z ≠ B.z := fun e => hAB (HPoint.ext e)
  obtain ⟨α, c, hlt, hA, hB, -⟩ := exists_unique_hline A.norm_lt B.norm_lt hne
  have han : ‖-A.z‖ < 1 := by simpa using A.norm_lt
  have key : ∀ w : ℂ, ‖w‖ < 1 → (w ∈ hline α c ↔
      mobius A.z w ∈ hline (mα (-A.z) α c) (mc (-A.z) α c)) := by
    intro w hw
    have := mobius_mem_hline_iff (α := α) (c := c) han (norm_mobius_lt_one A.norm_lt hw)
    rw [mobius_neg_mobius A.norm_lt hw] at this
    exact this
  have h0 : mobius A.z A.z ∈ hline (mα (-A.z) α c) (mc (-A.z) α c) := (key _ A.norm_lt).1 hA
  rw [mobius_self A.norm_lt] at h0
  have hα : mα (-A.z) α c = 0 := by
    have := h0.2
    simpa using this
  have hB' := (key _ B.norm_lt).1 hB
  rw [hα] at hB'
  have hC : mobius A.z C.z ∈ hline (mα (-A.z) α c) (mc (-A.z) α c) := by
    rw [hα]
    refine ⟨norm_mobius_lt_one A.norm_lt C.norm_lt, ?_⟩
    have := hB'.2
    rw [h]
    simp only [zero_mul] at this ⊢
    have e : (conj (mc (-A.z) α c) * ((t : ℂ) * mobius A.z B.z)).re =
        t * (conj (mc (-A.z) α c) * mobius A.z B.z).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [e]
    have hx : (conj (mc (-A.z) α c) * mobius A.z B.z).re = 0 := by linarith
    rw [hx]; ring
  have hCl := (key _ C.norm_lt).2 hC
  refine ⟨HPoint.hlineSet α c, (HPoint.isLine_iff _).2 ⟨α, c, hlt, HPoint.image_z_hlineSet _ _⟩,
    hA, hB, hCl⟩

theorem hnondeg_of_not_degenerate {A B C : HPoint} (hAB : A ≠ B) (hAC : A ≠ C)
    (h : ¬ IsTriangle.Degenerate A B C) : HTriangleNondeg A.z B.z C.z := by
  refine ⟨A.norm_lt, B.norm_lt, C.norm_lt, fun e => hAB (HPoint.ext e.symm),
    fun e => hAC (HPoint.ext e.symm), fun t ht => h (degenerate_of_mobius_smul hAB ht)⟩

theorem uangle_h {A O B : HPoint} (hA : A ≠ O) (hB : B ≠ O) :
    hyperbolicNeutralPlane.uangle A O B = hangle B.z O.z A.z := by
  rw [hangle_eq_abs_toReal O.norm_lt B.norm_lt A.norm_lt (fun e => hB (HPoint.ext e))
    (fun e => hA (HPoint.ext e))]
  rfl

/-- (e) fails in the h-plane: every nondegenerate h-triangle has positive defect (Theorem 13.10). -/
@[kb "petrunin2025" "Theorem 11.16 (e), p. 88"]
theorem hyperbolic_not_zeroDefect : ¬ hyperbolicNeutralPlane.ZeroDefectTriangle := by
  rintro ⟨A, B, C, ⟨hAB, hBC, hCA⟩, hnd, h0⟩
  have hn := hnondeg_of_not_degenerate hAB hCA.symm hnd
  have := hangle_sum_lt_pi hn
  unfold NeutralPlane.defect at h0
  rw [uangle_h hAB hBC.symm, uangle_h hBC hCA.symm, uangle_h hCA hAB.symm] at h0
  have c1 := hangle_comm A.z B.z C.z
  have c2 := hangle_comm B.z C.z A.z
  have c3 := hangle_comm C.z A.z B.z
  have c4 : hangle A.z C.z B.z = hangle B.z C.z A.z := hangle_comm _ _ _
  linarith

/-- The cross product `a.re * b.im - a.im * b.re = Im (conj a * b)`. -/
def cross2 (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

theorem sign_hoangle (P Q R : ℂ) :
    (hoangle P Q R).sign = SignType.sign (cross2 (mobius Q P) (mobius Q R)) := by
  have hm : ∀ a b : ℂ, SignType.sign (b / a).im = SignType.sign (cross2 a b) := by
    intro a b
    by_cases ha : a = 0
    · simp [ha, cross2]
    · have hn : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
      have : (b / a).im = cross2 a b / Complex.normSq a := by
        rw [Complex.div_im]; unfold cross2; ring
      rw [this, div_eq_mul_inv, sign_mul, sign_pos (inv_pos.2 hn), mul_one]
  rw [← hm]
  unfold hoangle
  rw [Real.Angle.sign, Real.Angle.sin_coe, Complex.sin_arg]
  set x := mobius Q R / mobius Q P
  by_cases h : x.im = 0
  · simp [h]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 (fun hx => h (by simp [hx]))
    rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.2 hpos), mul_one]

theorem cross2_identity (a b c : ℂ) :
    ((cross2 b c : ℝ) : ℂ) * a + ((cross2 c a : ℝ) : ℂ) * b + ((cross2 a b : ℝ) : ℂ) * c = 0 := by
  apply Complex.ext <;> simp [cross2] <;> ring

/-- (d) fails in the h-plane: the inradius of every h-triangle is `< ½ ln 3` (Theorem 13.6). -/
@[kb "petrunin2025" "Theorem 11.16 (d), p. 88"]
theorem hyperbolic_not_largeInradius : ¬ hyperbolicNeutralPlane.ArbitrarilyLargeInradius := by
  intro h
  obtain ⟨A, B, C, ⟨hAB, hBC, hCA⟩, -, I, ⟨s1, s2, s3⟩, hd⟩ := h (Real.log 3)
  have ne : ∀ {X Y : HPoint}, X ≠ Y → X.z ≠ Y.z := fun h e => h (HPoint.ext e)
  obtain ⟨α₁, c₁, h₁, hA1, hB1, -⟩ := exists_unique_hline A.norm_lt B.norm_lt (ne hAB)
  obtain ⟨α₂, c₂, h₂, hB2, hC2, -⟩ := exists_unique_hline B.norm_lt C.norm_lt (ne hBC)
  obtain ⟨α₃, c₃, h₃, hC3, hA3, -⟩ := exists_unique_hline C.norm_lt A.norm_lt (ne hCA)
  have mk : ∀ {α : ℝ} {c : ℂ} {U V : HPoint}, α ^ 2 < ‖c‖ ^ 2 → U.z ∈ hline α c → V.z ∈ hline α c →
      (U ∈ HPoint.hlineSet α c ∧ V ∈ HPoint.hlineSet α c) := fun _ hU hV => ⟨hU, hV⟩
  have av : ∀ {α : ℝ} {c : ℂ}, α ^ 2 < ‖c‖ ^ 2 →
      ((A ∈ HPoint.hlineSet α c ∧ B ∈ HPoint.hlineSet α c) ∨
        (B ∈ HPoint.hlineSet α c ∧ C ∈ HPoint.hlineSet α c) ∨
        (C ∈ HPoint.hlineSet α c ∧ A ∈ HPoint.hlineSet α c)) →
      ∀ X ∈ hline α c, ¬ hdist I.z X < Real.log 3 := by
    intro α c hlt hor X hX hlt'
    have := hd _ ((HPoint.isLine_iff _).2 ⟨α, c, hlt, HPoint.image_z_hlineSet _ _⟩) hor
      ⟨X, hX.1⟩ hX
    have e : dist I ⟨X, hX.1⟩ = hdist I.z X := rfl
    linarith
  have hav1 := av h₁ (Or.inl (mk h₁ hA1 hB1))
  have hav2 := av h₂ (Or.inr (Or.inl (mk h₂ hB2 hC2)))
  have hav3 := av h₃ (Or.inr (Or.inr (mk h₃ hC3 hA3)))
  -- positive dependence of the tangent directions
  have e1 : hyperbolicNeutralPlane.angle A I B = hoangle A.z I.z B.z := rfl
  have e2 : hyperbolicNeutralPlane.angle B I C = hoangle B.z I.z C.z := rfl
  have e3 : hyperbolicNeutralPlane.angle C I A = hoangle C.z I.z A.z := rfl
  simp only [e1, e2, e3, sign_hoangle] at s1 s2 s3
  have fin : ∀ l1 l2 l3 : ℝ, 0 < l1 → 0 < l2 → 0 < l3 →
      (l1 : ℂ) * mobius I.z A.z + l2 * mobius I.z B.z + l3 * mobius I.z C.z = 0 →
      False := by
    intro l1 l2 l3 p1 p2 p3 hs
    have := inradius_lt_general I.norm_lt h₁ h₂ h₃ hA1 hB1 hB2 hC2 hC3 hA3 p1 p2 p3 hs
      (Real.log_pos (by norm_num)) hav1 hav2 hav3
    have hl := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
    linarith
  set a := mobius I.z A.z
  set b := mobius I.z B.z
  set c := mobius I.z C.z
  have hid := cross2_identity a b c
  rcases lt_trichotomy (cross2 a b) 0 with hu | hu | hu
  · have hv : cross2 b c < 0 := by
      rw [← sign_eq_neg_one_iff, ← s1]; exact sign_eq_neg_one_iff.2 hu
    have hw : cross2 c a < 0 := by
      rw [← sign_eq_neg_one_iff, ← s2]; exact sign_eq_neg_one_iff.2 hv
    refine fin (-cross2 b c) (-cross2 c a) (-cross2 a b) (by linarith) (by linarith) (by linarith) ?_
    push_cast
    linear_combination (-1 : ℂ) * hid
  · exact s3 (by rw [hu]; simp)
  · have hv : 0 < cross2 b c := by
      rw [← sign_eq_one_iff, ← s1]; exact sign_eq_one_iff.2 hu
    have hw : 0 < cross2 c a := by
      rw [← sign_eq_one_iff, ← s2]; exact sign_eq_one_iff.2 hv
    exact fin _ _ _ hv hw hu hid

/-- A point of the h-plane from real coordinates. -/
def hptXY (x y : ℝ) (h : x ^ 2 + y ^ 2 < 1) : HPoint :=
  ⟨⟨x, y⟩, by
    have : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 < 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]; nlinarith
    exact (sq_lt_one_iff₀ (norm_nonneg _)).1 this⟩

/-- (b) fails in the h-plane: three points on a Euclidean circle that leaves the disc have no
h-circumcircle (every h-circle is a Euclidean circle inside the disc, Lemma 12.10, and a Euclidean circle
is determined by three of its points). -/
@[kb "petrunin2025" "Theorem 11.16 (b), p. 88"]
theorem hyperbolic_not_circumscribable : ¬ hyperbolicNeutralPlane.AllTrianglesCircumscribable := by
  intro h
  set A := hptXY (-1 / 10) 0 (by norm_num) with hA
  set B := hptXY (1 / 2) (3 / 5) (by norm_num) with hB
  set C := hptXY (1 / 2) (-3 / 5) (by norm_num) with hC
  have zA : A.z = ⟨-1 / 10, 0⟩ := rfl
  have zB : B.z = ⟨1 / 2, 3 / 5⟩ := rfl
  have zC : C.z = ⟨1 / 2, -3 / 5⟩ := rfl
  have neq : ∀ {X Y : HPoint}, X.z ≠ Y.z → X ≠ Y := fun h e => h (by rw [e])
  have hAB : A ≠ B := neq (by rw [zA, zB]; intro e; have := congrArg Complex.re e; norm_num at this)
  have hBC : B ≠ C := neq (by rw [zB, zC]; intro e; have := congrArg Complex.im e; norm_num at this)
  have hCA : C ≠ A := neq (by rw [zC, zA]; intro e; have := congrArg Complex.re e; norm_num at this)
  have hnd : ¬ IsTriangle.Degenerate A B C := by
    rintro ⟨L, hL, hAL, hBL, hCL⟩
    obtain ⟨α, c, hlt, himg⟩ := (HPoint.isLine_iff L).1 hL
    have mem : ∀ X ∈ L, X.z ∈ hline α c := fun X hX => himg ▸ ⟨X, hX, rfl⟩
    have e1 := (mem A hAL).2
    have e2 := (mem B hBL).2
    have e3 := (mem C hCL).2
    rw [zA, re_conj_mul, sq_norm_eq] at e1
    rw [zB, re_conj_mul, sq_norm_eq] at e2
    rw [zC, re_conj_mul, sq_norm_eq] at e3
    simp only at e1 e2 e3
    have hci : c.im = 0 := by nlinarith
    have hα : α = 0 := by nlinarith
    have hcr : c.re = 0 := by nlinarith
    have : ‖c‖ ^ 2 = 0 := by rw [sq_norm_eq, hci, hcr]; ring
    nlinarith [sq_nonneg α]
  obtain ⟨O, r, hOA, hOB, hOC⟩ := h A B C ⟨hAB, hBC, hCA⟩ hnd
  have hr : 0 < r := by
    rcases (show 0 ≤ r from hOA ▸ dist_nonneg).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      rw [← h0, dist_eq_zero] at hOA hOB
      exact hAB (hOA.symm.trans hOB)
  obtain ⟨Cc, ρ, hρ, hlt, -, hcirc⟩ := hcircle_eq_sphere O.norm_lt hr
  have mem : ∀ X : HPoint, dist O X = r → ‖X.z - Cc‖ = ρ := by
    intro X hX
    have : X.z ∈ hcircle O.z r := ⟨X.norm_lt, hX⟩
    rw [hcirc] at this
    simpa [dist_eq_norm] using this
  have q1 := mem A hOA
  have q2 := mem B hOB
  have q3 := mem C hOC
  rw [zA] at q1
  rw [zB] at q2
  rw [zC] at q3
  have sq : ∀ z : ℂ, ‖z - Cc‖ = ρ → (z.re - Cc.re) ^ 2 + (z.im - Cc.im) ^ 2 = ρ ^ 2 := by
    intro z hz
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]; simp [pow_two]
  have s1 := sq _ q1
  have s2 := sq _ q2
  have s3 := sq _ q3
  simp only at s1 s2 s3
  have hy : Cc.im = 0 := by nlinarith
  have hx : Cc.re = 1 / 2 := by nlinarith
  have hρ' : ρ = 3 / 5 := by nlinarith
  have hn : ‖Cc‖ = 1 / 2 := by
    have : ‖Cc‖ ^ 2 = (1 / 2) ^ 2 := by rw [sq_norm_eq, hx, hy]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1 this
  rw [hn, hρ'] at hlt
  norm_num at hlt

/-- A right h-angle at `X` makes `X, Y, Z` a nondegenerate h-triangle (based at `X`). -/
theorem hnondeg_of_right {X Y Z : HPoint} (hYX : Y ≠ X) (hZX : Z ≠ X)
    (h : hangle Y.z X.z Z.z = Real.pi / 2) : HTriangleNondeg X.z Y.z Z.z := by
  refine ⟨X.norm_lt, Y.norm_lt, Z.norm_lt, fun e => hYX (HPoint.ext e), fun e => hZX (HPoint.ext e),
    fun t ht => ?_⟩
  have hi : inner ℝ (mobius X.z Y.z) (mobius X.z Z.z) = 0 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).2 h
  have hY0 := mobius_ne_zero X.norm_lt Y.norm_lt (fun e => hYX (HPoint.ext e))
  have hZ0 := mobius_ne_zero X.norm_lt Z.norm_lt (fun e => hZX (HPoint.ext e))
  rw [ht, ← Complex.real_smul, inner_smul_right, real_inner_self_eq_norm_sq] at hi
  rcases mul_eq_zero.1 hi with h0 | h0
  · rw [h0] at ht; simp at ht; exact hZ0 ht
  · exact hY0 (by simpa using h0)

/-- (f) fails in the h-plane: the angle sum of an h-quadrangle is `< 2π` (cut along a diagonal). -/
@[kb "petrunin2025" "Theorem 11.16 (f), p. 88"]
theorem hyperbolic_not_rectangle : ¬ hyperbolicNeutralPlane.HasRectangle := by
  rintro ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, r1, r2, r3, r4⟩
  rw [uangle_h hAB hBC.symm] at r1
  rw [uangle_h hBC hCD.symm] at r2
  rw [uangle_h hCD hAD] at r3
  rw [uangle_h hAD.symm hAB.symm] at r4
  have n1 : HTriangleNondeg B.z A.z C.z :=
    hnondeg_of_right hAB hBC.symm (by rw [hangle_comm]; exact r1)
  have n2 : HTriangleNondeg D.z C.z A.z :=
    hnondeg_of_right hCD hAD (by rw [hangle_comm]; exact r3)
  have s1 := hangle_sum_lt_pi n1
  have s2 := hangle_sum_lt_pi n2
  have t1 : hangle D.z A.z B.z ≤ hangle D.z A.z C.z + hangle C.z A.z B.z :=
    InnerProductGeometry.angle_le_angle_add_angle _ _ _
  have t2 : hangle B.z C.z D.z ≤ hangle B.z C.z A.z + hangle A.z C.z D.z :=
    InnerProductGeometry.angle_le_angle_add_angle _ _ _
  have c1 := hangle_comm D.z A.z B.z
  have c2 := hangle_comm B.z C.z D.z
  have c3 := hangle_comm C.z A.z B.z
  have c4 := hangle_comm A.z C.z D.z
  have c5 := hangle_comm D.z A.z C.z
  have c6 := hangle_comm B.z C.z A.z
  have c7 := hangle_comm A.z B.z C.z
  have c8 := hangle_comm C.z D.z A.z
  have c9 := hangle_comm D.z C.z A.z
  have c10 := hangle_comm A.z C.z B.z
  have c11 := hangle_comm A.z D.z C.z
  linarith

/-! ### (c): distinct h-lines are not at bounded distance -/

section Bounded

open Filter Topology

theorem tendsto_tanh_half : Tendsto (fun t : ℝ => Real.tanh (t / 2)) atTop (𝓝 1) := by
  have hf : (fun t : ℝ => Real.tanh (t / 2)) = fun t => 1 - 2 / (Real.exp t + 1) := by
    funext t
    have : Real.exp t + 1 ≠ 0 := by positivity
    rw [tanh_half_eq]; field_simp; ring
  rw [hf]
  have h1 : Tendsto (fun t : ℝ => Real.exp t + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ Real.tendsto_exp_atTop
  have h2 : Tendsto (fun t : ℝ => 2 / (Real.exp t + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2

/-- If `X` is within h-distance `C` of a point `Y` of the h-line `hline β d`, then `hE β d X` is small
compared to `√(1 - ‖X‖²)`. -/
theorem hE_bound {β : ℝ} {d X Y : ℂ} {C : ℝ} (hX : ‖X‖ < 1) (hY : Y ∈ hline β d)
    (hC : hdist X Y ≤ C) :
    |hE β d X| ≤ (2 * |β| + 2 * ‖d‖) * (Real.sinh (C / 2) * Real.sqrt (1 - ‖X‖ ^ 2)) := by
  have hY1 := hY.1
  have hY0 : hE β d Y = 0 := (mem_hline_iff.1 hY).2
  have hn : ‖X - Y‖ ≤ Real.sinh (C / 2) * Real.sqrt (1 - ‖X‖ ^ 2) := by
    have h := hdist_eq_two_arsinh hX hY1
    set s := ‖X - Y‖ * hscale X Y with hs
    have hs0 : 0 ≤ s := mul_nonneg (norm_nonneg _) (hscale_pos hX hY1).le
    have hs' : s = Real.sinh (hdist X Y / 2) := by
      rw [h, mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]
    have hsle : s ≤ Real.sinh (C / 2) := by
      rw [hs']; exact Real.sinh_le_sinh.2 (by linarith)
    have hD : 0 < (1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2) := mul_pos (one_sub_sq_pos hX) (one_sub_sq_pos hY1)
    have hsq : 0 < Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2)) := Real.sqrt_pos.2 hD
    have hnorm : ‖X - Y‖ = s * Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2)) := by
      rw [hs, hscale]; field_simp
    have hle : Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - ‖Y‖ ^ 2)) ≤ Real.sqrt (1 - ‖X‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      have := one_sub_sq_pos hX
      nlinarith [sq_nonneg ‖Y‖]
    rw [hnorm]
    exact mul_le_mul hsle hle hsq.le (hs0.trans hsle)
  have e : hE β d X = β * (‖X‖ ^ 2 - ‖Y‖ ^ 2) - 2 * (conj d * (X - Y)).re := by
    have : hE β d X = hE β d X - hE β d Y := by rw [hY0]; ring
    rw [this]; unfold hE; simp only [mul_sub, Complex.sub_re]; ring
  have b1 : |‖X‖ ^ 2 - ‖Y‖ ^ 2| ≤ 2 * ‖X - Y‖ := by
    have : ‖X‖ ^ 2 - ‖Y‖ ^ 2 = (‖X‖ - ‖Y‖) * (‖X‖ + ‖Y‖) := by ring
    rw [this, abs_mul]
    have h1 := abs_norm_sub_norm_le X Y
    have h2 : |‖X‖ + ‖Y‖| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]; linarith
    calc |‖X‖ - ‖Y‖| * |‖X‖ + ‖Y‖| ≤ ‖X - Y‖ * 2 :=
          mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = 2 * ‖X - Y‖ := by ring
  have b2 : |(conj d * (X - Y)).re| ≤ ‖d‖ * ‖X - Y‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  rw [e]
  calc |β * (‖X‖ ^ 2 - ‖Y‖ ^ 2) - 2 * (conj d * (X - Y)).re|
      ≤ |β * (‖X‖ ^ 2 - ‖Y‖ ^ 2)| + |2 * (conj d * (X - Y)).re| := abs_sub _ _
    _ ≤ |β| * (2 * ‖X - Y‖) + 2 * (‖d‖ * ‖X - Y‖) := by
        rw [abs_mul, abs_mul, abs_two]
        gcongr
    _ = (2 * |β| + 2 * ‖d‖) * ‖X - Y‖ := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hn
        positivity

theorem continuous_hE (β : ℝ) (d : ℂ) : Continuous (hE β d) := by
  unfold hE; fun_prop

/-- A path in the disc that tends to a point `e` of the absolute, along which the points stay within
bounded h-distance of `hline β d`, forces `hE β d e = 0`. -/
theorem hE_zero_of_bounded {F : Filter ℝ} [F.NeBot] {γ : ℝ → ℂ} {e : ℂ} (hγ : ∀ t, ‖γ t‖ < 1)
    (hT : Tendsto γ F (𝓝 e)) (he : ‖e‖ = 1) {β : ℝ} {d : ℂ} {C : ℝ}
    (h : ∀ t, ∃ Y ∈ hline β d, hdist (γ t) Y ≤ C) : hE β d e = 0 := by
  have hf : Tendsto (fun t => |hE β d (γ t)|) F (𝓝 |hE β d e|) :=
    ((continuous_hE β d).abs.tendsto e).comp hT
  have hc : Continuous (fun z : ℂ =>
      (2 * |β| + 2 * ‖d‖) * (Real.sinh (C / 2) * Real.sqrt (1 - ‖z‖ ^ 2))) := by fun_prop
  have hg := (hc.tendsto e).comp hT
  rw [he] at hg
  simp only [Function.comp_def, one_pow, sub_self, Real.sqrt_zero, mul_zero] at hg
  have := le_of_tendsto_of_tendsto hf hg (Eventually.of_forall fun t => by
    obtain ⟨Y, hY, hd⟩ := h t
    exact hE_bound (hγ t) hY hd)
  exact abs_eq_zero.1 (le_antisymm this (abs_nonneg _))

theorem norm_mobius_neg_unit {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) : ‖mobius (-a) w‖ = 1 := by
  have hcw := conj_mul_self_unit hw
  have e : 1 - conj (-a) * w = conj (w - (-a)) * w := by
    simp only [map_neg, map_sub]
    linear_combination (-1 : ℂ) * hcw
  have hne : w - (-a) ≠ 0 := by
    intro h0
    have : w = -a := by linear_combination h0
    rw [this, norm_neg] at hw
    linarith
  unfold mobius
  rw [e, norm_div, norm_mul, Complex.norm_conj, hw, mul_one]
  exact div_self (norm_ne_zero_iff.2 hne)

theorem continuousAt_mobius_neg_unit {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) :
    ContinuousAt (mobius (-a)) w := by
  have hden : 1 - conj (-a) * w ≠ 0 := by
    intro h0
    have h1 : conj (-a) * w = 1 := by linear_combination -h0
    have h2 : ‖conj (-a) * w‖ = ‖(1 : ℂ)‖ := by rw [h1]
    rw [norm_mul, Complex.norm_conj, norm_neg, hw, norm_one, mul_one] at h2
    exact absurd h2 (ne_of_lt ha)
  have k1 : ContinuousAt (fun z : ℂ => z - -a) w := by fun_prop
  have k2 : ContinuousAt (fun z : ℂ => 1 - conj (-a) * z) w := by fun_prop
  exact k1.div k2 hden

theorem tendsto_endpoint {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) :
    Tendsto (fun t : ℝ => mobius (-a) (w * ((Real.tanh (t / 2) : ℝ) : ℂ))) atTop
      (𝓝 (mobius (-a) w)) := by
  have h1 : Tendsto (fun t : ℝ => w * ((Real.tanh (t / 2) : ℝ) : ℂ)) atTop (𝓝 w) := by
    have := (Complex.continuous_ofReal.tendsto 1).comp tendsto_tanh_half
    have := this.const_mul w
    simpa using this
  exact (continuousAt_mobius_neg_unit ha hw).tendsto.comp h1

theorem mobius_neg_unit_injective {a w₁ w₂ : ℂ} (ha : ‖a‖ < 1) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (h : mobius (-a) w₁ = mobius (-a) w₂) : w₁ = w₂ := by
  have den : ∀ w : ℂ, ‖w‖ = 1 → 1 - conj (-a) * w ≠ 0 := by
    intro w hw h0
    have h1 : conj (-a) * w = 1 := by linear_combination -h0
    have h2 : ‖conj (-a) * w‖ = ‖(1 : ℂ)‖ := by rw [h1]
    rw [norm_mul, Complex.norm_conj, norm_neg, hw, norm_one, mul_one] at h2
    exact absurd h2 (ne_of_lt ha)
  unfold mobius at h
  rw [div_eq_div_iff (den _ hw₁) (den _ hw₂)] at h
  have h3 : (w₁ - w₂) * (1 - a * conj a) = 0 := by
    simp only [map_neg] at h; linear_combination h
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact sub_eq_zero.1 h4
  · exfalso
    have h5 : a * conj a = 1 := by linear_combination -h4
    have h6 : ‖a * conj a‖ = ‖(1 : ℂ)‖ := by rw [h5]
    rw [norm_mul, Complex.norm_conj, norm_one] at h6
    nlinarith [norm_nonneg a]

/-- Distinct h-lines are never at bounded h-distance: some end of `ℓ` is not an end of `m`, and
approaching it along `ℓ` the points get far from `m`. -/
theorem hline_not_bounded {α β : ℝ} {c d : ℂ} (hα : α ^ 2 < ‖c‖ ^ 2) (hβ : β ^ 2 < ‖d‖ ^ 2)
    (hne : hline α c ≠ hline β d) (C : ℝ) :
    ¬ ∀ X ∈ hline α c, ∃ Y ∈ hline β d, hdist X Y ≤ C := by
  intro h
  obtain ⟨a, ha⟩ := exists_mem_hline hα
  obtain ⟨u, hu, hz⟩ := exists_motion hα ha
  have hr := range_hpar ha hu hz
  have ha1 := ha.1
  have hcu : ‖conj u‖ = 1 := by rw [Complex.norm_conj, hu]
  have hcu' : ‖-conj u‖ = 1 := by rw [norm_neg, hcu]
  have m1 : ∀ t, mobius (-a) (conj u * ((Real.tanh (t / 2) : ℝ) : ℂ)) ∈ hline α c :=
    fun t => hr ▸ ⟨t, rfl⟩
  have m2 : ∀ t, mobius (-a) (-conj u * ((Real.tanh (t / 2) : ℝ) : ℂ)) ∈ hline α c := by
    intro t
    refine hr ▸ ⟨-t, ?_⟩
    unfold hpar
    rw [neg_div, Real.tanh_neg]
    push_cast
    ring_nf
  -- generic argument for an end
  have key : ∀ (γ : ℝ → ℂ) (e : ℂ), (∀ t, γ t ∈ hline α c) → Tendsto γ atTop (𝓝 e) →
      ‖e‖ = 1 → e ∉ idealPts β d → False := by
    intro γ e hγ hT he hnot
    have h0 := hE_zero_of_bounded (F := atTop) (fun t => (hγ t).1) hT he (β := β) (d := d)
      (C := C) (fun t => h _ (hγ t))
    apply hnot
    refine ⟨he, ?_⟩
    unfold hE at h0
    rw [he] at h0
    linarith
  have idl : ∀ (γ : ℝ → ℂ) (e : ℂ), (∀ t, γ t ∈ hline α c) → Tendsto γ atTop (𝓝 e) →
      ‖e‖ = 1 → e ∈ idealPts α c := by
    intro γ e hγ hT he
    refine ⟨he, ?_⟩
    have h1 : Tendsto (fun t => hE α c (γ t)) atTop (𝓝 (hE α c e)) :=
      (continuous_hE α c).tendsto e |>.comp hT
    have h2 : Tendsto (fun t => hE α c (γ t)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr (fun t => ((mem_hline_iff.1 (hγ t)).2).symm)
    have h3 := tendsto_nhds_unique h1 h2
    unfold hE at h3
    rw [he] at h3
    linarith
  have T1 := tendsto_endpoint ha1 hcu
  have T2 := tendsto_endpoint ha1 hcu'
  have n1 := norm_mobius_neg_unit ha1 hcu
  have n2 := norm_mobius_neg_unit ha1 hcu'
  have i1 := idl _ _ m1 T1 n1
  have i2 := idl _ _ m2 T2 n2
  have hdiff : mobius (-a) (conj u) ≠ mobius (-a) (-conj u) := by
    intro e
    have := mobius_neg_unit_injective ha1 hcu hcu' e
    have h0 : conj u = 0 := by linear_combination (1 / 2 : ℂ) * this
    rw [h0] at hcu
    simp at hcu
  by_cases c1 : mobius (-a) (conj u) ∈ idealPts β d ∧ mobius (-a) (-conj u) ∈ idealPts β d
  · exact hne (hline_eq_of_idealPts hα hβ hdiff i1 i2 c1.1 c1.2)
  · rcases not_and_or.1 c1 with n | n
    · exact key _ _ m1 T1 n1 n
    · exact key _ _ m2 T2 n2 n

end Bounded

/-- (c) fails in the h-plane: two distinct h-lines are not at bounded h-distance. -/
@[kb "petrunin2025" "Theorem 11.16 (c), p. 88"]
theorem hyperbolic_not_boundedDistantLines : ¬ hyperbolicNeutralPlane.BoundedDistantLines := by
  rintro ⟨ℓ, m, hℓ, hm, hne, C, h⟩
  obtain ⟨α, c, hα, hℓ'⟩ := (HPoint.isLine_iff ℓ).1 hℓ
  obtain ⟨β, d, hβ, hm'⟩ := (HPoint.isLine_iff m).1 hm
  refine hline_not_bounded hα hβ ?_ C ?_
  · intro e
    apply hne
    apply Set.image_injective.2 HPoint.z_injective
    rw [hℓ', hm', e]
  · intro X hX
    have : X ∈ HPoint.z '' ℓ := hℓ' ▸ hX
    obtain ⟨X', hX', rfl⟩ := this
    obtain ⟨Y, hY, hd⟩ := h X' hX'
    exact ⟨Y.z, hm' ▸ ⟨Y, hY, rfl⟩, hd⟩

end HPlane

/-! ## The Euclidean plane: all six conditions hold -/

section Euclid

open EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "J" =>
  Orientation.rightAngleRotation (Module.Oriented.positiveOrientation (R := ℝ) (M := V) (ι := Fin 2))

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
theorem neq_mem_line_iff {A B p : P} : p ∈ line[ℝ, A, B] ↔ ∃ r : ℝ, r • (B -ᵥ A) +ᵥ A = p := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply]

/-- In the plane there is a point off any line. -/
theorem exists_not_mem_line {X Y : P} (h : X ≠ Y) : ∃ Q : P, Q ∉ line[ℝ, X, Y] := by
  have hv : Y -ᵥ X ≠ 0 := vsub_ne_zero.2 h.symm
  refine ⟨J (Y -ᵥ X) +ᵥ X, fun hQ => ?_⟩
  obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.1 hQ
  have h1 : inner ℝ (r • (Y -ᵥ X)) (Y -ᵥ X) = inner ℝ (J (Y -ᵥ X)) (Y -ᵥ X) := by rw [hr]
  rw [inner_smul_left] at h1
  simp only [Orientation.inner_rightAngleRotation_self, conj_trivial, real_inner_self_eq_norm_sq] at h1
  have hn : ‖Y -ᵥ X‖ ^ 2 ≠ 0 := by positivity
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h1 with h0 | h0
    · exact h0
    · exact absurd h0 hn
  rw [hr0, zero_smul] at hr
  exact hv ((LinearIsometryEquiv.map_eq_zero_iff _).1 hr.symm)

/-- (a) holds in the Euclidean plane (Theorem 7.2: exactly one parallel). -/
@[kb "petrunin2025" "Theorem 11.16 (a), p. 88"]
theorem euclid_onlyOneParallel : (euclideanNeutralPlane (V := V) (P := P)).OnlyOneParallel := by
  obtain ⟨X, Y, hXY⟩ := (euclideanNeutralPlane (V := V) (P := P)).axiomI
  obtain ⟨Q, hQ⟩ := exists_not_mem_line hXY
  set v := Y -ᵥ X with hvdef
  have hv : v ≠ 0 := vsub_ne_zero.2 hXY.symm
  have hne : v +ᵥ Q ≠ Q := fun e => hv (by simpa using congrArg (· -ᵥ Q) e)
  have hQmem : ∀ r s : ℝ, r • v +ᵥ X = s • v +ᵥ Q → Q ∈ line[ℝ, X, Y] := by
    intro r s h2
    rw [← vsub_vadd Q X]
    refine vadd_left_mem_affineSpan_pair.2 ⟨r - s, ?_⟩
    have : (s • v +ᵥ Q) -ᵥ X = r • v := by rw [← h2]; simp
    rw [vadd_vsub_assoc] at this
    rw [sub_smul]
    have h3 : Q -ᵥ X = r • v - s • v := by rw [eq_sub_iff_add_eq, add_comm]; exact this
    rw [h3]
  refine ⟨(line[ℝ, X, Y] : Set P), isLine_iff_exists_affineSpan.2 ⟨X, Y, hXY, rfl⟩, Q, hQ,
    (line[ℝ, Q, v +ᵥ Q] : Set P), ⟨isLine_iff_exists_affineSpan.2 ⟨Q, v +ᵥ Q, hne.symm, rfl⟩,
      left_mem_affineSpan_pair ℝ _ _, ?_⟩, ?_⟩
  · rw [Set.disjoint_left]
    intro p hp hp'
    obtain ⟨r, hr⟩ := neq_mem_line_iff.1 hp
    obtain ⟨s, hs⟩ := neq_mem_line_iff.1 hp'
    rw [vadd_vsub] at hs
    exact hQmem r s (hr.trans hs.symm) |> hQ
  · rintro y ⟨hy, hQy, hdis⟩
    obtain ⟨P1, P2, hP12, rfl⟩ := isLine_iff_exists_affineSpan.1 hy
    set w := P2 -ᵥ P1 with hwdef
    have hw : w ≠ 0 := vsub_ne_zero.2 hP12.symm
    have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ (n := 1) (Fact.out)
    by_cases hk : ∃ a : ℝ, a • v = w
    · obtain ⟨a, ha⟩ := hk
      have ha0 : a ≠ 0 := by rintro rfl; exact hw (by rw [← ha]; simp)
      have hdir : (line[ℝ, P1, P2]).direction = (line[ℝ, Q, v +ᵥ Q]).direction := by
        rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair, vectorSpan_pair]
        have e1 : P1 -ᵥ P2 = (-a) • v := by rw [neg_smul, ha, hwdef, neg_vsub_eq_vsub_rev]
        have e2 : Q -ᵥ (v +ᵥ Q) = (-1 : ℝ) • v := by
          rw [neg_one_smul, ← neg_vsub_eq_vsub_rev (v +ᵥ Q) Q, vadd_vsub]
        rw [e1, e2, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (neg_ne_zero.2 ha0)),
          Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 (by norm_num))]
      have := AffineSubspace.ext_of_direction_eq hdir
        ⟨Q, hQy, left_mem_affineSpan_pair ℝ _ _⟩
      rw [this]
    · exfalso
      simp only [not_exists] at hk
      have hli : LinearIndependent ℝ ![v, w] := (LinearIndependent.pair_iff' hv).2 hk
      have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [Fact.out (p := Module.finrank ℝ V = 2)])
      have hrange : Set.range ![v, w] = {v, w} := by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]; simp [Set.pair_comm]
      rw [hrange] at htop
      have hsup : (line[ℝ, X, Y]).direction ⊔ (line[ℝ, P1, P2]).direction = ⊤ := by
        rw [eq_top_iff, ← htop, Submodule.span_le]
        intro z hz
        rcases hz with rfl | rfl
        · exact Submodule.mem_sup_left (AffineSubspace.vsub_mem_direction
            (right_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _))
        · exact Submodule.mem_sup_right (AffineSubspace.vsub_mem_direction
            (right_mem_affineSpan_pair ℝ _ _) (left_mem_affineSpan_pair ℝ _ _))
      obtain ⟨p, hp1, hp2⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
        ⟨X, left_mem_affineSpan_pair ℝ _ _⟩ ⟨P1, left_mem_affineSpan_pair ℝ _ _⟩ hsup
      exact Set.disjoint_left.1 hdis hp1 hp2

/-- (b) holds in the Euclidean plane: the circumcentre (Mathlib `Affine.Simplex.circumcenter`). -/
@[kb "petrunin2025" "Theorem 11.16 (b), p. 88"]
theorem euclid_circumscribable : (euclideanNeutralPlane (V := V) (P := P)).AllTrianglesCircumscribable := by
  intro A B C hT hnd
  have hcol : ¬ Collinear ℝ ({A, B, C} : Set P) := fun h =>
    hnd ((IsTriangle.degenerate_iff_collinear (V := V) hT).2 h)
  have hind : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.2 hcol
  let T : Affine.Triangle ℝ P := ⟨![A, B, C], hind⟩
  exact ⟨T.circumcenter, T.circumradius, T.dist_circumcenter_eq_circumradius' 0,
    T.dist_circumcenter_eq_circumradius' 1, T.dist_circumcenter_eq_circumradius' 2⟩

/-- (c) holds in the Euclidean plane: a line and its translate by a vector off the line. -/
@[kb "petrunin2025" "Theorem 11.16 (c), p. 88"]
theorem euclid_boundedDistantLines :
    (euclideanNeutralPlane (V := V) (P := P)).BoundedDistantLines := by
  obtain ⟨X, Y, hXY⟩ := (euclideanNeutralPlane (V := V) (P := P)).axiomI
  obtain ⟨Q, hQ⟩ := exists_not_mem_line hXY
  set v := Y -ᵥ X with hvdef
  have hv : v ≠ 0 := vsub_ne_zero.2 hXY.symm
  have hne : v +ᵥ Q ≠ Q := fun e => hv (by simpa using congrArg (· -ᵥ Q) e)
  refine ⟨(line[ℝ, X, Y] : Set P), (line[ℝ, Q, v +ᵥ Q] : Set P),
    isLine_iff_exists_affineSpan.2 ⟨X, Y, hXY, rfl⟩,
    isLine_iff_exists_affineSpan.2 ⟨Q, v +ᵥ Q, hne.symm, rfl⟩, ?_, dist Q X, ?_⟩
  · intro e
    have : Q ∈ (line[ℝ, Q, v +ᵥ Q] : Set P) := left_mem_affineSpan_pair ℝ _ _
    rw [← e] at this
    exact hQ this
  · intro p hp
    obtain ⟨r, hr⟩ := neq_mem_line_iff.1 hp
    refine ⟨r • v +ᵥ Q, ?_, ?_⟩
    · have := smul_vsub_vadd_mem_affineSpan_pair r Q (v +ᵥ Q)
      rwa [vadd_vsub] at this
    · rw [← hr, dist_vadd_cancel_left, dist_comm]

section Frame

theorem exists_unit_vector (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] : ∃ x : V, ‖x‖ = 1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out (p := Module.finrank ℝ V = 2))
  exact exists_norm_eq V zero_le_one

theorem frame_nsq {x : V} (hx : ‖x‖ = 1) (a b : ℝ) : ‖a • x + b • J x‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h1 : inner ℝ x (J x) = 0 := by simp
  have h2 : inner ℝ (J x) x = 0 := by simp
  have h3 : ‖J x‖ = 1 := by simp [hx]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, h2,
    real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hx, h3]
  ring

theorem neq_frame_inj {x : V} (hx : ‖x‖ = 1) {a b a' b' : ℝ}
    (h : a • x + b • J x = a' • x + b' • J x) : a = a' ∧ b = b' := by
  have h0 : (a - a') • x + (b - b') • J x = 0 := by
    rw [sub_smul, sub_smul]; rw [← sub_eq_zero] at h; rw [← h]; abel
  have := frame_nsq hx (a - a') (b - b')
  rw [h0, norm_zero] at this
  constructor <;> nlinarith [sq_nonneg (a - a'), sq_nonneg (b - b')]

/-- The point `O + a x + b J x` of the frame at `O` spanned by the unit vector `x`. -/
noncomputable def framePt (O : P) (x : V) (a b : ℝ) : P := (a • x + b • J x) +ᵥ O

theorem framePt_inj {x : V} (hx : ‖x‖ = 1) {O : P} {a b a' b' : ℝ}
    (h : framePt O x a b = framePt O x a' b') : a = a' ∧ b = b' :=
  neq_frame_inj hx (vadd_right_cancel O h)

theorem framePt_line (O : P) (x : V) (a₁ b₁ a₂ b₂ r : ℝ) :
    r • (framePt O x a₂ b₂ -ᵥ framePt O x a₁ b₁) +ᵥ framePt O x a₁ b₁ =
      framePt O x ((1 - r) * a₁ + r * a₂) ((1 - r) * b₁ + r * b₂) := by
  unfold framePt
  rw [vadd_vsub_vadd_cancel_right, vadd_vadd]
  congr 1
  module

theorem framePt_dist (O : P) (x : V) (a b : ℝ) : dist (framePt O x a b) O = ‖a • x + b • J x‖ :=
  dist_vadd_left _ _

/-- Points of a line through two frame points are at distance `≥ k/3` from `O` provided all the
points of the segment-line are. -/
theorem side_far {O : P} {x : V} (hx : ‖x‖ = 1) {k : ℝ} (hk : 0 < k) {a₁ b₁ a₂ b₂ : ℝ}
    (hne : (a₁, b₁) ≠ (a₂, b₂))
    (h : ∀ r : ℝ, k ^ 2 / 5 ≤ ((1 - r) * a₁ + r * a₂) ^ 2 + ((1 - r) * b₁ + r * b₂) ^ 2)
    {L : Set P} (hL : IsLine L) (h1 : framePt O x a₁ b₁ ∈ L) (h2 : framePt O x a₂ b₂ ∈ L) :
    ∀ X ∈ L, k / 3 ≤ dist O X := by
  intro X hX
  have hAB : framePt O x a₁ b₁ ≠ framePt O x a₂ b₂ := fun e => by
    have := framePt_inj hx e
    exact hne (by rw [this.1, this.2])
  obtain ⟨X', Y', -, rfl⟩ := isLine_iff_exists_affineSpan.1 hL
  have hcol := collinear_triple_of_mem_affineSpan_pair h1 h2 hX
  have hmem : X ∈ line[ℝ, framePt O x a₁ b₁, framePt O x a₂ b₂] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
  obtain ⟨r, hr⟩ := neq_mem_line_iff.1 hmem
  rw [framePt_line] at hr
  rw [dist_comm, ← hr, framePt_dist]
  have hn := frame_nsq hx ((1 - r) * a₁ + r * a₂) ((1 - r) * b₁ + r * b₂)
  have h0 := norm_nonneg (((1 - r) * a₁ + r * a₂) • x + ((1 - r) * b₁ + r * b₂) • J x)
  have := h r
  by_contra hlt
  push Not at hlt
  nlinarith

theorem framePt_vsub_base (O : P) (x : V) (a b : ℝ) :
    framePt O x a b -ᵥ O = a • x + b • J x := vadd_vsub _ _

theorem frame_sign_base {x : V} (hx : ‖x‖ = 1) :
    ((o : Orientation ℝ V (Fin 2)).oangle x (J x)).sign = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  rw [← Orientation.rotation_pi_div_two, Orientation.oangle_rotation_self_right _ hx0]
  exact Real.Angle.sign_coe_pi_div_two

theorem frame_sign_swap {x : V} (hx : ‖x‖ = 1) :
    ((o : Orientation ℝ V (Fin 2)).oangle (J x) x).sign = -1 := by
  rw [Orientation.oangle_rev, Real.Angle.sign_neg, frame_sign_base hx]

/-- The explicit triangle with incentre `O` and inradius `≥ k/3` (inside the Euclidean plane). -/
theorem euclid_triangle (O : P) {x : V} (hx : ‖x‖ = 1) {k : ℝ} (hk : 0 < k) :
    IsTriangle (framePt O x k 0) (framePt O x 0 k) (framePt O x (-k) (-k)) ∧
    ¬ IsTriangle.Degenerate (framePt O x k 0) (framePt O x 0 k) (framePt O x (-k) (-k)) ∧
    (euclideanNeutralPlane (V := V) (P := P)).InradiusGE (framePt O x k 0) (framePt O x 0 k)
      (framePt O x (-k) (-k)) (k / 3) := by
  have hT : IsTriangle (framePt O x k 0) (framePt O x 0 k) (framePt O x (-k) (-k)) := by
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · obtain ⟨h1, h2⟩ := framePt_inj hx e; linarith
    · obtain ⟨h1, h2⟩ := framePt_inj hx e; linarith
    · obtain ⟨h1, h2⟩ := framePt_inj hx e; linarith
  refine ⟨hT, ?_, O, ?_, ?_⟩
  · intro hd
    have hcol := (IsTriangle.degenerate_iff_collinear (V := V) hT).1 hd
    have hmem : framePt O x (-k) (-k) ∈ line[ℝ, framePt O x k 0, framePt O x 0 k] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hT.1
    obtain ⟨r, hr⟩ := neq_mem_line_iff.1 hmem
    rw [framePt_line] at hr
    obtain ⟨h1, h2⟩ := framePt_inj hx hr
    nlinarith
  · -- interior point
    have e1 : (euclideanNeutralPlane (V := V) (P := P)).angle (framePt O x k 0) O (framePt O x 0 k) =
        (o : Orientation ℝ V (Fin 2)).oangle (k • x) (k • J x) := by
      show EuclideanGeometry.oangle _ _ _ = _
      simp [EuclideanGeometry.oangle, framePt_vsub_base]
    have e2 : (euclideanNeutralPlane (V := V) (P := P)).angle (framePt O x 0 k) O (framePt O x (-k) (-k)) =
        (o : Orientation ℝ V (Fin 2)).oangle (k • J x) ((-k) • x + (-k) • J x) := by
      show EuclideanGeometry.oangle _ _ _ = _
      simp [EuclideanGeometry.oangle, framePt_vsub_base]
    have e3 : (euclideanNeutralPlane (V := V) (P := P)).angle (framePt O x (-k) (-k)) O (framePt O x k 0) =
        (o : Orientation ℝ V (Fin 2)).oangle ((-k) • x + (-k) • J x) (k • x) := by
      show EuclideanGeometry.oangle _ _ _ = _
      simp [EuclideanGeometry.oangle, framePt_vsub_base]
    have hk1 : SignType.sign k = 1 := sign_pos hk
    have hk2 : SignType.sign (-k) = -1 := sign_neg (by linarith)
    have s1 : ((o : Orientation ℝ V (Fin 2)).oangle (k • x) (k • J x)).sign = 1 := by
      rw [Orientation.oangle_sign_smul_left, Orientation.oangle_sign_smul_right, hk1,
        frame_sign_base hx]; rfl
    have s2 : ((o : Orientation ℝ V (Fin 2)).oangle (k • J x) ((-k) • x + (-k) • J x)).sign = 1 := by
      rw [Orientation.oangle_sign_smul_left, add_comm,
        Orientation.oangle_sign_smul_add_smul_right, hk1, hk2, frame_sign_swap hx]; rfl
    have s3 : ((o : Orientation ℝ V (Fin 2)).oangle ((-k) • x + (-k) • J x) (k • x)).sign = 1 := by
      rw [Orientation.oangle_sign_smul_right, add_comm,
        Orientation.oangle_sign_smul_add_smul_left, hk1, hk2, frame_sign_swap hx]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, e2, s1, s2]
    · rw [e2, e3, s2, s3]
    · rw [e1, s1]; simp
  · intro L hL hor X hX
    have hx0 : ∀ r : ℝ, 0 ≤ r → True := fun _ _ => trivial
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine side_far hx hk (a₁ := k) (b₁ := 0) (a₂ := 0) (b₂ := k) ?_ ?_ hL h1 h2 X hX
      · intro e; have := Prod.mk.inj e; linarith [this.1]
      · intro r; nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg (2 * r - 1))]
    · refine side_far hx hk (a₁ := 0) (b₁ := k) (a₂ := -k) (b₂ := -k) ?_ ?_ hL h1 h2 X hX
      · intro e; have := Prod.mk.inj e; linarith [this.1, this.2]
      · intro r; nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg (5 * r - 2))]
    · refine side_far hx hk (a₁ := -k) (b₁ := -k) (a₂ := k) (b₂ := 0) ?_ ?_ hL h1 h2 X hX
      · intro e; have := Prod.mk.inj e; linarith [this.1, this.2]
      · intro r; nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg (5 * r - 3))]

theorem frame_inner {x : V} (hx : ‖x‖ = 1) (a b a' b' : ℝ) :
    inner ℝ (a • x + b • J x) (a' • x + b' • J x) = a * a' + b * b' := by
  have h1 : inner ℝ x (J x) = 0 := by simp
  have h2 : inner ℝ (J x) x = 0 := by simp
  have h3 : ‖J x‖ = 1 := by simp [hx]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, h2,
    real_inner_self_eq_norm_sq, hx, h3]
  ring

theorem framePt_vsub_framePt (O : P) (x : V) (a b a' b' : ℝ) :
    framePt O x a b -ᵥ framePt O x a' b' = (a - a') • x + (b - b') • J x := by
  unfold framePt
  rw [vadd_vsub_vadd_cancel_right]
  module

end Frame

theorem NeutralPlane.InradiusGE.mono {N : NeutralPlane P} {A B C : P} {r r' : ℝ} (h : r' ≤ r)
    (hI : N.InradiusGE A B C r) : N.InradiusGE A B C r' := by
  obtain ⟨I, hI1, hI2⟩ := hI
  exact ⟨I, hI1, fun L hL hor X hX => h.trans (hI2 L hL hor X hX)⟩

/-- The unsigned angle of the Euclidean neutral plane is the unoriented angle. -/
theorem euclid_uangle {A O B : P} (hA : A ≠ O) (hB : B ≠ O) :
    (euclideanNeutralPlane (V := V) (P := P)).uangle A O B = ∠ A O B :=
  (angle_eq_abs_oangle_toReal hA hB).symm

/-- (d) holds in the Euclidean plane: scale a triangle about its incentre. -/
@[kb "petrunin2025" "Theorem 11.16 (d), p. 88"]
theorem euclid_largeInradius :
    (euclideanNeutralPlane (V := V) (P := P)).ArbitrarilyLargeInradius := by
  intro r
  obtain ⟨O⟩ := (inferInstance : Nonempty P)
  obtain ⟨x, hx⟩ := exists_unit_vector V
  have hk : 0 < 3 * (|r| + 1) := by positivity
  obtain ⟨hT, hnd, hI⟩ := euclid_triangle O hx hk
  refine ⟨_, _, _, hT, hnd, hI.mono ?_⟩
  have := le_abs_self r
  linarith

/-- (e) holds in the Euclidean plane: every nondegenerate triangle has zero defect (Theorem 7.13). -/
@[kb "petrunin2025" "Theorem 11.16 (e), p. 88"]
theorem euclid_zeroDefect : (euclideanNeutralPlane (V := V) (P := P)).ZeroDefectTriangle := by
  obtain ⟨O⟩ := (inferInstance : Nonempty P)
  obtain ⟨x, hx⟩ := exists_unit_vector V
  obtain ⟨hT, hnd, -⟩ := euclid_triangle O hx (zero_lt_one (α := ℝ))
  obtain ⟨hAB, hBC, hCA⟩ := hT
  refine ⟨_, _, _, ⟨hAB, hBC, hCA⟩, hnd, ?_⟩
  unfold NeutralPlane.defect
  rw [euclid_uangle hAB hBC.symm, euclid_uangle hBC hCA.symm, euclid_uangle hCA hAB.symm]
  have := defect_eq_zero (V := V) (C := framePt O x (-1) (-1)) hAB.symm
  unfold defect at this
  linarith

/-- (f) holds in the Euclidean plane: the unit square. -/
@[kb "petrunin2025" "Theorem 11.16 (f), p. 88"]
theorem euclid_hasRectangle : (euclideanNeutralPlane (V := V) (P := P)).HasRectangle := by
  obtain ⟨O⟩ := (inferInstance : Nonempty P)
  obtain ⟨x, hx⟩ := exists_unit_vector V
  have ne : ∀ {a b a' b' : ℝ}, (a ≠ a' ∨ b ≠ b') → framePt O x a b ≠ framePt O x a' b' := by
    intro a b a' b' h e
    obtain ⟨h1, h2⟩ := framePt_inj hx e
    rcases h with h | h <;> contradiction
  have hAB := ne (a := 0) (b := 0) (a' := 1) (b' := 0) (Or.inl (by norm_num))
  have hAC := ne (a := 0) (b := 0) (a' := 1) (b' := 1) (Or.inl (by norm_num))
  have hAD := ne (a := 0) (b := 0) (a' := 0) (b' := 1) (Or.inr (by norm_num))
  have hBC := ne (a := 1) (b := 0) (a' := 1) (b' := 1) (Or.inr (by norm_num))
  have hBD := ne (a := 1) (b := 0) (a' := 0) (b' := 1) (Or.inl (by norm_num))
  have hCD := ne (a := 1) (b := 1) (a' := 0) (b' := 1) (Or.inl (by norm_num))
  have right : ∀ {a b a' b' a'' b'' : ℝ}, framePt O x a b ≠ framePt O x a' b' →
      framePt O x a'' b'' ≠ framePt O x a' b' →
      (a - a') * (a'' - a') + (b - b') * (b'' - b') = 0 →
      (euclideanNeutralPlane (V := V) (P := P)).uangle (framePt O x a b) (framePt O x a' b')
        (framePt O x a'' b'') = Real.pi / 2 := by
    intro a b a' b' a'' b'' h1 h2 h3
    rw [euclid_uangle h1 h2, EuclideanGeometry.angle, framePt_vsub_framePt, framePt_vsub_framePt,
      ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, frame_inner hx]
    exact h3
  exact ⟨_, _, _, _, hAB, hAC, hAD, hBC, hBD, hCD, right hAB hBC.symm (by norm_num),
    right hBC hCD.symm (by norm_num), right hCD hAD (by norm_num),
    right hAD.symm hAB.symm (by norm_num)⟩


end Euclid

/-! ## Packaging: Theorem 11.16 on the two models -/

/-- **Theorem 11.16 on the Euclidean model.**  In the Euclidean plane (an oriented two-dimensional Euclidean
affine space with the oriented angle), which satisfies Axiom V, each of the conditions (a)-(f) holds. -/
@[kb "petrunin2025" "Theorem 11.16, p. 88"]
theorem theorem_11_16_euclidean {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
    [Module.Oriented ℝ V (Fin 2)] :
    let N := euclideanNeutralPlane (V := V) (P := P)
    (N.AxiomV ↔ N.OnlyOneParallel) ∧ (N.AxiomV ↔ N.AllTrianglesCircumscribable) ∧
    (N.AxiomV ↔ N.BoundedDistantLines) ∧ (N.AxiomV ↔ N.ArbitrarilyLargeInradius) ∧
    (N.AxiomV ↔ N.ZeroDefectTriangle) ∧ (N.AxiomV ↔ N.HasRectangle) := by
  intro N
  have hV := euclideanNeutralPlane_axiomV (V := V) (P := P)
  exact ⟨iff_of_true hV euclid_onlyOneParallel, iff_of_true hV euclid_circumscribable,
    iff_of_true hV euclid_boundedDistantLines, iff_of_true hV euclid_largeInradius,
    iff_of_true hV euclid_zeroDefect, iff_of_true hV euclid_hasRectangle⟩

/-- **Theorem 11.16 on the h-plane.**  The h-plane does not satisfy Axiom V, and none of the conditions
(a)-(f) holds in it. -/
@[kb "petrunin2025" "Theorem 11.16, p. 88"]
theorem theorem_11_16_hyperbolic :
    let N := hyperbolicNeutralPlane
    (N.AxiomV ↔ N.OnlyOneParallel) ∧ (N.AxiomV ↔ N.AllTrianglesCircumscribable) ∧
    (N.AxiomV ↔ N.BoundedDistantLines) ∧ (N.AxiomV ↔ N.ArbitrarilyLargeInradius) ∧
    (N.AxiomV ↔ N.ZeroDefectTriangle) ∧ (N.AxiomV ↔ N.HasRectangle) := by
  intro N
  have hV := hyperbolicNeutralPlane_not_axiomV
  exact ⟨iff_of_false hV hyperbolic_not_onlyOneParallel, iff_of_false hV hyperbolic_not_circumscribable,
    iff_of_false hV hyperbolic_not_boundedDistantLines, iff_of_false hV hyperbolic_not_largeInradius,
    iff_of_false hV hyperbolic_not_zeroDefect, iff_of_false hV hyperbolic_not_rectangle⟩

end UndergradKB.Geometry
