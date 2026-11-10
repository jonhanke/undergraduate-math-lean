import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.MongePoint
import UndergradKB.Geometry.Inversion
import UndergradKB.Geometry.Parallels
import UndergradKB.Geometry.ComplexCoordinates
import UndergradKB.Geometry.Arcs
import UndergradKB.Common.Attr

/-! # Leftover results of chapters 4, 7-10, 18 (Petrunin)

The transversal property (Proposition 7.9, signed angles), the Euler line (Advanced exercise 8.8),
the signed-angle behaviour of inversion (Lemma 10.2, Theorem 10.6(b)), the line case of Corollary 10.16,
Exercise 10.8, Corollary 10.26, Problem 4.9 (existence form), the elementary transformations of
Section 18H and Problem 18.7, and Exercises 9.29, 9.30 on tangent half-lines. -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real
open scoped Affine

section Transversal

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Transversal property** (Petrunin, Proposition 7.9, the equivalences; the side refinement
about `A`, `D` on opposite/same sides of `(BC)` is not formalized): for `A ≠ B ≠ C ≠ D`,
`(AB) ∥ (CD)` iff `2·(∡ABC + ∡BCD) = 0` iff `∡ABC + ∡BCD` is `0` or `π`. -/
@[kb "petrunin2025" "Proposition 7.9, p. 52"]
theorem parallel_iff_two_zsmul_oangle_add {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) :
    (line[ℝ, A, B] ∥ line[ℝ, C, D] ↔ (2 : ℤ) • (∡ A B C + ∡ B C D) = 0) ∧
    ((2 : ℤ) • (∡ A B C + ∡ B C D) = 0 ↔ ∡ A B C + ∡ B C D = 0 ∨ ∡ A B C + ∡ B C D = π) := by
  refine ⟨?_, Real.Angle.two_zsmul_eq_zero_iff⟩
  rw [← two_zsmul_oangle_iff_parallel hAB hBC hCD, smul_add, oangle_rev B C D, smul_neg,
    eq_neg_iff_add_eq_zero]

end Transversal

section Euler

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Euler line** (Petrunin, Advanced exercise 8.8): in a triangle, the centroid `M` satisfies
`M - H = 2 (O - M)` where `H` is the orthocentre and `O` the circumcentre; in particular `H`, `M`, `O`
are collinear, and `M` divides `[HO]` in ratio `2 : 1`. Valid in any real inner product space. -/
@[kb "petrunin2025" "Advanced exercise 8.8, p. 60"]
theorem euler_line (t : Affine.Triangle ℝ P) :
    (Finset.univ.centroid ℝ t.points -ᵥ t.orthocenter : V) =
      (2 : ℝ) • (t.circumcenter -ᵥ Finset.univ.centroid ℝ t.points) ∧
    Collinear ℝ ({t.orthocenter, Finset.univ.centroid ℝ t.points, t.circumcenter} : Set P) := by
  set M := Finset.univ.centroid ℝ t.points
  have h := t.orthocenter_eq_smul_vsub_vadd_circumcenter
  have key : (M -ᵥ t.orthocenter : V) = (2 : ℝ) • (t.circumcenter -ᵥ M) := by
    rw [h, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev M t.circumcenter]
    module
  refine ⟨key, ?_⟩
  rw [collinear_iff_of_mem (p₀ := M) (by simp)]
  refine ⟨t.circumcenter -ᵥ M, ?_⟩
  intro p hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-2, ?_⟩
    rw [eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev, key]
    module
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

end Euler

section InversionAngles

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

theorem oangle_inversion_center {O A B : P} {R : ℝ} (hR : R ≠ 0) :
    ∡ (inversion O R A) O (inversion O R B) = ∡ A O B := by
  by_cases hA : A = O
  · subst hA; simp [inversion_self]
  by_cases hB : B = O
  · subst hB; simp [inversion_self]
  have h1 : 0 < dist A O := dist_pos.2 hA
  have h2 : 0 < dist B O := dist_pos.2 hB
  unfold EuclideanGeometry.oangle
  rw [inversion_vsub_center, inversion_vsub_center,
    Orientation.oangle_smul_left_of_pos _ _ _ (by positivity),
    Orientation.oangle_smul_right_of_pos _ _ _ (by positivity)]

/-- **Lemma 10.2, angle part** (Petrunin, p. 73; the oriented-angle content of `△OAB ∼ △OB'A'`):
for `A, B` different from the centre `O` of an inversion, with images `A'`, `B'`,
`∡ O A B = -∡ O B' A'`, equivalently `∡ O A B = ∡ A' B' O`. -/
@[kb "petrunin2025" "Lemma 10.2, p. 73"]
theorem oangle_inversion_triangle {O A B : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O) :
    ∡ O A B = -∡ O (inversion O R B) (inversion O R A) := by
  rw [oangle_rev (inversion O R A) (inversion O R B) O, neg_neg]
  by_cases hAB : A = B
  · subst hAB; simp
  have hA' : inversion O R A ≠ O := by simpa [inversion_eq_center hR] using hA
  have hB' : inversion O R B ≠ O := by simpa [inversion_eq_center hR] using hB
  have hang : ∠ O A B = ∠ (inversion O R A) (inversion O R B) O := by
    have := (similar_inversion hR hA hB).angle_eq
    rw [this, angle_comm]
  apply oangle_eq_of_angle_eq_of_sign_eq hang
  have e := oangle_inversion_center (O := O) (A := B) (B := A) hR
  have s1 := oangle_rotate_sign O A B
  have s2 := oangle_rotate_sign A B O
  have s3 := oangle_rotate_sign (inversion O R A) (inversion O R B) O
  rw [← s1, ← s2, ← s3, e]

/-- The four signed angles of a quadrangle `ABCD` (consecutive vertices distinct) add up to `0`
(Petrunin, Exercise 7.17). -/
theorem oangle_quadrangle_sum {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D)
    (hDA : D ≠ A) : ∡ A B C + ∡ B C D + ∡ C D A + ∡ D A B = 0 := by
  by_cases hAC : A = C
  · subst hAC
    have := oangle_add_oangle_rev B A D
    simp only [oangle_self_left_right, zero_add, add_zero]
    exact this
  have t1 := oangle_add_oangle_add_oangle_eq_pi hAB.symm hBC.symm hAC
  have t2 := oangle_add_oangle_add_oangle_eq_pi (Ne.symm hAC) hCD.symm hDA.symm
  have a1 := oangle_add (p := C) (p₁ := B) (p₂ := A) (p₃ := D) hBC hAC (Ne.symm hCD)
  have a2 := oangle_add (p := A) (p₁ := D) (p₂ := C) (p₃ := B) hDA (Ne.symm hAC) hAB.symm
  have hpi : (π : Real.Angle) + π = 0 := Real.Angle.coe_pi_add_coe_pi
  rw [← sub_eq_zero]
  linear_combination (norm := abel) t1 + t2 + hpi - a1 - a2

/-- **Theorem 10.6(b)** (Petrunin, p. 74): for a quadrangle `ABCD` (consecutive vertices distinct)
with vertices different from the centre `O` of an inversion, and images `A', B', C', D'`,
`∡ABC + ∡CDA = -(∡A'B'C' + ∡C'D'A')`. -/
@[kb "petrunin2025" "Theorem 10.6(b), p. 74"]
theorem oangle_add_oangle_inversion {O A B C D : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hD : D ≠ O) (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDA : D ≠ A) :
    ∡ A B C + ∡ C D A =
      -(∡ (inversion O R A) (inversion O R B) (inversion O R C) +
        ∡ (inversion O R C) (inversion O R D) (inversion O R A)) := by
  have ne' : ∀ X : P, X ≠ O → inversion O R X ≠ O := fun X hX => by
    simpa [inversion_eq_center hR] using hX
  have inj : ∀ X Y : P, X ≠ Y → inversion O R X ≠ inversion O R Y := fun X Y h h' =>
    h (by simpa [inversion_inversion O hR] using congrArg (inversion O R) h')
  have L := fun X Y (hX : X ≠ O) (hY : Y ≠ O) => oangle_inversion_triangle (R := R) hR hX hY
  have M : ∀ X Y : P, X ≠ O → Y ≠ O →
      ∡ X Y O = -∡ (inversion O R Y) (inversion O R X) O := fun X Y hX hY => by
    have h := L Y X hY hX
    rw [oangle_rev X Y O] at h
    rw [neg_inj.mp h, oangle_rev (inversion O R Y) (inversion O R X) O]
  have N : ∀ X Y : P, X ≠ O → Y ≠ O →
      ∡ O X Y = ∡ (inversion O R X) (inversion O R Y) O := fun X Y hX hY => by
    rw [L X Y hX hY, oangle_rev (inversion O R X) (inversion O R Y) O, neg_neg]
  have hA' := ne' A hA
  have hB' := ne' B hB
  have hC' := ne' C hC
  have hD' := ne' D hD
  set A' := inversion O R A
  set B' := inversion O R B
  set C' := inversion O R C
  set D' := inversion O R D
  have e1 : ∡ A B C = -∡ B' A' O + ∡ B' C' O := by
    rw [← oangle_add (p := B) (p₁ := A) (p₂ := O) (p₃ := C) hAB hB.symm hBC.symm, M A B hA hB,
      N B C hB hC]
  have e2 : ∡ C D A = -∡ D' C' O + ∡ D' A' O := by
    rw [← oangle_add (p := D) (p₁ := C) (p₂ := O) (p₃ := A) hCD hD.symm hDA.symm, M C D hC hD,
      N D A hD hA]
  have q : ∡ A' B' C' + ∡ B' C' D' + ∡ C' D' A' + ∡ D' A' B' = 0 :=
    oangle_quadrangle_sum (inj A B hAB) (inj B C hBC) (inj C D hCD) (inj D A hDA)
  have r1 := oangle_rev D' C' B'
  have r2 := oangle_rev B' A' D'
  have x1 := oangle_add (p := C') (p₁ := D') (p₂ := O) (p₃ := B') (inj C D hCD).symm hC'.symm
    (inj B C hBC)
  have x2 := oangle_add (p := A') (p₁ := B') (p₂ := O) (p₃ := D') (inj A B hAB).symm hA'.symm
    (inj D A hDA)
  have y1 := oangle_rev B' C' O
  have y2 := oangle_rev D' A' O
  rw [e1, e2, ← sub_eq_zero]
  linear_combination (norm := abel) q - r1 - r2 - x1 - x2 + y1 + y2

end InversionAngles

section LineInversion

open Metric
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- If three collinear points `P₁`, `P₁ + v`, `P₁ + 2v` (`v ≠ 0`) lie on a sphere centred at `c`
we get a contradiction (a line meets a sphere in at most two points). -/
theorem false_of_three_collinear_mem_sphere {c P₁ P₂ : P} {R : ℝ} (h12 : P₁ ≠ P₂)
    (h1 : P₁ ∈ sphere c R) (h2 : P₂ ∈ sphere c R)
    (h3 : AffineMap.lineMap P₁ P₂ (2 : ℝ) ∈ sphere c R) : False := by
  rw [Metric.mem_sphere, dist_eq_norm_vsub V] at h1 h2 h3
  have e2 : P₂ -ᵥ c = (P₂ -ᵥ P₁) + (P₁ -ᵥ c) := (vsub_add_vsub_cancel _ _ _).symm
  have e3 : AffineMap.lineMap P₁ P₂ (2 : ℝ) -ᵥ c = (2 : ℝ) • (P₂ -ᵥ P₁) + (P₁ -ᵥ c) := by
    rw [AffineMap.lineMap_apply, vadd_vsub_assoc]
  rw [e2] at h2
  rw [e3] at h3
  have n2 := congrArg (· ^ 2) h2
  have n3 := congrArg (· ^ 2) h3
  have n1 := congrArg (· ^ 2) h1
  simp only [norm_add_sq_real, norm_smul, inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs,
    conj_trivial] at n2 n3
  have hv : ‖P₂ -ᵥ P₁‖ ^ 2 = 0 := by nlinarith
  have : P₂ -ᵥ P₁ = 0 := by simpa using hv
  exact h12 (vsub_eq_zero_iff_eq.mp this).symm

/-- **Corollary 10.16, line case** (Petrunin, p. 79): the inversion across a circle `Ω` (centre `c`,
radius `R > 0`) maps a line `Γ = (P₁P₂)` onto itself iff `Γ` passes through the centre `c`. (The
case of a circle `Γ` is `orthogonalCircles_iff_image_eq`; the book's "iff `Γ ⟂ Ω`" for lines means
"`Γ` passes through the centre".) Valid in any real inner product space. -/
@[kb "petrunin2025" "Corollary 10.16, p. 79"]
theorem image_inversion_line_eq_iff {c P₁ P₂ : P} {R : ℝ} (hR : 0 < R) (h12 : P₁ ≠ P₂) :
    inversion c R '' (line[ℝ, P₁, P₂] : Set P) = line[ℝ, P₁, P₂] ↔ c ∈ line[ℝ, P₁, P₂] := by
  refine ⟨fun himg => ?_, fun h => image_inversion_line_through_centre hR.ne' h⟩
  by_contra hc
  have hmaps : ∀ x ∈ line[ℝ, P₁, P₂], inversion c R x ∈ line[ℝ, P₁, P₂] := fun x hx => by
    have : inversion c R x ∈ inversion c R '' (line[ℝ, P₁, P₂] : Set P) := ⟨x, hx, rfl⟩
    rw [himg] at this
    exact this
  have key : ∀ x ∈ line[ℝ, P₁, P₂], x ∈ sphere c R := by
    intro x hx
    by_contra hxs
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    have hne : inversion c R x ≠ x := fun h =>
      hxs ((inversion_basic hR hxc).2.2.2.1.mp h)
    set t : ℝ := (R / dist x c) ^ 2 with ht
    have ht1 : t ≠ 1 := by
      intro h1
      apply hne
      have : inversion c R x = AffineMap.lineMap c x t := by
        rw [AffineMap.lineMap_apply]; rfl
      rw [this, h1, AffineMap.lineMap_apply_one]
    have hx' := hmaps x hx
    have hcx : AffineMap.lineMap x (inversion c R x) (1 / (1 - t)) = c := by
      have h1 : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
      have hx'c : inversion c R x -ᵥ c = t • (x -ᵥ c) := inversion_vsub_center c R x
      have hv : (1 / (1 - t)) • (inversion c R x -ᵥ x) = c -ᵥ x := by
        rw [← vsub_sub_vsub_cancel_right (inversion c R x) x c, hx'c, ← neg_vsub_eq_vsub_rev x c]
        match_scalars
        field_simp
        ring
      rw [AffineMap.lineMap_apply, hv, vsub_vadd]
    apply hc
    have hsub : line[ℝ, x, inversion c R x] ≤ line[ℝ, P₁, P₂] :=
      affineSpan_pair_le_of_mem_of_mem hx hx'
    have hm := AffineMap.lineMap_mem_affineSpan_pair (k := ℝ) (1 / (1 - t)) x (inversion c R x)
    rw [hcx] at hm
    exact hsub hm
  exact false_of_three_collinear_mem_sphere h12 (key _ (left_mem_affineSpan_pair ℝ _ _))
    (key _ (right_mem_affineSpan_pair ℝ _ _))
    (key _ (AffineMap.lineMap_mem_affineSpan_pair _ _ _))

end LineInversion

section InverseOfInverse

open Metric
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem norm_sq_smul_add_smul (p σ : V) (x y : ℝ) :
    ‖x • p + y • σ‖ ^ 2 = x ^ 2 * ‖p‖ ^ 2 + 2 * x * y * ⟪p, σ⟫ + y ^ 2 * ‖σ‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs, conj_trivial]
  ring

theorem key_vec {p σ : V} {a b m k R : ℝ} (ha0 : a ≠ 0) (hm0 : m ≠ 0)
    (hD : b - k * m ≠ 0) (hR : R ≠ 0)
    (hN0 : k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b ≠ 0) :
    (R ^ 2 / (k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b)) •
      (k • p + (1 - k) • σ) =
    (R ^ 2 / (b - k * m)) • σ +
      (R ^ 4 * (k * m) / (b - k * m) ^ 2 /
        ((R ^ 2 / a) ^ 2 * a - 2 * (R ^ 2 / a) * (R ^ 2 / (b - k * m)) * ((a + b - m) / 2) +
          (R ^ 2 / (b - k * m)) ^ 2 * b)) •
      ((R ^ 2 / a) • p + (-(R ^ 2 / (b - k * m))) • σ) := by
  have hE : (R ^ 2 / a) ^ 2 * a - 2 * (R ^ 2 / a) * (R ^ 2 / (b - k * m)) * ((a + b - m) / 2) +
          (R ^ 2 / (b - k * m)) ^ 2 * b =
      R ^ 4 * m * (k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b) /
        (a * (b - k * m) ^ 2) := by
    field_simp
    ring
  rw [hE]
  have hR4 : R ^ 4 ≠ 0 := pow_ne_zero 4 hR
  generalize hN : k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b = N at hN0 ⊢
  match_scalars
  · field_simp
  · field_simp
    rw [← hN]
    ring

/-- **Corollary 10.26** (Petrunin, p. 82; case where the circle `Γ` does not pass through the
centre `O` of the inversion across `Ω`): if `Q` is the inverse of `Pt` across the circle `Γ`
(centre `S`, radius `s`) then the inverse `Q'` of `Q` across `Ω` (centre `O`, radius `R`) is the
inverse, across the image circle `Γ'` (centre `invSphereCenter`, radius `invSphereRadius`, see
`image_inversion_sphere`), of the inverse `P'` of `Pt`. The hypotheses `Pt ≠ O`, `Pt ≠ S`,
`Q ≠ O` say that all the inverses involved are defined (in the inversive plane they are
`∞`-cases). Valid in any real inner product space. -/
@[kb "petrunin2025" "Corollary 10.26, p. 82"]
theorem inversion_inversion_conj {O S Pt : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 ≤ s)
    (hd : dist S O ≠ s) (hP : Pt ≠ O) (hPS : Pt ≠ S) (hQ : inversion S s Pt ≠ O) :
    inversion O R (inversion S s Pt) =
      inversion (invSphereCenter O R S s) (invSphereRadius O R S s) (inversion O R Pt) := by
  have hD0 := power_ne_zero hs hd
  set p : V := Pt -ᵥ O with hp
  set σ : V := S -ᵥ O with hσ
  have hpS : Pt -ᵥ S = p - σ := (vsub_sub_vsub_cancel_right Pt S O).symm
  have hdP : dist Pt O = ‖p‖ := dist_eq_norm_vsub V _ _
  have hdS : dist S O = ‖σ‖ := dist_eq_norm_vsub V _ _
  have hdPS : dist Pt S = ‖p - σ‖ := by rw [dist_eq_norm_vsub V, hpS]
  have hpn : ‖p‖ ≠ 0 := by rw [← hdP]; exact dist_ne_zero.mpr hP
  have hpSn : ‖p - σ‖ ≠ 0 := by rw [← hdPS]; exact dist_ne_zero.mpr hPS
  set a := ‖p‖ ^ 2 with ha
  set b := ‖σ‖ ^ 2 with hb
  set ip := ⟪p, σ⟫ with hip
  set m := ‖p - σ‖ ^ 2 with hm
  have hmab : m = a - 2 * ip + b := norm_sub_sq_real p σ
  have hip' : ip = (a + b - m) / 2 := by rw [hmab]; ring
  have ha0 : a ≠ 0 := pow_ne_zero 2 hpn
  have hm0 : m ≠ 0 := pow_ne_zero 2 hpSn
  have hDb : b - s ^ 2 ≠ 0 := by rw [hb, ← hdS]; exact hD0
  set k : ℝ := s ^ 2 / m with hk
  have hkm : k * m = s ^ 2 := by rw [hk]; field_simp
  -- the inverse Q of Pt across Γ
  have hQvec : inversion S s Pt -ᵥ O = k • p + (1 - k) • σ := by
    rw [← vsub_add_vsub_cancel (inversion S s Pt) S O, inversion_vsub_center, hpS, hdPS, div_pow,
      ← hm]
    simp only [hk]
    module
  have hdQ : dist (inversion S s Pt) O ^ 2 =
      k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b := by
    rw [dist_eq_norm_vsub V, hQvec, norm_sq_smul_add_smul, ← hip']
  have hN0 : k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b ≠ 0 := by
    rw [← hdQ]; exact pow_ne_zero 2 (dist_ne_zero.mpr hQ)
  -- left side
  have hL : inversion O R (inversion S s Pt) -ᵥ O =
      (R ^ 2 / (k ^ 2 * a + 2 * k * (1 - k) * ((a + b - m) / 2) + (1 - k) ^ 2 * b)) •
        (k • p + (1 - k) • σ) := by
    rw [inversion_vsub_center, div_pow, hdQ, hQvec]
  -- right side
  have hP'vec : inversion O R Pt -ᵥ O = (R ^ 2 / a) • p := by
    rw [inversion_vsub_center, hdP, div_pow]
  have hS'vec : invSphereCenter O R S s -ᵥ O = (R ^ 2 / (b - k * m)) • σ := by
    rw [invSphereCenter, AffineMap.lineMap_vsub_left, hkm, hdS]
  have hr2 : invSphereRadius O R S s ^ 2 = R ^ 4 * (k * m) / (b - k * m) ^ 2 := by
    rw [invSphereRadius, div_pow, mul_pow, sq_abs, hkm, hdS]
    ring
  have hPS' : inversion O R Pt -ᵥ invSphereCenter O R S s =
      (R ^ 2 / a) • p + (-(R ^ 2 / (b - k * m))) • σ := by
    rw [← vsub_sub_vsub_cancel_right _ _ O, hP'vec, hS'vec]
    module
  have hdE : dist (inversion O R Pt) (invSphereCenter O R S s) ^ 2 =
      (R ^ 2 / a) ^ 2 * a - 2 * (R ^ 2 / a) * (R ^ 2 / (b - k * m)) * ((a + b - m) / 2) +
          (R ^ 2 / (b - k * m)) ^ 2 * b := by
    rw [dist_eq_norm_vsub V, hPS', norm_sq_smul_add_smul, ← hip']
    ring
  have hRv : inversion (invSphereCenter O R S s) (invSphereRadius O R S s) (inversion O R Pt) -ᵥ O =
      (R ^ 2 / (b - k * m)) • σ +
      (R ^ 4 * (k * m) / (b - k * m) ^ 2 /
        ((R ^ 2 / a) ^ 2 * a - 2 * (R ^ 2 / a) * (R ^ 2 / (b - k * m)) * ((a + b - m) / 2) +
          (R ^ 2 / (b - k * m)) ^ 2 * b)) •
      ((R ^ 2 / a) • p + (-(R ^ 2 / (b - k * m))) • σ) := by
    rw [← vsub_add_vsub_cancel _ (invSphereCenter O R S s) O, inversion_vsub_center, div_pow, hr2,
      hdE, hPS', hS'vec, add_comm]
  have hDk : b - k * m ≠ 0 := by rw [hkm]; exact hDb
  apply vsub_left_cancel (p := O)
  rw [hL, hRv]
  exact key_vec ha0 hm0 hDk hR hN0

end InverseOfInverse

section CentreNotCentre

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Exercise 10.8** (Petrunin, p. 77): let `Γ` be a circle with centre `Q ≠ O` and radius `s > 0`
not passing through the centre `O` of an inversion of radius `R`. Then the inverse `Q'` of `Q` is not
the centre of the image circle `Γ'` (whose centre is `invSphereCenter O R Q s`). -/
@[kb "petrunin2025" "Exercise 10.8, p. 77"]
theorem inversion_centre_ne_centre_image {O Q : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 < s)
    (hd : dist Q O ≠ s) (hQ : Q ≠ O) :
    inversion O R Q ≠ invSphereCenter O R Q s := by
  have hD0 := power_ne_zero hs.le hd
  have hq : 0 < dist Q O := dist_pos.mpr hQ
  have h1 : inversion O R Q = AffineMap.lineMap O Q ((R / dist Q O) ^ 2) := by
    rw [AffineMap.lineMap_apply]; rfl
  rw [h1, invSphereCenter]
  intro h
  have := AffineMap.lineMap_injective ℝ hQ.symm h
  rw [div_pow] at this
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  field_simp at this
  nlinarith [sq_pos_of_pos hs]

end CentreNotCentre

section Bisected

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

omit [Fact (Module.finrank ℝ V = 2)] in
theorem direction_map_pointReflection (O : P) (m : AffineSubspace ℝ P) :
    (m.map (AffineEquiv.pointReflection ℝ O).toAffineMap).direction = m.direction := by
  rw [AffineSubspace.map_direction]
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    rw [pointReflection_linear_apply]
    exact m.direction.neg_mem hu
  · intro u hu
    refine ⟨-u, m.direction.neg_mem hu, ?_⟩
    rw [pointReflection_linear_apply, neg_neg]

/-- **Problem 4.9** (Petrunin, p. 35; the book asks for a ruler-and-compass construction; here the
existence statement, with the point reflection of the book's construction): given lines `ℓ` and `m`
(subspaces with one-dimensional direction in the plane) and a point `M` on neither, such that `ℓ` is
not parallel to the reflection `m'` of `m` through `M`, there is a segment `[XY]` with `X ∈ ℓ`,
`Y ∈ m`, bisected by `M`: `X` is the intersection point of `ℓ` and `m'`. -/
@[kb "petrunin2025" "Problem 4.9, p. 35"]
theorem exists_segment_bisected {ℓ m : AffineSubspace ℝ P} {M : P}
    (hℓ : Module.finrank ℝ ℓ.direction = 1) (hm : Module.finrank ℝ m.direction = 1)
    (hMℓ : M ∉ ℓ) (_hMm : M ∉ m)
    (hpar : ¬ ℓ ∥ m.map (AffineEquiv.pointReflection ℝ M).toAffineMap) :
    ∃ X ∈ ℓ, ∃ Y ∈ m, X ≠ Y ∧ midpoint ℝ X Y = M := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ (n := 1) (Fact.out)
  set f := (AffineEquiv.pointReflection ℝ M).toAffineMap with hf
  have hdir := direction_map_pointReflection M m
  have hne : ℓ.direction ≠ m.direction := by
    intro h
    apply hpar
    rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    refine ⟨h.trans hdir.symm, iff_of_false (ne_bot_of_finrank_direction_eq_one hℓ) ?_⟩
    intro hb
    exact ne_bot_of_finrank_direction_eq_one hm (by simpa using hb)
  have hle : ¬ m.direction ≤ ℓ.direction := fun hle =>
    hne (Submodule.eq_of_le_of_finrank_eq hle (by rw [hℓ, hm])).symm
  have hlt : ℓ.direction < ℓ.direction ⊔ m.direction :=
    lt_of_le_of_ne le_sup_left (fun h => hle (h ▸ le_sup_right))
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have htop : ℓ.direction ⊔ m.direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (ℓ.direction ⊔ m.direction)
    rw [Fact.out (p := Module.finrank ℝ V = 2)] at this ⊢
    omega
  have hne' : ∀ n : AffineSubspace ℝ P, n ≠ ⊥ → (n : Set P).Nonempty := fun n hn => by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hn ((AffineSubspace.coe_eq_bot_iff n).1 h)
  have hm'ne : m.map f ≠ ⊥ := fun h =>
    ne_bot_of_finrank_direction_eq_one hm (by simpa using h)
  rw [← hdir] at htop
  obtain ⟨X, hXℓ, hXm⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
    (hne' ℓ (ne_bot_of_finrank_direction_eq_one hℓ)) (hne' _ hm'ne) htop
  obtain ⟨Y, hY, hYX⟩ := hXm
  have hfY : f Y = X := hYX
  have hmid : midpoint ℝ X Y = M := by
    rw [midpoint_eq_iff, ← hfY]
    simp only [hf, AffineEquiv.coe_toAffineMap, AffineEquiv.coe_pointReflection]
    exact Equiv.pointReflection_involutive M Y
  refine ⟨X, hXℓ, Y, hY, ?_, hmid⟩
  intro hXY
  apply hMℓ
  rw [← hmid, hXY, midpoint_self]
  rw [← hXY]
  exact hXℓ

end Bisected

section ComplexPlane

open ComplexCoordinates ComplexConjugate

/-- The standard orientation of `ℂ` (a local copy, equal to the one of `ComplexCoordinates`). -/
noncomputable local instance instOrientedComplexLeftovers : Module.Oriented ℝ ℂ (Fin 2) :=
  ⟨Complex.orientation⟩

local instance instFactFinrankComplexLeftovers : Fact (Module.finrank ℝ ℂ = 2) :=
  ⟨Complex.finrank_real_complex⟩

theorem sub_eq_I_mul_of_oangle_eq_pi_div_two {A B C : ℂ} (h : ∡ A B C = ((π / 2 : ℝ) : Real.Angle))
    (hd : dist B C = dist B A) : C - B = Complex.I * (A - B) := by
  have hne : (∡ A B C) ≠ 0 := by rw [h]; exact Real.Angle.pi_div_two_ne_zero
  have hA : A ≠ B := left_ne_of_oangle_ne_zero hne
  have hC : C ≠ B := right_ne_of_oangle_ne_zero hne
  rw [oangle_eq_arg_div hA hC] at h
  have hA' : A - B ≠ 0 := sub_ne_zero.mpr hA
  have hq : (C - B) / (A - B) = Complex.I := by
    apply Complex.ext_norm_arg
    · rw [norm_div, Complex.norm_I, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hA')]
      rw [dist_comm B C, dist_comm B A, Complex.dist_eq, Complex.dist_eq] at hd
      simpa using hd
    · rw [Complex.arg_I]
      have := (Complex.arg_coe_angle_eq_iff (x := (C - B) / (A - B)) (y := Complex.I)).mp
        (by rw [Complex.arg_I]; exact h)
      rwa [Complex.arg_I] at this
  rw [← hq]
  field_simp

/-- **Problem 18.7** (Petrunin, pp. 150-151; solved with complex coordinates): let `△OPV` and `△OQW`
be isosceles (`PO = PV`, `QO = QW`) with right angles `∡VPO = ∡OQW = π/2`, and let `M` be the
midpoint of `[VW]`, with `P, Q, M` distinct. Then `△PMQ` is an isosceles right triangle:
`MP = MQ` and `∡QMP = π/2`. The book works with `O` the origin; here `O` is arbitrary. -/
@[kb "petrunin2025" "Problem 18.7, p. 150"]
theorem problem_18_7 {O P V Q W : ℂ} (hPd : dist P O = dist P V) (hPa : ∡ V P O = ((π / 2 : ℝ) : Real.Angle))
    (hQd : dist Q O = dist Q W) (hQa : ∡ O Q W = ((π / 2 : ℝ) : Real.Angle))
    (hPM : P ≠ midpoint ℝ V W) (hQM : Q ≠ midpoint ℝ V W) :
    dist (midpoint ℝ V W) P = dist (midpoint ℝ V W) Q ∧
      ∡ Q (midpoint ℝ V W) P = ((π / 2 : ℝ) : Real.Angle) := by
  have h1 := sub_eq_I_mul_of_oangle_eq_pi_div_two hPa hPd
  have h2 := sub_eq_I_mul_of_oangle_eq_pi_div_two hQa hQd.symm
  have hM : midpoint ℝ V W = (V + W) / 2 := by
    rw [midpoint_eq_smul_add, Complex.real_smul]
    simp
    ring
  have key : P - midpoint ℝ V W = Complex.I * (Q - midpoint ℝ V W) := by
    rw [hM]
    linear_combination (-(1 + Complex.I) / 2) * h1 + ((Complex.I - 1) / 2) * h2 +
      ((P - V + O - Q) / 2) * Complex.I_sq
  have hQM' : Q - midpoint ℝ V W ≠ 0 := sub_ne_zero.mpr hQM
  constructor
  · rw [Complex.dist_eq, Complex.dist_eq, norm_sub_rev, key, norm_mul, Complex.norm_I, one_mul,
      norm_sub_rev]
  · have hdiv : (P - midpoint ℝ V W) / (Q - midpoint ℝ V W) = Complex.I := by
      rw [key]; field_simp
    rw [oangle_eq_arg_div hQM hPM, hdiv, Complex.arg_I]

/-- **Elementary transformation 1** (Petrunin, Section 18H, p. 152): the translation `z ↦ z + w` is an
isometry of `ℂ` and preserves signed angles. -/
@[kb "petrunin2025" "Section 18H, p. 152"]
theorem translation_isometry_oangle (w : ℂ) :
    Isometry (fun z : ℂ => z + w) ∧ ∀ a b c : ℂ, ∡ (a + w) (b + w) (c + w) = ∡ a b c := by
  refine ⟨(IsometryEquiv.addRight w).isometry, fun a b c => ?_⟩
  simp [EuclideanGeometry.oangle]

/-- **Elementary transformation 2** (Petrunin, Section 18H, p. 152): for `w ≠ 0` the map `z ↦ w·z`
(rotational homothety with centre `0`) multiplies distances by `|w|`, preserves signed angles, and
sends a point `Z ≠ 0` to a point `Z'` with `OZ' = |w|·OZ` and `∡ Z O Z' = arg w`. -/
@[kb "petrunin2025" "Section 18H, p. 152"]
theorem rotational_homothety {w : ℂ} (hw : w ≠ 0) :
    (∀ a b : ℂ, dist (w * a) (w * b) = ‖w‖ * dist a b) ∧
    (∀ a b c : ℂ, ∡ (w * a) (w * b) (w * c) = ∡ a b c) ∧
    (∀ z : ℂ, z ≠ 0 →
      dist 0 (w * z) = ‖w‖ * dist 0 z ∧ ∡ z 0 (w * z) = (Complex.arg w : Real.Angle)) := by
  refine ⟨fun a b => by simp [Complex.dist_eq, ← mul_sub], fun a b c => ?_,
    fun z hz => ⟨by simp [Complex.dist_eq], ?_⟩⟩
  · by_cases hab : a = b
    · subst hab; simp
    by_cases hcb : c = b
    · subst hcb; simp
    have h1 : w * a ≠ w * b := fun h => hab (mul_left_cancel₀ hw h)
    have h2 : w * c ≠ w * b := fun h => hcb (mul_left_cancel₀ hw h)
    rw [oangle_eq_arg_div h1 h2, oangle_eq_arg_div hab hcb, ← mul_sub, ← mul_sub,
      mul_div_mul_left _ _ hw]
  · have : w * z ≠ 0 := mul_ne_zero hw hz
    rw [oangle_eq_arg_div hz this]
    simp [mul_div_cancel_right₀ _ hz]

/-- **Elementary transformation 3** (Petrunin, Section 18H, p. 152): the map `z ↦ 1/z` satisfies
`OZ · OZ' = 1` and sends the signed angle at the origin `∡ A O B` to `-∡ A O B` (it is the inversion
across the unit circle, which preserves such angles, followed by the conjugation, which negates
them; see `inv_eq_conj_inversion`). -/
@[kb "petrunin2025" "Section 18H, p. 152"]
theorem inv_dist_oangle {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    dist 0 a * dist 0 a⁻¹ = 1 ∧ ∡ a⁻¹ 0 b⁻¹ = -∡ a 0 b := by
  refine ⟨?_, ?_⟩
  · simp [Complex.dist_eq, ha]
  · rw [oangle_eq_arg_div ha hb, oangle_eq_arg_div (inv_ne_zero ha) (inv_ne_zero hb)]
    have : (b⁻¹ - 0) / (a⁻¹ - 0) = ((b - 0) / (a - 0))⁻¹ := by
      simp only [sub_zero, inv_div]
      field_simp
    rw [this, Complex.arg_inv_coe_angle]

end ComplexPlane

section TangentHalfLines

open Filter Topology AffineSubspace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- The tangent-chord angle equals the inscribed angle: if `[AX)` is tangent at `A` to the arc `ABC`
of `s` and `Y` lies on the arc `ABC` (on `s`, strictly on the side of `(AC)` containing `B`), then
`∡XAY = ∡ACY`. -/
theorem oangle_tangent_chord_eq {s : Sphere P} {A B C X Y : P} (hA : A ∈ s)
    (hC : C ∈ s) (hAC : A ≠ C) (hXA : X ≠ A)
    (htan : s.IsTangentAt A line[ℝ, A, X] ∧ line[ℝ, A, C].SSameSide X B) (hY : Y ∈ s)
    (hYs : line[ℝ, A, C].SSameSide B Y) : ∡ X A Y = ∡ A C Y := by
  have hYl : Y ∉ line[ℝ, A, C] := hYs.right_notMem
  have hYA : Y ≠ A := fun h => hYl (h ▸ left_mem_affineSpan_pair ℝ A C)
  have hYC : Y ≠ C := fun h => hYl (h ▸ right_mem_affineSpan_pair ℝ A C)
  have h1 := (tangent_halfline_iff hA hY hC hAC hYA hYC hXA).1 ⟨htan.1, htan.2.trans hYs⟩
  have h2 := oangle_add_oangle_add_oangle_eq_pi (p₁ := A) (p₂ := Y) (p₃ := C) hYA hYC.symm hAC
  have h3 := oangle_add (p := A) (p₁ := X) (p₂ := C) (p₃ := Y) hXA hAC.symm hYA
  have h4 := oangle_rev X A C
  have h5 := oangle_rev A C Y
  rw [← sub_eq_zero]
  linear_combination (norm := abel) h3.symm + h2 - h1 + h4 - h5

/-- **Exercise 9.29** (Petrunin, p. 72): if `[AX)` is the tangent half-line at `A` to the arc `ABC` of
a circle `s`, then the angle `∠XAY` between it and the chord `AY` tends to `0` as `Y` tends to `A`
along the arc (`Y ∈ s` strictly on the side of `(AC)` containing `B`). -/
@[kb "petrunin2025" "Exercise 9.29, p. 72"]
theorem tendsto_angle_tangent_chord {s : Sphere P} {A B C X : P} (hA : A ∈ s)
    (hC : C ∈ s) (hAC : A ≠ C) (hXA : X ≠ A)
    (htan : s.IsTangentAt A line[ℝ, A, X] ∧ line[ℝ, A, C].SSameSide X B) :
    Tendsto (fun Y => ∠ X A Y)
      (𝓝[{Y | Y ∈ s ∧ line[ℝ, A, C].SSameSide B Y}] A) (𝓝 0) := by
  have hcont : ContinuousAt (fun Y : P => ∠ A C Y) A := by
    have := (EuclideanGeometry.continuousAt_angle (x := (A, C, A)) hAC hAC).comp
      (f := fun Y : P => (A, C, Y)) (x := A) (by fun_prop)
    exact this
  have hlim : Tendsto (fun Y => ∠ A C Y) (𝓝[{Y | Y ∈ s ∧ line[ℝ, A, C].SSameSide B Y}] A)
      (𝓝 0) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {Y | Y ∈ s ∧
      line[ℝ, A, C].SSameSide B Y}))
    rwa [angle_self_of_ne hAC] at this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Y hY
  obtain ⟨hYs, hYside⟩ := hY
  have hYl : Y ∉ line[ℝ, A, C] := hYside.right_notMem
  have hYA : Y ≠ A := fun h => hYl (h ▸ left_mem_affineSpan_pair ℝ A C)
  have hYC : Y ≠ C := fun h => hYl (h ▸ right_mem_affineSpan_pair ℝ A C)
  have h := oangle_tangent_chord_eq hA hC hAC hXA htan hYs hYside
  rw [angle_eq_abs_oangle_toReal hXA hYA, h]
  exact angle_eq_abs_oangle_toReal hAC hYC

/-- **Exercise 9.30** (Petrunin, p. 72): let `AB₁C` and `AB₂C` be arcs of circles `s₁`, `s₂` (distinct
points on each circle), `[AX₁)`, `[AX₂)` the tangent half-lines at `A` and `[CY₁)`, `[CY₂)` the tangent
half-lines at `C`. Then `∡X₁AX₂ = -∡Y₁CY₂`. -/
@[kb "petrunin2025" "Exercise 9.30, p. 72"]
theorem oangle_tangents_arcs {s₁ s₂ : Sphere P} {A C B₁ B₂ X₁ X₂ Y₁ Y₂ : P}
    (hA₁ : A ∈ s₁) (hB₁ : B₁ ∈ s₁) (hC₁ : C ∈ s₁) (hA₂ : A ∈ s₂) (hB₂ : B₂ ∈ s₂) (hC₂ : C ∈ s₂)
    (hAC : A ≠ C) (hB₁A : B₁ ≠ A) (hB₁C : B₁ ≠ C) (hB₂A : B₂ ≠ A) (hB₂C : B₂ ≠ C)
    (hX₁ : X₁ ≠ A) (hX₂ : X₂ ≠ A) (hY₁ : Y₁ ≠ C) (hY₂ : Y₂ ≠ C)
    (tX₁ : s₁.IsTangentAt A line[ℝ, A, X₁] ∧ line[ℝ, A, C].SSameSide X₁ B₁)
    (tX₂ : s₂.IsTangentAt A line[ℝ, A, X₂] ∧ line[ℝ, A, C].SSameSide X₂ B₂)
    (tY₁ : s₁.IsTangentAt C line[ℝ, C, Y₁] ∧ line[ℝ, C, A].SSameSide Y₁ B₁)
    (tY₂ : s₂.IsTangentAt C line[ℝ, C, Y₂] ∧ line[ℝ, C, A].SSameSide Y₂ B₂) :
    ∡ X₁ A X₂ = -∡ Y₁ C Y₂ := by
  have a1 := (tangent_halfline_iff hA₁ hB₁ hC₁ hAC hB₁A hB₁C hX₁).1 tX₁
  have a2 := (tangent_halfline_iff hA₂ hB₂ hC₂ hAC hB₂A hB₂C hX₂).1 tX₂
  have c1 := (tangent_halfline_iff hC₁ hB₁ hA₁ hAC.symm hB₁C hB₁A hY₁).1 tY₁
  have c2 := (tangent_halfline_iff hC₂ hB₂ hA₂ hAC.symm hB₂C hB₂A hY₂).1 tY₂
  have x := oangle_add (p := A) (p₁ := X₁) (p₂ := C) (p₃ := X₂) hX₁ hAC.symm hX₂
  have y := oangle_add (p := C) (p₁ := Y₁) (p₂ := A) (p₃ := Y₂) hY₁ hAC hY₂
  have rx := oangle_rev X₁ A C
  have ry := oangle_rev Y₁ C A
  have r1 := oangle_rev A B₁ C
  have r2 := oangle_rev A B₂ C
  rw [eq_neg_iff_add_eq_zero]
  linear_combination (norm := abel) -a1 + a2 - c1 + c2 + r1 - r2 + rx + ry - x - y

end TangentHalfLines

end UndergradKB.Geometry
