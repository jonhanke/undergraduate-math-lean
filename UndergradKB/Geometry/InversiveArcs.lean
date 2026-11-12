import UndergradKB.Geometry.InversivePlane
import UndergradKB.Geometry.ComplexCoordinates
import UndergradKB.Common.Attr

/-! # Arcs of the inversive plane and their inverses (Petrunin, Proposition 10.24, p. 81)

In the inversive plane `OnePoint ℂ` we define, uniformly for all points `A, B, C` (including `∞`),
the arc `ABC` through `B` with endpoints `A`, `C` by a cross-ratio condition: a point `D` lies on
the arc iff the cross-ratio `[C D][A B] / ([A D][C B])` is a positive real number (or `D` is one of the
three points), where `[X Y]` is the determinant of homogeneous coordinates (`∞ = (1 : 0)`,
`z = (z : 1)`).  For finite points this is the criterion `∡ADC = ∡ABC` of Proposition 9.23, and we
prove that the finite part of the arc is exactly `arcOrient A B C`.

The inversion `inversionOP O R` conjugates the cross-ratio, because in homogeneous coordinates it is
a conjugate-linear map of determinant `-R²`; hence it maps every arc onto an arc, for all
positions of `A, B, C` relative to the centre `O` and to `∞`. -/

namespace UndergradKB.Geometry

open EuclideanGeometry OnePoint ComplexConjugate

namespace InversiveArcs

/-- Homogeneous coordinates of a point of the inversive plane `OnePoint ℂ`: `∞ ↦ (1, 0)`,
`z ↦ (z, 1)`. -/
def rep (z : OnePoint ℂ) : ℂ × ℂ := z.elim (1, 0) (fun x => (x, 1))

/-- The determinant of two homogeneous coordinate pairs. -/
def det (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

/-- The cross-ratio of four points of the inversive plane `OnePoint ℂ`, with the convention that
`ρ A B C D = (C - D) (A - B) / ((A - D) (C - B))` for finite points; it is defined uniformly (also
with `∞`) by homogeneous coordinates. -/
noncomputable def rho (A B C D : OnePoint ℂ) : ℂ :=
  det (rep C) (rep D) * det (rep A) (rep B) / (det (rep A) (rep D) * det (rep C) (rep B))

theorem rho_coe (A B C D : ℂ) :
    rho A B C D = (C - D) * (A - B) / ((A - D) * (C - B)) := by
  simp only [rho, rep, det, OnePoint.elim_some]
  ring

end InversiveArcs

open InversiveArcs

/-- **The arc `ABC` of the inversive plane** (Petrunin, Section 9 D and Proposition 10.24, p. 81):
the arc with endpoints `A`, `C` passing through `B`, for any points of `OnePoint ℂ`.  A point `D` lies
on it iff `D ∈ {A, B, C}` or the cross-ratio `ρ A B C D` is a positive real number.  For finite points
this is `∡ADC = ∡ABC` (see `mem_arcOP_coe_iff_arcOrient`); when `∞` is involved, or when `A, B, C`
are collinear, it gives half-lines, segments and complements of segments together with `∞`. -/
@[kb "petrunin2025" "Proposition 10.24, p. 81"]
def arcOP (A B C : OnePoint ℂ) : Set (OnePoint ℂ) :=
  {D | D = A ∨ D = B ∨ D = C ∨ ∃ t : ℝ, 0 < t ∧ rho A B C D = t}

noncomputable local instance instOrientedComplex : Module.Oriented ℝ ℂ (Fin 2) :=
  ⟨Complex.orientation⟩

local instance instFactFinrankComplex : Fact (Module.finrank ℝ ℂ = 2) :=
  ⟨Complex.finrank_real_complex⟩

theorem aux {q1 q2 : ℂ} (h1 : q1 ≠ 0) (h2 : q2 ≠ 0) :
    (∃ t : ℝ, 0 < t ∧ q1 / q2 = t) ↔ (‖q2‖ / ‖q1‖ : ℂ) * q1 = q2 := by
  have hn1 : ‖q1‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have hn2 : ‖q2‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  have c1 : (‖q1‖ : ℂ) ≠ 0 := by exact_mod_cast hn1
  have c2 : (‖q2‖ : ℂ) ≠ 0 := by exact_mod_cast hn2
  constructor
  · rintro ⟨t, ht, h⟩
    rw [div_eq_iff h2] at h
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
  · intro h
    refine ⟨‖q1‖ / ‖q2‖, by positivity, ?_⟩
    rw [div_eq_iff h2]
    have e : q1 = ((‖q1‖ / ‖q2‖ : ℝ) : ℂ) * ((‖q2‖ / ‖q1‖ : ℂ) * q1) := by
      push_cast
      field_simp
    rw [h] at e
    exact e

/-- The finite part of the inversive arc is the oriented-angle arc `arcOrient` of
Proposition 9.23 (for `A ≠ B`, `B ≠ C`). -/
@[kb "petrunin2025" "Proposition 10.24, p. 81"]
theorem mem_arcOP_coe_iff_arcOrient {A B C D : ℂ} (hAB : A ≠ B) (hBC : B ≠ C) :
    (D : OnePoint ℂ) ∈ arcOP A B C ↔ D ∈ arcOrient A B C := by
  by_cases hDA : D = A
  · subst hDA; simp [arcOP, arcOrient]
  by_cases hDC : D = C
  · subst hDC; simp [arcOP, arcOrient]
  have h1 : A - D ≠ 0 := sub_ne_zero.mpr (Ne.symm hDA)
  have h2 : C - D ≠ 0 := sub_ne_zero.mpr (Ne.symm hDC)
  have h3 : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have h4 : C - B ≠ 0 := sub_ne_zero.mpr (Ne.symm hBC)
  have hq1 : (C - D) / (A - D) ≠ 0 := div_ne_zero h2 h1
  have hq2 : (C - B) / (A - B) ≠ 0 := div_ne_zero h4 h3
  have hr : rho A B C D = ((C - D) / (A - D)) / ((C - B) / (A - B)) := by
    rw [rho_coe]; field_simp
  have hn1 : ‖(C - D) / (A - D)‖ ≠ 0 := norm_ne_zero_iff.mpr hq1
  have hn2 : ‖(C - B) / (A - B)‖ ≠ 0 := norm_ne_zero_iff.mpr hq2
  have hcore : (∃ t : ℝ, 0 < t ∧ rho A B C D = t) ↔ ∡ A D C = ∡ A B C := by
    rw [ComplexCoordinates.oangle_eq_arg_div (Ne.symm hDA) (Ne.symm hDC),
      ComplexCoordinates.oangle_eq_arg_div hAB hBC.symm, Complex.arg_coe_angle_eq_iff,
      Complex.arg_eq_arg_iff hq1 hq2]
    rw [hr]; exact aux hq1 hq2
  simp only [arcOP, arcOrient, Set.mem_ofPred_eq, OnePoint.coe_eq_coe, hDA, hDC, false_or]
  rw [← hcore]
  by_cases hDB : D = B
  · subst hDB; simp [hr]
    exact ⟨1, one_pos, by simp [div_self hq2]⟩
  · simp [hDB]

/-! ### Inversion conjugates the cross-ratio -/

namespace InversiveArcs

theorem inversion_complex {O x : ℂ} {R : ℝ} (hx : x ≠ O) :
    inversion O R x = O + (R : ℂ) ^ 2 / conj (x - O) := by
  have hw : x - O ≠ 0 := sub_ne_zero.mpr hx
  have hc : conj (x - O) ≠ 0 := (map_ne_zero _).mpr hw
  have hn : ((‖x - O‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have hm : (x - O) * conj (x - O) = ((‖x - O‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [inversion_def]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul, dist_eq_norm]
  push_cast
  field_simp
  rw [← hm]; ring

/-- The conjugate-linear map of `ℂ²` that represents the inversion with centre `O` and radius `R`. -/
def invMap (O : ℂ) (R : ℝ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (O * conj u.1 + ((R : ℂ) ^ 2 - O * conj O) * conj u.2, conj u.1 - conj O * conj u.2)

theorem det_invMap (O : ℂ) (R : ℝ) (u v : ℂ × ℂ) :
    det (invMap O R u) (invMap O R v) = -(R : ℂ) ^ 2 * conj (det u v) := by
  simp only [det, invMap, map_sub, map_mul]
  ring

theorem rep_inversionOP {O : ℂ} {R : ℝ} (hR : R ≠ 0) (z : OnePoint ℂ) :
    ∃ l : ℂ, l ≠ 0 ∧ rep (inversionOP O R z) = l • invMap O R (rep z) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  induction z using OnePoint.rec with
  | infty =>
    refine ⟨1, one_ne_zero, ?_⟩
    simp [rep, invMap]
  | coe x =>
    by_cases hx : x = O
    · subst hx
      refine ⟨1 / (R : ℂ) ^ 2, by simp [hR'], ?_⟩
      simp [rep, invMap, Prod.ext_iff]
      field_simp
    · have hw : x - O ≠ 0 := sub_ne_zero.mpr hx
      have hc : conj (x - O) ≠ 0 := (map_ne_zero _).mpr hw
      refine ⟨1 / conj (x - O), one_div_ne_zero hc, ?_⟩
      rw [inversionOP_coe_of_ne hx, inversion_complex hx]
      simp only [rep, invMap, OnePoint.elim_some, map_one, Prod.smul_mk, smul_eq_mul,
        Prod.ext_iff]
      simp only [map_sub] at hc ⊢
      constructor
      · field_simp
        ring
      · field_simp

theorem det_smul_smul (l l' : ℂ) (u v : ℂ × ℂ) : det (l • u) (l' • v) = l * l' * det u v := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The inversion with centre `O` conjugates the cross-ratio. -/
theorem rho_inversionOP {O : ℂ} {R : ℝ} (hR : R ≠ 0) (A B C D : OnePoint ℂ) :
    rho (inversionOP O R A) (inversionOP O R B) (inversionOP O R C) (inversionOP O R D) =
      conj (rho A B C D) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  obtain ⟨a, ha, hA⟩ := rep_inversionOP (O := O) hR A
  obtain ⟨b, hb, hB⟩ := rep_inversionOP (O := O) hR B
  obtain ⟨c, hc, hC⟩ := rep_inversionOP (O := O) hR C
  obtain ⟨d, hd, hD⟩ := rep_inversionOP (O := O) hR D
  unfold rho
  rw [hA, hB, hC, hD, det_smul_smul, det_smul_smul, det_smul_smul, det_smul_smul, det_invMap,
    det_invMap, det_invMap, det_invMap, map_div₀, map_mul, map_mul]
  have hK : c * d * (-(R : ℂ) ^ 2) * (a * b * (-(R : ℂ) ^ 2)) ≠ 0 := by
    simp [ha, hb, hc, hd, hR']
  have e1 : c * d * (-(R : ℂ) ^ 2 * conj (det (rep C) (rep D))) *
      (a * b * (-(R : ℂ) ^ 2 * conj (det (rep A) (rep B)))) =
      (c * d * (-(R : ℂ) ^ 2) * (a * b * (-(R : ℂ) ^ 2))) *
        (conj (det (rep C) (rep D)) * conj (det (rep A) (rep B))) := by ring
  have e2 : a * d * (-(R : ℂ) ^ 2 * conj (det (rep A) (rep D))) *
      (c * b * (-(R : ℂ) ^ 2 * conj (det (rep C) (rep B)))) =
      (c * d * (-(R : ℂ) ^ 2) * (a * b * (-(R : ℂ) ^ 2))) *
        (conj (det (rep A) (rep D)) * conj (det (rep C) (rep B))) := by ring
  rw [e1, e2, mul_div_mul_left _ _ hK]

end InversiveArcs

theorem inversionOP_mem_arcOP {O : ℂ} {R : ℝ} (hR : R ≠ 0) {A B C D : OnePoint ℂ}
    (h : D ∈ arcOP A B C) :
    inversionOP O R D ∈ arcOP (inversionOP O R A) (inversionOP O R B) (inversionOP O R C) := by
  rcases h with h | h | h | ⟨t, ht, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inl (by rw [h]))
  · exact Or.inr (Or.inr (Or.inl (by rw [h])))
  · refine Or.inr (Or.inr (Or.inr ⟨t, ht, ?_⟩))
    rw [rho_inversionOP hR, h, Complex.conj_ofReal]

/-- **Petrunin, Proposition 10.24** (the inverse of an arc is an arc, in the inversive plane
`OnePoint ℂ`): the inversion with centre `O` and radius `R ≠ 0` maps the arc `ABC` onto the arc
`A'B'C'` of the inverted points, for all points `A, B, C` of the inversive plane, in particular
whether or not the arc passes through the centre `O` (which the inversion sends to `∞`) or
through `∞` (sent to `O`).  The agreement with the angle description for finite arcs is
`mem_arcOP_coe_iff_arcOrient`. -/
@[kb "petrunin2025" "Proposition 10.24, p. 81"]
theorem image_inversionOP_arcOP {O : ℂ} {R : ℝ} (hR : R ≠ 0) (A B C : OnePoint ℂ) :
    inversionOP O R '' arcOP A B C =
      arcOP (inversionOP O R A) (inversionOP O R B) (inversionOP O R C) := by
  refine inversionOP_image_eq_of_maps hR (fun z hz => inversionOP_mem_arcOP hR hz) fun z hz => ?_
  have := inversionOP_mem_arcOP (O := O) hR hz
  rwa [inversionOP_involutive hR A, inversionOP_involutive hR B,
    inversionOP_involutive hR C] at this

end UndergradKB.Geometry
