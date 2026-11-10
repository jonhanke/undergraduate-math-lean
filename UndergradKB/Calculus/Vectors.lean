import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import UndergradKB.Common.Attr

/-! # Calculus: vectors in the plane and in space

Vectors of space are `Fin 3 → ℝ` with Mathlib's `⬝ᵥ` (dot product) and `⨯₃` (cross product). The Euclidean length
is `len v = √(v ⬝ᵥ v)`; the angle between vectors is Mathlib's `InnerProductGeometry.angle` transported along
`WithLp.toLp 2`. -/

namespace UndergradKB.Calculus

open Matrix InnerProductGeometry

/-- Euclidean length (magnitude) of a vector of `ℝ³`: `√(v ⬝ᵥ v)`. -/
noncomputable def len (v : Fin 3 → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The angle between two vectors of `ℝ³` (Mathlib's unoriented angle on `EuclideanSpace ℝ (Fin 3)`). -/
noncomputable def vangle (u v : Fin 3 → ℝ) : ℝ := angle (WithLp.toLp 2 u) (WithLp.toLp 2 v)

lemma dot_expand (u v : Fin 3 → ℝ) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [dotProduct, Fin.sum_univ_three]

lemma cross_0 (u v : Fin 3 → ℝ) : (u ⨯₃ v) 0 = u 1 * v 2 - u 2 * v 1 := by simp [cross_apply]
lemma cross_1 (u v : Fin 3 → ℝ) : (u ⨯₃ v) 1 = u 2 * v 0 - u 0 * v 2 := by simp [cross_apply]
lemma cross_2 (u v : Fin 3 → ℝ) : (u ⨯₃ v) 2 = u 0 * v 1 - u 1 * v 0 := by simp [cross_apply]

lemma dot_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [dot_expand]; nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2)]

lemma len_sq (v : Fin 3 → ℝ) : len v ^ 2 = v ⬝ᵥ v := by
  unfold len; exact Real.sq_sqrt (dot_self_nonneg v)

lemma len_nonneg (v : Fin 3 → ℝ) : 0 ≤ len v := Real.sqrt_nonneg _

lemma len_eq_zero {v : Fin 3 → ℝ} : len v = 0 ↔ v = 0 := by
  unfold len
  rw [Real.sqrt_eq_zero (dot_self_nonneg v)]
  exact dotProduct_self_eq_zero

lemma len_pos {v : Fin 3 → ℝ} (h : v ≠ 0) : 0 < len v :=
  lt_of_le_of_ne (len_nonneg v) (fun h0 => h (len_eq_zero.1 h0.symm))

lemma len_smul (c : ℝ) (v : Fin 3 → ℝ) : len (c • v) = |c| * len v := by
  unfold len
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Real.sqrt_mul (by nlinarith [sq_nonneg c] : 0 ≤ c * c) , Real.sqrt_mul_self_eq_abs]

lemma len_neg (v : Fin 3 → ℝ) : len (-v) = len v := by
  have := len_smul (-1) v
  simpa using this

lemma norm_toLp (v : Fin 3 → ℝ) : ‖WithLp.toLp 2 v‖ = len v := by
  rw [EuclideanSpace.norm_eq]
  unfold len
  simp [dotProduct, Fin.sum_univ_three, sq]

lemma len_sub_comm (u v : Fin 3 → ℝ) : len (u - v) = len (v - u) := by
  rw [← neg_sub, len_neg]

/-- Lagrange identity: `‖u × v‖² = ‖u‖²‖v‖² − (u·v)²`. -/
lemma lagrange (u v : Fin 3 → ℝ) :
    (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  rw [cross_dot_cross]; rw [dotProduct_comm v u]; ring

/-! ## Standard unit vectors and cross products (CA-449, CA-453) -/

/-- The standard unit vector `i`. -/
def ei : Fin 3 → ℝ := ![1, 0, 0]
/-- The standard unit vector `j`. -/
def ej : Fin 3 → ℝ := ![0, 1, 0]
/-- The standard unit vector `k`. -/
def ek : Fin 3 → ℝ := ![0, 0, 1]

/-- OpenStax Calculus 3:§2.4 text (cross products of standard unit vectors), p. 160 (CA-449):
`i × j = k`, `j × k = i`, `k × i = j`, reverse order gives negatives, and `i × i = j × j = k × k = 0`. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (cross products of standard unit vectors), p. 160"]
theorem cross_unit_vectors :
    ei ⨯₃ ej = ek ∧ ej ⨯₃ ek = ei ∧ ek ⨯₃ ei = ej ∧
    ej ⨯₃ ei = -ek ∧ ek ⨯₃ ej = -ei ∧ ei ⨯₃ ek = -ej ∧
    ei ⨯₃ ei = 0 ∧ ej ⨯₃ ej = 0 ∧ ek ⨯₃ ek = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, cross_self _, cross_self _, cross_self _⟩ <;>
  · ext i; fin_cases i <;> simp [ei, ej, ek, cross_apply]

/-- OpenStax Calculus 3:§2.4 Rule (cross product calculated by a determinant), p. 164 (CA-453):
the `l`-th component of `u × v` is the determinant of the matrix whose first row is the `l`-th
standard unit vector (the formal `i, j, k` row) and whose other rows are `u` and `v`. -/
@[kb "openstaxcalculus2016" "3:§2.4 Rule: Cross Product Calculated by a Determinant, p. 164"]
theorem cross_apply_eq_det (u v : Fin 3 → ℝ) (l : Fin 3) :
    (u ⨯₃ v) l = Matrix.det ![Pi.single l 1, u, v] := by
  rw [← triple_product_eq_det]
  simp [dotProduct, Pi.single_apply]

/-- OpenStax Calculus 3:§2.4 Rule (cross product calculated by a determinant), p. 164 (CA-453):
cofactor expansion along the first row `(i, j, k)`:
`u × v = det₂(u₂ u₃; v₂ v₃) i − det₂(u₁ u₃; v₁ v₃) j + det₂(u₁ u₂; v₁ v₂) k`. -/
@[kb "openstaxcalculus2016" "3:§2.4 Rule: Cross Product Calculated by a Determinant, p. 164"]
theorem cross_eq_cofactor (u v : Fin 3 → ℝ) :
    u ⨯₃ v = Matrix.det !![u 1, u 2; v 1, v 2] • ei - Matrix.det !![u 0, u 2; v 0, v 2] • ej
      + Matrix.det !![u 0, u 1; v 0, v 1] • ek := by
  ext i; fin_cases i <;> simp [ei, ej, ek, cross_apply, Matrix.det_fin_two]

/-! ## Triple scalar product (CA-455, CA-456, CA-448) -/

/-- OpenStax Calculus 3:§2.4 text (identities for permuting a triple scalar product), p. 168 (CA-456):
the triple product is invariant under cyclic permutation. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (identities for permuting a triple scalar product), p. 168"]
theorem triple_cyclic (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ v ⨯₃ w = v ⬝ᵥ w ⨯₃ u ∧ v ⬝ᵥ w ⨯₃ u = w ⬝ᵥ u ⨯₃ v :=
  ⟨triple_product_permutation u v w, triple_product_permutation v w u⟩

/-- OpenStax Calculus 3:§2.4 text (identities for permuting a triple scalar product), p. 168 (CA-456):
swapping two of the vectors changes the sign. -/
@[kb "openstaxcalculus2016" "3:§2.4 text (identities for permuting a triple scalar product), p. 168"]
theorem triple_swap (u v w : Fin 3 → ℝ) :
    u ⬝ᵥ v ⨯₃ w = -(v ⬝ᵥ u ⨯₃ w) ∧ u ⬝ᵥ v ⨯₃ w = -(u ⬝ᵥ w ⨯₃ v) ∧
      u ⬝ᵥ v ⨯₃ w = -(w ⬝ᵥ v ⨯₃ u) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [dot_expand, cross_0, cross_1, cross_2] <;> ring

/-- OpenStax Calculus 3:§2.4 text (right-hand rule), p. 158 (CA-448): the triple `(u, v, u × v)` has
determinant `‖u × v‖² ≥ 0`, so it is positively oriented (strictly when `u × v ≠ 0`). -/
@[kb "openstaxcalculus2016" "3:§2.4 text (right-hand rule), p. 158"]
theorem det_self_cross (u v : Fin 3 → ℝ) :
    Matrix.det ![u, v, u ⨯₃ v] = len (u ⨯₃ v) ^ 2 ∧ 0 ≤ Matrix.det ![u, v, u ⨯₃ v] ∧
      (u ⨯₃ v ≠ 0 → 0 < Matrix.det ![u, v, u ⨯₃ v]) := by
  have h : Matrix.det ![u, v, u ⨯₃ v] = len (u ⨯₃ v) ^ 2 := by
    rw [← triple_product_eq_det, (triple_product_permutation u v _).trans
      (triple_product_permutation v (u ⨯₃ v) u), len_sq]
  refine ⟨h, by rw [h]; positivity, fun hne => ?_⟩
  rw [h]; exact pow_pos (len_pos hne) 2

/-! ## Area (CA-454), torque (CA-459), work (CA-445) -/

/-- OpenStax Calculus 3:Theorem 2.7, p. 162 (CA-451): `‖u × v‖ = ‖u‖‖v‖ sin θ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.7, p. 162"]
theorem len_cross_eq (u v : Fin 3 → ℝ) :
    len (u ⨯₃ v) = len u * len v * Real.sin (vangle u v) := by
  have := norm_toLp_symm_crossProduct u v
  simpa [norm_toLp, vangle] using this

/-- OpenStax Calculus 3:Theorem 2.8, p. 165 (CA-454): the parallelogram with sides `u`, `v` has
area `‖u × v‖ = (base ‖u‖) · (height ‖v‖ sin θ)`, and the triangle on them has half of it. The
Lagrange identity is the algebraic form of this equality. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.8, p. 165"]
theorem parallelogram_area (u v : Fin 3 → ℝ) :
    len (u ⨯₃ v) = len u * (len v * Real.sin (vangle u v)) ∧
    len (u ⨯₃ v) ^ 2 = len u ^ 2 * len v ^ 2 - (u ⬝ᵥ v) ^ 2 := by
  refine ⟨by rw [len_cross_eq]; ring, ?_⟩
  rw [len_sq, lagrange, len_sq, len_sq]

/-- OpenStax Calculus 3:Example 2.44, p. 171 (CA-459): torque `r × F` has magnitude
`‖r‖‖F‖ sin θ`. -/
@[kb "openstaxcalculus2016" "3:§2.4 Definition (torque), p. 170"]
theorem torque_magnitude (r F : Fin 3 → ℝ) :
    len (r ⨯₃ F) = len r * len F * Real.sin (vangle r F) := len_cross_eq r F

/-- OpenStax Calculus 3:§2.3 Definition (work), p. 151 (CA-445): `F · s = ‖F‖‖s‖ cos θ`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (work, Eq 2.8), p. 151"]
theorem work_eq (F s : Fin 3 → ℝ) : F ⬝ᵥ s = len F * len s * Real.cos (vangle F s) := by
  have := cos_angle_mul_norm_mul_norm (WithLp.toLp 2 F) (WithLp.toLp 2 s)
  rw [norm_toLp, norm_toLp] at this
  have h2 : (inner ℝ (WithLp.toLp 2 F) (WithLp.toLp 2 s)) = F ⬝ᵥ s := by
    simp [PiLp.inner_apply, dot_expand, Fin.sum_univ_three, mul_comm]
  rw [h2] at this
  unfold vangle
  linarith

/-! ## Parallelepiped volume (CA-457) and coplanarity (CA-458) -/

open MeasureTheory in
/-- OpenStax Calculus 3:Theorem 2.10, p. 168 (CA-457): the Lebesgue volume of the parallelepiped
spanned by `u, v, w` in `ℝ³` is `|u · (v × w)|`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.10, p. 168"]
theorem volume_parallelepiped_triple (u v w : Fin 3 → ℝ) :
    volume (parallelepiped ![u, v, w]) = ENNReal.ofReal |u ⬝ᵥ v ⨯₃ w| := by
  rw [← addHaarMeasure_eq_volume_pi, ← Module.Basis.parallelepiped_basisFun,
    ← Module.Basis.addHaar_def, Measure.addHaar_parallelepiped, Module.Basis.det_apply,
    triple_product_eq_det, ← Matrix.det_transpose]
  congr 3

/-- Three vectors of `ℝ³` are coplanar when they span a subspace of dimension less than three. -/
def Coplanar (u v w : Fin 3 → ℝ) : Prop :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range ![u, v, w])) < 3

/-- OpenStax Calculus 3:Example 2.42, p. 169 (CA-458): three vectors are coplanar (linearly
dependent) if and only if their triple scalar product vanishes. -/
@[kb "openstaxcalculus2016" "3:Example 2.42, p. 169"]
theorem coplanar_iff_triple_eq_zero (u v w : Fin 3 → ℝ) :
    Coplanar u v w ↔ u ⬝ᵥ v ⨯₃ w = 0 := by
  have hli : LinearIndependent ℝ ![u, v, w] ↔ Matrix.det ![u, v, w] ≠ 0 := by
    have := Matrix.linearIndependent_row_iff_isUnit (A := (Matrix.of ![u, v, w] : Matrix (Fin 3) (Fin 3) ℝ))
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
    exact this
  have hcop : Coplanar u v w ↔ ¬ LinearIndependent ℝ ![u, v, w] := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    unfold Coplanar
    have := finrank_range_le_card (R := ℝ) (ι := Fin 3) ![u, v, w]
    simp only [Fintype.card_fin, Set.finrank] at *
    omega
  rw [hcop, hli, triple_product_eq_det, not_not]

/-! ## Parallel vectors, direction cosines, components, projections -/

/-- OpenStax Calculus 3:§2.1 Definition (parallel vectors), p. 98 (CA-423): two nonzero vectors are
scalar multiples of each other exactly when their angle is `0` (same direction) or `π` (opposite). -/
@[kb "openstaxcalculus2016" "3:§2.1 Definition (parallel vectors), p. 98"]
theorem parallel_iff_angle {u v : Fin 3 → ℝ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (∃ c : ℝ, u = c • v) ↔ (vangle u v = 0 ∨ vangle u v = Real.pi) := by
  have hu' : WithLp.toLp 2 u ≠ 0 := fun h => hu (by simpa using congrArg WithLp.ofLp h)
  have hv' : WithLp.toLp 2 v ≠ 0 := fun h => hv (by simpa using congrArg WithLp.ofLp h)
  unfold vangle
  rw [angle_eq_zero_iff, angle_eq_pi_iff]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := fun h => hu (by simp [h])
    have e : WithLp.toLp 2 v = c⁻¹ • WithLp.toLp 2 (c • v) := by
      ext i; simp [hc]
    rcases lt_or_gt_of_ne hc with h | h
    · exact Or.inr ⟨hu', c⁻¹, inv_lt_zero.2 h, e⟩
    · exact Or.inl ⟨hu', c⁻¹, inv_pos.2 h, e⟩
  · rintro (⟨_, r, hr, h⟩ | ⟨_, r, hr, h⟩) <;>
    · have hr0 : r ≠ 0 := by intro h0; subst h0; simp at hr
      refine ⟨r⁻¹, ?_⟩
      ext i
      have := congrArg (fun x => x.ofLp i) h
      simp at this
      simp [this, hr0]

/-- OpenStax Calculus 3:§2.3 Definition (direction angles and direction cosines), p. 146 (CA-441):
the squares of the direction cosines of a nonzero vector (cosines of its angles with `i`, `j`, `k`)
sum to one; each is the matching coordinate over the length. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (direction angles and direction cosines), p. 146"]
theorem direction_cosines {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    Real.cos (vangle v ei) = v 0 / len v ∧ Real.cos (vangle v ej) = v 1 / len v ∧
    Real.cos (vangle v ek) = v 2 / len v ∧
    Real.cos (vangle v ei) ^ 2 + Real.cos (vangle v ej) ^ 2 + Real.cos (vangle v ek) ^ 2 = 1 := by
  have key : ∀ e : Fin 3 → ℝ, len e = 1 → Real.cos (vangle v e) = (v ⬝ᵥ e) / len v := by
    intro e he
    unfold vangle
    rw [cos_angle, norm_toLp, norm_toLp, he, mul_one]
    simp [PiLp.inner_apply, dot_expand, Fin.sum_univ_three, mul_comm]
  have l1 : ∀ e : Fin 3 → ℝ, e = ei ∨ e = ej ∨ e = ek → len e = 1 := by
    intro e he
    unfold len
    rcases he with rfl | rfl | rfl <;> simp [ei, ej, ek]
  have h1 := key ei (l1 _ (Or.inl rfl))
  have h2 := key ej (l1 _ (Or.inr (Or.inl rfl)))
  have h3 := key ek (l1 _ (Or.inr (Or.inr rfl)))
  have e1 : v ⬝ᵥ ei = v 0 := by simp [dotProduct, Fin.sum_univ_three, ei]
  have e2 : v ⬝ᵥ ej = v 1 := by simp [dotProduct, Fin.sum_univ_three, ej]
  have e3 : v ⬝ᵥ ek = v 2 := by simp [dotProduct, Fin.sum_univ_three, ek]
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  refine ⟨h1, h2, h3, ?_⟩
  have hl := len_pos hv
  rw [h1, h2, h3, div_pow, div_pow, div_pow, ← add_div, ← add_div, div_eq_one_iff_eq (by positivity),
    len_sq, dot_expand]
  ring

/-- OpenStax Calculus 3:§2.1 text (components from magnitude and angle), p. 107 (CA-429): a plane
vector `(x, y)` of magnitude `m = √(x²+y²)` and angle `θ` with the positive x-axis (the argument of
`x + y i`) has components `m cos θ` and `m sin θ`. -/
@[kb "openstaxcalculus2016" "3:§2.1 text (components from magnitude and angle), p. 107"]
theorem plane_vector_components (x y : ℝ) :
    x = Real.sqrt (x ^ 2 + y ^ 2) * Real.cos (Complex.arg ⟨x, y⟩) ∧
    y = Real.sqrt (x ^ 2 + y ^ 2) * Real.sin (Complex.arg ⟨x, y⟩) := by
  have hn : ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; ring
  have h1 := Complex.norm_mul_cos_arg (⟨x, y⟩ : ℂ)
  have h2 := Complex.norm_mul_sin_arg (⟨x, y⟩ : ℂ)
  rw [hn] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- OpenStax Calculus 3:§2.1 text (components from magnitude and angle), p. 107 (CA-429), converse:
the vector `(m cos θ, m sin θ)` has magnitude `|m|`. -/
@[kb "openstaxcalculus2016" "3:Example 2.6, p. 108"]
theorem sqrt_polar_components (m θ : ℝ) :
    Real.sqrt ((m * Real.cos θ) ^ 2 + (m * Real.sin θ) ^ 2) = |m| := by
  have : (m * Real.cos θ) ^ 2 + (m * Real.sin θ) ^ 2 = m ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  rw [this, Real.sqrt_sq_eq_abs]

/-- The vector projection of `v` onto `u`. -/
noncomputable def vecProj (u v : Fin 3 → ℝ) : Fin 3 → ℝ := ((u ⬝ᵥ v) / (u ⬝ᵥ u)) • u

/-- The scalar projection (signed component) of `v` onto `u`: `(u · v) / ‖u‖`. -/
noncomputable def scalarProj (u v : Fin 3 → ℝ) : ℝ := (u ⬝ᵥ v) / len u

/-- OpenStax Calculus 3:§2.3 Definition (scalar projection, Eq 2.7), p. 148 (CA-443): the scalar
projection is the signed length of the vector projection along the unit vector `u/‖u‖`, its
absolute value is the length of the vector projection, and it equals `‖v‖ cos θ`. -/
@[kb "openstaxcalculus2016" "3:§2.3 Definition (scalar projection, Eq 2.7), p. 148"]
theorem scalarProj_spec {u : Fin 3 → ℝ} (hu : u ≠ 0) (v : Fin 3 → ℝ) :
    vecProj u v = scalarProj u v • ((len u)⁻¹ • u) ∧ |scalarProj u v| = len (vecProj u v) ∧
    scalarProj u v = len v * Real.cos (vangle u v) ∧ (v - vecProj u v) ⬝ᵥ u = 0 := by
  have hl := len_pos hu
  have huu : u ⬝ᵥ u = len u ^ 2 := (len_sq u).symm
  have hne : u ⬝ᵥ u ≠ 0 := by rw [huu]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold vecProj scalarProj
    rw [smul_smul, huu]; congr 1; field_simp
  · unfold vecProj scalarProj
    rw [len_smul, huu, abs_div, abs_of_pos hl, abs_div, abs_of_pos (by positivity : 0 < len u ^ 2)]
    field_simp
  · unfold scalarProj
    have := work_eq u v
    rw [this]; field_simp
  · unfold vecProj
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    field_simp
    rw [dotProduct_comm]; ring

end UndergradKB.Calculus
