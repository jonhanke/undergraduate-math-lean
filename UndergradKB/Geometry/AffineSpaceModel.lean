import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import UndergradKB.Common.Attr
import UndergradKB.Geometry.ProjectiveDuality
import UndergradKB.Geometry.Inversion

/-! # Leftover results of chapter 14 (Petrunin): affine transformations

Section 14A (Exercise 14.3, the definition on p. 114), Section 14C (Exercise 14.10) and Exercise 14.15.

* An *affine transformation* is a bijection of the plane sending lines to lines (`IsAffineTransformation`);
  every `AffineEquiv` is one (`affineEquiv_image_line`, `isAffineTransformation_of_affineEquiv`).
* `affineMat` is the affine equivalence `(x, y) ↦ (a x + b y + r, c x + d y + s)` of `ℝ × ℝ` with
  `a d - b c ≠ 0`; shear, rescaling and the axis scalings are special cases (Exercise 14.3).
* Affine equivalences preserve vector equalities and parallelograms (Exercise 14.10).
* An affine equivalence mapping a circle into itself is a motion fixing the centre (Exercise 14.15).
-/

namespace UndergradKB.Geometry

open AffineSubspace Affine

section General

variable {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]

/-- A map sends lines to lines: the image of every line is a line (Petrunin, definition on p. 114). -/
def SendsLinesToLines (f : P₁ → P₂) : Prop :=
  ∀ p q : P₁, p ≠ q → ∃ p' q' : P₂, p' ≠ q' ∧ f '' (line[ℝ, p, q] : Set P₁) = (line[ℝ, p', q'] : Set P₂)

/-- An *affine transformation* in the sense of the book (Definition, p. 114): a bijection that maps lines to
lines. -/
def IsAffineTransformation (f : P₁ → P₂) : Prop := Function.Bijective f ∧ SendsLinesToLines f

/-- An affine equivalence maps the line through `p`, `q` onto the line through `f p`, `f q`. -/
theorem affineEquiv_image_line (f : P₁ ≃ᵃ[ℝ] P₂) (p q : P₁) :
    f '' (line[ℝ, p, q] : Set P₁) = (line[ℝ, f p, f q] : Set P₂) := by
  have h := AffineSubspace.map_span (f : P₁ →ᵃ[ℝ] P₂) ({p, q} : Set P₁)
  rw [Set.image_pair] at h
  have h2 := congrArg ((↑) : AffineSubspace ℝ P₂ → Set P₂) h
  rw [AffineSubspace.coe_map] at h2
  exact h2

theorem affineEquiv_linear_vsub (f : P₁ ≃ᵃ[ℝ] P₂) (p q : P₁) : f.linear (p -ᵥ q) = f p -ᵥ f q :=
  (f : P₁ →ᵃ[ℝ] P₂).linear_apply_vsub p q

/-- **Every affine equivalence is an affine transformation** in the book's sense (Petrunin, definition on
p. 114: a bijection sending lines to lines; Mathlib's `AffineEquiv` is defined structurally, this is the
bridge). -/
@[kb "petrunin2025" "Definition of affine transformation, p. 114"]
theorem isAffineTransformation_of_affineEquiv (f : P₁ ≃ᵃ[ℝ] P₂) : IsAffineTransformation f :=
  ⟨f.bijective, fun p q hpq =>
    ⟨f p, f q, fun h => hpq (f.injective h), affineEquiv_image_line f p q⟩⟩

/-- Affine equivalences preserve vector equalities in both directions (Petrunin, Exercise 14.10). -/
theorem affineEquiv_vsub_eq_iff (f : P₁ ≃ᵃ[ℝ] P₂) (X Y A B : P₁) :
    f Y -ᵥ f X = f B -ᵥ f A ↔ Y -ᵥ X = B -ᵥ A := by
  rw [← affineEquiv_linear_vsub f, ← affineEquiv_linear_vsub f]
  exact f.linear.injective.eq_iff

/-- The image of a collinear set under an affine map is collinear. -/
theorem collinear_image_of_affineMap (f : P₁ →ᵃ[ℝ] P₂) {s : Set P₁} (hs : Collinear ℝ s) :
    Collinear ℝ (f '' s) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hs ⊢
  obtain ⟨p₀, v, h⟩ := hs
  refine ⟨f p₀, f.linear v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := h p hp
  exact ⟨r, by simp [AffineMap.map_vadd]⟩

/-- Affine equivalences preserve collinearity of triples in both directions. -/
theorem affineEquiv_collinear_iff (f : P₁ ≃ᵃ[ℝ] P₂) (A B C : P₁) :
    Collinear ℝ ({f A, f B, f C} : Set P₂) ↔ Collinear ℝ ({A, B, C} : Set P₁) := by
  constructor
  · intro h
    have := collinear_image_of_affineMap (f.symm : P₂ →ᵃ[ℝ] P₁) h
    simpa [Set.image_insert_eq] using this
  · intro h
    have := collinear_image_of_affineMap (f : P₁ →ᵃ[ℝ] P₂) h
    simpa [Set.image_insert_eq] using this

/-- A (nondegenerate) parallelogram `ABCD`: `AB` and `DC` are equal vectors and `A`, `B`, `D` are not
collinear. -/
def IsVectorParallelogram (A B C D : P₁) : Prop :=
  B -ᵥ A = C -ᵥ D ∧ ¬ Collinear ℝ ({A, B, D} : Set P₁)

/-- **Affine transformations map parallelograms to parallelograms; vector equality is preserved in both
directions** (Petrunin, Exercise 14.10; proved here for affine equivalences). -/
@[kb "petrunin2025" "Exercise 14.10, p. 116"]
theorem affineEquiv_parallelogram (f : P₁ ≃ᵃ[ℝ] P₂) (A B C D : P₁) :
    IsVectorParallelogram (f A) (f B) (f C) (f D) ↔ IsVectorParallelogram A B C D := by
  unfold IsVectorParallelogram
  rw [affineEquiv_vsub_eq_iff f A B D C, affineEquiv_collinear_iff f A B D]

/-- Part two of Exercise 14.10: `XY = AB` as vectors iff `X'Y' = A'B'` (Petrunin, Exercise 14.10). -/
@[kb "petrunin2025" "Exercise 14.10, p. 116"]
theorem affineEquiv_vsub_eq_iff' (f : P₁ ≃ᵃ[ℝ] P₂) (X Y A B : P₁) :
    Y -ᵥ X = B -ᵥ A ↔ f Y -ᵥ f X = f B -ᵥ f A :=
  (affineEquiv_vsub_eq_iff f X Y A B).symm

end General

section Matrix

/-- The linear equivalence `(x, y) ↦ (a x + b y, c x + d y)` of `ℝ × ℝ` for `a d - b c ≠ 0`. -/
noncomputable def matLin (a b c d : ℝ) (h : a * d - b * c ≠ 0) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (a * p.1 + b * p.2, c * p.1 + d * p.2)
  invFun q := ((d * q.1 - b * q.2) / (a * d - b * c), (-c * q.1 + a * q.2) / (a * d - b * c))
  map_add' p q := by ext <;> simp <;> ring
  map_smul' t p := by ext <;> simp <;> ring
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show (d * (a * p.1 + b * p.2) - b * (c * p.1 + d * p.2)) / (a * d - b * c) = p.1
      rw [div_eq_iff h]; ring
    · show (-c * (a * p.1 + b * p.2) + a * (c * p.1 + d * p.2)) / (a * d - b * c) = p.2
      rw [div_eq_iff h]; ring
  right_inv q := by
    refine Prod.ext ?_ ?_
    · show a * ((d * q.1 - b * q.2) / (a * d - b * c)) + b * ((-c * q.1 + a * q.2) / (a * d - b * c)) = q.1
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]; ring
    · show c * ((d * q.1 - b * q.2) / (a * d - b * c)) + d * ((-c * q.1 + a * q.2) / (a * d - b * c)) = q.2
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff h]; ring

/-- The affine equivalence `(x, y) ↦ (a x + b y + r, c x + d y + s)` of `ℝ × ℝ` (Petrunin, Exercise 14.3(d)). -/
noncomputable def affineMat (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) :=
  (matLin a b c d h).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (r, s))

theorem affineMat_apply (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) (p : ℝ × ℝ) :
    affineMat a b c d r s h p = (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s) := by
  ext <;> simp [affineMat, matLin, add_comm]

/-- **Maps `(x, y) ↦ (a x + b y + r, c x + d y + s)` with invertible matrix are affine transformations**
(Petrunin, Exercise 14.3(d)); they are affine equivalences and send the line through `p`, `q` onto the line
through the images. -/
@[kb "petrunin2025" "Exercise 14.3(d), p. 115"]
theorem affine_transformation_matrix (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) :
    IsAffineTransformation (fun p : ℝ × ℝ => (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s)) ∧
      (∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ), ⇑f = fun p : ℝ × ℝ => (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s)) ∧
      ∀ p q : ℝ × ℝ, (fun p : ℝ × ℝ => (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s)) ''
          (line[ℝ, p, q] : Set (ℝ × ℝ)) =
        (line[ℝ, (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s),
          (a * q.1 + b * q.2 + r, c * q.1 + d * q.2 + s)] : Set (ℝ × ℝ)) := by
  have hf : ⇑(affineMat a b c d r s h) =
      fun p : ℝ × ℝ => (a * p.1 + b * p.2 + r, c * p.1 + d * p.2 + s) :=
    funext (affineMat_apply a b c d r s h)
  refine ⟨hf ▸ isAffineTransformation_of_affineEquiv (affineMat a b c d r s h), ⟨_, hf⟩, fun p q => ?_⟩
  have := affineEquiv_image_line (affineMat a b c d r s h) p q
  rw [hf] at this
  exact this

/-- **Shear** `(x, y) ↦ (x + k y, y)` is an affine transformation (Petrunin, Exercise 14.3(a)). -/
@[kb "petrunin2025" "Exercise 14.3(a), p. 114"]
theorem shear_isAffineTransformation (k : ℝ) :
    IsAffineTransformation (fun p : ℝ × ℝ => (p.1 + k * p.2, p.2)) ∧
      ∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ), ⇑f = fun p : ℝ × ℝ => (p.1 + k * p.2, p.2) := by
  have := affine_transformation_matrix 1 k 0 1 0 0 (by norm_num)
  have e : (fun p : ℝ × ℝ => (p.1 + k * p.2, p.2)) = fun p : ℝ × ℝ => (1 * p.1 + k * p.2 + 0, 0 * p.1 + 1 * p.2 + 0) := by
    funext p; simp
  rw [e]; exact ⟨this.1, this.2.1⟩

/-- **Rescaling** `(x, y) ↦ (a x, a y)`, `a ≠ 0`, is an affine transformation (Petrunin, Exercise 14.3(b)). -/
@[kb "petrunin2025" "Exercise 14.3(b), p. 114"]
theorem rescaling_isAffineTransformation {a : ℝ} (ha : a ≠ 0) :
    IsAffineTransformation (fun p : ℝ × ℝ => (a * p.1, a * p.2)) ∧
      ∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ), ⇑f = fun p : ℝ × ℝ => (a * p.1, a * p.2) := by
  have := affine_transformation_matrix a 0 0 a 0 0 (by simpa using ha)
  have e : (fun p : ℝ × ℝ => (a * p.1, a * p.2)) = fun p : ℝ × ℝ => (a * p.1 + 0 * p.2 + 0, 0 * p.1 + a * p.2 + 0) := by
    funext p; simp
  rw [e]; exact ⟨this.1, this.2.1⟩

/-- **x-scaling** `(x, y) ↦ (a x, y)`, `a ≠ 0`, is an affine transformation (Petrunin, Exercise 14.3(c)). -/
@[kb "petrunin2025" "Exercise 14.3(c), p. 114"]
theorem xScaling_isAffineTransformation {a : ℝ} (ha : a ≠ 0) :
    IsAffineTransformation (fun p : ℝ × ℝ => (a * p.1, p.2)) ∧
      ∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ), ⇑f = fun p : ℝ × ℝ => (a * p.1, p.2) := by
  have := affine_transformation_matrix a 0 0 1 0 0 (by simpa using ha)
  have e : (fun p : ℝ × ℝ => (a * p.1, p.2)) = fun p : ℝ × ℝ => (a * p.1 + 0 * p.2 + 0, 0 * p.1 + 1 * p.2 + 0) := by
    funext p; simp
  rw [e]; exact ⟨this.1, this.2.1⟩

/-- **y-scaling** `(x, y) ↦ (x, a y)`, `a ≠ 0`, is an affine transformation (Petrunin, Exercise 14.3(c)). -/
@[kb "petrunin2025" "Exercise 14.3(c), p. 114"]
theorem yScaling_isAffineTransformation {a : ℝ} (ha : a ≠ 0) :
    IsAffineTransformation (fun p : ℝ × ℝ => (p.1, a * p.2)) ∧
      ∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ), ⇑f = fun p : ℝ × ℝ => (p.1, a * p.2) := by
  have := affine_transformation_matrix 1 0 0 a 0 0 (by simpa using ha)
  have e : (fun p : ℝ × ℝ => (p.1, a * p.2)) = fun p : ℝ × ℝ => (1 * p.1 + 0 * p.2 + 0, 0 * p.1 + a * p.2 + 0) := by
    funext p; simp
  rw [e]; exact ⟨this.1, this.2.1⟩

end Matrix

section Circle

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- **An affine transformation mapping a circle into itself is a motion fixing the centre** (Petrunin,
Exercise 14.15; in any dimension, for an affine equivalence `f` and a sphere of positive radius `r`
about `c`: if `f` maps the sphere into itself then `f c = c` and `f` preserves distances). -/
@[kb "petrunin2025" "Exercise 14.15, p. 117"]
theorem affineEquiv_sphere_isometry (f : P ≃ᵃ[ℝ] P) {c : P} {r : ℝ} (hr : 0 < r)
    (h : ∀ x : P, dist x c = r → dist (f x) c = r) :
    f c = c ∧ ∀ x y : P, dist (f x) (f y) = dist x y := by
  set L := f.linear with hL
  set u : V := f c -ᵥ c with hu
  have hscale : ∀ v : V, v ≠ 0 → ‖(r / ‖v‖) • v‖ = r := by
    intro v hv
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have key : ∀ v : V, ‖v‖ = r → ‖L v + u‖ = r := by
    intro v hv
    have h1 := h (v +ᵥ c) (by rw [dist_eq_norm_vsub V, vadd_vsub, hv])
    rw [dist_eq_norm_vsub V, f.map_vadd, vadd_vsub_assoc] at h1
    exact h1
  have h0 : ∀ v : V, ‖v‖ = r → inner ℝ (L v) u = 0 := by
    intro v hv
    have a1 := key v hv
    have a2 := key (-v) (by rw [norm_neg, hv])
    rw [map_neg, neg_add_eq_sub] at a2
    have s1 : ‖L v + u‖ ^ 2 = r ^ 2 := by rw [a1]
    have s2 : ‖u - L v‖ ^ 2 = r ^ 2 := by rw [a2]
    rw [norm_add_sq_real] at s1
    rw [norm_sub_sq_real, real_inner_comm] at s2
    linarith
  have orth : ∀ v : V, inner ℝ (L v) u = 0 := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have := h0 _ (hscale v hv)
      rw [map_smul, real_inner_smul_left] at this
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
  have hu0 : u = 0 := by
    have := orth (f.linear.symm u)
    rw [LinearEquiv.apply_symm_apply] at this
    simpa using this
  have hfc : f c = c := by
    have : f c -ᵥ c = 0 := hu0
    exact vsub_eq_zero_iff_eq.mp this
  refine ⟨hfc, fun x y => ?_⟩
  have hnorm : ∀ v : V, ‖L v‖ = ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have := key _ (hscale v hv)
      rw [map_smul, hu0, add_zero, norm_smul, Real.norm_eq_abs] at this
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [abs_of_pos (by positivity)] at this
      field_simp at this
      linarith
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← affineEquiv_linear_vsub f _ _, hnorm]

end Circle


/-! ## Chapter 16: great circles, central projection, inversion in space -/

section Sphere

open scoped RealInnerProductSpace

/-- The great circle in the plane `ℓ` (a plane thru the origin) on the unit sphere of `ℝ³`. -/
def greatCircle (ℓ : ProjLine) : Set Space3 := {x | ‖x‖ = 1 ∧ x ∈ ℓ.1}

theorem linearIndependent_pair_of_unit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {A B : V}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hne : A ≠ B) (hanti : A ≠ -B) : LinearIndependent ℝ ![A, B] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : s = 0 := by
    by_contra hs
    have hA' : A = (-(s⁻¹ * t)) • B := by
      have : s • A = -(t • B) := eq_neg_of_add_eq_zero_left h
      have h2 : A = s⁻¹ • (s • A) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [h2, this, smul_neg, smul_smul, neg_smul]
    have hn : |(-(s⁻¹ * t))| = 1 := by
      have := congrArg norm hA'
      rw [norm_smul, hA, hB, mul_one, Real.norm_eq_abs] at this
      exact this.symm
    rcases (abs_eq (zero_le_one' ℝ)).mp hn with h1 | h1
    · exact hne (by rw [hA', h1, one_smul])
    · exact hanti (by rw [hA', h1, neg_smul, one_smul])
  subst hs
  rw [zero_smul, zero_add] at h
  have ht : t = 0 := by
    by_contra ht
    have := (smul_eq_zero.mp h).resolve_left ht
    rw [this, norm_zero] at hB
    exact zero_ne_one hB
  exact ⟨rfl, ht⟩

/-- **Two distinct non-antipodal points of the unit sphere lie on a unique great circle** (Petrunin, p. 132):
the plane thru `O`, `A`, `B` is the unique plane thru the origin containing `A` and `B`, so there is exactly
one plane `ℓ` whose great circle `greatCircle ℓ` contains `A` and `B`. -/
@[kb "petrunin2025" "Definition of spherical distance, p. 132"]
theorem existsUnique_greatCircle {A B : Space3} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hne : A ≠ B)
    (hanti : A ≠ -B) : ∃! ℓ : ProjLine, A ∈ greatCircle ℓ ∧ B ∈ greatCircle ℓ := by
  have hli := linearIndependent_pair_of_unit hA hB hne hanti
  have hfin : Module.finrank ℝ (Submodule.span ℝ {A, B}) = 2 := by
    have := finrank_span_eq_card hli
    have hr : Set.range ![A, B] = {A, B} := by
      ext x; simp [or_comm]
    rw [hr] at this
    simpa using this
  have hmem : ∀ ℓ : Submodule ℝ Space3, ({A, B} : Set Space3) ⊆ ℓ ↔ Submodule.span ℝ {A, B} ≤ ℓ :=
    fun ℓ => (Submodule.span_le).symm
  refine ⟨⟨Submodule.span ℝ {A, B}, hfin⟩, ⟨⟨hA, Submodule.subset_span (by simp)⟩,
    ⟨hB, Submodule.subset_span (by simp)⟩⟩, ?_⟩
  rintro ℓ ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  apply Subtype.ext
  have hle : Submodule.span ℝ {A, B} ≤ ℓ.1 := by
    rw [← hmem]
    intro x hx
    rcases hx with rfl | hx
    · exact h1
    · rw [Set.mem_singleton_iff.mp hx]; exact h2
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, ℓ.2])).symm

/-- The central projection `P ↦ P / P₃`: a point `P` with `P₃ > 0` goes to the point where the half-line
`[OP)` meets the plane `z = 1` (Petrunin, Section 16C). -/
noncomputable def centralProj (P : Space3) : Space3 := (P 2)⁻¹ • P

/-- The northern half-sphere `Σ⁺` (unit vectors with `z > 0`). -/
def northHalfSphere : Set Space3 := {P | ‖P‖ = 1 ∧ 0 < P 2}

/-- The plane `Π⁺ : z = 1`. -/
def planeZOne : Set Space3 := {Q | Q 2 = 1}

/-- **The central projection is a bijection of the northern half-sphere onto the plane `z = 1`** (Petrunin,
Section 16C, p. 133). -/
@[kb "petrunin2025" "Central projection, p. 133"]
theorem centralProj_bijOn : Set.BijOn centralProj northHalfSphere planeZOne := by
  refine ⟨?_, ?_, ?_⟩
  · rintro P ⟨-, hP⟩
    simp only [planeZOne, Set.mem_ofPred_eq, centralProj, PiLp.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hP.ne'
  · rintro P ⟨hP, hP2⟩ P' ⟨hP', hP2'⟩ h
    have h' : (P 2)⁻¹ • P = (P' 2)⁻¹ • P' := h
    have e : P = (P 2 * (P' 2)⁻¹) • P' := by
      have := congrArg (fun x => P 2 • x) h'
      simp only [smul_smul, mul_inv_cancel₀ hP2.ne', one_smul] at this
      exact this
    have hk : 0 < P 2 * (P' 2)⁻¹ := by positivity
    have hn := congrArg norm e
    rw [norm_smul, hP, hP', mul_one, Real.norm_eq_abs, abs_of_pos hk] at hn
    rw [e, ← hn, one_smul]
  · intro Q hQ
    have hQ1 : Q 2 = 1 := hQ
    have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ1
    have hn : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
    refine ⟨‖Q‖⁻¹ • Q, ⟨?_, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · simp only [PiLp.smul_apply, smul_eq_mul, hQ1, mul_one]; positivity
    · simp only [centralProj, PiLp.smul_apply, smul_eq_mul, hQ1, mul_one, smul_smul, inv_inv]
      rw [mul_inv_cancel₀ hn.ne', one_smul]

/-- The great circle on the unit sphere with normal vector `n`. -/
def greatCircleOf (n : Space3) : Set Space3 := {x | ‖x‖ = 1 ∧ ⟪x, n⟫ = 0}

theorem inner_space3 (x n : Space3) : ⟪x, n⟫ = n 0 * x 0 + n 1 * x 1 + n 2 * x 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]

theorem planeZOne_inter_eq_line {n : Space3} (hn : n 0 ≠ 0 ∨ n 1 ≠ 0) :
    ∃ p q : Space3, p ≠ q ∧
      {Q : Space3 | Q 2 = 1 ∧ ⟪Q, n⟫ = 0} = (line[ℝ, p, q] : Set Space3) := by
  have hN : n 0 ^ 2 + n 1 ^ 2 ≠ 0 := by
    rcases hn with h | h <;> positivity
  set N := n 0 ^ 2 + n 1 ^ 2 with hNdef
  let p : Space3 := !₂[-n 2 * n 0 / N, -n 2 * n 1 / N, 1]
  let q : Space3 := !₂[-n 2 * n 0 / N - n 1, -n 2 * n 1 / N + n 0, 1]
  refine ⟨p, q, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun x : Space3 => x 0) h
    have h1 := congrArg (fun x : Space3 => x 1) h
    simp [p, q] at h0 h1
    rcases hn with h | h
    · exact h (by linarith)
    · exact h (by linarith)
  · ext Q
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq]
    constructor
    · rintro ⟨hQ2, hQ⟩
      rw [inner_space3, hQ2] at hQ
      refine ⟨(-n 1 * (Q 0 - (-n 2 * n 0 / N)) + n 0 * (Q 1 - (-n 2 * n 1 / N))) / N, ?_⟩
      ext i
      fin_cases i
      · simp [p, q, AffineMap.lineMap_apply]
        field_simp
        linear_combination (-N * n 0) * hQ - (N * Q 0) * hNdef
      · simp [p, q, AffineMap.lineMap_apply]
        field_simp
        linear_combination (-N * n 1) * hQ - (N * Q 1) * hNdef
      · simp [p, q, AffineMap.lineMap_apply, hQ2]
    · rintro ⟨r, rfl⟩
      refine ⟨by simp [p, q, AffineMap.lineMap_apply], ?_⟩
      rw [inner_space3]
      simp [p, q, AffineMap.lineMap_apply]
      field_simp
      linear_combination n 2 * hNdef

/-- A great circle meeting the northern half-sphere has `(n₀, n₁) ≠ 0` (the equator `z = 0` does not). -/
theorem exists_northHalf_greatCircle {n : Space3} (hn : n ≠ 0)
    (h : (northHalfSphere ∩ greatCircleOf n).Nonempty) : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
  obtain ⟨P, ⟨hP, hP2⟩, ⟨-, hPn⟩⟩ := h
  by_contra hcon
  push Not at hcon
  rw [inner_space3, hcon.1, hcon.2] at hPn
  have h2 : n 2 = 0 := by
    have : n 2 * P 2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hP2.ne'
  apply hn
  ext i
  fin_cases i
  · exact hcon.1
  · exact hcon.2
  · exact h2

theorem centralProj_image_greatCircle (n : Space3) :
    centralProj '' (northHalfSphere ∩ greatCircleOf n) = {Q : Space3 | Q 2 = 1 ∧ ⟪Q, n⟫ = 0} := by
  ext Q
  constructor
  · rintro ⟨P, ⟨hPn, ⟨-, hPn'⟩⟩, rfl⟩
    refine ⟨centralProj_bijOn.mapsTo hPn, ?_⟩
    change ⟪(P 2)⁻¹ • P, n⟫ = 0
    rw [real_inner_smul_left, hPn', mul_zero]
  · rintro ⟨hQ1, hQn⟩
    obtain ⟨P, hP, rfl⟩ := centralProj_bijOn.surjOn (show Q ∈ planeZOne from hQ1)
    refine ⟨P, ⟨hP, ?_, ?_⟩, rfl⟩
    · exact hP.1
    · change ⟪(P 2)⁻¹ • P, n⟫ = 0 at hQn
      rw [real_inner_smul_left] at hQn
      exact (mul_eq_zero.mp hQn).resolve_left (inv_ne_zero hP.2.ne')

/-- **The central projection sends the intersection of a great circle with `Σ⁺` to a line of `Π⁺`**
(Petrunin, Section 16C, p. 133). The great circle has the normal vector `n`; it meets `Σ⁺` exactly when
`(n₀, n₁) ≠ 0`, and then its image is the line `{z = 1} ∩ nᗮ` of the plane `z = 1`. -/
@[kb "petrunin2025" "Central projection, p. 133"]
theorem centralProj_greatCircle_line {n : Space3} (hn : n 0 ≠ 0 ∨ n 1 ≠ 0) :
    ∃ p q : Space3, p ≠ q ∧ p ∈ planeZOne ∧ q ∈ planeZOne ∧
      centralProj '' (northHalfSphere ∩ greatCircleOf n) = (line[ℝ, p, q] : Set Space3) := by
  obtain ⟨p, q, hpq, h⟩ := planeZOne_inter_eq_line hn
  refine ⟨p, q, hpq, ?_, ?_, by rw [centralProj_image_greatCircle, h]⟩
  · have : p ∈ (line[ℝ, p, q] : Set Space3) := left_mem_affineSpan_pair ℝ p q
    rw [← h] at this
    exact this.1
  · have : q ∈ (line[ℝ, p, q] : Set Space3) := right_mem_affineSpan_pair ℝ p q
    rw [← h] at this
    exact this.1

end Sphere

section InversionSpace

open scoped RealInnerProductSpace

/-- **Inversion across a sphere in space** (Petrunin, Theorem 16.5 (a), (c); the statements of
Inversion.lean in dimension 3). For the inversion with centre `c` and radius `R ≠ 0`: (a) a sphere not thru
`c` goes to a sphere not thru `c`; a plane not thru `c` goes to a sphere thru `c` minus `c`; a sphere thru `c`
minus `c` goes to a plane not thru `c`; a plane thru `c` goes to itself; (c) the cross-ratio of four points
different from `c` is preserved. Parts (b), (d), (e) are not formalized. -/
@[kb "petrunin2025" "Theorem 16.5 (a), (c), p. 135"]
theorem inversion_space (c : Space3) {R : ℝ} (hR : R ≠ 0) :
    (∀ (Q : Space3) (s : ℝ), 0 ≤ s → dist Q c ≠ s →
      EuclideanGeometry.inversion c R '' Metric.sphere Q s =
          Metric.sphere (invSphereCenter c R Q s) (invSphereRadius c R Q s) ∧
        c ∉ Metric.sphere (invSphereCenter c R Q s) (invSphereRadius c R Q s)) ∧
    (∀ (n : Space3), n ≠ 0 → ∀ t : ℝ, t ≠ 0 →
      EuclideanGeometry.inversion c R '' {x : Space3 | ⟪x -ᵥ c, n⟫ = t} =
          Metric.sphere (EuclideanGeometry.inversion c R (((2 * t / ‖n‖ ^ 2) • n) +ᵥ c))
            (R ^ 2 / dist (((2 * t / ‖n‖ ^ 2) • n) +ᵥ c) c) \ {c} ∧
        c ∉ {x : Space3 | ⟪x -ᵥ c, n⟫ = t}) ∧
    (∀ Q : Space3, Q ≠ c →
      EuclideanGeometry.inversion c R '' (Metric.sphere Q (dist Q c) \ {c}) =
          (AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R Q) : Set Space3) ∧
        c ∉ (AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R Q) : Set Space3)) ∧
    (∀ L : AffineSubspace ℝ Space3, c ∈ L → EuclideanGeometry.inversion c R '' (L : Set Space3) = L) ∧
    (∀ A B C D : Space3, A ≠ c → B ≠ c → C ≠ c → D ≠ c →
      crossRatio (EuclideanGeometry.inversion c R A) (EuclideanGeometry.inversion c R B)
        (EuclideanGeometry.inversion c R C) (EuclideanGeometry.inversion c R D) = crossRatio A B C D) :=
  ⟨fun _ _ hs hd => image_inversion_sphere hR hs hd,
    fun _ hn _ ht => image_inversion_hyperplane hR hn ht,
    fun _ hQ => image_inversion_sphere_through_centre hR hQ,
    fun _ hc => image_inversion_line_through_centre hR hc,
    fun _ _ _ _ hA hB hC hD => crossRatio_inversion hR hA hB hC hD⟩

end InversionSpace

section SpaceModel

open scoped RealInnerProductSpace

/-- The point `(x, y, 1)` of the plane `z = 1` in `ℝ³`. -/
def spacePoint (x y : ℝ) : Space3 := !₂[x, y, 1]

theorem spacePoint_ne_zero (x y : ℝ) : spacePoint x y ≠ 0 := by
  intro h
  have := congrArg (fun v : Space3 => v 2) h
  simp [spacePoint] at this

/-- Space model (Petrunin, Section 15C, p. 122): the point `(x, y)` of the affine plane `z = 1` corresponds
to the line thru the origin spanned by `(x, y, 1)`. -/
noncomputable def affineToProj (x y : ℝ) : ProjPoint :=
  ⟨Submodule.span ℝ {spacePoint x y}, finrank_span_singleton (spacePoint_ne_zero x y)⟩

theorem lineVec_ne_zero {a b c : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (!₂[a, b, c] : Space3) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun v : Space3 => v 0) h0
  have h2 := congrArg (fun v : Space3 => v 1) h0
  simp at h1 h2
  tauto

/-- The line `a x + b y + c = 0` (`(a, b) ≠ 0`) of the affine plane `z = 1` corresponds to the plane thru the
origin orthogonal to `(a, b, c)`. -/
noncomputable def affineLineToProj (a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : ProjLine :=
  ⟨(Submodule.span ℝ {(!₂[a, b, c] : Space3)})ᗮ, by
    rw [finrank_orthogonal_space3, finrank_span_singleton (lineVec_ne_zero h)]⟩

/-- **The space-model bijection preserves incidence** (Petrunin, Observation 15.1, p. 123): the point `(x, y)`
lies on the line `a x + b y + c = 0` iff the line `ℝ·(x, y, 1)` lies in the plane of the line. -/
@[kb "petrunin2025" "Observation 15.1, p. 123"]
theorem affineToProj_liesOn_iff (x y a b c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (affineToProj x y).LiesOn (affineLineToProj a b c h) ↔ a * x + b * y + c = 0 := by
  change Submodule.span ℝ {spacePoint x y} ≤ (Submodule.span ℝ {(!₂[a, b, c] : Space3)})ᗮ ↔ _
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_space3]
  simp only [spacePoint]
  constructor <;> intro h' <;> simp at h' ⊢ <;> linarith

/-- **The map from the plane `z = 1` to the lines thru the origin is injective** (Petrunin, construction
before Observation 15.1, p. 122). -/
@[kb "petrunin2025" "Construction of the space model, p. 122"]
theorem affineToProj_injective : Function.Injective (fun p : ℝ × ℝ => affineToProj p.1 p.2) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : Submodule.span ℝ {spacePoint x y} = Submodule.span ℝ {spacePoint x' y'} :=
    congrArg Subtype.val h
  have hmem : spacePoint x y ∈ Submodule.span ℝ {spacePoint x' y'} := by
    rw [← h']; exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 := congrArg (fun v : Space3 => v 0) ht
  have h1 := congrArg (fun v : Space3 => v 1) ht
  have h2 := congrArg (fun v : Space3 => v 2) ht
  simp [spacePoint] at h0 h1 h2
  subst h2
  simp at h0 h1
  simp [h0, h1]

/-- The ideal points of the space model: lines thru the origin lying in the plane `z = 0`. -/
def ProjPoint.IsIdeal (P : ProjPoint) : Prop := ∀ v ∈ P.1, v 2 = 0

/-- **The lines thru the origin that are not ideal are exactly the images of points of the plane `z = 1`**
(Petrunin, construction before Observation 15.1, p. 122): together with `affineToProj_injective`, the plane
`z = 1` is in bijection with the non-ideal points of the space model. -/
@[kb "petrunin2025" "Construction of the space model, p. 122"]
theorem range_affineToProj (P : ProjPoint) :
    P ∈ Set.range (fun p : ℝ × ℝ => affineToProj p.1 p.2) ↔ ¬ P.IsIdeal := by
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩ hid
    have := hid (spacePoint x y) (Submodule.mem_span_singleton_self _)
    simp [spacePoint] at this
  · intro hP
    unfold ProjPoint.IsIdeal at hP
    push Not at hP
    obtain ⟨v, hv, hv2⟩ := hP
    have hv0 : v ≠ 0 := by rintro rfl; exact hv2 rfl
    have hspan : Submodule.span ℝ {v} = P.1 := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_singleton_le_iff_mem]; exact hv
      · rw [finrank_span_singleton hv0, P.2]
    have hpt : spacePoint (v 0 / v 2) (v 1 / v 2) = (v 2)⁻¹ • v := by
      ext i
      fin_cases i <;> simp [spacePoint] <;> field_simp
    refine ⟨(v 0 / v 2, v 1 / v 2), Subtype.ext ?_⟩
    change Submodule.span ℝ {spacePoint (v 0 / v 2) (v 1 / v 2)} = P.1
    rw [hpt, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hv2)), hspan]

end SpaceModel

/-! ## Exercise 15.3: invariance of the cross-ratio of collinear points -/

section CrossRatio

variable {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]

open Classical in
/-- The signed ratio of two vectors: the real `c` with `u = c • v` (and `0` if there is none; for `v ≠ 0`
the value is characterised by `vratio_eq`). -/
noncomputable def vratio (u v : V₁) : ℝ := if h : ∃ c : ℝ, u = c • v then h.choose else 0

theorem vratio_eq {u v : V₁} (hv : v ≠ 0) {c : ℝ} (h : u = c • v) : vratio u v = c := by
  have hex : ∃ c : ℝ, u = c • v := ⟨c, h⟩
  unfold vratio
  simp only [hex, ↓reduceDIte]
  exact smul_left_injective ℝ hv (hex.choose_spec.symm.trans h)

/-- The signed cross-ratio `AB·CD / (BC·DA)` of four collinear points (Petrunin, Exercise 15.3, p. 125),
where each segment length is replaced by the signed ratio of the vectors (they are all parallel). -/
noncomputable def signedCrossRatio (A B C D : P₁) : ℝ :=
  vratio (B -ᵥ A) (C -ᵥ B) * vratio (D -ᵥ C) (A -ᵥ D)

theorem signedCrossRatio_of_smul {A B C D : P₁} {w : V₁} (hw : w ≠ 0) {a₁ a₂ a₃ a₄ : ℝ}
    (h₁ : B -ᵥ A = a₁ • w) (h₂ : C -ᵥ B = a₂ • w) (h₃ : D -ᵥ C = a₃ • w) (h₄ : A -ᵥ D = a₄ • w)
    (ha₂ : a₂ ≠ 0) (ha₄ : a₄ ≠ 0) : signedCrossRatio A B C D = a₁ / a₂ * (a₃ / a₄) := by
  unfold signedCrossRatio
  have e1 : vratio (B -ᵥ A) (C -ᵥ B) = a₁ / a₂ := by
    apply vratio_eq (by rw [h₂]; exact smul_ne_zero ha₂ hw)
    rw [h₁, h₂, smul_smul, div_mul_cancel₀ _ ha₂]
  have e2 : vratio (D -ᵥ C) (A -ᵥ D) = a₃ / a₄ := by
    apply vratio_eq (by rw [h₄]; exact smul_ne_zero ha₄ hw)
    rw [h₃, h₄, smul_smul, div_mul_cancel₀ _ ha₄]
  rw [e1, e2]

theorem signedCrossRatio_param {p₀ : P₁} {v : V₁} (hv : v ≠ 0) {tA tB tC tD : ℝ} (hBC : tC ≠ tB)
    (hDA : tA ≠ tD) :
    signedCrossRatio (tA • v +ᵥ p₀) (tB • v +ᵥ p₀) (tC • v +ᵥ p₀) (tD • v +ᵥ p₀) =
      (tB - tA) / (tC - tB) * ((tD - tC) / (tA - tD)) :=
  signedCrossRatio_of_smul hv (by rw [vadd_vsub_vadd_cancel_right, sub_smul])
    (by rw [vadd_vsub_vadd_cancel_right, sub_smul]) (by rw [vadd_vsub_vadd_cancel_right, sub_smul])
    (by rw [vadd_vsub_vadd_cancel_right, sub_smul]) (sub_ne_zero.mpr hBC) (sub_ne_zero.mpr hDA)

/-- **Affine maps preserve the cross-ratio of four collinear points** (Petrunin, Exercise 15.3(a)): for four
points on a line with `B ≠ C`, `D ≠ A`. -/
@[kb "petrunin2025" "Exercise 15.3(a), p. 125"]
theorem signedCrossRatio_affineEquiv (f : P₁ ≃ᵃ[ℝ] P₂) {A B C D : P₁}
    (hcol : Collinear ℝ ({A, B, C, D} : Set P₁)) (hBC : B ≠ C) (hDA : D ≠ A) :
    signedCrossRatio (f A) (f B) (f C) (f D) = signedCrossRatio A B C D := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨p₀, v, h⟩ := hcol
  obtain ⟨tA, rfl⟩ := h A (by simp)
  obtain ⟨tB, rfl⟩ := h B (by simp)
  obtain ⟨tC, rfl⟩ := h C (by simp)
  obtain ⟨tD, rfl⟩ := h D (by simp)
  have hv : v ≠ 0 := by
    rintro rfl
    exact hBC (by simp)
  have hBC' : tC ≠ tB := by
    rintro h'
    exact hBC (by rw [h'])
  have hDA' : tA ≠ tD := by
    rintro h'
    exact hDA (by rw [h'])
  have hfv : f.linear v ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hv
  simp only [AffineEquiv.map_vadd, map_smul]
  rw [signedCrossRatio_param hv hBC' hDA', signedCrossRatio_param hfv hBC' hDA']

theorem cr_alg {tA tB tC tD yA yB yC yD : ℝ} (hyA : yA ≠ 0) (hyB : yB ≠ 0) (hyC : yC ≠ 0)
    (hyD : yD ≠ 0) (e1 : tB - tC ≠ 0) (e2 : tD - tA ≠ 0) (e3 : tC - tB ≠ 0) (e4 : tA - tD ≠ 0) :
    (tA - tB) / (yA * yB) / ((tB - tC) / (yB * yC)) * ((tC - tD) / (yC * yD) / ((tD - tA) / (yD * yA))) =
      (tB - tA) / (tC - tB) * ((tD - tC) / (tA - tD)) := by
  field_simp
  ring

/-- The perspective projection `(x, y) ↦ (x / y, 1 / y)` (Petrunin, Exercise 15.3(b), p. 125). -/
noncomputable def perspective (p : ℝ × ℝ) : ℝ × ℝ := (p.1 / p.2, 1 / p.2)

/-- **The perspective projection `(x, y) ↦ (x/y, 1/y)` preserves the cross-ratio of four collinear points**
not on the line `y = 0` (Petrunin, Exercise 15.3(b), p. 125). -/
@[kb "petrunin2025" "Exercise 15.3(b), p. 125"]
theorem signedCrossRatio_perspective {A B C D : ℝ × ℝ} (hcol : Collinear ℝ ({A, B, C, D} : Set (ℝ × ℝ)))
    (hBC : B ≠ C) (hDA : D ≠ A) (hA : A.2 ≠ 0) (hB : B.2 ≠ 0) (hC : C.2 ≠ 0) (hD : D.2 ≠ 0) :
    signedCrossRatio (perspective A) (perspective B) (perspective C) (perspective D) =
      signedCrossRatio A B C D := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
  obtain ⟨p₀, v, h⟩ := hcol
  obtain ⟨tA, rfl⟩ := h A (by simp)
  obtain ⟨tB, rfl⟩ := h B (by simp)
  obtain ⟨tC, rfl⟩ := h C (by simp)
  obtain ⟨tD, rfl⟩ := h D (by simp)
  have hv : v ≠ 0 := by
    rintro rfl
    exact hBC (by simp)
  have hBC' : tC ≠ tB := by
    rintro h'
    exact hBC (by rw [h'])
  have hDA' : tA ≠ tD := by
    rintro h'
    exact hDA (by rw [h'])
  simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hA hB hC hD
  have hw : ((p₀.1 * v.2 - p₀.2 * v.1, v.2) : ℝ × ℝ) ≠ 0 := by
    intro h0
    have h1 : v.2 = 0 := congrArg Prod.snd h0
    have h2 : p₀.1 * v.2 - p₀.2 * v.1 = 0 := congrArg Prod.fst h0
    rw [h1] at hA
    have hp : p₀.2 ≠ 0 := by simpa using hA
    have : v.1 = 0 := by
      rw [h1, mul_zero, zero_sub, neg_eq_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hp
    exact hv (Prod.ext this h1)
  have key : ∀ s t : ℝ, s * v.2 + p₀.2 ≠ 0 → t * v.2 + p₀.2 ≠ 0 →
      perspective (t • v +ᵥ p₀) -ᵥ perspective (s • v +ᵥ p₀) =
        ((s - t) / ((s * v.2 + p₀.2) * (t * v.2 + p₀.2))) • ((p₀.1 * v.2 - p₀.2 * v.1, v.2) : ℝ × ℝ) := by
    intro s t hs ht
    refine Prod.ext ?_ ?_
    · simp only [perspective, vsub_eq_sub, vadd_eq_add, Prod.fst_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
      obtain ⟨ys, hys⟩ : ∃ y, y = s * v.2 + p₀.2 := ⟨_, rfl⟩
      obtain ⟨yt, hyt⟩ : ∃ y, y = t * v.2 + p₀.2 := ⟨_, rfl⟩
      rw [← hys] at hs ⊢
      rw [← hyt] at ht ⊢
      field_simp
      subst hys hyt
      ring
    · simp only [perspective, vsub_eq_sub, vadd_eq_add, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
      obtain ⟨ys, hys⟩ : ∃ y, y = s * v.2 + p₀.2 := ⟨_, rfl⟩
      obtain ⟨yt, hyt⟩ : ∃ y, y = t * v.2 + p₀.2 := ⟨_, rfl⟩
      rw [← hys] at hs ⊢
      rw [← hyt] at ht ⊢
      field_simp
      subst hys hyt
      ring
  have e1 : tB - tC ≠ 0 := sub_ne_zero.mpr hBC'.symm
  have e2 : tD - tA ≠ 0 := sub_ne_zero.mpr hDA'.symm
  have e3 : tC - tB ≠ 0 := sub_ne_zero.mpr hBC'
  have e4 : tA - tD ≠ 0 := sub_ne_zero.mpr hDA'
  rw [signedCrossRatio_of_smul hw (key tA tB hA hB) (key tB tC hB hC) (key tC tD hC hD)
      (key tD tA hD hA) (div_ne_zero e1 (mul_ne_zero hB hC)) (div_ne_zero e2 (mul_ne_zero hD hA)),
    signedCrossRatio_param hv hBC' hDA']
  exact cr_alg hA hB hC hD e1 e2 e3 e4

end CrossRatio

end UndergradKB.Geometry
