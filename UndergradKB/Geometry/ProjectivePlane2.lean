import Mathlib.Geometry.Euclidean.Sphere.PolePolar
import Mathlib.Geometry.Euclidean.Sphere.Tangent
import UndergradKB.Common.Attr
import UndergradKB.Geometry.ProjectivePlane

/-! # The projective plane in the space model, part 2 (Petrunin, chapter 15)

Continuation of `ProjectivePlane.lean`: projective transformations induced by `GL₃` (Sections 15D, 15E),
Theorem 15.2 (moving a line to infinity and the classification of the transformations), the invariance of
the cross-ratio (Exercise 15.3) and polars with respect to a circle (Section 15H: Claim 15.17 and
Exercise 15.19).
-/

namespace UndergradKB.Geometry

open Module
open scoped RealInnerProductSpace

/-! ## Projective transformations induced by `GL₃` (Sections 15D and 15E) -/

section Transformations

/-- The linear map of `ℝ³` with a given matrix. -/
noncomputable def matLin3 (M : Matrix (Fin 3) (Fin 3) ℝ) : Space3 →ₗ[ℝ] Space3 where
  toFun v := WithLp.toLp 2 (M.mulVec v.ofLp)
  map_add' x y := by ext i; simp [Matrix.mulVec_add]
  map_smul' c x := by ext i; simp [Matrix.mulVec_smul]

theorem matLin3_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Space3) (i : Fin 3) :
    matLin3 M v i = ∑ j, M i j * v j := by
  simp [matLin3, Matrix.mulVec, dotProduct]

/-- The linear automorphism of `ℝ³` with a given invertible matrix. -/
noncomputable def glOfMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0) : Space3 ≃ₗ[ℝ] Space3 :=
  LinearEquiv.ofLinear (matLin3 M) (matLin3 M⁻¹)
    (LinearMap.ext fun v => by
      ext i
      simp [matLin3, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 h)])
    (LinearMap.ext fun v => by
      ext i
      simp [matLin3, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 h)])

theorem glOfMatrix_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0) (v : Space3) (i : Fin 3) :
    glOfMatrix M h v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  change matLin3 M v i = _
  rw [matLin3_apply, Fin.sum_univ_three]

/-- The image of a point of the projective plane under a linear automorphism of `ℝ³`. -/
noncomputable def ProjPoint.map (g : Space3 ≃ₗ[ℝ] Space3) (P : ProjPoint) : ProjPoint :=
  ⟨P.1.map (g : Space3 →ₗ[ℝ] Space3), by rw [LinearEquiv.finrank_map_eq]; exact P.2⟩

/-- The image of a line of the projective plane under a linear automorphism of `ℝ³`. -/
noncomputable def ProjLine.map (g : Space3 ≃ₗ[ℝ] Space3) (ℓ : ProjLine) : ProjLine :=
  ⟨ℓ.1.map (g : Space3 →ₗ[ℝ] Space3), by rw [LinearEquiv.finrank_map_eq]; exact ℓ.2⟩

theorem ProjPoint.map_liesOn_iff (g : Space3 ≃ₗ[ℝ] Space3) (P : ProjPoint) (ℓ : ProjLine) :
    (P.map g).LiesOn (ℓ.map g) ↔ P.LiesOn ℓ :=
  Submodule.map_le_map_iff_of_injective g.injective _ _

theorem ProjPoint.map_symm_map (g : Space3 ≃ₗ[ℝ] Space3) (P : ProjPoint) : (P.map g).map g.symm = P := by
  apply Subtype.ext
  ext x
  simp [ProjPoint.map, Submodule.mem_map]

theorem ProjPoint.map_map_symm (g : Space3 ≃ₗ[ℝ] Space3) (P : ProjPoint) : (P.map g.symm).map g = P := by
  simpa using ProjPoint.map_symm_map g.symm P

theorem ProjPoint.map_mk' (g : Space3 ≃ₗ[ℝ] Space3) {v : Space3} (hv : v ≠ 0) :
    (ProjPoint.mk' v hv).map g = ProjPoint.mk' (g v) (g.map_ne_zero_iff.2 hv) := by
  apply Subtype.ext
  simp [ProjPoint.map, ProjPoint.mk', Submodule.map_span]

/-- A *projective transformation* (Petrunin, Section 15E, p. 124): a bijection of the projective plane
sending lines to lines. -/
@[kb "petrunin2025" "Projective transformation, p. 124"]
def IsProjectiveTransformation (f : ProjPoint → ProjPoint) : Prop :=
  Function.Bijective f ∧ ∀ ℓ : ProjLine, ∃ ℓ' : ProjLine, f '' {P | P.LiesOn ℓ} = {P | P.LiesOn ℓ'}

/-- **A linear automorphism of `ℝ³` induces a projective transformation** (Petrunin, Sections 15D and 15E,
pp. 123-124): the induced map on the lines thru the origin is a bijection sending lines (planes thru the
origin) to lines. -/
@[kb "petrunin2025" "Projective transformations from the space model, p. 123"]
theorem isProjectiveTransformation_map (g : Space3 ≃ₗ[ℝ] Space3) :
    IsProjectiveTransformation (ProjPoint.map g) := by
  refine ⟨⟨fun P Q h => ?_, fun Q => ⟨Q.map g.symm, ProjPoint.map_map_symm g Q⟩⟩, fun ℓ => ?_⟩
  · simpa [ProjPoint.map_symm_map] using congrArg (ProjPoint.map g.symm) h
  · refine ⟨ℓ.map g, Set.ext fun Q => ⟨?_, fun hQ => ?_⟩⟩
    · rintro ⟨P, hP, rfl⟩
      exact (ProjPoint.map_liesOn_iff g P ℓ).2 hP
    · refine ⟨Q.map g.symm, ?_, ProjPoint.map_map_symm g Q⟩
      show (Q.map g.symm).LiesOn ℓ
      rw [← ProjPoint.map_liesOn_iff g, ProjPoint.map_map_symm]
      exact hQ

theorem mem_lineOfNormal {n : Space3} (hn : n ≠ 0) (x : Space3) :
    x ∈ (lineOfNormal n hn).1 ↔ n 0 * x 0 + n 1 * x 1 + n 2 * x 2 = 0 := by
  change x ∈ (Submodule.span ℝ {n})ᗮ ↔ _
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm, inner_space3]

/-- A linear automorphism transforms the plane with normal `n` into the plane with normal `m` when
`m ∘ g = n`. -/
theorem ProjLine.map_lineOfNormal {g : Space3 ≃ₗ[ℝ] Space3} {n m : Space3} (hn : n ≠ 0) (hm : m ≠ 0)
    (h : ∀ y : Space3, m 0 * g y 0 + m 1 * g y 1 + m 2 * g y 2 = n 0 * y 0 + n 1 * y 1 + n 2 * y 2) :
    (lineOfNormal n hn).map g = lineOfNormal m hm := by
  apply Subtype.ext
  ext x
  change x ∈ Submodule.map (g : Space3 →ₗ[ℝ] Space3) (lineOfNormal n hn).1 ↔ _
  rw [Submodule.mem_map, mem_lineOfNormal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_lineOfNormal] at hy
    show m 0 * g y 0 + m 1 * g y 1 + m 2 * g y 2 = 0
    rw [h]; exact hy
  · intro hx
    refine ⟨g.symm x, ?_, by simp⟩
    rw [mem_lineOfNormal, ← h]
    simpa using hx

theorem ProjLine.map_trans (g h : Space3 ≃ₗ[ℝ] Space3) (ℓ : ProjLine) :
    ℓ.map (g.trans h) = (ℓ.map g).map h := by
  apply Subtype.ext
  change Submodule.map (g.trans h : Space3 →ₗ[ℝ] Space3) ℓ.1 =
    Submodule.map (h : Space3 →ₗ[ℝ] Space3) (Submodule.map (g : Space3 →ₗ[ℝ] Space3) ℓ.1)
  rw [← Submodule.map_comp]
  rfl

theorem e1_ne_zero : (!₂[0, 1, 0] : Space3) ≠ 0 := by
  intro h; have := congrArg (fun v : Space3 => v 1) h; simp at this

theorem e2_ne_zero : (!₂[0, 0, 1] : Space3) ≠ 0 := by
  intro h; have := congrArg (fun v : Space3 => v 2) h; simp at this

/-- The transformation `(x, y, z) ↦ (x, z, y)` of `ℝ³`; on the plane `z = 1` it induces the perspective
projection `β : (x, y) ↦ (x / y, 1 / y)` of Theorem 15.2. -/
noncomputable def swapYZ : Space3 ≃ₗ[ℝ] Space3 :=
  glOfMatrix !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by simp [Matrix.det_fin_three])

/-- The transformation `(x, y, z) ↦ (z, y, x)` of `ℝ³`; on the plane `z = 1` it induces the extended
perspective projection `(x, y) ↦ (1 / x, y / x)` of Section 15D. -/
noncomputable def swapXZ : Space3 ≃ₗ[ℝ] Space3 :=
  glOfMatrix !![0, 0, 1; 0, 1, 0; 1, 0, 0] (by simp [Matrix.det_fin_three])

theorem swapYZ_apply (v : Space3) : swapYZ v = !₂[v 0, v 2, v 1] := by
  ext i
  fin_cases i <;> simp [swapYZ, glOfMatrix_apply]

theorem swapXZ_apply (v : Space3) : swapXZ v = !₂[v 2, v 1, v 0] := by
  ext i
  fin_cases i <;> simp [swapXZ, glOfMatrix_apply]

/-- **The perspective projection of the book's example is induced by a linear automorphism of `ℝ³`**
(Petrunin, Section 15D, p. 124): the transformation `(x, y, z) ↦ (z, y, x)` acts on the points of the plane
`z = 1` with `x ≠ 0` as `(x, y) ↦ (1/x, y/x)`. -/
@[kb "petrunin2025" "Perspective projection in coordinates, p. 124"]
theorem map_swapXZ_affineToProj {x y : ℝ} (hx : x ≠ 0) :
    (affineToProj x y).map swapXZ = affineToProj (1 / x) (y / x) := by
  have e : affineToProj x y = ProjPoint.mk' (spacePoint x y) (spacePoint_ne_zero x y) := rfl
  rw [e, ProjPoint.map_mk']
  change _ = ProjPoint.mk' (spacePoint (1 / x) (y / x)) (spacePoint_ne_zero _ _)
  rw [ProjPoint.mk'_eq_iff]
  refine ⟨1 / x, ?_⟩
  ext i
  fin_cases i <;> simp [swapXZ_apply, spacePoint] <;> field_simp

/-- **The map `β : (x, y) ↦ (x / y, 1 / y)` is induced by a linear automorphism of `ℝ³`** (Petrunin,
Theorem 15.2, p. 124): `(x, y, z) ↦ (x, z, y)`; it is the projective transformation from the proof of the
theorem, defined by the perspective formula of the wave 1 file on the points off the line `y = 0`. -/
@[kb "petrunin2025" "Theorem 15.2 (the map β), p. 124"]
theorem map_swapYZ_affineToProj {x y : ℝ} (hy : y ≠ 0) :
    (affineToProj x y).map swapYZ = affineToProj (perspective (x, y)).1 (perspective (x, y)).2 := by
  have e : affineToProj x y = ProjPoint.mk' (spacePoint x y) (spacePoint_ne_zero x y) := rfl
  rw [e, ProjPoint.map_mk']
  change _ = ProjPoint.mk' (spacePoint (x / y) (1 / y)) (spacePoint_ne_zero _ _)
  rw [ProjPoint.mk'_eq_iff]
  refine ⟨1 / y, ?_⟩
  ext i
  fin_cases i <;> simp [swapYZ_apply, spacePoint] <;> field_simp

/-- A perspective projection with center the origin from a plane to the plane `⟪·, n'⟫ = 1`:
`P ↦ P / ⟪P, n'⟫` (defined when `⟪P, n'⟫ ≠ 0`; Petrunin, Section 15D, p. 123). -/
noncomputable def perspectiveProj (n' P : Space3) : Space3 := (⟪P, n'⟫)⁻¹ • P

/-- **A perspective projection is induced by the identity of `ℝ³`** (Petrunin, Section 15D, p. 123): the
image `P'` of `P` lies in the plane `⟪·, n'⟫ = 1` and spans the same line thru the origin as `P`. -/
@[kb "petrunin2025" "Perspective projection, p. 123"]
theorem perspectiveProj_spec {n' P : Space3} (hP : ⟪P, n'⟫ ≠ 0) :
    ⟪perspectiveProj n' P, n'⟫ = 1 ∧
      ∃ (hP0 : P ≠ 0) (hP' : perspectiveProj n' P ≠ 0),
        ProjPoint.mk' (perspectiveProj n' P) hP' = (ProjPoint.mk' P hP0).map (LinearEquiv.refl ℝ Space3) := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hP' : perspectiveProj n' P ≠ 0 := smul_ne_zero (inv_ne_zero hP) hP0
  refine ⟨?_, hP0, hP', ?_⟩
  · unfold perspectiveProj
    rw [real_inner_smul_left, inv_mul_cancel₀ hP]
  · rw [ProjPoint.map_mk', ProjPoint.mk'_eq_iff]
    exact ⟨⟪P, n'⟫, by unfold perspectiveProj; simp [smul_smul, mul_inv_cancel₀ hP]⟩

/-- The linear automorphism of `ℝ³` with matrix `[[a, b, r], [c, d, s], [0, 0, 1]]`: the extension of the
affine transformation `(x, y) ↦ (a x + b y + r, c x + d y + s)` to the space model. -/
noncomputable def affineGL (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) : Space3 ≃ₗ[ℝ] Space3 :=
  glOfMatrix !![a, b, r; c, d, s; 0, 0, 1] (by simpa [Matrix.det_fin_three] using h)

/-- **An affine transformation induces a projective transformation fixing the ideal line** (Petrunin,
Section 15E, p. 124): the linear automorphism of `ℝ³` with matrix `[[a, b, r], [c, d, s], [0, 0, 1]]` acts on
the points of the plane `z = 1` as `(x, y) ↦ (a x + b y + r, c x + d y + s)`. -/
@[kb "petrunin2025" "Affine transformations are projective, p. 124"]
theorem map_affineGL_affineToProj (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) (x y : ℝ) :
    (affineToProj x y).map (affineGL a b c d r s h) =
      affineToProj (a * x + b * y + r) (c * x + d * y + s) := by
  have e : affineToProj x y = ProjPoint.mk' (spacePoint x y) (spacePoint_ne_zero x y) := rfl
  rw [e, ProjPoint.map_mk']
  change _ = ProjPoint.mk' (spacePoint (a * x + b * y + r) (c * x + d * y + s)) (spacePoint_ne_zero _ _)
  rw [ProjPoint.mk'_eq_iff]
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [affineGL, glOfMatrix_apply, spacePoint]

/-- **Affine transformations fix the ideal line** (Petrunin, Section 15E, p. 124): the induced projective
transformation sends the ideal line (the plane `z = 0`) onto itself. -/
@[kb "petrunin2025" "Affine transformations fix the ideal line, p. 124"]
theorem map_affineGL_idealProjLine (a b c d r s : ℝ) (h : a * d - b * c ≠ 0) :
    idealProjLine.map (affineGL a b c d r s h) = idealProjLine := by
  unfold idealProjLine
  apply ProjLine.map_lineOfNormal
  intro y
  simp [affineGL, glOfMatrix_apply]

end Transformations

/-! ## Theorem 15.2: moving a line to infinity -/

section MovingToInfinity

/-- **Any line of the projective plane can be sent to the ideal line** by a projective transformation
induced by a linear automorphism of `ℝ³` (Petrunin, Theorem 15.2, first part, p. 124). -/
@[kb "petrunin2025" "Theorem 15.2, p. 124"]
theorem exists_map_eq_idealProjLine (ℓ : ProjLine) :
    ∃ g : Space3 ≃ₗ[ℝ] Space3, ℓ.map g = idealProjLine := by
  have hfin : finrank ℝ ℓ.1 = finrank ℝ idealProjLine.1 := by rw [ℓ.2, idealProjLine.2]
  let f : ℓ.1 ≃ₗ[ℝ] idealProjLine.1 := LinearEquiv.ofFinrankEq _ _ hfin
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, Subtype.ext ?_⟩
  ext x
  change x ∈ Submodule.map (g : Space3 →ₗ[ℝ] Space3) ℓ.1 ↔ x ∈ idealProjLine.1
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := hg ⟨y, hy⟩
    show g y ∈ idealProjLine.1
    rw [← this]
    exact (f ⟨y, hy⟩).2
  · intro hx
    refine ⟨(f.symm ⟨x, hx⟩ : Space3), (f.symm ⟨x, hx⟩).2, ?_⟩
    have := hg (f.symm ⟨x, hx⟩)
    show g _ = x
    rw [← this]
    simp

theorem lineOfNormal_eq_ideal {n : Space3} (hn : n ≠ 0) (h0 : n 0 = 0) (h1 : n 1 = 0) :
    lineOfNormal n hn = idealProjLine := by
  apply Subtype.ext
  ext x
  have h2 : n 2 ≠ 0 := by
    intro h2
    apply hn
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  change x ∈ (lineOfNormal n hn).1 ↔ x ∈ (lineOfNormal _ _).1
  rw [mem_lineOfNormal, mem_lineOfNormal]
  simp [h0, h1, h2]

theorem swapYZ_swapYZ (v : Space3) : swapYZ (swapYZ v) = v := by
  ext i
  fin_cases i <;> simp [swapYZ_apply]

/-- **Classification of projective transformations induced by `GL₃`** (Petrunin, Theorem 15.2, second part,
p. 124): a transformation `g` either fixes the ideal line (it is then *affine*), or, after a change of the
affine coordinates `k` (itself affine), it is the composition `g = k⁻¹ ∘ β ∘ α` of an affine transformation
`α` and the perspective projection `β : (x, y) ↦ (x / y, 1 / y)` (induced by `swapYZ`).

Faithfulness: this is the statement for the transformations induced by `GL₃`; that every line-preserving
bijection of the projective plane is induced by `GL₃` (the fundamental theorem of projective geometry) is not
proved. -/
@[kb "petrunin2025" "Theorem 15.2 (classification), p. 124"]
theorem projective_classification (g : Space3 ≃ₗ[ℝ] Space3) :
    idealProjLine.map g = idealProjLine ∨
      ∃ k α : Space3 ≃ₗ[ℝ] Space3, idealProjLine.map k = idealProjLine ∧ idealProjLine.map α = idealProjLine ∧
        ∀ y, g y = k.symm (swapYZ (α y)) := by
  by_cases h : idealProjLine.map g = idealProjLine
  · exact Or.inl h
  right
  obtain ⟨n, hn, hℓ⟩ := (idealProjLine.map g).exists_normal
  have hab : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (hℓ.trans (lineOfNormal_eq_ideal hn hc.1 hc.2))
  have hdet : (!![n 1, -n 0, 0; n 0, n 1, n 2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    have hpos : 0 < n 1 * n 1 + n 0 * n 0 := by
      rcases hab with h0 | h1
      · nlinarith [mul_self_pos.2 h0, mul_self_nonneg (n 1)]
      · nlinarith [mul_self_pos.2 h1, mul_self_nonneg (n 0)]
    have : (!![n 1, -n 0, 0; n 0, n 1, n 2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ).det =
        n 1 * n 1 + n 0 * n 0 := by
      simp [Matrix.det_fin_three]
    rw [this]
    exact hpos.ne'
  let k : Space3 ≃ₗ[ℝ] Space3 := glOfMatrix _ hdet
  have hk1 : (lineOfNormal n hn).map k = lineOfNormal !₂[0, 1, 0] e1_ne_zero := by
    apply ProjLine.map_lineOfNormal
    intro y
    simp [k, glOfMatrix_apply]
  have hk2 : idealProjLine.map k = idealProjLine := by
    unfold idealProjLine
    apply ProjLine.map_lineOfNormal
    intro y
    simp [k, glOfMatrix_apply]
  have hR : (lineOfNormal !₂[0, 1, 0] e1_ne_zero).map swapYZ = idealProjLine := by
    unfold idealProjLine
    apply ProjLine.map_lineOfNormal
    intro y
    simp [swapYZ_apply]
  refine ⟨k, (g.trans k).trans swapYZ, hk2, ?_, fun y => ?_⟩
  · rw [ProjLine.map_trans, ProjLine.map_trans, hℓ, hk1, hR]
  · simp [swapYZ_swapYZ]

theorem mem_idealProjLine (x : Space3) : x ∈ idealProjLine.1 ↔ x 2 = 0 := by
  unfold idealProjLine
  rw [mem_lineOfNormal]
  simp

/-- **A transformation fixing the ideal line is affine** (Petrunin, Section 15E, p. 124, converse of
`map_affineGL_affineToProj`): if `g` maps the plane `z = 0` onto itself, then on the points of the plane
`z = 1` it acts as an invertible affine map `(x, y) ↦ (a x + b y + r, c x + d y + s)`. -/
@[kb "petrunin2025" "Affine = fixes the ideal line, p. 124"]
theorem exists_affine_of_map_ideal {g : Space3 ≃ₗ[ℝ] Space3} (hg : idealProjLine.map g = idealProjLine) :
    ∃ (a b c d r s : ℝ), a * d - b * c ≠ 0 ∧ ∀ x y : ℝ,
      (affineToProj x y).map g = affineToProj (a * x + b * y + r) (c * x + d * y + s) := by
  have hz : ∀ v : Space3, v 2 = 0 ↔ g v 2 = 0 := by
    intro v
    have key : v ∈ idealProjLine.1 ↔ g v ∈ idealProjLine.1 := by
      constructor
      · intro hv
        have : g v ∈ (idealProjLine.map g).1 := Submodule.mem_map_of_mem hv
        rwa [hg] at this
      · intro hv
        rw [← hg] at hv
        obtain ⟨y, hy, hyv⟩ := hv
        have : y = v := g.injective hyv
        rwa [← this]
    rwa [mem_idealProjLine, mem_idealProjLine] at key
  have hexp : ∀ v : Space3, g v = v 0 • g !₂[1, 0, 0] + v 1 • g !₂[0, 1, 0] + v 2 • g !₂[0, 0, 1] := by
    intro v
    have : v = v 0 • (!₂[1, 0, 0] : Space3) + v 1 • (!₂[0, 1, 0] : Space3) + v 2 • (!₂[0, 0, 1] : Space3) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [this]
    simp [map_add, map_smul]
  have hu0 : g !₂[1, 0, 0] 2 = 0 := (hz _).1 (by simp)
  have hu1 : g !₂[0, 1, 0] 2 = 0 := (hz _).1 (by simp)
  have hc : g !₂[0, 0, 1] 2 ≠ 0 := fun h => by simpa using (hz _).2 h
  have hsurj : ∀ w : Space3, w 2 = 0 → ∃ v : Space3, v 2 = 0 ∧ g v = w := by
    intro w hw
    have hw' : w ∈ (idealProjLine.map g).1 := by
      rw [hg, mem_idealProjLine]; exact hw
    obtain ⟨v, hv, hvw⟩ := hw'
    exact ⟨v, (mem_idealProjLine v).1 hv, hvw⟩
  obtain ⟨v, hv2, hv⟩ := hsurj !₂[1, 0, 0] (by simp)
  obtain ⟨w, hw2, hw⟩ := hsurj !₂[0, 1, 0] (by simp)
  have hv' := hexp v
  have hw' := hexp w
  rw [hv] at hv'
  rw [hw] at hw'
  have a0 := congrArg (fun u : Space3 => u 0) hv'
  have a1 := congrArg (fun u : Space3 => u 1) hv'
  have b0 := congrArg (fun u : Space3 => u 0) hw'
  have b1 := congrArg (fun u : Space3 => u 1) hw'
  simp [hv2, hw2] at a0 a1 b0 b1
  set c0 := g !₂[0, 0, 1] 2 with hc0
  set u00 := g !₂[1, 0, 0] 0
  set u01 := g !₂[1, 0, 0] 1
  set u10 := g !₂[0, 1, 0] 0
  set u11 := g !₂[0, 1, 0] 1
  have hD : u00 * u11 - u10 * u01 ≠ 0 := by
    intro hD
    have key : (v 0 * u00 + v 1 * u10) * (w 0 * u01 + w 1 * u11) -
        (v 0 * u01 + v 1 * u11) * (w 0 * u00 + w 1 * u10) =
        (v 0 * w 1 - v 1 * w 0) * (u00 * u11 - u10 * u01) := by ring
    rw [hD, mul_zero] at key
    have e1 : v 0 * u00 + v 1 * u10 = 1 := by linarith
    have e2 : v 0 * u01 + v 1 * u11 = 0 := by linarith
    have e3 : w 0 * u00 + w 1 * u10 = 0 := by linarith
    have e4 : w 0 * u01 + w 1 * u11 = 1 := by linarith
    rw [e1, e2, e3, e4] at key
    norm_num at key
  refine ⟨u00 / c0, u10 / c0, u01 / c0, u11 / c0, g !₂[0, 0, 1] 0 / c0, g !₂[0, 0, 1] 1 / c0, ?_, ?_⟩
  · have : u00 / c0 * (u11 / c0) - u10 / c0 * (u01 / c0) = (u00 * u11 - u10 * u01) / c0 ^ 2 := by
      field_simp
    rw [this]
    exact div_ne_zero hD (pow_ne_zero 2 hc)
  · intro x y
    have e : affineToProj x y = ProjPoint.mk' (spacePoint x y) (spacePoint_ne_zero x y) := rfl
    rw [e, ProjPoint.map_mk']
    change _ = ProjPoint.mk' (spacePoint _ _) (spacePoint_ne_zero _ _)
    rw [ProjPoint.mk'_eq_iff]
    refine ⟨1 / c0, ?_⟩
    ext i
    rw [hexp]
    fin_cases i <;> simp [spacePoint, hu0, hu1] <;> field_simp <;> ring

end MovingToInfinity

/-! ## Exercise 15.3: the cross-ratio is invariant under projective transformations -/

section CrossRatioInvariance

theorem det3_eq_basis_det (u v w : Space3) :
    det3 u v w = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det ![u, v, w] := by
  rw [Module.Basis.det_apply, Matrix.det_fin_three]
  simp [Module.Basis.toMatrix_apply, det3]
  ring

theorem det3_map (g : Space3 ≃ₗ[ℝ] Space3) (u v w : Space3) :
    det3 (g u) (g v) (g w) = LinearMap.det (g : Space3 →ₗ[ℝ] Space3) * det3 u v w := by
  rw [det3_eq_basis_det, det3_eq_basis_det]
  have : ![g u, g v, g w] = (g : Space3 →ₗ[ℝ] Space3) ∘ ![u, v, w] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [this, Module.Basis.det_comp]

/-- The cross-ratio `[a, b][c, d] / ([b, c][d, a])` of four vectors of a plane thru the origin, where
`[p, q] = det (p, q, w)` for a vector `w` outside the plane; this is the space-model version of the ratio
`AB·CD / (BC·DA)` of Petrunin's Exercise 15.3. -/
noncomputable def crossRatioVec (w a b c d : Space3) : ℝ :=
  det3 a b w * det3 c d w / (det3 b c w * det3 d a w)

/-- The cross-ratio is unchanged by a linear automorphism of `ℝ³` (applied also to `w`). -/
theorem crossRatioVec_map (g : Space3 ≃ₗ[ℝ] Space3) (w a b c d : Space3) :
    crossRatioVec (g w) (g a) (g b) (g c) (g d) = crossRatioVec w a b c d := by
  have hg : LinearMap.det (g : Space3 →ₗ[ℝ] Space3) ≠ 0 := g.isUnit_det'.ne_zero
  unfold crossRatioVec
  rw [det3_map, det3_map, det3_map, det3_map]
  set δ := LinearMap.det (g : Space3 →ₗ[ℝ] Space3)
  have : δ * det3 a b w * (δ * det3 c d w) = (δ * δ) * (det3 a b w * det3 c d w) := by ring
  rw [this]
  have : δ * det3 b c w * (δ * det3 d a w) = (δ * δ) * (det3 b c w * det3 d a w) := by ring
  rw [this]
  exact mul_div_mul_left _ _ (mul_ne_zero hg hg)

theorem det3_smul_smul (s t : ℝ) (a b w : Space3) : det3 (s • a) (t • b) w = (s * t) * det3 a b w := by
  unfold det3
  simp
  ring

theorem crossRatioVec_smul {s t u v : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (w a b c d : Space3) :
    crossRatioVec w (s • a) (t • b) (u • c) (v • d) = crossRatioVec w a b c d := by
  unfold crossRatioVec
  rw [det3_smul_smul, det3_smul_smul, det3_smul_smul, det3_smul_smul]
  have h1 : s * t * det3 a b w * (u * v * det3 c d w) = (s * t * u * v) * (det3 a b w * det3 c d w) := by ring
  have h2 : t * u * det3 b c w * (v * s * det3 d a w) = (s * t * u * v) * (det3 b c w * det3 d a w) := by ring
  rw [h1, h2]
  exact mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hu) hv)

/-- The cross-ratio of four points of the projective plane, relative to a vector `w` (representatives of
the points are chosen; the value does not depend on the choice, see `ProjPoint.crossRatio_mk'`). -/
noncomputable def ProjPoint.crossRatio (w : Space3) (A B C D : ProjPoint) : ℝ :=
  crossRatioVec w A.exists_rep.choose B.exists_rep.choose C.exists_rep.choose D.exists_rep.choose

theorem ProjPoint.exists_scalar_rep (A : ProjPoint) {a : Space3} (ha : a ≠ 0) (hA : A = ProjPoint.mk' a ha) :
    ∃ t : ℝ, t ≠ 0 ∧ A.exists_rep.choose = t • a := by
  obtain ⟨t, ht⟩ := (ProjPoint.mk'_eq_iff ha A.exists_rep.choose_spec.choose).1
    (hA.symm.trans A.exists_rep.choose_spec.choose_spec)
  refine ⟨t, ?_, ht.symm⟩
  rintro rfl
  exact A.exists_rep.choose_spec.choose (by rw [← ht]; simp)

theorem ProjPoint.crossRatio_mk' (w : Space3) {a b c d : Space3} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    ProjPoint.crossRatio w (ProjPoint.mk' a ha) (ProjPoint.mk' b hb) (ProjPoint.mk' c hc)
      (ProjPoint.mk' d hd) = crossRatioVec w a b c d := by
  obtain ⟨s, hs, e1⟩ := ProjPoint.exists_scalar_rep _ ha rfl
  obtain ⟨t, ht, e2⟩ := ProjPoint.exists_scalar_rep _ hb rfl
  obtain ⟨u, hu, e3⟩ := ProjPoint.exists_scalar_rep _ hc rfl
  obtain ⟨v, hv, e4⟩ := ProjPoint.exists_scalar_rep _ hd rfl
  unfold ProjPoint.crossRatio
  rw [e1, e2, e3, e4]
  exact crossRatioVec_smul hs ht hu hv _ _ _ _ _

/-- **Projective transformations induced by `GL₃` preserve the cross-ratio** (Petrunin, Exercise 15.3(c),
p. 125): the cross-ratio `AB·CD / (BC·DA)` of four points of a line, computed in the space model, is
unchanged by a linear automorphism of `ℝ³` (the vector `w` outside the plane of the line is transformed
together with the points).  Part (c) of the exercise for the transformations induced by `GL₃`; the
independence of the value of the choice of `w` is `crossRatioVec_indep`. -/
@[kb "petrunin2025" "Exercise 15.3(c), p. 125"]
theorem ProjPoint.crossRatio_map (g : Space3 ≃ₗ[ℝ] Space3) (w : Space3) (A B C D : ProjPoint) :
    ProjPoint.crossRatio (g w) (A.map g) (B.map g) (C.map g) (D.map g) = ProjPoint.crossRatio w A B C D := by
  obtain ⟨a, ha, rfl⟩ := A.exists_rep
  obtain ⟨b, hb, rfl⟩ := B.exists_rep
  obtain ⟨c, hc, rfl⟩ := C.exists_rep
  obtain ⟨d, hd, rfl⟩ := D.exists_rep
  rw [ProjPoint.map_mk', ProjPoint.map_mk', ProjPoint.map_mk', ProjPoint.map_mk',
    ProjPoint.crossRatio_mk', ProjPoint.crossRatio_mk', crossRatioVec_map]

theorem det3_zero_of_orth {n u v w : Space3} (hn : n ≠ 0) (hu : n 0 * u 0 + n 1 * u 1 + n 2 * u 2 = 0)
    (hv : n 0 * v 0 + n 1 * v 1 + n 2 * v 2 = 0) (hw : n 0 * w 0 + n 1 * w 1 + n 2 * w 2 = 0) :
    det3 u v w = 0 := by
  have e0 : det3 u v w * n 0 = 0 := by
    unfold det3
    linear_combination (v 1 * w 2 - v 2 * w 1) * hu - (u 1 * w 2 - u 2 * w 1) * hv +
      (u 1 * v 2 - u 2 * v 1) * hw
  have e1 : det3 u v w * n 1 = 0 := by
    unfold det3
    linear_combination -(v 0 * w 2 - v 2 * w 0) * hu + (u 0 * w 2 - u 2 * w 0) * hv -
      (u 0 * v 2 - u 2 * v 0) * hw
  have e2 : det3 u v w * n 2 = 0 := by
    unfold det3
    linear_combination (v 0 * w 1 - v 1 * w 0) * hu - (u 0 * w 1 - u 1 * w 0) * hv +
      (u 0 * v 1 - u 1 * v 0) * hw
  by_contra hd
  apply hn
  ext i
  fin_cases i
  · simpa [hd] using e0
  · simpa [hd] using e1
  · simpa [hd] using e2

/-- The cross-ratio does not depend on the vector `w` outside the plane `n^⊥` of the four vectors. -/
theorem crossRatioVec_indep {n a b c d w w' : Space3} (hn : n ≠ 0)
    (ha : n 0 * a 0 + n 1 * a 1 + n 2 * a 2 = 0) (hb : n 0 * b 0 + n 1 * b 1 + n 2 * b 2 = 0)
    (hc : n 0 * c 0 + n 1 * c 1 + n 2 * c 2 = 0) (hd : n 0 * d 0 + n 1 * d 1 + n 2 * d 2 = 0)
    (hw : n 0 * w 0 + n 1 * w 1 + n 2 * w 2 ≠ 0) (hw' : n 0 * w' 0 + n 1 * w' 1 + n 2 * w' 2 ≠ 0) :
    crossRatioVec w' a b c d = crossRatioVec w a b c d := by
  set κ := n 0 * w 0 + n 1 * w 1 + n 2 * w 2 with hκ
  set κ' := n 0 * w' 0 + n 1 * w' 1 + n 2 * w' 2 with hκ'
  have key : ∀ p q : Space3, n 0 * p 0 + n 1 * p 1 + n 2 * p 2 = 0 →
      n 0 * q 0 + n 1 * q 1 + n 2 * q 2 = 0 → κ * det3 p q w' = κ' * det3 p q w := by
    intro p q hp hq
    have hu : n 0 * (κ • w' - κ' • w) 0 + n 1 * (κ • w' - κ' • w) 1 + n 2 * (κ • w' - κ' • w) 2 = 0 := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      rw [hκ, hκ']
      ring
    have := det3_zero_of_orth hn hp hq hu
    unfold det3 at this ⊢
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this
    linear_combination this
  unfold crossRatioVec
  have h1 := key a b ha hb
  have h2 := key c d hc hd
  have h3 := key b c hb hc
  have h4 := key d a hd ha
  have e : ∀ p q : Space3, n 0 * p 0 + n 1 * p 1 + n 2 * p 2 = 0 →
      n 0 * q 0 + n 1 * q 1 + n 2 * q 2 = 0 → det3 p q w' = (κ' / κ) * det3 p q w := by
    intro p q hp hq
    field_simp
    linear_combination key p q hp hq
  rw [e a b ha hb, e c d hc hd, e b c hb hc, e d a hd ha]
  have hk : κ' / κ ≠ 0 := div_ne_zero hw' hw
  have : κ' / κ * det3 a b w * (κ' / κ * det3 c d w) = (κ' / κ * (κ' / κ)) * (det3 a b w * det3 c d w) := by ring
  rw [this]
  have : κ' / κ * det3 b c w * (κ' / κ * det3 d a w) = (κ' / κ * (κ' / κ)) * (det3 b c w * det3 d a w) := by ring
  rw [this]
  exact mul_div_mul_left _ _ (mul_ne_zero hk hk)

/-- **The space-model cross-ratio of four collinear affine points is the signed cross-ratio** `AB·CD / (BC·DA)`
of the plane (Petrunin, Exercise 15.3, p. 125): for the points `tᵢ • v + p₀` of a line of the plane `z = 1`,
represented by `(point, 1)`, and any `w` outside the plane of the line (`κ ≠ 0`). -/
@[kb "petrunin2025" "Exercise 15.3 (affine form), p. 125"]
theorem crossRatioVec_affine {p₀ v : ℝ × ℝ} (hv : v ≠ 0) {tA tB tC tD : ℝ} (hBC : tC ≠ tB) (hDA : tA ≠ tD)
    (w : Space3) (hκ : det3 (spacePoint p₀.1 p₀.2) !₂[v.1, v.2, 0] w ≠ 0) :
    crossRatioVec w (spacePoint (tA • v +ᵥ p₀).1 (tA • v +ᵥ p₀).2) (spacePoint (tB • v +ᵥ p₀).1 (tB • v +ᵥ p₀).2)
      (spacePoint (tC • v +ᵥ p₀).1 (tC • v +ᵥ p₀).2) (spacePoint (tD • v +ᵥ p₀).1 (tD • v +ᵥ p₀).2) =
      signedCrossRatio (tA • v +ᵥ p₀) (tB • v +ᵥ p₀) (tC • v +ᵥ p₀) (tD • v +ᵥ p₀) := by
  rw [signedCrossRatio_param hv hBC hDA]
  set κ := det3 (spacePoint p₀.1 p₀.2) !₂[v.1, v.2, 0] w with hκdef
  have key : ∀ s t : ℝ, det3 (spacePoint (s • v +ᵥ p₀).1 (s • v +ᵥ p₀).2)
      (spacePoint (t • v +ᵥ p₀).1 (t • v +ᵥ p₀).2) w = (t - s) * κ := by
    intro s t
    rw [hκdef]
    unfold det3
    simp [spacePoint]
    ring
  unfold crossRatioVec
  rw [key, key, key, key]
  have h1 : (tB - tA) * κ * ((tD - tC) * κ) = (κ * κ) * ((tB - tA) * (tD - tC)) := by ring
  have h2 : (tC - tB) * κ * ((tA - tD) * κ) = (κ * κ) * ((tC - tB) * (tA - tD)) := by ring
  rw [h1, h2, mul_div_mul_left _ _ (mul_ne_zero hκ hκ), mul_div_mul_comm]

end CrossRatioInvariance

/-! ## Polar and pole with respect to a circle (Section 15H) -/

section Polar

/-- A symmetric bilinear form `β` on `ℝ³` defines a conic: the points `P` of the space model with
`β v v = 0` for `v` spanning `P`. -/
def OnConic (β : Space3 →ₗ[ℝ] Space3 →ₗ[ℝ] ℝ) (P : ProjPoint) : Prop := ∀ v ∈ P.1, β v v = 0

/-- The points `P`, `Q` are conjugate with respect to `β`: `β p q = 0` for the vectors of the two lines. -/
def PolarOrth (β : Space3 →ₗ[ℝ] Space3 →ₗ[ℝ] ℝ) (P Q : ProjPoint) : Prop := ∀ p ∈ P.1, ∀ q ∈ Q.1, β p q = 0

/-- **The diagonal point of an inscribed quadrangle lies on the polar** (the heart of Petrunin,
Claim 15.17, p. 129, for an arbitrary conic): let `X, X', Y, Y'` be distinct points of a conic, and let
`P` lie on the lines `XX'` and `YY'`.  Then `Z = XY ∩ X'Y'` is conjugate to `P`, i.e. lies on the polar of `P`. -/
theorem secant_on_polar (β : Space3 →ₗ[ℝ] Space3 →ₗ[ℝ] ℝ) (hsymm : ∀ u v, β u v = β v u)
    {X X' Y Y' P Z : ProjPoint} (hXY : X ≠ Y) (hXX' : X ≠ X') (hYY' : Y ≠ Y') (hX'Y' : X' ≠ Y')
    (hX : OnConic β X) (hX' : OnConic β X') (hY : OnConic β Y) (hY' : OnConic β Y')
    (hP1 : ProjCollinear X X' P) (hP2 : ProjCollinear Y Y' P)
    (hZ1 : ProjCollinear X Y Z) (hZ2 : ProjCollinear X' Y' Z)
    (hl : ¬ ∃ ℓ : ProjLine, X.LiesOn ℓ ∧ Y.LiesOn ℓ ∧ X'.LiesOn ℓ ∧ Y'.LiesOn ℓ) :
    PolarOrth β P Z := by
  obtain ⟨x, hx, rfl⟩ := X.exists_rep
  obtain ⟨x', hx', rfl⟩ := X'.exists_rep
  obtain ⟨y, hy, rfl⟩ := Y.exists_rep
  obtain ⟨y', hy', rfl⟩ := Y'.exists_rep
  obtain ⟨p, hp, rfl⟩ := P.exists_rep
  have hxx : β x x = 0 := hX x (Submodule.mem_span_singleton_self _)
  have hx'x' : β x' x' = 0 := hX' x' (Submodule.mem_span_singleton_self _)
  have hyy : β y y = 0 := hY y (Submodule.mem_span_singleton_self _)
  have hy'y' : β y' y' = 0 := hY' y' (Submodule.mem_span_singleton_self _)
  rw [projCollinear_iff_liesOn_join hXX'] at hP1
  obtain ⟨γ, δ, hp1⟩ := (mem_sup_mk' hx hx' hp).1 hP1
  rw [projCollinear_iff_liesOn_join hYY'] at hP2
  obtain ⟨γ', δ', hp2⟩ := (mem_sup_mk' hy hy' hp).1 hP2
  have hW : γ • x - γ' • y ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep_pair hXY (s := γ) (t := -γ') (by rw [neg_smul, ← sub_eq_add_neg]; exact h0)
    have h2' : γ' = 0 := neg_eq_zero.1 h2
    rw [h1] at hp1
    rw [h2'] at hp2
    simp only [zero_smul, zero_add] at hp1 hp2
    have hδ : δ ≠ 0 := by
      rintro rfl
      simp at hp1
      exact hp hp1.symm
    have hδ' : δ' ≠ 0 := by
      rintro rfl
      simp at hp2
      exact hp hp2.symm
    exact hX'Y' (mk'_eq_of_smul_eq hx' hy' hδ hδ' (hp1.trans hp2.symm))
  have hZeq := eq_mk'_of_two hW hXY hX'Y' hl ⟨γ, -γ', by rw [neg_smul, ← sub_eq_add_neg]⟩
    ⟨-δ, δ', by linear_combination (norm := module) hp2 - hp1⟩ hZ1 hZ2
  have E1 : β p p = 2 * γ * δ * β x x' := by
    conv_lhs => rw [← hp1]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxx, hx'x',
      hsymm x' x]
    ring
  have E2 : β p p = 2 * γ' * δ' * β y y' := by
    conv_lhs => rw [← hp2]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyy, hy'y',
      hsymm y' y]
    ring
  have E3 : β x p = δ * β x x' := by
    conv_lhs => rw [← hp1]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxx]
    ring
  have E4 : β y p = δ' * β y y' := by
    conv_lhs => rw [← hp2]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hyy]
    ring
  have key : β (γ • x - γ' • y) p = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, E3, E4]
    linear_combination (1 / 2 : ℝ) * E2 - (1 / 2 : ℝ) * E1
  intro q hq z hz
  rw [hZeq] at hz
  obtain ⟨t, rfl⟩ := (ProjPoint.mem_mk' hp).1 hq
  obtain ⟨s, rfl⟩ := (ProjPoint.mem_mk' hW).1 hz
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm p, key]
  ring

/-- The symmetric bilinear form of `ℝ³` whose zero set is the circle with center `(c₀, c₁)` and radius `r`
in the plane `z = 1`: `⟪u' - c u₂, v' - c v₂⟫ - r² u₂ v₂` where `u' = (u₀, u₁)`. -/
def circleForm (c0 c1 r : ℝ) (u v : Space3) : ℝ :=
  (u 0 - c0 * u 2) * (v 0 - c0 * v 2) + (u 1 - c1 * u 2) * (v 1 - c1 * v 2) - r ^ 2 * (u 2 * v 2)

/-- `circleForm` as a bilinear map. -/
noncomputable def circleBil (c0 c1 r : ℝ) : Space3 →ₗ[ℝ] Space3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (circleForm c0 c1 r)
    (fun u u' v => by simp only [circleForm, PiLp.add_apply]; ring)
    (fun a u v => by simp only [circleForm, PiLp.smul_apply, smul_eq_mul]; ring)
    (fun u v v' => by simp only [circleForm, PiLp.add_apply]; ring)
    (fun a u v => by simp only [circleForm, PiLp.smul_apply, smul_eq_mul]; ring)

theorem circleBil_apply (c0 c1 r : ℝ) (u v : Space3) : circleBil c0 c1 r u v = circleForm c0 c1 r u v := rfl

theorem circleBil_symm (c0 c1 r : ℝ) (u v : Space3) : circleBil c0 c1 r u v = circleBil c0 c1 r v u := by
  simp only [circleBil_apply, circleForm]
  ring

/-- The normal vector of the polar line of the point spanned by `p`. -/
def polarNormal (c0 c1 r : ℝ) (p : Space3) : Space3 :=
  !₂[p 0 - c0 * p 2, p 1 - c1 * p 2, -c0 * (p 0 - c0 * p 2) - c1 * (p 1 - c1 * p 2) - r ^ 2 * p 2]

theorem polarNormal_ne_zero {c0 c1 r : ℝ} (hr : r ≠ 0) {p : Space3} (hp : p ≠ 0) :
    polarNormal c0 c1 r p ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Space3 => v 0) h
  have h1 := congrArg (fun v : Space3 => v 1) h
  have h2 := congrArg (fun v : Space3 => v 2) h
  simp [polarNormal] at h0 h1 h2
  have : p 2 = 0 := by
    have : r ^ 2 * p 2 = 0 := by linear_combination -h2 - c0 * h0 - c1 * h1
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hr)
  apply hp
  ext i
  fin_cases i
  · rw [this] at h0; simpa using h0
  · rw [this] at h1; simpa using h1
  · simpa using this

theorem polarNormal_dot (c0 c1 r : ℝ) (p v : Space3) :
    polarNormal c0 c1 r p 0 * v 0 + polarNormal c0 c1 r p 1 * v 1 + polarNormal c0 c1 r p 2 * v 2 =
      circleBil c0 c1 r p v := by
  simp only [polarNormal, circleBil_apply, circleForm]
  simp
  ring

/-- **The polar line of a point of the projective plane with respect to the circle** with center
`(c₀, c₁)` and radius `r ≠ 0` (Petrunin, Section 15H, p. 129): the line of the space model with normal
`polarNormal`; on the affine plane it is `⟪x - c, p - c⟫ = r²` (see `mem_polar_iff_circleBil`). -/
@[kb "petrunin2025" "Polar line, p. 130"]
noncomputable def ProjPoint.circlePolar (c0 c1 r : ℝ) (hr : r ≠ 0) (P : ProjPoint) : ProjLine :=
  lineOfNormal (polarNormal c0 c1 r P.exists_rep.choose)
    (polarNormal_ne_zero hr P.exists_rep.choose_spec.choose)

theorem ProjPoint.liesOn_circlePolar_iff (c0 c1 r : ℝ) (hr : r ≠ 0) (P Q : ProjPoint) :
    Q.LiesOn (P.circlePolar c0 c1 r hr) ↔ PolarOrth (circleBil c0 c1 r) P Q := by
  obtain ⟨q, hq, rfl⟩ := Q.exists_rep
  have hP : P.1 = Submodule.span ℝ {P.exists_rep.choose} :=
    congrArg Subtype.val P.exists_rep.choose_spec.choose_spec
  unfold ProjPoint.circlePolar
  rw [mk'_liesOn_lineOfNormal, polarNormal_dot]
  constructor
  · intro h p hp z hz
    rw [hP] at hp
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hp
    obtain ⟨s, rfl⟩ := (ProjPoint.mem_mk' hq).1 hz
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h]
    ring
  · intro h
    exact h _ (by rw [hP]; exact Submodule.mem_span_singleton_self _) q (Submodule.mem_span_singleton_self _)

/-- **Independence of the secant construction, projective form** (Petrunin, Claim 15.17, p. 129): for four
distinct points `X, X', Y, Y'` of the circle with `P` on the lines `XX'` and `YY'`, the points
`Z = XY ∩ X'Y'` and `Z' = XY' ∩ X'Y` both lie on the polar line of `P`; hence, when `Z ≠ Z'`, the line `ZZ'`
is the polar line, which depends only on `P` and the circle, not on the two secants. -/
@[kb "petrunin2025" "Claim 15.17, p. 129"]
theorem secant_construction_polar (c0 c1 r : ℝ) (hr : r ≠ 0) {X X' Y Y' P Z Z' : ProjPoint}
    (hXX' : X ≠ X') (hYY' : Y ≠ Y') (hXY : X ≠ Y) (hX'Y' : X' ≠ Y') (hXY' : X ≠ Y') (hX'Y : X' ≠ Y)
    (hX : OnConic (circleBil c0 c1 r) X) (hX' : OnConic (circleBil c0 c1 r) X')
    (hY : OnConic (circleBil c0 c1 r) Y) (hY' : OnConic (circleBil c0 c1 r) Y')
    (hP1 : ProjCollinear X X' P) (hP2 : ProjCollinear Y Y' P)
    (hZ : ProjCollinear X Y Z ∧ ProjCollinear X' Y' Z) (hZ' : ProjCollinear X Y' Z' ∧ ProjCollinear X' Y Z')
    (hl : ¬ ∃ ℓ : ProjLine, X.LiesOn ℓ ∧ Y.LiesOn ℓ ∧ X'.LiesOn ℓ ∧ Y'.LiesOn ℓ) :
    Z.LiesOn (P.circlePolar c0 c1 r hr) ∧ Z'.LiesOn (P.circlePolar c0 c1 r hr) := by
  have hsymm := circleBil_symm c0 c1 r
  have hl' : ¬ ∃ ℓ : ProjLine, X.LiesOn ℓ ∧ Y'.LiesOn ℓ ∧ X'.LiesOn ℓ ∧ Y.LiesOn ℓ := by
    rintro ⟨ℓ, h1, h2, h3, h4⟩
    exact hl ⟨ℓ, h1, h4, h3, h2⟩
  rw [ProjPoint.liesOn_circlePolar_iff, ProjPoint.liesOn_circlePolar_iff]
  exact ⟨secant_on_polar _ hsymm hXY hXX' hYY' hX'Y' hX hX' hY hY' hP1 hP2 hZ.1 hZ.2 hl,
    secant_on_polar _ hsymm hXY' hXX' hYY'.symm hX'Y hX hX' hY' hY hP1 hP2.symm12 hZ'.1 hZ'.2 hl'⟩

/-- **The polar line is the line `ZZ'` of the construction** (Petrunin, Claim 15.17): with the notation of
`secant_construction_polar` and `Z ≠ Z'`, the line through `Z` and `Z'` is the polar line of `P`. -/
theorem secant_construction_join_eq_polar (c0 c1 r : ℝ) (hr : r ≠ 0) {P Z Z' : ProjPoint} (hZZ' : Z ≠ Z')
    (hZ : Z.LiesOn (P.circlePolar c0 c1 r hr)) (hZ' : Z'.LiesOn (P.circlePolar c0 c1 r hr)) :
    P.circlePolar c0 c1 r hr = Z.join Z' hZZ' :=
  ProjPoint.eq_join_of hZZ' hZ hZ'

/-- The point `(p₀, p₁, 1)` of the space model attached to a point of the Euclidean plane. -/
def planeVec (p : EuclideanSpace ℝ (Fin 2)) : Space3 := spacePoint (p 0) (p 1)

/-- A point of the plane lies on the circle `s` iff its image in the space model lies on the conic
`circleBil` (the circle as a conic of the projective plane). -/
theorem mem_sphere_iff_circleBil (s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (hr : 0 ≤ s.radius) (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ s ↔ circleBil (s.center 0) (s.center 1) s.radius (planeVec p) (planeVec p) = 0 := by
  rw [EuclideanGeometry.mem_sphere, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [circleBil_apply, circleForm, planeVec, spacePoint]
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, mul_one, Real.norm_eq_abs, sq_abs,
    Real.dist_eq]
  constructor
  · intro h
    have := Real.sq_sqrt (add_nonneg (sq_nonneg (p 0 - s.center 0)) (sq_nonneg (p 1 - s.center 1)))
    rw [h] at this
    nlinarith
  · intro h
    rw [show (p 0 - s.center 0) ^ 2 + (p 1 - s.center 1) ^ 2 = s.radius ^ 2 by nlinarith]
    exact Real.sqrt_sq hr

/-- **The polar of Mathlib's `Sphere.polar` is the affine part of the projective polar** (Petrunin,
Section 15H, p. 129): for a point `p₂` different from the center, `p₁` lies on the polar of `p₂` with
respect to the circle iff the points `p₂` and `p₁` of the space model are conjugate for the conic. -/
@[kb "petrunin2025" "Polar and pole, p. 130"]
theorem mem_polar_iff_circleBil (s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (hr : 0 < s.radius) {p₁ p₂ : EuclideanSpace ℝ (Fin 2)} (hp₂ : p₂ ≠ s.center) :
    p₁ ∈ s.polar p₂ ↔
      circleBil (s.center 0) (s.center 1) s.radius (planeVec p₂) (planeVec p₁) = 0 := by
  rw [EuclideanGeometry.Sphere.mem_polar_iff_inner]
  simp only [hr.ne', hp₂, false_or]
  simp only [circleBil_apply, circleForm, planeVec, spacePoint, vsub_eq_sub]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  constructor <;> intro h <;> linarith

/-- **The tangent lines from a point to a circle** (Petrunin, Exercise 15.19, p. 130): if `V` is a point
of the circle lying on the polar of `A`, then the line `AV` is tangent to the circle at `V`. -/
@[kb "petrunin2025" "Exercise 15.19, p. 130"]
theorem polar_isTangentAt {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] {s : EuclideanGeometry.Sphere P} {A T : P} (hA : A ≠ s.center) (hT : T ∈ s)
    (hTp : T ∈ s.polar A) : s.IsTangentAt T (affineSpan ℝ {A, T}) := by
  have hA' : A ∈ s.orthRadius T :=
    (EuclideanGeometry.Sphere.mem_orthRadius_iff_mem_polar_of_mem hA hT).2 hTp
  exact ⟨hT, right_mem_affineSpan_pair ℝ A T,
    affineSpan_pair_le_of_mem_of_mem hA' (EuclideanGeometry.Sphere.self_mem_orthRadius s T)⟩

/-- **The polar of a point outside a circle meets it at exactly two points, and the lines from the point to
them are tangent** (Petrunin, Exercise 15.19, p. 130). -/
@[kb "petrunin2025" "Exercise 15.19 (two tangents), p. 130"]
theorem polar_inter_tangent {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
    {s : EuclideanGeometry.Sphere P} (hs : 0 < s.radius) {A : P} (hA : s.radius < dist A s.center) :
    ∃ V₁ V₂ : P, V₁ ≠ V₂ ∧ (∀ T, (T ∈ s ∧ T ∈ s.polar A) ↔ T = V₁ ∨ T = V₂) ∧
      s.IsTangentAt V₁ (affineSpan ℝ {A, V₁}) ∧ s.IsTangentAt V₂ (affineSpan ℝ {A, V₂}) := by
  have hAc : A ≠ s.center := by
    rintro rfl
    rw [dist_self] at hA
    linarith
  obtain ⟨V₁, V₂, hne, heq⟩ := Set.ncard_eq_two.1
    (EuclideanGeometry.Sphere.ncard_inter_polar_eq_two_of_radius_lt_dist hs hA)
  have hmem : ∀ T, (T ∈ s ∧ T ∈ s.polar A) ↔ T = V₁ ∨ T = V₂ := fun T => by
    have := Set.ext_iff.1 heq T
    simpa using this
  have h1 := (hmem V₁).2 (Or.inl rfl)
  have h2 := (hmem V₂).2 (Or.inr rfl)
  exact ⟨V₁, V₂, hne, hmem, polar_isTangentAt hAc h1.1 h1.2, polar_isTangentAt hAc h2.1 h2.2⟩

end Polar

end UndergradKB.Geometry
