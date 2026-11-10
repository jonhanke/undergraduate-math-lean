import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import UndergradKB.Common.Attr
import UndergradKB.Geometry.ProjectivePlane2
import UndergradKB.Geometry.AffineFundamental

/-! # The fundamental theorem of projective geometry for the real plane (Petrunin, Chapter 15E)

Petrunin, Section 15E (p. 124): a *projective transformation* is a bijection of the projective plane
sending lines to lines (`IsProjectiveTransformation`). We prove that every such bijection is induced by a
linear automorphism of `ℝ³` in the space model (`fundamental_projective`), deduced from the fundamental
theorem of affine geometry (`fundamental_affine`, Theorem 14.12) by moving the image of the ideal line back
to the ideal line. We also derive the book's dichotomy of Theorem 15.2 for *all* projective transformations
(`projective_transformation_classification`): affine, or an affine map composed with the perspective
projection `β : (x, y) ↦ (x / y, 1 / y)` and another affine map. -/

namespace UndergradKB.Geometry

open Module

section Basics

/-- The affine point `(x, y)` as a function on pairs. -/
noncomputable abbrev Aff (p : ℝ × ℝ) : ProjPoint := affineToProj p.1 p.2

theorem Aff_eq_mk' (p : ℝ × ℝ) : Aff p = ProjPoint.mk' (spacePoint p.1 p.2) (spacePoint_ne_zero _ _) := rfl

theorem Aff_injective : Function.Injective Aff := affineToProj_injective

theorem liesOn_ideal_iff (P : ProjPoint) : P.LiesOn idealProjLine ↔ P.IsIdeal := by
  constructor
  · intro h v hv
    exact (mem_idealProjLine v).1 (h hv)
  · intro h v hv
    exact (mem_idealProjLine v).2 (h v hv)

theorem IsProjectiveTransformation.comp {f g : ProjPoint → ProjPoint} (hf : IsProjectiveTransformation f)
    (hg : IsProjectiveTransformation g) : IsProjectiveTransformation (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, fun ℓ => ?_⟩
  obtain ⟨ℓ', h'⟩ := hf.2 ℓ
  obtain ⟨ℓ'', h''⟩ := hg.2 ℓ'
  exact ⟨ℓ'', by rw [Set.image_comp, h', h'']⟩

theorem ProjPoint.map_trans (g h : Space3 ≃ₗ[ℝ] Space3) (P : ProjPoint) :
    P.map (g.trans h) = (P.map g).map h := by
  apply Subtype.ext
  change Submodule.map (g.trans h : Space3 →ₗ[ℝ] Space3) P.1 =
    Submodule.map (h : Space3 →ₗ[ℝ] Space3) (Submodule.map (g : Space3 →ₗ[ℝ] Space3) P.1)
  rw [← Submodule.map_comp]
  rfl

theorem image_map_liesOn (g : Space3 ≃ₗ[ℝ] Space3) (ℓ : ProjLine) :
    ProjPoint.map g '' {P | P.LiesOn ℓ} = {P | P.LiesOn (ℓ.map g)} := by
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (ProjPoint.map_liesOn_iff g P ℓ).2 hP
  · intro hQ
    refine ⟨Q.map g.symm, ?_, ProjPoint.map_map_symm g Q⟩
    show (Q.map g.symm).LiesOn ℓ
    rw [← ProjPoint.map_liesOn_iff g, ProjPoint.map_map_symm]
    exact hQ

/-- A line through a projective transformation: the image line is the join of the images of two points. -/
theorem image_line_eq_join {G : ProjPoint → ProjPoint} (hG : IsProjectiveTransformation G) {P Q : ProjPoint}
    (hPQ : P ≠ Q) : G '' {R | R.LiesOn (P.join Q hPQ)} =
      {R | R.LiesOn ((G P).join (G Q) (fun h => hPQ (hG.1.1 h)))} := by
  obtain ⟨ℓ', h'⟩ := hG.2 (P.join Q hPQ)
  have hP : G P ∈ G '' {R | R.LiesOn (P.join Q hPQ)} := ⟨P, P.left_liesOn_join hPQ, rfl⟩
  have hQ : G Q ∈ G '' {R | R.LiesOn (P.join Q hPQ)} := ⟨Q, ProjPoint.right_liesOn_join hPQ, rfl⟩
  rw [h'] at hP hQ ⊢
  rw [ProjPoint.eq_join_of (fun h => hPQ (hG.1.1 h)) hP hQ]

/-- A projective transformation fixing two points fixes the line through them setwise, so a point of the
line goes to a point of the line. -/
theorem liesOn_join_of_fixed {K : ProjPoint → ProjPoint} (hK : IsProjectiveTransformation K) {P Q : ProjPoint}
    (hPQ : P ≠ Q) (hP : K P = P) (hQ : K Q = Q) {X : ProjPoint} (hX : X.LiesOn (P.join Q hPQ)) :
    (K X).LiesOn (P.join Q hPQ) := by
  have := image_line_eq_join hK hPQ
  have hX' : K X ∈ K '' {R | R.LiesOn (P.join Q hPQ)} := ⟨X, hX, rfl⟩
  rw [this] at hX'
  simp only [hP, hQ] at hX'
  exact hX'

end Basics

section AffineLines

theorem Aff_liesOn_join_iff {p q : ℝ × ℝ} (hpq : p ≠ q) (r : ℝ × ℝ) :
    (Aff r).LiesOn ((Aff p).join (Aff q) (fun h => hpq (Aff_injective h))) ↔ r ∈ line[ℝ, p, q] := by
  change (ProjPoint.mk' (spacePoint r.1 r.2) (spacePoint_ne_zero _ _)).1 ≤
    (ProjPoint.mk' (spacePoint p.1 p.2) (spacePoint_ne_zero _ _)).1 ⊔
      (ProjPoint.mk' (spacePoint q.1 q.2) (spacePoint_ne_zero _ _)).1 ↔ _
  rw [mem_sup_mk', mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨s, t, h⟩
    have h0 := congrArg (fun v : Space3 => v 0) h
    have h1 := congrArg (fun v : Space3 => v 1) h
    have h2 := congrArg (fun v : Space3 => v 2) h
    simp [spacePoint] at h0 h1 h2
    obtain rfl : s = 1 - t := by linarith
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply]
    ext
    · simp; nlinarith
    · simp; nlinarith
  · rintro ⟨t, rfl⟩
    refine ⟨1 - t, t, ?_⟩
    ext i
    fin_cases i <;> simp [spacePoint, AffineMap.lineMap_apply] <;> ring

end AffineLines

section Restriction

variable {G : ProjPoint → ProjPoint}

theorem exists_aff_image (hG : IsProjectiveTransformation G)
    (hI : G '' {P | P.LiesOn idealProjLine} = {P | P.LiesOn idealProjLine}) (p : ℝ × ℝ) :
    ∃ q, Aff q = G (Aff p) := by
  have hn : ¬ (G (Aff p)).IsIdeal := by
    intro h
    have h' : G (Aff p) ∈ G '' {P | P.LiesOn idealProjLine} := by
      rw [hI]; exact (liesOn_ideal_iff _).2 h
    obtain ⟨P, hP, hPe⟩ := h'
    have := hG.1.1 hPe
    subst this
    exact (range_affineToProj _).1 ⟨p, rfl⟩ ((liesOn_ideal_iff _).1 hP)
  obtain ⟨q, hq⟩ := (range_affineToProj _).2 hn
  exact ⟨q, hq⟩

theorem liesOn_join_congr {P P' Q Q' : ProjPoint} (hP : P = P') (hQ : Q = Q') (h : P ≠ Q) (h' : P' ≠ Q')
    (X : ProjPoint) : X.LiesOn (P.join Q h) ↔ X.LiesOn (P'.join Q' h') := by
  subst hP; subst hQ; rfl

/-- The restriction of a projective transformation preserving the ideal line to the affine plane. -/
theorem exists_restriction (hG : IsProjectiveTransformation G)
    (hI : G '' {P | P.LiesOn idealProjLine} = {P | P.LiesOn idealProjLine}) :
    ∃ f : ℝ × ℝ → ℝ × ℝ, (∀ p, Aff (f p) = G (Aff p)) ∧ IsAffineTransformation f := by
  choose f hf using exists_aff_image hG hI
  have hbij : Function.Bijective f := by
    constructor
    · intro p p' h
      apply Aff_injective
      apply hG.1.1
      rw [← hf, ← hf, h]
    · intro q
      obtain ⟨P, hP⟩ := hG.1.2 (Aff q)
      have hn : ¬ P.IsIdeal := by
        intro h
        have : G P ∈ {P | P.LiesOn idealProjLine} := by
          rw [← hI]; exact ⟨P, (liesOn_ideal_iff _).2 h, rfl⟩
        rw [hP] at this
        exact (range_affineToProj _).1 ⟨q, rfl⟩ ((liesOn_ideal_iff _).1 this)
      obtain ⟨p, rfl⟩ := (range_affineToProj _).2 hn
      exact ⟨p, Aff_injective (by rw [hf, hP])⟩
  refine ⟨f, hf, hbij, ?_⟩
  intro p q hpq
  have hpq' : Aff p ≠ Aff q := fun h => hpq (Aff_injective h)
  have hfpq : f p ≠ f q := fun h => hpq (hbij.1 h)
  refine ⟨f p, f q, hfpq, ?_⟩
  have himg := image_line_eq_join hG hpq'
  have key : ∀ X : ProjPoint, X.LiesOn ((Aff (f p)).join (Aff (f q)) (fun h => hfpq (Aff_injective h))) ↔
      X.LiesOn ((G (Aff p)).join (G (Aff q)) (fun h => hpq' (hG.1.1 h))) :=
    fun X => liesOn_join_congr (hf p) (hf q) _ _ X
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h1 : (Aff r).LiesOn ((Aff p).join (Aff q) hpq') := (Aff_liesOn_join_iff hpq r).2 hr
    have h2 : G (Aff r) ∈ G '' {R | R.LiesOn ((Aff p).join (Aff q) hpq')} := ⟨_, h1, rfl⟩
    rw [himg] at h2
    rw [SetLike.mem_coe, ← Aff_liesOn_join_iff hfpq, key, hf r]
    exact h2
  · intro hz
    obtain ⟨r, rfl⟩ := hbij.2 z
    refine ⟨r, ?_, rfl⟩
    rw [SetLike.mem_coe, ← Aff_liesOn_join_iff hfpq, key, hf r] at hz
    have h2 : G (Aff r) ∈ G '' {R | R.LiesOn ((Aff p).join (Aff q) hpq')} := by
      rw [himg]; exact hz
    obtain ⟨R, hR, hRe⟩ := h2
    have := hG.1.1 hRe
    subst this
    exact (Aff_liesOn_join_iff hpq r).1 hR

end Restriction

section Coordinates

theorem det_ne_zero_of_inj (a b c d : ℝ)
    (k : ∀ x y : ℝ, x * a + y * b = 0 → x * c + y * d = 0 → x = 0 ∧ y = 0) : a * d - b * c ≠ 0 := by
  intro h
  by_cases h1 : d = 0 ∧ c = 0
  · by_cases h2 : b = 0 ∧ a = 0
    · have := k 1 0 (by simp [h2.2]) (by simp [h1.2])
      norm_num at this
    · have := k (-b) a (by ring) (by linear_combination h)
      exact h2 ⟨by linarith [this.1], this.2⟩
  · have := k d (-c) (by linear_combination h) (by ring)
    exact h1 ⟨this.1, by linarith [this.2]⟩

/-- An affine equivalence of the plane `ℝ²` has the coordinate form `(x, y) ↦ (a x + b y + r, c x + d y + s)`
with `a d - b c ≠ 0`. -/
theorem exists_matrix_of_affineEquiv (e : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) :
    ∃ a b c d r s : ℝ, a * d - b * c ≠ 0 ∧ ∀ x y : ℝ, e (x, y) = (a * x + b * y + r, c * x + d * y + s) := by
  have hap : ∀ p, e p = e.linear p + e 0 := by
    intro p
    have h := affineEquiv_linear_vsub e p 0
    rw [vsub_eq_sub, vsub_eq_sub, sub_zero] at h
    rw [h]; abel
  have hL : ∀ x y : ℝ, e.linear (x, y) = (x * (e.linear (1, 0)).1 + y * (e.linear (0, 1)).1,
      x * (e.linear (1, 0)).2 + y * (e.linear (0, 1)).2) := by
    intro x y
    have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul]
    ext <;> simp
  refine ⟨(e.linear (1, 0)).1, (e.linear (0, 1)).1, (e.linear (1, 0)).2, (e.linear (0, 1)).2,
    (e 0).1, (e 0).2, ?_, ?_⟩
  · apply det_ne_zero_of_inj
    intro x y h1 h2
    have h0 : e.linear (x, y) = e.linear 0 := by
      rw [hL, map_zero]; ext <;> simp [h1, h2]
    have := e.linear.injective h0
    simpa [Prod.ext_iff] using this
  · intro x y
    rw [hap, hL]
    ext <;> simp <;> ring

end Coordinates

section Ideal

/-- A projective transformation fixing every affine point is the identity on the ideal points too (each
ideal point is the intersection of two lines, each through two affine points). -/
theorem fixed_ideal {K : ProjPoint → ProjPoint} (hK : IsProjectiveTransformation K)
    (hfix : ∀ p, K (Aff p) = Aff p) (X : ProjPoint) (hX : X.IsIdeal) : K X = X := by
  obtain ⟨v, hv0, rfl⟩ := X.exists_rep
  have hv2 : v 2 = 0 := hX v (Submodule.mem_span_singleton_self v)
  have hne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    ext i
    fin_cases i <;> simp [h.1, h.2, hv2]
  have hp : ((0, 0) : ℝ × ℝ) ≠ (v 0, v 1) := by
    intro h
    rcases hne with h0 | h1
    · exact h0 (by simpa using (congrArg Prod.fst h).symm)
    · exact h1 (by simpa using (congrArg Prod.snd h).symm)
  have hq : ((-v 1, v 0) : ℝ × ℝ) ≠ (v 0 - v 1, v 1 + v 0) := by
    intro h
    have e1 := congrArg Prod.fst h
    have e2 := congrArg Prod.snd h
    simp at e1 e2
    rcases hne with h0 | h1
    · exact h0 (by linarith)
    · exact h1 (by linarith)
  have hp' : Aff (0, 0) ≠ Aff (v 0, v 1) := fun h => hp (Aff_injective h)
  have hq' : Aff (-v 1, v 0) ≠ Aff (v 0 - v 1, v 1 + v 0) := fun h => hq (Aff_injective h)
  have hXp : (ProjPoint.mk' v hv0).LiesOn ((Aff (0, 0)).join (Aff (v 0, v 1)) hp') := by
    change (ProjPoint.mk' v hv0).1 ≤ (ProjPoint.mk' (spacePoint 0 0) (spacePoint_ne_zero _ _)).1 ⊔
      (ProjPoint.mk' (spacePoint (v 0) (v 1)) (spacePoint_ne_zero _ _)).1
    rw [mem_sup_mk']
    refine ⟨-1, 1, ?_⟩
    ext i
    fin_cases i <;> simp [spacePoint, hv2]
  have hXq : (ProjPoint.mk' v hv0).LiesOn ((Aff (-v 1, v 0)).join (Aff (v 0 - v 1, v 1 + v 0)) hq') := by
    change (ProjPoint.mk' v hv0).1 ≤ (ProjPoint.mk' (spacePoint (-v 1) (v 0)) (spacePoint_ne_zero _ _)).1 ⊔
      (ProjPoint.mk' (spacePoint (v 0 - v 1) (v 1 + v 0)) (spacePoint_ne_zero _ _)).1
    rw [mem_sup_mk']
    refine ⟨-1, 1, ?_⟩
    ext i
    fin_cases i <;> simp [spacePoint, hv2]
  have hlines : (Aff (0, 0)).join (Aff (v 0, v 1)) hp' ≠
      (Aff (-v 1, v 0)).join (Aff (v 0 - v 1, v 1 + v 0)) hq' := by
    intro h
    have hm : (Aff (-v 1, v 0)).LiesOn ((Aff (0, 0)).join (Aff (v 0, v 1)) hp') := by
      rw [h]
      exact ProjPoint.left_liesOn_join hq'
    rw [Aff_liesOn_join_iff hp] at hm
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hm
    have e1 := congrArg Prod.fst ht
    have e2 := congrArg Prod.snd ht
    simp [AffineMap.lineMap_apply] at e1 e2
    have h3 : v 0 * (t ^ 2 + 1) = 0 := by linear_combination t * e1 - e2
    have h0 : v 0 = 0 := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact h
      · nlinarith [sq_nonneg t]
    have h1 : v 1 = 0 := by rw [h0] at e1; nlinarith [e1]
    rcases hne with h | h
    · exact h h0
    · exact h h1
  have k1 := liesOn_join_of_fixed hK hp' (hfix _) (hfix _) hXp
  have k2 := liesOn_join_of_fixed hK hq' (hfix _) (hfix _) hXq
  exact (existsUnique_point_on hlines).unique ⟨k1, k2⟩ ⟨hXp, hXq⟩

end Ideal

section Main

/-- **The fundamental theorem of projective geometry for the real plane** (Petrunin, Section 15E, p. 124;
the book's definition of projective transformations together with the space model of Section 15C): every
bijection of the projective plane sending lines to lines is induced by a linear automorphism of `ℝ³`. -/
@[kb "petrunin2025" "Theorem 15.2, p. 124"]
theorem fundamental_projective {F : ProjPoint → ProjPoint} (hF : IsProjectiveTransformation F) :
    ∃ M : Space3 ≃ₗ[ℝ] Space3, F = ProjPoint.map M := by
  obtain ⟨ℓ, hℓ⟩ := hF.2 idealProjLine
  obtain ⟨g, hg⟩ := exists_map_eq_idealProjLine ℓ
  have hG := hF.comp (isProjectiveTransformation_map g)
  have hI : (ProjPoint.map g ∘ F) '' {P | P.LiesOn idealProjLine} = {P | P.LiesOn idealProjLine} := by
    rw [Set.image_comp, hℓ, image_map_liesOn, hg]
  obtain ⟨f, hf, hfa⟩ := exists_restriction hG hI
  obtain ⟨e, he⟩ := fundamental_affine hfa (V₁ := ℝ × ℝ) (V₂ := ℝ × ℝ) (by simp) (by simp)
  obtain ⟨a, b, c, d, r, s, hdet, hea⟩ := exists_matrix_of_affineEquiv e
  have hGH : ∀ p : ℝ × ℝ, ProjPoint.map g (F (Aff p)) = (Aff p).map (affineGL a b c d r s hdet) := by
    intro p
    have h1 : Aff (f p) = ProjPoint.map g (F (Aff p)) := hf p
    rw [← h1, ← he]
    have h2 := hea p.1 p.2
    rw [Prod.mk.eta] at h2
    rw [h2]
    exact (map_affineGL_affineToProj a b c d r s hdet p.1 p.2).symm
  set H := affineGL a b c d r s hdet with hH
  have hK := hG.comp (isProjectiveTransformation_map H.symm)
  have hfix : ∀ p, (ProjPoint.map H.symm ∘ (ProjPoint.map g ∘ F)) (Aff p) = Aff p := by
    intro p
    change (ProjPoint.map g (F (Aff p))).map H.symm = _
    rw [hGH, ProjPoint.map_symm_map]
  have hKid : ∀ P, (ProjPoint.map g (F P)).map H.symm = P := by
    intro P
    by_cases hP : P.IsIdeal
    · exact fixed_ideal hK hfix P hP
    · obtain ⟨p, rfl⟩ := (range_affineToProj P).2 hP
      exact hfix p
  refine ⟨H.trans g.symm, funext fun P => ?_⟩
  rw [ProjPoint.map_trans]
  have h2 : ProjPoint.map g (F P) = P.map H := by
    have := congrArg (ProjPoint.map H) (hKid P)
    rwa [ProjPoint.map_map_symm] at this
  rw [← h2, ProjPoint.map_symm_map]

/-- A bijection of the projective plane sends lines to lines if and only if it is induced by a linear
automorphism of `ℝ³` (Petrunin, Section 15E, p. 124). -/
@[kb "petrunin2025" "Definition of projective transformations, p. 124"]
theorem isProjectiveTransformation_iff (F : ProjPoint → ProjPoint) :
    IsProjectiveTransformation F ↔ ∃ M : Space3 ≃ₗ[ℝ] Space3, F = ProjPoint.map M := by
  constructor
  · exact fundamental_projective
  · rintro ⟨M, rfl⟩
    exact isProjectiveTransformation_map M

/-- **Theorem 15.2, second part, for all projective transformations** (Petrunin, p. 124): a bijection of the
projective plane sending lines to lines either sends the ideal line onto itself and is then affine (given on
the affine points by `(x, y) ↦ (a x + b y + r, c x + d y + s)`), or, in a suitable affine coordinate system
(the affine map `k`), it is the composition of an affine map `α`, the perspective projection
`β : (x, y) ↦ (x / y, 1 / y)` (induced by `swapYZ`) and the affine map `k⁻¹`. -/
@[kb "petrunin2025" "Theorem 15.2, p. 124"]
theorem projective_transformation_classification {F : ProjPoint → ProjPoint}
    (hF : IsProjectiveTransformation F) :
    (F '' {P | P.LiesOn idealProjLine} = {P | P.LiesOn idealProjLine} ∧
      ∃ a b c d r s : ℝ, a * d - b * c ≠ 0 ∧ ∀ x y : ℝ,
        F (affineToProj x y) = affineToProj (a * x + b * y + r) (c * x + d * y + s)) ∨
    (∃ k α : Space3 ≃ₗ[ℝ] Space3, idealProjLine.map k = idealProjLine ∧ idealProjLine.map α = idealProjLine ∧
      ∀ P, F P = ((P.map α).map swapYZ).map k.symm) := by
  obtain ⟨M, rfl⟩ := fundamental_projective hF
  rcases projective_classification M with h | ⟨k, α, hk, hα, hM⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [image_map_liesOn, h]
    · obtain ⟨a, b, c, d, r, s, hdet, hall⟩ := exists_affine_of_map_ideal h
      exact ⟨a, b, c, d, r, s, hdet, hall⟩
  · right
    refine ⟨k, α, hk, hα, fun P => ?_⟩
    have : M = α.trans (swapYZ.trans k.symm) := LinearEquiv.ext fun y => hM y
    rw [this, ProjPoint.map_trans, ProjPoint.map_trans]

end Main

end UndergradKB.Geometry
