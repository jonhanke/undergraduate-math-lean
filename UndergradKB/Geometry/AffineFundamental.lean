import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import UndergradKB.Common.Attr
import UndergradKB.Geometry.AffineSpaceModel
import UndergradKB.Geometry.AffineTheorems

/-! # The fundamental theorem of affine geometry (Petrunin, chapter 14)

Section 14A (Exercise 14.4), Section 14C (Exercise 14.10, Theorem 14.12) and the algebraic lemma 14.17.

A bijection `f` between real affine planes (more generally: affine spaces of dimension `2` over `ℝ`) that sends
lines onto lines, or only collinear triples to collinear triples, is an affine equivalence.

* `PreservesCollinear f`: collinear triples go to collinear triples, and conversely.
* `reflect_collinear` (Exercise 14.4, first part): a bijection mapping collinear triples to collinear triples
  also maps non-collinear triples to non-collinear triples.
* `vsub_eq_of_preservesCollinear`: such a map preserves vector equality `XY = AB` (hence parallelograms).
* `exists_affineEquiv_of_collinear`, `fundamental_affine` (Theorem 14.12): `f` is an `AffineEquiv`.
  The route is the book's: parallelograms preserved, hence `f` is additive on vectors; the induced coordinate
  map on the two axes is a ring homomorphism `ℝ → ℝ` (collinearity of three points of the form
  `(1,0)`, `(0,t)`, `(s, t(1-s))`), hence the identity (`Real.RingHom.unique`, the book's algebraic lemma 14.17).
-/

namespace UndergradKB.Geometry

open AffineSubspace Affine

section Helpers

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- A point whose vector from `A` is a multiple of `AB` gives a collinear triple. -/
theorem collinear_of_vsub_smul {A B D : P} (c : ℝ) (h : D -ᵥ A = c • (B -ᵥ A)) :
    Collinear ℝ ({A, B, D} : Set P) := by
  have hD : D ∈ line[ℝ, A, B] := by
    have := smul_vsub_vadd_mem_affineSpan_pair c A B
    rwa [← h, vsub_vadd] at this
  have := collinear_insert_of_mem_affineSpan_pair hD
  have e : ({D, A, B} : Set P) = {A, B, D} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rwa [e] at this

/-- In a collinear triple with `A ≠ B`, the vector `AC` is a multiple of `AB`. -/
theorem exists_smul_of_collinear {A B C : P} (hAB : A ≠ B) (h : Collinear ℝ ({A, B, C} : Set P)) :
    ∃ c : ℝ, C -ᵥ A = c • (B -ᵥ A) := by
  have := h.mem_affineSpan_of_mem_of_ne (p₁ := A) (p₂ := B) (p₃ := C) (by simp) (by simp) (by simp) hAB
  rw [← vsub_vadd C A, vadd_left_mem_affineSpan_pair] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr.symm⟩

/-- Given `A ≠ B` in a space of dimension at least two there is a point `E` with `A B E` non-collinear. -/
theorem exists_third (hV : 1 < Module.finrank ℝ V) {A B : P} (hAB : A ≠ B) :
    ∃ E : P, ¬ Collinear ℝ ({A, B, E} : Set P) := by
  have hv : B -ᵥ A ≠ 0 := by
    intro h; exact hAB (vsub_eq_zero_iff_eq.mp h).symm
  obtain ⟨w, hw⟩ := exists_linearIndependent_pair_of_one_lt_finrank hV hv
  refine ⟨w +ᵥ A, fun hcol => ?_⟩
  rw [LinearIndependent.pair_iff] at hw
  rw [collinear_iff_of_mem (p₀ := A) (by simp)] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨r1, h1⟩ := hu B (by simp)
  obtain ⟨r2, h2⟩ := hu (w +ᵥ A) (by simp)
  have e1 : B -ᵥ A = r1 • u := by rw [h1]; simp
  have e2 : w = r2 • u := by
    have := congrArg (fun x => x -ᵥ A) h2
    simpa using this
  have := hw r2 (-r1) (by rw [e1, e2]; module)
  apply hv
  rw [e1, (by simpa using this.2 : r1 = 0)]; simp

/-- A space of dimension two contains a non-degenerate triangle. -/
theorem exists_frame (hV : Module.finrank ℝ V = 2) : ∃ O X Y : P, ¬ Collinear ℝ ({O, X, Y} : Set P) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨O⟩ := (inferInstance : Nonempty P)
  have hne : O ≠ v +ᵥ O := by
    intro h; apply hv
    have := congrArg (fun x => x -ᵥ O) h
    simpa using this.symm
  obtain ⟨E, hE⟩ := exists_third (by omega) hne
  exact ⟨O, _, E, hE⟩

end Helpers

section Core

variable {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]

/-- A map `f` *preserves collinearity* if three points are collinear exactly when their images are. -/
def PreservesCollinear (f : P₁ → P₂) : Prop :=
  ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) ↔ Collinear ℝ ({f A, f B, f C} : Set P₂)

/-- The coefficient `n` of the image of the fourth vertex of a parallelogram equals `1`. -/
theorem coef_one {f : P₁ → P₂} (hf : Function.Bijective f) (hc : PreservesCollinear f)
    {A B D C : P₁} (hABD : ¬ Collinear ℝ ({A, B, D} : Set P₁)) (hC : C -ᵥ D = B -ᵥ A) {m n : ℝ}
    (h : f C -ᵥ f A = m • (f B -ᵥ f A) + n • (f D -ᵥ f A)) : n = 1 := by
  by_contra hn
  have hn' : n - 1 ≠ 0 := sub_ne_zero.mpr hn
  set s : ℝ := -(n - 1)⁻¹ with hs
  have hAB : A ≠ B := by
    rintro rfl; exact hABD (by simp [collinear_pair])
  set Z' : P₂ := (s * m) • (f B -ᵥ f A) +ᵥ f A with hZ'
  have hZ1 : Z' ∈ line[ℝ, f A, f B] := smul_vsub_vadd_mem_affineSpan_pair _ _ _
  have hZ2 : Z' = s • (f C -ᵥ f D) +ᵥ f D := by
    have e1 : f C -ᵥ f D = (f C -ᵥ f A) - (f D -ᵥ f A) := (vsub_sub_vsub_cancel_right _ _ _).symm
    have e2 : s • (f C -ᵥ f D) +ᵥ f D = (s • (f C -ᵥ f D) + (f D -ᵥ f A)) +ᵥ f A := by
      rw [add_vadd, vsub_vadd]
    rw [e2, hZ', e1, h]
    congr 1
    have : s * (n - 1) = -1 := by rw [hs]; field_simp
    have h3 : s • (m • (f B -ᵥ f A) + n • (f D -ᵥ f A) - (f D -ᵥ f A)) + (f D -ᵥ f A)
        = (s * m) • (f B -ᵥ f A) + (s * (n - 1) + 1) • (f D -ᵥ f A) := by module
    rw [h3, this]; simp
  have hZ2' : Z' ∈ line[ℝ, f D, f C] := by
    rw [hZ2]; exact smul_vsub_vadd_mem_affineSpan_pair _ _ _
  obtain ⟨Z, hZ⟩ := hf.2 Z'
  have c1 : Collinear ℝ ({A, B, Z} : Set P₁) := by
    rw [hc]; rw [hZ]
    have := collinear_insert_of_mem_affineSpan_pair hZ1
    have e : ({Z', f A, f B} : Set P₂) = {f A, f B, Z'} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [e] at this
  have c2 : Collinear ℝ ({D, C, Z} : Set P₁) := by
    rw [hc]; rw [hZ]
    have := collinear_insert_of_mem_affineSpan_pair hZ2'
    have e : ({Z', f D, f C} : Set P₂) = {f D, f C, Z'} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [e] at this
  have hDC : D ≠ C := by
    intro hDC
    rw [← hDC, vsub_self] at hC
    exact hAB (vsub_eq_zero_iff_eq.mp hC.symm).symm
  obtain ⟨t, ht⟩ := exists_smul_of_collinear hAB c1
  obtain ⟨u, hu⟩ := exists_smul_of_collinear hDC c2
  apply hABD
  refine collinear_of_vsub_smul (t - u) ?_
  rw [sub_smul, ← ht, ← hC, ← hu]
  exact (vsub_sub_vsub_cancel_left D A Z).symm

/-- A non-degenerate parallelogram goes to a parallelogram (Exercise 14.10, first part). -/
theorem vec_nondeg {f : P₁ → P₂} (hf : Function.Bijective f) (hc : PreservesCollinear f)
    (hV₂ : Module.finrank ℝ V₂ = 2) {A B D C : P₁} (hABD : ¬ Collinear ℝ ({A, B, D} : Set P₁))
    (hC : C -ᵥ D = B -ᵥ A) : f C -ᵥ f D = f B -ᵥ f A := by
  have hnc : ¬ Collinear ℝ ({f A, f B, f D} : Set P₂) := fun h => hABD ((hc A B D).mpr h)
  obtain ⟨m, n, h⟩ := exists_coords hV₂ hnc (f C)
  have hn := coef_one hf hc hABD hC h
  have hC' : C -ᵥ B = D -ᵥ A := by
    calc C -ᵥ B = (C -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right _ _ _).symm
      _ = (C -ᵥ A) - (C -ᵥ D) := by rw [hC]
      _ = D -ᵥ A := vsub_sub_vsub_cancel_left D A C
  have hABD' : ¬ Collinear ℝ ({A, D, B} : Set P₁) := by
    intro h'
    apply hABD
    have e : ({A, D, B} : Set P₁) = {A, B, D} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [e] at h'
  have hm := coef_one hf hc hABD' hC' (m := n) (n := m) (by rw [h]; abel)
  subst hn; subst hm
  rw [← vsub_sub_vsub_cancel_right (f C) (f D) (f A), h]
  simp

/-- A collinearity-preserving bijection of planes preserves equality of vectors `AB = DC`. -/
theorem vsub_eq_of_preservesCollinear {f : P₁ → P₂} (hf : Function.Bijective f) (hc : PreservesCollinear f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) {A B C D : P₁}
    (h : B -ᵥ A = C -ᵥ D) : f B -ᵥ f A = f C -ᵥ f D := by
  by_cases hABD : Collinear ℝ ({A, B, D} : Set P₁)
  swap
  · exact (vec_nondeg hf hc hV₂ hABD h.symm).symm
  by_cases hAB : A = B
  · subst hAB
    rw [vsub_self] at h
    have : C = D := vsub_eq_zero_iff_eq.mp h.symm
    subst this; simp
  obtain ⟨E, hE⟩ := exists_third (by omega) hAB
  set F : P₁ := (B -ᵥ A) +ᵥ E with hF
  have hFE : F -ᵥ E = B -ᵥ A := by rw [hF]; simp
  have h1 := vec_nondeg hf hc hV₂ hE hFE
  have hDC : D ≠ C := by
    intro hDC
    rw [← hDC, vsub_self] at h
    exact hAB (vsub_eq_zero_iff_eq.mp h).symm
  have hDCE : ¬ Collinear ℝ ({D, C, E} : Set P₁) := by
    intro hcol
    apply hE
    obtain ⟨u, hu⟩ := exists_smul_of_collinear hDC hcol
    obtain ⟨d, hd⟩ := exists_smul_of_collinear hAB hABD
    refine collinear_of_vsub_smul (u + d) ?_
    have hu' : u • (B -ᵥ A) = E -ᵥ D := by rw [h, ← hu]
    rw [add_smul, ← hd, hu']
    exact (vsub_add_vsub_cancel E D A).symm
  have h2 := vec_nondeg hf hc hV₂ hDCE (show F -ᵥ E = C -ᵥ D by rw [hFE, h])
  rw [← h1, h2]

theorem collinear_swap_last (A B C : P₁) :
    Collinear ℝ ({A, B, C} : Set P₁) ↔ Collinear ℝ ({A, C, B} : Set P₁) := by
  rw [Set.pair_comm]

/-- **Fundamental theorem of affine geometry, in terms of collinearity.** A bijection between real
affine spaces of dimension `2` that preserves collinearity of triples is (the underlying map of) an
affine equivalence. -/
theorem exists_affineEquiv_of_collinear {f : P₁ → P₂} (hf : Function.Bijective f)
    (hc : PreservesCollinear f) (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) :
    ∃ g : P₁ ≃ᵃ[ℝ] P₂, ⇑g = f := by
  obtain ⟨O, X, Y, hnc⟩ := exists_frame (P := P₁) hV₁
  have hnc' : ¬ Collinear ℝ ({f O, f X, f Y} : Set P₂) := fun h => hnc ((hc _ _ _).mpr h)
  have hOX : O ≠ X := by rintro rfl; exact hnc (by simp [collinear_pair])
  have hOY : O ≠ Y := by
    rintro rfl; exact hnc (collinear_of_vsub_smul 0 (by simp))
  have hne1 : f X -ᵥ f O ≠ 0 := vsub_ne_zero.mpr (hf.1.ne hOX).symm
  have hne2 : f Y -ᵥ f O ≠ 0 := vsub_ne_zero.mpr (hf.1.ne hOY).symm
  let h : V₁ → V₂ := fun v => f (v +ᵥ O) -ᵥ f O
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    have := vsub_eq_of_preservesCollinear hf hc hV₁ hV₂ (A := O) (B := u +ᵥ O) (C := (u + v) +ᵥ O)
      (D := v +ᵥ O) (by simp)
    show f ((u + v) +ᵥ O) -ᵥ f O = (f (u +ᵥ O) -ᵥ f O) + (f (v +ᵥ O) -ᵥ f O)
    rw [this, vsub_add_vsub_cancel]
  have coef : ∀ Q : P₁, O ≠ Q → ∀ t : ℝ, ∃ c : ℝ, h (t • (Q -ᵥ O)) = c • (f Q -ᵥ f O) := by
    intro Q hOQ t
    have col : Collinear ℝ ({O, Q, t • (Q -ᵥ O) +ᵥ O} : Set P₁) :=
      collinear_of_vsub_smul t (by simp)
    exact exists_smul_of_collinear (hf.1.ne hOQ) ((hc _ _ _).mp col)
  choose c1 hc1 using coef X hOX
  choose c2 hc2 using coef Y hOY
  have c1add : ∀ s t, c1 (s + t) = c1 s + c1 t := by
    intro s t
    have := hc1 (s + t)
    rw [add_smul, hadd, hc1 s, hc1 t, ← add_smul] at this
    exact (smul_left_injective ℝ hne1 this).symm
  have c2add : ∀ s t, c2 (s + t) = c2 s + c2 t := by
    intro s t
    have := hc2 (s + t)
    rw [add_smul, hadd, hc2 s, hc2 t, ← add_smul] at this
    exact (smul_left_injective ℝ hne2 this).symm
  have c11 : c1 1 = 1 := by
    have := hc1 1
    simp only [h, one_smul, vsub_vadd] at this
    exact (smul_left_injective ℝ hne1 (by simpa using this.symm))
  have c21 : c2 1 = 1 := by
    have := hc2 1
    simp only [h, one_smul, vsub_vadd] at this
    exact (smul_left_injective ℝ hne2 (by simpa using this.symm))
  have c20 : c2 0 = 0 := by have := c2add 0 0; simp at this; linarith
  have c2sub : ∀ a b, c2 (a - b) = c2 a - c2 b := by
    intro a b; have := c2add (a - b) b; simp at this; linarith
  have mult : ∀ s t, c2 (t * s) = c1 s * c2 t := by
    intro s t
    by_cases ht : t = 0
    · subst ht; simp [c20]
    have col : Collinear ℝ ({(X -ᵥ O) +ᵥ O, t • (Y -ᵥ O) +ᵥ O,
        (s • (X -ᵥ O) + (t * (1 - s)) • (Y -ᵥ O)) +ᵥ O} : Set P₁) := by
      refine collinear_of_vsub_smul (1 - s) ?_
      rw [vadd_vsub_vadd_cancel_right, vadd_vsub_vadd_cancel_right]
      module
    have fcol := (hc _ _ _).mp col
    rw [vsub_vadd] at fcol
    have q2 : f (t • (Y -ᵥ O) +ᵥ O) -ᵥ f O = c2 t • (f Y -ᵥ f O) := hc2 t
    have q3 : f ((s • (X -ᵥ O) + (t * (1 - s)) • (Y -ᵥ O)) +ᵥ O) -ᵥ f O
        = c1 s • (f X -ᵥ f O) + c2 (t * (1 - s)) • (f Y -ᵥ f O) := by
      show h _ = _
      rw [hadd, hc1, hc2]
    have hne12 : f X ≠ f (t • (Y -ᵥ O) +ᵥ O) := by
      intro heq
      apply hnc'
      have : f X -ᵥ f O = c2 t • (f Y -ᵥ f O) := by rw [← q2, heq]
      rw [collinear_swap_last]
      exact collinear_of_vsub_smul (c2 t) this
    obtain ⟨l, hl⟩ := exists_smul_of_collinear hne12 fcol
    have hl' : (c1 s • (f X -ᵥ f O) + c2 (t * (1 - s)) • (f Y -ᵥ f O)) - (f X -ᵥ f O)
        = l • (c2 t • (f Y -ᵥ f O) - (f X -ᵥ f O)) := by
      rw [← q3, ← q2, vsub_sub_vsub_cancel_right, vsub_sub_vsub_cancel_right]
      exact hl
    obtain ⟨E1, E2⟩ := coord_eq hnc' (x := c1 s - 1) (y := c2 (t * (1 - s))) (x' := -l)
      (y' := l * c2 t) (by linear_combination (norm := module) hl')
    have e3 : t * (1 - s) = t - t * s := by ring
    rw [e3, c2sub] at E2
    linear_combination (-1 : ℝ) * E2 - c2 t * E1
  have c12 : ∀ s, c1 s = c2 s := by
    intro s; have := mult s 1; simp [c21] at this; exact this.symm
  let φ : ℝ →+* ℝ :=
    { toFun := c2
      map_one' := c21
      map_mul' := fun x y => by rw [mult y x, c12 y, mul_comm]
      map_zero' := c20
      map_add' := c2add }
  have hid2 : ∀ t, c2 t = t := fun t => RingHom.congr_fun (Subsingleton.elim φ (RingHom.id ℝ)) t
  have hid1 : ∀ t, c1 t = t := fun t => by rw [c12, hid2]
  have hform : ∀ x y : ℝ, h (x • (X -ᵥ O) + y • (Y -ᵥ O)) = x • (f X -ᵥ f O) + y • (f Y -ᵥ f O) := by
    intro x y; rw [hadd, hc1, hc2, hid1, hid2]
  have coords : ∀ v : V₁, ∃ x y : ℝ, v = x • (X -ᵥ O) + y • (Y -ᵥ O) := by
    intro v
    obtain ⟨x, y, hxy⟩ := exists_coords hV₁ hnc (v +ᵥ O)
    exact ⟨x, y, by simpa using hxy⟩
  let L : V₁ →ₗ[ℝ] V₂ :=
    { toFun := h
      map_add' := hadd
      map_smul' := by
        intro r v
        obtain ⟨x, y, rfl⟩ := coords v
        rw [smul_add, smul_smul, smul_smul, hform, hform]
        simp only [RingHom.id_apply]
        module }
  let g : P₁ →ᵃ[ℝ] P₂ :=
    { toFun := fun p => L (p -ᵥ O) +ᵥ f O
      linear := L
      map_vadd' := by
        intro p v
        simp only [vadd_vsub_assoc, map_add, add_vadd] }
  have hg : ⇑g = f := by
    funext p
    show h (p -ᵥ O) +ᵥ f O = f p
    simp [h]
  exact ⟨AffineEquiv.ofBijective (φ := g) (hg ▸ hf), by
    funext p
    rw [AffineEquiv.ofBijective_apply]
    exact congrFun hg p⟩

/-- **Exercise 14.4, first part.** A bijection of planes sending collinear triples to collinear triples
sends non-collinear triples to non-collinear triples: if `f A, f B, f C` are collinear then so are `A, B, C`.
Proof: otherwise everything is in the span of `A, B, C`, and the images of the lines `AB`, `AC` lie on the
line `f A f B`; every point is the midpoint of a point on `AB` and a point on `AC`; so the image of `f`
lies on a line, contradicting surjectivity. -/
theorem reflect_collinear {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) (A B C : P₁)
    (h : Collinear ℝ ({f A, f B, f C} : Set P₂)) : Collinear ℝ ({A, B, C} : Set P₁) := by
  by_contra hn
  have hAB : A ≠ B := by
    rintro rfl; exact hn (by simp [collinear_pair])
  have hAC : A ≠ C := by
    rintro rfl; exact hn (collinear_of_vsub_smul 0 (by simp))
  have hfAB : f A ≠ f B := hf.1.ne hAB
  have hfAC : f A ≠ f C := hf.1.ne hAC
  have hfC : f C ∈ line[ℝ, f A, f B] := h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hfAB
  have key1 : ∀ W, Collinear ℝ ({A, B, W} : Set P₁) → f W ∈ line[ℝ, f A, f B] := fun W hW =>
    (hfwd _ _ _ hW).mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hfAB
  have key2 : ∀ W, Collinear ℝ ({A, C, W} : Set P₁) → f W ∈ line[ℝ, f A, f B] := fun W hW =>
    affineSpan_pair_le_of_mem_of_mem (left_mem_affineSpan_pair _ _ _) hfC
      ((hfwd _ _ _ hW).mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hfAC)
  have hall : ∀ Z : P₁, f Z ∈ line[ℝ, f A, f B] := by
    intro Z
    obtain ⟨x, y, hxy⟩ := exists_coords hV₁ hn Z
    have hUA : ((2 * x) • (B -ᵥ A) +ᵥ A) -ᵥ A = (2 * x) • (B -ᵥ A) := vadd_vsub _ _
    have hVA : ((2 * y) • (C -ᵥ A) +ᵥ A) -ᵥ A = (2 * y) • (C -ᵥ A) := vadd_vsub _ _
    generalize hU' : (2 * x) • (B -ᵥ A) +ᵥ A = U at hUA
    generalize hV' : (2 * y) • (C -ᵥ A) +ᵥ A = V at hVA
    have hU : f U ∈ line[ℝ, f A, f B] :=
      key1 U (collinear_of_vsub_smul (2 * x) (by rw [← hU', vadd_vsub]))
    have hV : f V ∈ line[ℝ, f A, f B] :=
      key2 V (collinear_of_vsub_smul (2 * y) (by rw [← hV', vadd_vsub]))
    have hZ : Z -ᵥ U = (1 / 2 : ℝ) • (V -ᵥ U) := by
      rw [← vsub_sub_vsub_cancel_right Z U A, ← vsub_sub_vsub_cancel_right V U A, hUA, hVA, hxy]
      module
    by_cases hUV : U = V
    · have h0 : Z -ᵥ U = 0 := by rw [hZ, hUV, vsub_self, smul_zero]
      rw [vsub_eq_zero_iff_eq.mp h0]; exact hU
    · have col : Collinear ℝ ({U, V, Z} : Set P₁) := collinear_of_vsub_smul (1 / 2) hZ
      have := (hfwd _ _ _ col).mem_affineSpan_of_mem_of_ne (p₁ := f U) (p₂ := f V) (p₃ := f Z)
        (by simp) (by simp) (by simp) (hf.1.ne hUV)
      exact affineSpan_pair_le_of_mem_of_mem hU hV this
  obtain ⟨O', X', Y', hO'⟩ := exists_frame (P := P₂) hV₂
  obtain ⟨a, rfl⟩ := hf.2 O'
  obtain ⟨b, rfl⟩ := hf.2 X'
  obtain ⟨c, rfl⟩ := hf.2 Y'
  exact hO' (collinear_triple_of_mem_affineSpan_pair (hall a) (hall b) (hall c))

end Core

section Final

variable {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂]

/-- An affine transformation (in the book's sense) maps collinear triples to collinear triples. -/
theorem collinear_of_isAffineTransformation {f : P₁ → P₂} (hf : SendsLinesToLines f) (A B C : P₁)
    (h : Collinear ℝ ({A, B, C} : Set P₁)) : Collinear ℝ ({f A, f B, f C} : Set P₂) := by
  by_cases hAB : A = B
  · subst hAB; simp [collinear_pair]
  have hC : C ∈ line[ℝ, A, B] := h.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAB
  obtain ⟨p', q', -, himg⟩ := hf A B hAB
  have hmem : ∀ w ∈ line[ℝ, A, B], f w ∈ line[ℝ, p', q'] := fun w hw => by
    have : f w ∈ f '' (line[ℝ, A, B] : Set P₁) := ⟨w, hw, rfl⟩
    rw [himg] at this; exact this
  exact collinear_triple_of_mem_affineSpan_pair (hmem A (left_mem_affineSpan_pair _ _ _))
    (hmem B (right_mem_affineSpan_pair _ _ _)) (hmem C hC)

/-- **Exercise 14.4** (Petrunin, p. 115), first part: if a bijection of planes maps collinear triples to
collinear triples then it maps noncollinear triples to noncollinear ones. -/
@[kb "petrunin2025" "Exercise 14.4, p. 115"]
theorem noncollinear_of_collinear_preserving {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) {A B C : P₁}
    (h : ¬ Collinear ℝ ({A, B, C} : Set P₁)) : ¬ Collinear ℝ ({f A, f B, f C} : Set P₂) :=
  fun hc => h (reflect_collinear hf hfwd hV₁ hV₂ A B C hc)

theorem preservesCollinear_of_collinear_preserving {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) : PreservesCollinear f :=
  fun A B C => ⟨hfwd A B C, reflect_collinear hf hfwd hV₁ hV₂ A B C⟩

/-- The second part of **Exercise 14.4**: a bijection mapping collinear triples to collinear triples
maps lines onto lines, so it is an affine transformation in the book's sense. -/
@[kb "petrunin2025" "Exercise 14.4, p. 115"]
theorem isAffineTransformation_of_collinear_preserving {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) : IsAffineTransformation f := by
  have hc := preservesCollinear_of_collinear_preserving hf hfwd hV₁ hV₂
  refine ⟨hf, fun p q hpq => ⟨f p, f q, hf.1.ne hpq, ?_⟩⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : Collinear ℝ ({p, q, w} : Set P₁) := (collinear_insert_of_mem_affineSpan_pair hw).subset
      (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
    exact (hfwd _ _ _ this).mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (hf.1.ne hpq)
  · intro hz
    obtain ⟨w, rfl⟩ := hf.2 z
    refine ⟨w, ?_, rfl⟩
    have hcol : Collinear ℝ ({f p, f q, f w} : Set P₂) :=
      (collinear_insert_of_mem_affineSpan_pair hz).subset
        (by intro x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
    exact ((hc _ _ _).mpr hcol).mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq

/-- A line-preserving bijection preserves collinearity of triples in both directions. -/
theorem preservesCollinear_of_isAffineTransformation {f : P₁ → P₂} (hf : IsAffineTransformation f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) : PreservesCollinear f :=
  preservesCollinear_of_collinear_preserving hf.1 (collinear_of_isAffineTransformation hf.2) hV₁ hV₂

/-- **Exercise 14.4 (conclusion): a bijection of planes mapping collinear triples to collinear triples is an
affine map**, that is, the underlying map of an `AffineEquiv`. -/
@[kb "petrunin2025" "Exercise 14.4, p. 115"]
theorem exists_affineEquiv_of_collinear_preserving {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) :
    ∃ g : P₁ ≃ᵃ[ℝ] P₂, ⇑g = f :=
  exists_affineEquiv_of_collinear hf (preservesCollinear_of_collinear_preserving hf hfwd hV₁ hV₂) hV₁ hV₂

/-- **Fundamental theorem of affine geometry, first form** (Petrunin, Theorem 14.12 together with the
conclusion of 14.11): every affine transformation (a bijection sending lines to lines) of a real affine
plane is the underlying map of an `AffineEquiv`, i.e. has the coordinate form `x ↦ L x + r`. -/
@[kb "petrunin2025" "Theorem 14.12, p. 117"]
theorem fundamental_affine {f : P₁ → P₂} (hf : IsAffineTransformation f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) : ∃ g : P₁ ≃ᵃ[ℝ] P₂, ⇑g = f :=
  exists_affineEquiv_of_collinear hf.1 (preservesCollinear_of_isAffineTransformation hf hV₁ hV₂) hV₁ hV₂

/-- **Theorem 14.12 in the book's coordinate form.** An affine transformation of the plane maps a
nondegenerate triangle `OXY` to a nondegenerate triangle `O'X'Y'`, and `OP = x·OX + y·OY` holds if and only
if `O'P' = x·O'X' + y·O'Y'`. -/
@[kb "petrunin2025" "Theorem 14.12, p. 117"]
theorem fundamental_affine_coords {f : P₁ → P₂} (hf : IsAffineTransformation f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) {O X Y : P₁}
    (hOXY : ¬ Collinear ℝ ({O, X, Y} : Set P₁)) :
    ¬ Collinear ℝ ({f O, f X, f Y} : Set P₂) ∧ ∀ (P : P₁) (x y : ℝ),
      P -ᵥ O = x • (X -ᵥ O) + y • (Y -ᵥ O) ↔ f P -ᵥ f O = x • (f X -ᵥ f O) + y • (f Y -ᵥ f O) := by
  refine ⟨fun hc => hOXY ((preservesCollinear_of_isAffineTransformation hf hV₁ hV₂ _ _ _).mpr hc), ?_⟩
  obtain ⟨g, rfl⟩ := fundamental_affine hf hV₁ hV₂
  intro P x y
  rw [← affineEquiv_linear_vsub, ← affineEquiv_linear_vsub, ← affineEquiv_linear_vsub]
  rw [← map_smul, ← map_smul, ← map_add]
  exact g.linear.injective.eq_iff.symm

/-- **Fundamental theorem of affine geometry in the Euclidean plane `ℝ²`** (Petrunin, Theorem 14.12): a
bijection of `EuclideanSpace ℝ (Fin 2)` that maps lines onto lines is an affine equivalence. -/
@[kb "petrunin2025" "Theorem 14.12, p. 117"]
theorem fundamental_affine_plane {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hf : IsAffineTransformation f) :
    ∃ g : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2), ⇑g = f :=
  fundamental_affine hf (finrank_euclideanSpace_fin) (finrank_euclideanSpace_fin)

/-- **Exercise 14.10** (Petrunin, p. 116) for line-preserving bijections: they map parallelograms to
parallelograms (in both directions). -/
@[kb "petrunin2025" "Exercise 14.10, p. 116"]
theorem affineTransformation_parallelogram {f : P₁ → P₂} (hf : IsAffineTransformation f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) (A B C D : P₁) :
    IsVectorParallelogram (f A) (f B) (f C) (f D) ↔ IsVectorParallelogram A B C D := by
  obtain ⟨g, rfl⟩ := fundamental_affine hf hV₁ hV₂
  exact affineEquiv_parallelogram g A B C D

/-- **Exercise 14.10** (Petrunin, p. 116), second part, for line-preserving bijections: `XY = AB` as
vectors if and only if `X'Y' = A'B'`. -/
@[kb "petrunin2025" "Exercise 14.10, p. 116"]
theorem affineTransformation_vsub_eq_iff {f : P₁ → P₂} (hf : IsAffineTransformation f)
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) (X Y A B : P₁) :
    Y -ᵥ X = B -ᵥ A ↔ f Y -ᵥ f X = f B -ᵥ f A := by
  obtain ⟨g, rfl⟩ := fundamental_affine hf hV₁ hV₂
  exact affineEquiv_vsub_eq_iff' g X Y A B

end Final

section ConstructAngle

open EuclideanGeometry Module Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- The point `C_θ` of Petrunin's Proposition 3.19: the point at distance `r` from `B` obtained by turning the
ray `BA` by the oriented angle `θ` in the positive direction. -/
noncomputable def pointAtAngle (A B : P) (r : ℝ) (θ : Real.Angle) : P :=
  (positiveOrientation.rotation θ ((r / ‖A -ᵥ B‖) • (A -ᵥ B))) +ᵥ B

omit [Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
theorem norm_scaled_vsub {A B : P} (hAB : A ≠ B) {r : ℝ} (hr : 0 < r) :
    ‖(r / ‖A -ᵥ B‖) • (A -ᵥ B)‖ = r := by
  have hw : 0 < ‖A -ᵥ B‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hAB)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hw)]
  field_simp

theorem dist_pointAtAngle {A B : P} (hAB : A ≠ B) {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    dist B (pointAtAngle A B r θ) = r := by
  rw [dist_comm, pointAtAngle, dist_vadd_left, LinearIsometryEquiv.norm_map, norm_scaled_vsub hAB hr]

theorem oangle_pointAtAngle {A B : P} (hAB : A ≠ B) {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    ∡ A B (pointAtAngle A B r θ) = θ := by
  have hw : 0 < ‖A -ᵥ B‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hAB)
  have hx : (r / ‖A -ᵥ B‖) • (A -ᵥ B) ≠ 0 := by
    intro h
    have := norm_scaled_vsub hAB hr
    rw [h, norm_zero] at this
    exact hr.ne this
  rw [EuclideanGeometry.oangle, pointAtAngle, vadd_vsub,
    ← positiveOrientation.oangle_smul_left_of_pos (A -ᵥ B) _ (div_pos hr hw)]
  exact Orientation.oangle_rotation_self_right _ hx θ

theorem eq_pointAtAngle {A B C : P} (hAB : A ≠ B) {r : ℝ} (hr : 0 < r) {θ : Real.Angle}
    (hd : dist B C = r) (ha : ∡ A B C = θ) : C = pointAtAngle A B r θ := by
  have hw : 0 < ‖A -ᵥ B‖ := norm_pos_iff.mpr (vsub_ne_zero.mpr hAB)
  have hnorm : ‖C -ᵥ B‖ = r := by rw [← hd, dist_comm, dist_eq_norm_vsub V]
  have hx := norm_scaled_vsub hAB hr
  have hang : positiveOrientation.oangle ((r / ‖A -ᵥ B‖) • (A -ᵥ B)) (C -ᵥ B) = θ := by
    rw [positiveOrientation.oangle_smul_left_of_pos _ _ (div_pos hr hw)]; exact ha
  have := (Orientation.rotation_oangle_eq_iff_norm_eq positiveOrientation
    ((r / ‖A -ᵥ B‖) • (A -ᵥ B)) (C -ᵥ B)).mpr (by rw [hx, hnorm])
  rw [hang] at this
  rw [pointAtAngle, this, vsub_vadd]

/-- **Proposition 3.19** (Petrunin, p. 29), full form. Let `r > 0`, `A ≠ B` and `β ∈ [0, π]`. Then there is
exactly one point `C` with `BC = r`, unsigned angle `∠ABC = β` lying on the positive side of the ray
`BA` (that is, the oriented angle is `∡ABC = β`). The oriented-angle condition already forces uniqueness. -/
@[kb "petrunin2025" "Proposition 3.19, p. 29"]
theorem existsUnique_point_dist_angle {A B : P} (hAB : A ≠ B) {r β : ℝ} (hr : 0 < r) (h0 : 0 ≤ β)
    (hπ : β ≤ π) :
    ∃! C : P, (dist B C = r ∧ ∠ A B C = β) ∧ ∡ A B C = (β : Real.Angle) := by
  refine ⟨pointAtAngle A B r β, ⟨⟨dist_pointAtAngle hAB hr _, ?_⟩, oangle_pointAtAngle hAB hr _⟩,
    fun C hC => eq_pointAtAngle hAB hr hC.1.1 hC.2⟩
  have hC : pointAtAngle A B r β ≠ B := by
    intro h
    have := dist_pointAtAngle hAB hr (β : Real.Angle)
    rw [h, dist_self] at this
    exact hr.ne this
  rw [angle_eq_abs_oangle_toReal hAB hC, oangle_pointAtAngle hAB hr,
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], hπ⟩, abs_of_nonneg h0]

/-- **Proposition 3.19, continuity part**: the point `C_β` depends continuously on the angle `β`. -/
@[kb "petrunin2025" "Proposition 3.19, p. 29"]
theorem continuous_pointAtAngle (A B : P) (r : ℝ) :
    Continuous fun β : ℝ => pointAtAngle A B r (β : Real.Angle) := by
  simp only [pointAtAngle, Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
  fun_prop

end ConstructAngle

end UndergradKB.Geometry
