import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection
import UndergradKB.Geometry.InversivePlane
import UndergradKB.Geometry.AffineFundamental
import UndergradKB.Geometry.Motions
import UndergradKB.Common.Attr

/-! # Classification of inversive transformations (Petrunin, Exercise 14.16, p. 117)

Every inversive transformation of the inversive plane `OnePoint P` (a bijection mapping circlines
onto circlines, see `IsInversiveTransformation`) is a finite composition of extended inversions and
extended reflections across lines. The proof follows the hint of the book: after composing with an
inversion centred at the image of `∞` we may assume `∞` is fixed; then lines (circlines through `∞`)
go to lines, so the map is affine (fundamental theorem of affine geometry, `fundamental_affine`),
and circles go to circles, which forces the linear part to scale all lengths by one constant, i.e. the
map is a similarity. A similarity is an isometry (a product of at most three reflections,
`motion_eq_prod_reflections`) after a homothety, and a homothety is a product of two inversions with
the same centre. -/

namespace UndergradKB.Geometry

open EuclideanGeometry Metric OnePoint
open scoped RealInnerProductSpace

variable (V : Type*) (P : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The generators: extended inversions (positive radius) and extended reflections across lines
(perpendicular bisectors of two distinct points). -/
def inversiveGenerators : Set (Equiv.Perm (OnePoint P)) :=
  {g | (∃ (c : P) (R : ℝ) (h : 0 < R), g = inversionEquiv c R h.ne') ∨
    ∃ a b : P, a ≠ b ∧ g = extendEquiv (reflection (AffineSubspace.perpBisector a b))}

variable {V P}

theorem inversionEquiv_apply {c : P} {R : ℝ} (hR : R ≠ 0) (z : OnePoint P) :
    inversionEquiv c R hR z = inversionOP c R z := rfl

theorem extendEquiv_apply (e : P ≃ᵃⁱ[ℝ] P) (z : OnePoint P) : extendEquiv e z = extendOP e z := rfl

theorem extendOP_comp (f h : P → P) (z : OnePoint P) :
    extendOP (f ∘ h) z = extendOP f (extendOP h z) := by
  induction z using OnePoint.rec <;> rfl

theorem extendEquiv_prod (L : List (P ≃ᵃⁱ[ℝ] P)) (z : OnePoint P) :
    ((L.map extendEquiv).prod : Equiv.Perm (OnePoint P)) z = extendOP (⇑L.prod) z := by
  induction L generalizing z with
  | nil =>
    induction z using OnePoint.rec <;> simp [extendOP]
  | cons r L ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih, List.prod_cons,
      AffineIsometryEquiv.coe_mul, extendOP_comp]
    rfl

theorem hypOP_injective {A B : Set P} (h : hypOP A = hypOP B) : A = B := by
  ext x
  have := Set.ext_iff.mp h (x : OnePoint P)
  rwa [mem_hypOP_coe, mem_hypOP_coe] at this

section Reduction

theorem exists_map_of_fix_infty {G : Equiv.Perm (OnePoint P)} (hinf : G ∞ = ∞) :
    ∃ g : P → P, Function.Bijective g ∧ ∀ z, G z = extendOP g z := by
  have hne : ∀ x : P, G x ≠ ∞ := fun x h => coe_ne_infty x (G.injective (h.trans hinf.symm))
  choose g hg using fun x => OnePoint.ne_infty_iff_exists.mp (hne x)
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    have : G x = G y := by rw [← hg x, ← hg y, hxy]
    exact coe_injective (G.injective this)
  · intro y
    have hy : G.symm y ≠ ∞ := fun h => by
      have := congrArg G h
      rw [Equiv.apply_symm_apply, hinf] at this
      exact coe_ne_infty y this
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hy
    refine ⟨x, coe_injective ?_⟩
    rw [hg x, hx, Equiv.apply_symm_apply]
  · intro z
    induction z using OnePoint.rec with
    | infty => simp [extendOP, hinf]
    | coe x => simp [extendOP, hg x]

theorem sendsLinesToLines_of_inversive {G : Equiv.Perm (OnePoint P)} {g : P → P}
    (hG : IsInversiveTransformation V G) (hz : ∀ z, G z = extendOP g z) :
    SendsLinesToLines g := by
  intro p q hpq
  have hS : IsCircline V (hypOP ((line[ℝ, p, q] : AffineSubspace ℝ P) : Set P)) :=
    Or.inr ⟨p, q, hpq, rfl⟩
  have h1 := hG.1 _ hS
  have hGe : ⇑G = extendOP g := funext hz
  rw [hGe, extendOP_image_hypOP] at h1
  obtain ⟨p', q', hne, heq⟩ := (h1.infty_mem_iff).mp (infty_mem_hypOP _)
  exact ⟨p', q', hne, hypOP_injective heq⟩

theorem circles_of_inversive {G : Equiv.Perm (OnePoint P)} {g : P → P}
    (hG : IsInversiveTransformation V G) (hz : ∀ z, G z = extendOP g z) (Q : P) {s : ℝ}
    (hs : 0 < s) : ∃ (Q' : P) (s' : ℝ), 0 < s' ∧ g '' sphere Q s = sphere Q' s' := by
  have hS : IsCircline V (circOP Q s) := Or.inl ⟨Q, s, hs, rfl⟩
  have h1 := hG.1 _ hS
  have hGe : ⇑G = extendOP g := funext hz
  have himg : extendOP g '' circOP Q s = (fun x : P => (x : OnePoint P)) '' (g '' sphere Q s) :=
    extendOP_image_coe g _
  rw [hGe, himg] at h1
  have hnot : ¬ IsLineOP V ((fun x : P => (x : OnePoint P)) '' (g '' sphere Q s)) := by
    intro hl
    obtain ⟨y, _, hy⟩ := (h1.infty_mem_iff).mpr hl
    exact coe_ne_infty y hy
  rcases h1 with ⟨Q', s', hs', heq⟩ | hl
  · refine ⟨Q', s', hs', ?_⟩
    exact Set.image_injective.mpr coe_injective heq
  · exact absurd hl hnot

end Reduction

section Similarity

/-- An affine bijection of the plane mapping circles to circles scales all lengths by a constant. -/
theorem exists_const_norm_linear (A : P ≃ᵃ[ℝ] P)
    (h : ∀ (Q : P) (s : ℝ), 0 < s → ∃ (Q' : P) (s' : ℝ), 0 < s' ∧ A '' sphere Q s = sphere Q' s') :
    ∃ k : ℝ, 0 < k ∧ ∀ v : V, ‖A.linear v‖ = k * ‖v‖ := by
  obtain ⟨Q', s', hs', himg⟩ := h (Classical.arbitrary P) 1 one_pos
  set Q0 : P := Classical.arbitrary P
  set m : V := A Q0 -ᵥ Q' with hm
  have hmem : ∀ u : V, ‖u‖ = 1 → ‖A.linear u + m‖ = s' := by
    intro u hu
    have h1 : u +ᵥ Q0 ∈ sphere Q0 (1 : ℝ) := by
      rw [Metric.mem_sphere, dist_vadd_left, hu]
    have h2 : A (u +ᵥ Q0) ∈ sphere Q' s' := himg ▸ Set.mem_image_of_mem _ h1
    rw [Metric.mem_sphere, dist_eq_norm_vsub V, A.map_vadd, vadd_vsub_assoc] at h2
    exact h2
  have horth : ∀ v : V, ⟪A.linear v, m⟫ = 0 := by
    have hu : ∀ u : V, ‖u‖ = 1 → ⟪A.linear u, m⟫ = 0 := by
      intro u hu
      have a1 := hmem u hu
      have a2 := hmem (-u) (by rw [norm_neg, hu])
      rw [map_neg] at a2
      have b1 := congrArg (· ^ 2) a1
      have b2 := congrArg (· ^ 2) a2
      simp only [norm_add_sq_real, norm_neg, inner_neg_left] at b1 b2
      linarith
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hu1 : ‖(‖v‖⁻¹) • v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have := hu _ hu1
      rw [map_smul, inner_smul_left] at this
      simpa [hn] using this
  have hm0 : m = 0 := by
    have := horth (A.linear.symm m)
    rw [LinearEquiv.apply_symm_apply] at this
    exact inner_self_eq_zero.mp this
  have hu' : ∀ u : V, ‖u‖ = 1 → ‖A.linear u‖ = s' := by
    intro u hu
    have := hmem u hu
    rwa [hm0, add_zero] at this
  refine ⟨s', hs', fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu1 : ‖(‖v‖⁻¹) • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have := hu' _ hu1
    rw [map_smul, norm_smul, norm_inv, norm_norm] at this
    field_simp at this
    linarith

/-- A homothety with centre `O` and ratio `k > 0` is the product of two inversions centred at `O`
(radii `1` and `√k`), on the inversive plane. -/
theorem inversionOP_homothety (O : P) {k : ℝ} (hk : 0 < k) (z : OnePoint P) :
    inversionOP O (Real.sqrt k) (inversionOP O 1 z) =
      extendOP (fun x : P => k • (x -ᵥ O) +ᵥ O) z := by
  induction z using OnePoint.rec with
  | infty => simp [extendOP]
  | coe x =>
    by_cases hx : x = O
    · subst hx; simp [extendOP]
    · have hd : 0 < dist x O := dist_pos.mpr hx
      have hy : inversion O 1 x ≠ O := by simpa [inversion_eq_center one_ne_zero] using hx
      rw [inversionOP_coe_of_ne hx, inversionOP_coe_of_ne hy]
      show ((inversion O (Real.sqrt k) (inversion O 1 x) : P) : OnePoint P) = _
      congr 1
      rw [inversion, dist_inversion_center, inversion_vsub_center, smul_smul]
      congr 2
      have hs : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
      rw [div_pow, div_pow, div_pow, hs]
      field_simp

end Similarity

section Main

variable [Fact (Module.finrank ℝ V = 2)]

theorem mem_closure_of_fix_infty {G : Equiv.Perm (OnePoint P)}
    (hG : IsInversiveTransformation V G) (hinf : G ∞ = ∞) :
    G ∈ Subgroup.closure (inversiveGenerators V P) := by
  obtain ⟨g, hgb, hz⟩ := exists_map_of_fix_infty hinf
  have hsl := sendsLinesToLines_of_inversive hG hz
  obtain ⟨A, hA⟩ := fundamental_affine (V₁ := V) (V₂ := V) ⟨hgb, hsl⟩ Fact.out Fact.out
  subst hA
  obtain ⟨k, hk, hkv⟩ := exists_const_norm_linear A (fun Q s hs => circles_of_inversive hG hz Q hs)
  haveI : Module.Oriented ℝ V (Fin 2) :=
    ⟨(Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2)).orientation⟩
  set O : P := Classical.arbitrary P with hO
  let hU : P ≃ᵃ[ℝ] P := AffineEquiv.homothetyUnitsMulHom O (Units.mk0 k⁻¹ (inv_ne_zero hk.ne'))
  have hUx : ∀ x, hU x = k⁻¹ • (x -ᵥ O) +ᵥ O := fun x => by
    show AffineMap.homothety O k⁻¹ x = _
    rfl
  let Φ : P ≃ᵃ[ℝ] P := hU.trans A
  have hΦ : ∀ x y, dist (Φ x) (Φ y) = dist x y := by
    intro x y
    have e1 : Φ x -ᵥ Φ y = A.linear (hU x -ᵥ hU y) := by
      show A (hU x) -ᵥ A (hU y) = _
      exact (A.toAffineMap.linear_apply_vsub _ _).symm
    have e2 : hU x -ᵥ hU y = k⁻¹ • (x -ᵥ y) := by
      rw [hUx, hUx, vadd_vsub_vadd_cancel_right, ← smul_sub, vsub_sub_vsub_cancel_right]
    rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, e1, e2, hkv, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos hk]
    field_simp
  let φ : P ≃ᵢ P := { toEquiv := Φ.toEquiv, isometry_toFun := Isometry.of_dist_eq hΦ }
  obtain ⟨L, -, hLr, hLx⟩ := motion_eq_prod_reflections φ
  have hAx : ∀ x, A x = L.prod (k • (x -ᵥ O) +ᵥ O) := by
    intro x
    rw [← hLx]
    show A x = A (hU (k • (x -ᵥ O) +ᵥ O))
    rw [hUx, vadd_vsub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul, vsub_vadd]
  have hfun : ⇑A = ⇑L.prod ∘ (fun x : P => k • (x -ᵥ O) +ᵥ O) := funext hAx
  have hPmem : (L.map extendEquiv).prod ∈ Subgroup.closure (inversiveGenerators V P) := by
    refine Subgroup.list_prod_mem _ ?_
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
    obtain ⟨a, b, hab, rfl⟩ := hLr r hr
    exact Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)
  have hι1 : inversionEquiv O 1 one_pos.ne' ∈ Subgroup.closure (inversiveGenerators V P) :=
    Subgroup.subset_closure (Or.inl ⟨O, 1, one_pos, rfl⟩)
  have hι2 : inversionEquiv O (Real.sqrt k) (Real.sqrt_pos.2 hk).ne' ∈
      Subgroup.closure (inversiveGenerators V P) :=
    Subgroup.subset_closure (Or.inl ⟨O, Real.sqrt k, Real.sqrt_pos.2 hk, rfl⟩)
  have hG' : G = (L.map extendEquiv).prod * inversionEquiv O (Real.sqrt k) (Real.sqrt_pos.2 hk).ne' *
      inversionEquiv O 1 one_pos.ne' := by
    ext z
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inversionEquiv_apply, inversionEquiv_apply,
      inversionOP_homothety O hk, extendEquiv_prod, ← extendOP_comp, ← hfun, hz]
  rw [hG']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hPmem hι2) hι1

/-- **Petrunin, Exercise 14.16 (advanced)**: every inversive transformation of the inversive plane
is a finite composition of inversions (extended by exchanging the centre and `∞`) and reflections
across lines (extended by `∞ ↦ ∞`); more precisely it lies in the subgroup of permutations of
`OnePoint P` generated by these (the generators are involutions, so this subgroup consists of finite
compositions of generators). -/
@[kb "petrunin2025" "Exercise 14.16, p. 117"]
theorem inversiveTransformation_mem_closure {F : Equiv.Perm (OnePoint P)}
    (hF : IsInversiveTransformation V F) : F ∈ Subgroup.closure (inversiveGenerators V P) := by
  by_cases h : F ∞ = ∞
  · exact mem_closure_of_fix_infty hF h
  · obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp h
    have hι : IsInversiveTransformation V (inversionEquiv a 1 one_pos.ne') :=
      isInversiveTransformation_inversionEquiv one_pos
    have hG : IsInversiveTransformation V (inversionEquiv a 1 one_pos.ne' * F) := hF.trans hι
    have hinf : (inversionEquiv a 1 one_pos.ne' * F) ∞ = ∞ := by
      rw [Equiv.Perm.mul_apply, inversionEquiv_apply, ← ha]
      simp
    have hmem : inversionEquiv a 1 one_pos.ne' ∈ Subgroup.closure (inversiveGenerators V P) :=
      Subgroup.subset_closure (Or.inl ⟨a, 1, one_pos, rfl⟩)
    have hF' : F = inversionEquiv a 1 one_pos.ne' * (inversionEquiv a 1 one_pos.ne' * F) := by
      ext z
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inversionEquiv_apply, inversionEquiv_apply,
        inversionOP_involutive one_pos.ne']
    rw [hF']
    exact Subgroup.mul_mem _ hmem (mem_closure_of_fix_infty hG hinf)

/-- The converse: the generators, hence everything they generate, are inversive transformations. -/
theorem isInversiveTransformation_of_mem_closure {F : Equiv.Perm (OnePoint P)}
    (hF : F ∈ Subgroup.closure (inversiveGenerators V P)) : IsInversiveTransformation V F := by
  let S : Subgroup (Equiv.Perm (OnePoint P)) :=
    { carrier := {F | IsInversiveTransformation V F}
      one_mem' := IsInversiveTransformation.refl
      mul_mem' := fun {f g} hf hg => hg.trans hf
      inv_mem' := fun {f} hf => hf.symm }
  have : Subgroup.closure (inversiveGenerators V P) ≤ S := by
    rw [Subgroup.closure_le]
    rintro g (⟨c, R, h, rfl⟩ | ⟨a, b, -, rfl⟩)
    · exact isInversiveTransformation_inversionEquiv h
    · exact isInversiveTransformation_extendEquiv _
  exact this hF

/-- Exercise 14.16 together with its converse: the inversive transformations are exactly the
elements of the group generated by the extended inversions and reflections. -/
@[kb "petrunin2025" "Exercise 14.16, p. 117"]
theorem isInversiveTransformation_iff_mem_closure {F : Equiv.Perm (OnePoint P)} :
    IsInversiveTransformation V F ↔ F ∈ Subgroup.closure (inversiveGenerators V P) :=
  ⟨inversiveTransformation_mem_closure, isInversiveTransformation_of_mem_closure⟩

end Main

end UndergradKB.Geometry
