import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Geometry.Spherical2
import UndergradKB.Common.Attr

/-! # The converse of Petrunin's Lemma 16.9 (chapter 16, p. 136)

Lemma 16.9 says: a set `Σ` with two points is a sphere iff every plane through a fixed point `O` meets it
in `∅`, a point or a circle. The "only if" direction is `plane_inter_sphere` (in `Spherical2`). This file
proves the converse (with `O` the origin, planes = linear subspaces,
circles as in `IsCircleIn`):

* `isCircleIn_quadratic`: a circle in a plane `W` is the zero set in `W` of `‖x‖² - 2⟪a,x⟫ + k` with `a ∈ W`,
  `‖a‖² - k > 0` (`k` is the power of `O`).
* `quadratic_params_eq`: two such quadratics along a line with the same (nonempty) real zero set agree.
* `circle_planes_agree`: two circle sections of `Σ` by planes through a common line which meets `Σ` have the
  same power `k` and the same `⟪a,u⟫` along the line.

* `circle_three_indep`, `circle_subset_sphere` ("key fact F"): a circle in a plane that shares three distinct
  points with a sphere lies on that sphere.

* `exists_point_near` (the perturbation step), `SphereData.step3`, `SphereData.off_plane`,
  `exists_sphereData`: the proof of the converse, following the sketch: a base circle `C₀` in a plane,
  a point `Z` off the plane, the sphere `S` through `C₀` and `Z`, and the comparison of `Σ` and `S` on
  planes `span(u', Z)` for secant directions `u'` of `C₀`.
* `sphere_of_plane_sections` (**Lemma 16.9, direction "if"**), `sphere_iff_plane_sections`
  (both directions), and `sphere_of_plane_sections_at` (arbitrary `O`). -/

namespace UndergradKB.Geometry

open RealInnerProductSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A circle in the plane `W` is the zero set in `W` of the quadratic `‖x‖² - 2⟪a,x⟫ + k`, with `a ∈ W`
and `‖a‖² - k > 0`. -/
theorem isCircleIn_quadratic {W : Submodule ℝ E3} {S : Set E3} (h : IsCircleIn W S) :
    ∃ a ∈ W, ∃ k : ℝ, 0 < ‖a‖ ^ 2 - k ∧
      ∀ x, x ∈ S ↔ x ∈ W ∧ ‖x‖ ^ 2 - 2 * ⟪a, x⟫ + k = 0 := by
  obtain ⟨c, hc, r, hr, rfl⟩ := h
  refine ⟨c, hc, ‖c‖ ^ 2 - r ^ 2, by nlinarith, fun x => ?_⟩
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  rw [dist_eq_norm]
  have h1 : ‖x - c‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, c⟫ + ‖c‖ ^ 2 := norm_sub_sq_real x c
  rw [real_inner_comm c x] at h1
  constructor
  · intro h; rw [h] at h1; nlinarith
  · intro h
    have h2 : ‖x - c‖ ^ 2 = r ^ 2 := by nlinarith
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp h2

/-- Two monic-up-to-`q` real quadratics `q t² - 2 b t + k` (`q ≠ 0`) with the same real zero set, which is
nonempty, have the same coefficients. -/
theorem quadratic_params_eq {q b₁ b₂ k₁ k₂ t₀ : ℝ} (hq : q ≠ 0)
    (h₁ : q * t₀ ^ 2 - 2 * b₁ * t₀ + k₁ = 0) (h₂ : q * t₀ ^ 2 - 2 * b₂ * t₀ + k₂ = 0)
    (hset : ∀ t, q * t ^ 2 - 2 * b₁ * t + k₁ = 0 ↔ q * t ^ 2 - 2 * b₂ * t + k₂ = 0) :
    b₁ = b₂ ∧ k₁ = k₂ := by
  set s₁ := 2 * b₁ / q - t₀ with hs₁
  set s₂ := 2 * b₂ / q - t₀ with hs₂
  have e1 : ∀ t, q * t ^ 2 - 2 * b₁ * t + k₁ = q * (t - t₀) * (t - s₁) := by
    intro t
    have : k₁ = 2 * b₁ * t₀ - q * t₀ ^ 2 := by linarith
    rw [this, hs₁]; field_simp; ring
  have e2 : ∀ t, q * t ^ 2 - 2 * b₂ * t + k₂ = q * (t - t₀) * (t - s₂) := by
    intro t
    have : k₂ = 2 * b₂ * t₀ - q * t₀ ^ 2 := by linarith
    rw [this, hs₂]; field_simp; ring
  have r1 : q * s₁ ^ 2 - 2 * b₁ * s₁ + k₁ = 0 := by rw [e1]; ring
  have r2 : q * s₂ ^ 2 - 2 * b₂ * s₂ + k₂ = 0 := by rw [e2]; ring
  have a1 := (hset s₁).mp r1
  have a2 := (hset s₂).mpr r2
  rw [e2] at a1
  rw [e1] at a2
  have hs : s₁ = s₂ := by
    rcases mul_eq_zero.mp a1 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hq
      · -- s₁ = t₀
        have : s₁ = t₀ := by linarith
        rcases mul_eq_zero.mp a2 with h' | h'
        · rcases mul_eq_zero.mp h' with h' | h'
          · exact absurd h' hq
          · linarith
        · linarith
    · linarith
  have hb : b₁ = b₂ := by
    have : 2 * b₁ / q = 2 * b₂ / q := by linarith
    field_simp at this; linarith
  refine ⟨hb, ?_⟩
  subst hb
  linarith

/-- Two circle sections `Σ ∩ W₁`, `Σ ∩ W₂` (given as `IsCircleIn`) by planes through a line `ℝu` that meets
`Σ` (at `t₀ u`) have the same power `k` of the origin and the same `⟪a, u⟫`. -/
theorem circle_planes_agree {S : Set E3} {W₁ W₂ : Submodule ℝ E3} (h₁ : IsCircleIn W₁ (↑W₁ ∩ S))
    (h₂ : IsCircleIn W₂ (↑W₂ ∩ S)) {u : E3} (hu : u ≠ 0) (hu₁ : u ∈ W₁) (hu₂ : u ∈ W₂) {t₀ : ℝ}
    (ht₀ : t₀ • u ∈ S) :
    ∃ a₁ ∈ W₁, ∃ a₂ ∈ W₂, ∃ k : ℝ, (∀ x, x ∈ ↑W₁ ∩ S ↔ x ∈ W₁ ∧ ‖x‖ ^ 2 - 2 * ⟪a₁, x⟫ + k = 0) ∧
      (∀ x, x ∈ ↑W₂ ∩ S ↔ x ∈ W₂ ∧ ‖x‖ ^ 2 - 2 * ⟪a₂, x⟫ + k = 0) ∧ ⟪a₁, u⟫ = ⟪a₂, u⟫ := by
  obtain ⟨a₁, ha₁, k₁, -, hk₁⟩ := isCircleIn_quadratic h₁
  obtain ⟨a₂, ha₂, k₂, -, hk₂⟩ := isCircleIn_quadratic h₂
  have key : ∀ (W : Submodule ℝ E3) (a : E3) (k : ℝ), u ∈ W →
      (∀ x, x ∈ (↑W ∩ S : Set E3) ↔ x ∈ W ∧ ‖x‖ ^ 2 - 2 * ⟪a, x⟫ + k = 0) → ∀ t : ℝ,
      (t • u ∈ S ↔ ‖u‖ ^ 2 * t ^ 2 - 2 * ⟪a, u⟫ * t + k = 0) := by
    intro W a k huW hk t
    have := hk (t • u)
    simp only [Set.mem_inter_iff, SetLike.mem_coe] at this
    have hm : t • u ∈ W := W.smul_mem t huW
    simp only [hm, true_and, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs] at this
    rw [this]
    constructor <;> intro h <;> linarith
  have s₁ := key W₁ a₁ k₁ hu₁ hk₁
  have s₂ := key W₂ a₂ k₂ hu₂ hk₂
  have hq : ‖u‖ ^ 2 ≠ 0 := by positivity
  obtain ⟨hb, hk⟩ := quadratic_params_eq hq ((s₁ t₀).mp ht₀) ((s₂ t₀).mp ht₀)
    (fun t => (s₁ t).symm.trans (s₂ t))
  exact ⟨a₁, ha₁, a₂, ha₂, k₁, hk₁, by rw [hk]; exact hk₂, hb⟩

/-- Three distinct points of a circle are affinely independent: the difference vectors from the first point are
linearly independent. -/
theorem circle_three_indep {W : Submodule ℝ E3} {C : Set E3} (hC : IsCircleIn W C) {P₁ P₂ P₃ : E3}
    (h₁ : P₁ ∈ C) (h₂ : P₂ ∈ C) (h₃ : P₃ ∈ C) (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃) :
    LinearIndependent ℝ ![P₂ - P₁, P₃ - P₁] := by
  obtain ⟨a, -, r, hr, rfl⟩ := hC
  simp only [Set.mem_ofPred_eq, dist_eq_norm] at h₁ h₂ h₃
  have n1 : ‖P₁ - a‖ ^ 2 = r ^ 2 := by rw [h₁.2]
  have n2 : ‖P₂ - a‖ ^ 2 = r ^ 2 := by rw [h₂.2]
  have n3 : ‖P₃ - a‖ ^ 2 = r ^ 2 := by rw [h₃.2]
  set d₂ := P₂ - P₁ with hd₂
  set d₃ := P₃ - P₁ with hd₃
  have hd2 : d₂ ≠ 0 := sub_ne_zero.mpr h12.symm
  have hd3 : d₃ ≠ 0 := sub_ne_zero.mpr h13.symm
  have e2 : 2 * ⟪d₂, P₁ - a⟫ = -‖d₂‖ ^ 2 := by
    have : P₂ - a = (P₁ - a) + d₂ := by rw [hd₂]; abel
    rw [this, norm_add_sq_real] at n2
    rw [real_inner_comm] at n2; linarith
  have e3 : 2 * ⟪d₃, P₁ - a⟫ = -‖d₃‖ ^ 2 := by
    have : P₃ - a = (P₁ - a) + d₃ := by rw [hd₃]; abel
    rw [this, norm_add_sq_real] at n3
    rw [real_inner_comm] at n3; linarith
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hn2 : 0 < ‖d₂‖ := norm_pos_iff.mpr hd2
  have hn3 : 0 < ‖d₃‖ := norm_pos_iff.mpr hd3
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    rcases hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hd2
  · exfalso
    have hd : d₃ = (-s / t) • d₂ := by
      have : t • d₃ = -(s • d₂) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      calc d₃ = t⁻¹ • (t • d₃) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-s / t) • d₂ := by rw [this, smul_neg, ← neg_smul, smul_smul]; congr 1; field_simp
    set l := -s / t
    rw [hd, inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at e3
    simp only [RCLike.conj_to_real] at e3
    have hl : l * (-‖d₂‖ ^ 2) = l ^ 2 * (-‖d₂‖ ^ 2) := by
      have : l * (2 * ⟪d₂, P₁ - a⟫) = l * (-‖d₂‖ ^ 2) := by rw [e2]
      nlinarith
    have hl' : l * (1 - l) = 0 := by
      have : (l - l ^ 2) * ‖d₂‖ ^ 2 = 0 := by linarith
      have h2 : ‖d₂‖ ^ 2 ≠ 0 := by positivity
      have := (mul_eq_zero.mp this).resolve_right h2
      linarith
    rcases mul_eq_zero.mp hl' with h | h
    · rw [h, zero_smul] at hd; exact hd3 hd
    · have : l = 1 := by linarith
      rw [this, one_smul] at hd
      apply h23
      have : P₃ - P₁ = P₂ - P₁ := hd
      exact (sub_left_inj.mp this).symm

/-- **Key fact F.** If `C` is a circle in the plane `W` (`finrank W = 2`) and a sphere `S` contains three
distinct points of `C`, then `C ⊆ S`. -/
theorem circle_subset_sphere {W : Submodule ℝ E3} (hW : Module.finrank ℝ W = 2) {C : Set E3}
    (hC : IsCircleIn W C) {c : E3} {R : ℝ} {P₁ P₂ P₃ : E3} (h₁ : P₁ ∈ C) (h₂ : P₂ ∈ C) (h₃ : P₃ ∈ C)
    (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃) (s₁ : dist P₁ c = R) (s₂ : dist P₂ c = R)
    (s₃ : dist P₃ c = R) : C ⊆ Metric.sphere c R := by
  have hind := circle_three_indep hC h₁ h₂ h₃ h12 h13 h23
  obtain ⟨a, ha, r, hr, rfl⟩ := id hC
  simp only [Set.mem_ofPred_eq] at h₁ h₂ h₃
  have hspan : Submodule.span ℝ (Set.range ![P₂ - P₁, P₃ - P₁]) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact W.sub_mem h₂.1 h₁.1
      · exact W.sub_mem h₃.1 h₁.1
    · rw [finrank_span_eq_card hind, hW]; simp
  -- ⟪a - c, ·⟫ is constant on the three points
  have key : ∀ P, dist P a = r → dist P c = R →
      2 * ⟪a - c, P⟫ = (‖a‖ ^ 2 - r ^ 2) - (‖c‖ ^ 2 - R ^ 2) := by
    intro P hPa hPc
    rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) hr.le, norm_sub_sq_real] at hPa
    rw [dist_eq_norm] at hPc
    have : ‖P - c‖ ^ 2 = R ^ 2 := by rw [hPc]
    rw [norm_sub_sq_real] at this
    have e1 : ⟪a - c, P⟫ = ⟪a, P⟫ - ⟪c, P⟫ := inner_sub_left a c P
    have e2 := real_inner_comm a P
    have e3 := real_inner_comm c P
    rw [e1]
    nlinarith
  have k1 := key P₁ h₁.2 s₁
  have k2 := key P₂ h₂.2 s₂
  have k3 := key P₃ h₃.2 s₃
  have horth : ∀ w ∈ W, ⟪a - c, w⟫ = 0 := by
    intro w hw
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hw
    obtain ⟨f, rfl⟩ := hw
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_add_right,
      inner_smul_right, inner_sub_right]
    rw [show ⟪a - c, P₂⟫ = ⟪a - c, P₁⟫ by linarith, show ⟪a - c, P₃⟫ = ⟪a - c, P₁⟫ by linarith]
    ring
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  have hxP := horth (x - P₁) (W.sub_mem hx.1 h₁.1)
  rw [inner_sub_right] at hxP
  have hR : 0 ≤ R := by rw [← s₁]; exact dist_nonneg
  have hxa := hx.2
  rw [dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) hr.le, norm_sub_sq_real] at hxa
  rw [Metric.mem_sphere, dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) hR, norm_sub_sq_real]
  have e1 := real_inner_comm a x
  have e2 := real_inner_comm c x
  have e3 : ⟪a - c, P₁⟫ = ⟪a, P₁⟫ - ⟪c, P₁⟫ := inner_sub_left a c P₁
  have e4 : ⟪a - c, x⟫ = ⟪a, x⟫ - ⟪c, x⟫ := inner_sub_left a c x
  nlinarith

section Planes

/-- Two vectors have a common nonzero orthogonal vector in `ℝ³`. -/
theorem exists_normal (x y : E3) : ∃ n : E3, n ≠ 0 ∧ ⟪n, x⟫ = 0 ∧ ⟪n, y⟫ = 0 := by
  let f : E3 →ₗ[ℝ] ℝ × ℝ := LinearMap.prod (innerSL ℝ x).toLinearMap (innerSL ℝ y).toLinearMap
  have hlt : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E3 := by
    simp [Module.finrank_prod, finrank_euclideanSpace_fin]
  obtain ⟨n, hn, hn0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  have h := LinearMap.mem_ker.mp hn
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp [f] at h1 h2
  exact ⟨n, hn0, by rw [real_inner_comm]; exact h1, by rw [real_inner_comm]; exact h2⟩

/-- The plane through the origin with normal `n`. -/
theorem finrank_plane {n : E3} (hn : n ≠ 0) : Module.finrank ℝ (ℝ ∙ n)ᗮ = 2 := by
  haveI : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [finrank_euclideanSpace_fin]⟩
  exact Submodule.finrank_orthogonal_span_singleton hn

theorem mem_plane {n x : E3} : x ∈ (ℝ ∙ n)ᗮ ↔ ⟪n, x⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

/-- A circle in the plane `nᗮ` has a point different from two given points. -/
theorem circle_third_point {n : E3} (hn : n ≠ 0) {C : Set E3} (hC : IsCircleIn (ℝ ∙ n)ᗮ C) (p q : E3) :
    ∃ x ∈ C, x ≠ p ∧ x ≠ q := by
  obtain ⟨a, ha, r, hr, rfl⟩ := hC
  obtain ⟨e₁, he₁, h1n, -⟩ := exists_normal n n
  obtain ⟨e₂, he₂, h2n, h2e⟩ := exists_normal n e₁
  set e := ‖e₁‖⁻¹ • e₁ with he
  set f := ‖e₂‖⁻¹ • e₂ with hf
  have hen : ‖e‖ = 1 := norm_smul_inv_norm he₁
  have hfn : ‖f‖ = 1 := norm_smul_inv_norm he₂
  have hef : ⟪e, f⟫ = 0 := by
    simp only [he, hf, inner_smul_left, inner_smul_right]
    rw [real_inner_comm, h2e]; simp
  have heW : e ∈ (ℝ ∙ n)ᗮ := by
    rw [mem_plane, he, inner_smul_right, real_inner_comm, h1n]; simp
  have hfW : f ∈ (ℝ ∙ n)ᗮ := by
    rw [mem_plane, hf, inner_smul_right, real_inner_comm, h2n]; simp
  have hmem : ∀ v ∈ (ℝ ∙ n)ᗮ, ‖v‖ = 1 → a + r • v ∈ {x | x ∈ (ℝ ∙ n)ᗮ ∧ dist x a = r} := by
    intro v hv hv1
    refine ⟨add_mem ha (Submodule.smul_mem _ _ hv), ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv1, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hmem' : a - r • e ∈ {x | x ∈ (ℝ ∙ n)ᗮ ∧ dist x a = r} := by
    have := hmem (-e) (Submodule.neg_mem _ heW) (by rw [norm_neg, hen])
    simpa [sub_eq_add_neg] using this
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hen]; norm_num
  have d12 : a + r • e ≠ a - r • e := by
    intro h
    have : r • e = - (r • e) := by
      have := h; rw [sub_eq_add_neg] at this; exact add_left_cancel this
    have h2 : (2 * r) • e = 0 := by rw [two_mul, add_smul]; nth_rewrite 2 [this]; simp
    have := congrArg (fun v => ⟪e, v⟫) h2
    simp [inner_smul_right] at this
    rcases this with h0 | h0
    · exact hr.ne' h0
    · rw [h0] at hen; simp at hen
  have d13 : a + r • e ≠ a + r • f := by
    intro h
    have h' : r • e = r • f := add_left_cancel h
    have := congrArg (fun v => ⟪e, v⟫) h'
    simp [inner_smul_right, hef] at this
    rcases this with h0 | h0
    · exact hr.ne' h0
    · rw [h0] at hen; simp at hen
  have d23 : a - r • e ≠ a + r • f := by
    intro h
    have h' : -(r • e) = r • f := by rw [sub_eq_add_neg] at h; exact add_left_cancel h
    have := congrArg (fun v => ⟪e, v⟫) h'
    simp [inner_smul_right, hef] at this
    rcases this with h0 | h0
    · exact hr.ne' h0
    · rw [h0] at hen; simp at hen
  by_contra hcon
  push_neg at hcon
  have k1 := hcon _ (hmem e heW hen)
  have k2 := hcon _ hmem'
  have k3 := hcon _ (hmem f hfW hfn)
  by_cases a1 : a + r • e = p
  · by_cases a2 : a - r • e = p
    · exact d12 (a1.trans a2.symm)
    · have a2' := k2 a2
      by_cases a3 : a + r • f = p
      · exact d13 (a1.trans a3.symm)
      · exact d23 (a2'.trans (k3 a3).symm)
  · have a1' := k1 a1
    by_cases a2 : a - r • e = p
    · by_cases a3 : a + r • f = p
      · exact d23 (a2.trans a3.symm)
      · exact d13 (a1'.trans (k3 a3).symm)
    · exact d12 (a1'.trans (k2 a2).symm)

end Planes

section Quad

theorem quad_roots_distinct {q b κ t₁ t₂ : ℝ} (h₁ : q * t₁ ^ 2 - 2 * b * t₁ + κ = 0)
    (h₂ : q * t₂ ^ 2 - 2 * b * t₂ + κ = 0) (h12 : t₁ ≠ t₂) (hq : 0 < q) : 0 < b ^ 2 - q * κ := by
  have hs : q * (t₁ + t₂) = 2 * b := by
    have : (t₁ - t₂) * (q * (t₁ + t₂) - 2 * b) = 0 := by linear_combination h₁ - h₂
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
    linarith
  have hk : κ = q * t₁ * t₂ := by linear_combination h₁ - t₁ * hs
  have hb : b = q * (t₁ + t₂) / 2 := by linarith
  have : b ^ 2 - q * κ = q ^ 2 * (t₁ - t₂) ^ 2 / 4 := by rw [hk, hb]; ring
  rw [this]
  have : 0 < (t₁ - t₂) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr h12)))
  positivity

theorem quad_roots_exist {q b κ : ℝ} (hq : 0 < q) (hD : 0 < b ^ 2 - q * κ) :
    ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧ q * t₁ ^ 2 - 2 * b * t₁ + κ = 0 ∧ q * t₂ ^ 2 - 2 * b * t₂ + κ = 0 := by
  have hsq := Real.sq_sqrt hD.le
  have hpos := Real.sqrt_pos.mpr hD
  set s := Real.sqrt (b ^ 2 - q * κ)
  refine ⟨(b + s) / q, (b - s) / q, ?_, ?_, ?_⟩
  · intro h
    field_simp at h
    linarith
  · field_simp
    nlinarith
  · field_simp
    nlinarith

theorem quad_root_cases {q b κ t₁ t₂ t : ℝ} (hq : 0 < q) (h₁ : q * t₁ ^ 2 - 2 * b * t₁ + κ = 0)
    (h₂ : q * t₂ ^ 2 - 2 * b * t₂ + κ = 0) (h12 : t₁ ≠ t₂) (ht : q * t ^ 2 - 2 * b * t + κ = 0) :
    t = t₁ ∨ t = t₂ := by
  by_contra hcon
  push_neg at hcon
  have e1 : (t - t₁) * (q * (t + t₁) - 2 * b) = 0 := by linear_combination ht - h₁
  have e2 : (t - t₂) * (q * (t + t₂) - 2 * b) = 0 := by linear_combination ht - h₂
  have f1 := (mul_eq_zero.mp e1).resolve_left (sub_ne_zero.mpr hcon.1)
  have f2 := (mul_eq_zero.mp e2).resolve_left (sub_ne_zero.mpr hcon.2)
  have : q * (t₁ - t₂) = 0 := by linarith
  exact h12 (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq.ne'))

theorem quad_line (b u : E3) (κ t : ℝ) :
    ‖t • u‖ ^ 2 - 2 * ⟪b, t • u⟫ + κ = ‖u‖ ^ 2 * t ^ 2 - 2 * ⟪b, u⟫ * t + κ := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right]
  ring

theorem mem_sphere_quad {c x : E3} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ Metric.sphere c R ↔ ‖x‖ ^ 2 - 2 * ⟪c, x⟫ + (‖c‖ ^ 2 - R ^ 2) = 0 := by
  rw [Metric.mem_sphere, dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) hR, norm_sub_sq_real]
  have := real_inner_comm c x
  constructor <;> intro h <;> linarith

end Quad

section Sections

/-- The hypothesis of Lemma 16.9 (with `O` the origin): every plane through `O` meets `Sg` in `∅`, a point
or a circle. -/
def PlaneSections (Sg : Set E3) : Prop :=
  ∀ W : Submodule ℝ E3, Module.finrank ℝ W = 2 →
    ((W : Set E3) ∩ Sg = ∅ ∨ (∃ p, (W : Set E3) ∩ Sg = {p}) ∨ IsCircleIn W ((W : Set E3) ∩ Sg))

theorem PlaneSections.circle {Sg : Set E3} (h : PlaneSections Sg) {W : Submodule ℝ E3}
    (hW : Module.finrank ℝ W = 2) {P₁ P₂ : E3} (h₁ : P₁ ∈ W) (h₁' : P₁ ∈ Sg) (h₂ : P₂ ∈ W)
    (h₂' : P₂ ∈ Sg) (h12 : P₁ ≠ P₂) : IsCircleIn W ((W : Set E3) ∩ Sg) := by
  rcases h W hW with he | ⟨p, hp⟩ | hc
  · have : P₁ ∈ (W : Set E3) ∩ Sg := ⟨h₁, h₁'⟩
    rw [he] at this; exact absurd this (Set.notMem_empty _)
  · have a1 : P₁ ∈ (W : Set E3) ∩ Sg := ⟨h₁, h₁'⟩
    have a2 : P₂ ∈ (W : Set E3) ∩ Sg := ⟨h₂, h₂'⟩
    rw [hp] at a1 a2
    exact absurd ((Set.mem_singleton_iff.mp a1).trans (Set.mem_singleton_iff.mp a2).symm) h12
  · exact hc

/-- If a circle section of `Sg` by the plane `W` shares three distinct points with a sphere, then the two
sections of `W` coincide. -/
theorem section_eq_sphere {W : Submodule ℝ E3} (hW : Module.finrank ℝ W = 2) {C : Set E3}
    (hC : IsCircleIn W C) {c : E3} {R : ℝ} (hR : 0 ≤ R) {P₁ P₂ P₃ : E3} (h₁ : P₁ ∈ C) (h₂ : P₂ ∈ C)
    (h₃ : P₃ ∈ C) (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃) (s₁ : dist P₁ c = R)
    (s₂ : dist P₂ c = R) (s₃ : dist P₃ c = R) : (W : Set E3) ∩ Metric.sphere c R = C := by
  have hsub := circle_subset_sphere hW hC h₁ h₂ h₃ h12 h13 h23 s₁ s₂ s₃
  obtain ⟨a, ha, r, hr, hCeq⟩ := id hC
  have hCW : ∀ x ∈ C, x ∈ W ∧ dist x a = r := fun x hx => by rw [hCeq] at hx; exact hx
  ext x
  constructor
  · rintro ⟨hxW, hxS⟩
    rcases plane_inter_sphere c hR W with he | ⟨p, hp⟩ | hcirc
    · have : P₁ ∈ (W : Set E3) ∩ Metric.sphere c R := ⟨(hCW _ h₁).1, s₁⟩
      rw [he] at this; exact absurd this (Set.notMem_empty _)
    · have a1 : P₁ ∈ (W : Set E3) ∩ Metric.sphere c R := ⟨(hCW _ h₁).1, s₁⟩
      have a2 : P₂ ∈ (W : Set E3) ∩ Metric.sphere c R := ⟨(hCW _ h₂).1, s₂⟩
      rw [hp] at a1 a2
      exact absurd ((Set.mem_singleton_iff.mp a1).trans (Set.mem_singleton_iff.mp a2).symm) h12
    · have key := circle_subset_sphere hW hcirc (c := a) (R := r) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
        ⟨(hCW _ h₁).1, s₁⟩ ⟨(hCW _ h₂).1, s₂⟩ ⟨(hCW _ h₃).1, s₃⟩ h12 h13 h23 (hCW _ h₁).2 (hCW _ h₂).2
        (hCW _ h₃).2
      have := key ⟨hxW, hxS⟩
      rw [hCeq]
      exact ⟨hxW, this⟩
  · intro hx
    exact ⟨(hCW _ hx).1, hsub hx⟩

end Sections

section Near

open Filter Topology in
/-- The perturbation argument of the proof of Lemma 16.9: starting from a secant direction `u₀` of the
base circle (in the plane `n₀ᗮ`) and a plane `nᗮ ∋ u₀` not containing `Z ∉ n₀ᗮ`, one finds a nearby secant
direction `u'` and a point `Q` of the quadric `‖x‖² - 2⟪b,x⟫ + κ = 0` (which is cut twice by `ℝ u₀`) lying in
`nᗮ ∩ span(u', Z)` and not on the line `ℝ u₀`. -/
theorem exists_point_near {n₀ n u₀ v Z a₀ b : E3} {k₀ κ : ℝ}
    (hu₀n₀ : ⟪n₀, u₀⟫ = 0) (hvn₀ : ⟪n₀, v⟫ = 0) (hv : ∀ t : ℝ, v ≠ t • u₀)
    (hZ₀ : ⟪n₀, Z⟫ ≠ 0) (hun : ⟪n, u₀⟫ = 0) (hZn : ⟪n, Z⟫ ≠ 0)
    (hd₀ : 0 < ⟪a₀, u₀⟫ ^ 2 - k₀ * ‖u₀‖ ^ 2) (hdb : 0 < ⟪b, u₀⟫ ^ 2 - κ * ‖u₀‖ ^ 2) :
    ∃ u' : E3, ⟪n₀, u'⟫ = 0 ∧ u' ≠ 0 ∧ 0 < ⟪a₀, u'⟫ ^ 2 - k₀ * ‖u'‖ ^ 2 ∧
      ∃ Q : E3, ⟪n, Q⟫ = 0 ∧ (∃ α β : ℝ, Q = α • u' + β • Z) ∧ ‖Q‖ ^ 2 - 2 * ⟪b, Q⟫ + κ = 0 ∧
        ∀ t : ℝ, Q ≠ t • u₀ := by
  set U : ℝ → E3 := fun ε => u₀ + ε • v with hU
  set M : ℝ → E3 := fun ε => ⟪n, Z⟫ • U ε - ⟪n, U ε⟫ • Z with hM
  have hf : Continuous fun ε => ⟪a₀, U ε⟫ ^ 2 - k₀ * ‖U ε‖ ^ 2 := by
    simp only [hU]; fun_prop
  have hg : Continuous fun ε => ⟪b, M ε⟫ ^ 2 - κ * ‖M ε‖ ^ 2 := by
    simp only [hM, hU]; fun_prop
  have h0f : 0 < ⟪a₀, U 0⟫ ^ 2 - k₀ * ‖U 0‖ ^ 2 := by simpa [hU] using hd₀
  have h0g : 0 < ⟪b, M 0⟫ ^ 2 - κ * ‖M 0‖ ^ 2 := by
    have h : M 0 = ⟪n, Z⟫ • u₀ := by simp [hM, hU, hun]
    rw [h, inner_smul_right, norm_smul, Real.norm_eq_abs]
    simp only [mul_pow, sq_abs]
    have e : ⟪n, Z⟫ ^ 2 * ⟪b, u₀⟫ ^ 2 - κ * (⟪n, Z⟫ ^ 2 * ‖u₀‖ ^ 2) =
        ⟪n, Z⟫ ^ 2 * (⟪b, u₀⟫ ^ 2 - κ * ‖u₀‖ ^ 2) := by ring
    rw [e]; positivity
  have hA : ∀ᶠ ε in nhds (0 : ℝ), 0 < ⟪a₀, U ε⟫ ^ 2 - k₀ * ‖U ε‖ ^ 2 :=
    (isOpen_lt continuous_const hf).mem_nhds h0f
  have hB : ∀ᶠ ε in nhds (0 : ℝ), 0 < ⟪b, M ε⟫ ^ 2 - κ * ‖M ε‖ ^ 2 :=
    (isOpen_lt continuous_const hg).mem_nhds h0g
  obtain ⟨ε, ⟨hεA, hεB⟩, hε0⟩ := (((hA.and hB).filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ ε in nhdsWithin (0 : ℝ) {0}ᶜ, ε ∈ ({0}ᶜ : Set ℝ))).exists
  have hε : ε ≠ 0 := hε0
  have hn₀U : ⟪n₀, U ε⟫ = 0 := by simp [hU, inner_add_right, inner_smul_right, hu₀n₀, hvn₀]
  have hnU : ⟪n, U ε⟫ = ε * ⟪n, v⟫ := by simp [hU, inner_add_right, inner_smul_right, hun]
  have hU0 : U ε ≠ 0 := by
    intro h
    have h1 : ε • v = -u₀ := eq_neg_of_add_eq_zero_right h
    apply hv (-ε⁻¹)
    calc v = ε⁻¹ • (ε • v) := by rw [smul_smul, inv_mul_cancel₀ hε, one_smul]
      _ = (-ε⁻¹) • u₀ := by rw [h1]; module
  have hMn : ⟪n, M ε⟫ = 0 := by
    simp only [hM, inner_sub_right, inner_smul_right]; ring
  have hMnot : ∀ t : ℝ, M ε ≠ t • u₀ := by
    intro t ht
    have h1 : ⟪n₀, M ε⟫ = ⟪n₀, t • u₀⟫ := by rw [ht]
    simp only [hM, inner_sub_right, inner_smul_right, hn₀U, hu₀n₀] at h1
    have h2 : ⟪n, U ε⟫ = 0 := by
      have : ⟪n, U ε⟫ * ⟪n₀, Z⟫ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hZ₀
    have h3 : ⟪n, v⟫ = 0 := by
      rw [hnU] at h2; exact (mul_eq_zero.mp h2).resolve_left hε
    have h4 : (⟪n, Z⟫ * ε) • v = (t - ⟪n, Z⟫) • u₀ := by
      have := ht
      simp only [hM] at this
      rw [h2, zero_smul, sub_zero] at this
      simp only [hU] at this
      linear_combination (norm := module) this
    have hne : ⟪n, Z⟫ * ε ≠ 0 := mul_ne_zero hZn hε
    apply hv ((⟪n, Z⟫ * ε)⁻¹ * (t - ⟪n, Z⟫))
    calc v = (⟪n, Z⟫ * ε)⁻¹ • ((⟪n, Z⟫ * ε) • v) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [h4, smul_smul]
  have hM0 : M ε ≠ 0 := fun h => hMnot 0 (by simp [h])
  have hq : 0 < ‖M ε‖ ^ 2 := by positivity
  obtain ⟨t₁, t₂, h12, r₁, r₂⟩ := quad_roots_exist (q := ‖M ε‖ ^ 2) (b := ⟪b, M ε⟫) (κ := κ) hq (by nlinarith [hεB])
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, s ≠ 0 ∧ ‖M ε‖ ^ 2 * s ^ 2 - 2 * ⟪b, M ε⟫ * s + κ = 0 := by
    by_cases h : t₁ = 0
    · exact ⟨t₂, fun h' => h12 (h.trans h'.symm), r₂⟩
    · exact ⟨t₁, h, r₁⟩
  refine ⟨U ε, hn₀U, hU0, hεA, s • M ε, ?_, ⟨s * ⟪n, Z⟫, -(s * ⟪n, U ε⟫), ?_⟩, ?_, ?_⟩
  · rw [inner_smul_right, hMn, mul_zero]
  · simp only [hM]; module
  · rw [quad_line]; exact hs
  · intro t h
    apply hMnot (s⁻¹ * t)
    calc M ε = s⁻¹ • (s • M ε) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = _ := by rw [h, smul_smul]

end Near

section Main

theorem secant_roots {a₀ u : E3} {k₀ : ℝ} (hu : u ≠ 0) (hd : 0 < ⟪a₀, u⟫ ^ 2 - k₀ * ‖u‖ ^ 2) :
    ∃ t₁ t₂ : ℝ, t₁ ≠ t₂ ∧ ‖t₁ • u‖ ^ 2 - 2 * ⟪a₀, t₁ • u⟫ + k₀ = 0 ∧
      ‖t₂ • u‖ ^ 2 - 2 * ⟪a₀, t₂ • u⟫ + k₀ = 0 ∧
      ∀ t : ℝ, ‖t • u‖ ^ 2 - 2 * ⟪a₀, t • u⟫ + k₀ = 0 → t = t₁ ∨ t = t₂ := by
  have hq : 0 < ‖u‖ ^ 2 := by positivity
  obtain ⟨t₁, t₂, h12, r₁, r₂⟩ := quad_roots_exist (q := ‖u‖ ^ 2) (b := ⟪a₀, u⟫) (κ := k₀) hq
    (by nlinarith [hd])
  refine ⟨t₁, t₂, h12, by rw [quad_line]; exact r₁, by rw [quad_line]; exact r₂, fun t ht => ?_⟩
  rw [quad_line] at ht
  exact quad_root_cases hq r₁ r₂ h12 ht

theorem exists_secant_dir {n₀ a₀ : E3} {k₀ : ℝ} (ha₀ : ⟪n₀, a₀⟫ = 0) (hk₀ : 0 < ‖a₀‖ ^ 2 - k₀)
    (hn₀ : n₀ ≠ 0) :
    ∃ u : E3, u ≠ 0 ∧ ⟪n₀, u⟫ = 0 ∧ 0 < ⟪a₀, u⟫ ^ 2 - k₀ * ‖u‖ ^ 2 := by
  by_cases ha : a₀ = 0
  · subst ha
    obtain ⟨u, hu, hun, -⟩ := exists_normal n₀ n₀
    refine ⟨u, hu, by rw [real_inner_comm]; exact hun, ?_⟩
    have : 0 < ‖u‖ ^ 2 := by positivity
    simp only [norm_zero, inner_zero_left] at hk₀ ⊢
    nlinarith
  · refine ⟨a₀, ha, ha₀, ?_⟩
    rw [real_inner_self_eq_norm_sq]
    have : 0 < ‖a₀‖ ^ 2 := by positivity
    nlinarith [mul_pos this hk₀]

theorem exists_off_plane {Sg : Set E3} (h : PlaneSections Sg) {n₀ a₀ : E3} {k₀ : ℝ} (hn₀ : n₀ ≠ 0)
    (ha₀ : ⟪n₀, a₀⟫ = 0) (hk₀ : 0 < ‖a₀‖ ^ 2 - k₀)
    (hC₀ : ∀ x, ⟪n₀, x⟫ = 0 → (x ∈ Sg ↔ ‖x‖ ^ 2 - 2 * ⟪a₀, x⟫ + k₀ = 0)) :
    ∃ Z ∈ Sg, ⟪n₀, Z⟫ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u₀, hu₀, hu₀n, hd⟩ := exists_secant_dir ha₀ hk₀ hn₀
  obtain ⟨t₁, t₂, h12, r₁, r₂, rall⟩ := secant_roots hu₀ hd
  obtain ⟨nv, hnv, hnvn₀, hnvu⟩ := exists_normal n₀ u₀
  have inn : ∀ t : ℝ, ⟪n₀, t • u₀⟫ = 0 := fun t => by rw [inner_smul_right, hu₀n, mul_zero]
  have inW : ∀ t : ℝ, t • u₀ ∈ (ℝ ∙ nv)ᗮ := fun t => by
    rw [mem_plane, inner_smul_right, hnvu, mul_zero]
  have p₁ : t₁ • u₀ ∈ Sg := (hC₀ _ (inn _)).mpr r₁
  have p₂ : t₂ • u₀ ∈ Sg := (hC₀ _ (inn _)).mpr r₂
  have hne : t₁ • u₀ ≠ t₂ • u₀ := fun h' => h12 (smul_left_injective ℝ hu₀ h')
  have circ := h.circle (finrank_plane hnv) (inW t₁) p₁ (inW t₂) p₂ hne
  obtain ⟨P, ⟨hPW, hPS⟩, hP1, hP2⟩ := circle_third_point hnv circ (t₁ • u₀) (t₂ • u₀)
  have hPn : ⟪n₀, P⟫ = 0 := hcon P hPS
  have hPv : ⟪nv, P⟫ = 0 := mem_plane.mp hPW
  haveI : Fact (Module.finrank ℝ (ℝ ∙ n₀)ᗮ = 2) := ⟨finrank_plane hn₀⟩
  have hnvW : nv ∈ (ℝ ∙ n₀)ᗮ := mem_plane.mpr (by rw [real_inner_comm]; exact hnvn₀)
  have hPW0 : P ∈ (ℝ ∙ n₀)ᗮ := mem_plane.mpr hPn
  have hu0W : u₀ ∈ (ℝ ∙ n₀)ᗮ := mem_plane.mpr hu₀n
  have key : (⟨P, hPW0⟩ : (ℝ ∙ n₀)ᗮ) ∈ ℝ ∙ (⟨u₀, hu0W⟩ : (ℝ ∙ n₀)ᗮ) :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (v := (⟨nv, hnvW⟩ : (ℝ ∙ n₀)ᗮ)) (w := (⟨u₀, hu0W⟩ : (ℝ ∙ n₀)ᗮ)) (u := (⟨P, hPW0⟩ : (ℝ ∙ n₀)ᗮ))
      (fun h => hnv (congrArg Subtype.val h)) (fun h => hu₀ (congrArg Subtype.val h)) hPv hnvu
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp key
  have hPt : t • u₀ = P := congrArg Subtype.val ht
  have hq := (hC₀ P hPn).mp hPS
  rw [← hPt] at hq
  rcases rall t hq with h' | h'
  · exact hP1 (by rw [← hPt, h'])
  · exact hP2 (by rw [← hPt, h'])

/-- Data of the proof of Lemma 16.9: a base plane `n₀ᗮ` whose section is a circle (given by the quadric
`‖x‖² - 2⟪a₀,x⟫ + k₀ = 0`), a point `Z` of the set off the plane, and the sphere through the base circle and
`Z`. -/
structure SphereData (Sg : Set E3) where
  n₀ : E3
  a₀ : E3
  k₀ : ℝ
  Z : E3
  c : E3
  R : ℝ
  hn₀ : n₀ ≠ 0
  ha₀ : ⟪n₀, a₀⟫ = 0
  hk₀ : 0 < ‖a₀‖ ^ 2 - k₀
  hC₀ : ∀ x, ⟪n₀, x⟫ = 0 → (x ∈ Sg ↔ ‖x‖ ^ 2 - 2 * ⟪a₀, x⟫ + k₀ = 0)
  hZ : Z ∈ Sg
  hZ₀ : ⟪n₀, Z⟫ ≠ 0
  hR : 0 < R
  hSC₀ : ∀ x, ⟪n₀, x⟫ = 0 → (x ∈ Metric.sphere c R ↔ ‖x‖ ^ 2 - 2 * ⟪a₀, x⟫ + k₀ = 0)
  hZS : Z ∈ Metric.sphere c R

/-- Step 3: for a secant direction `u'` of the base circle, the plane `span(u', Z)` meets the set and the
sphere in the same points. -/
theorem SphereData.step3 {Sg : Set E3} (D : SphereData Sg) (h : PlaneSections Sg) {u' : E3} (hu : u' ≠ 0)
    (hun : ⟪D.n₀, u'⟫ = 0) (hd : 0 < ⟪D.a₀, u'⟫ ^ 2 - D.k₀ * ‖u'‖ ^ 2) {W : Submodule ℝ E3}
    (hW : Module.finrank ℝ W = 2) (hu'W : u' ∈ W) (hZW : D.Z ∈ W) :
    ∀ x ∈ W, (x ∈ Sg ↔ x ∈ Metric.sphere D.c D.R) := by
  obtain ⟨t₁, t₂, h12, r₁, r₂, -⟩ := secant_roots hu hd
  have inn : ∀ t : ℝ, ⟪D.n₀, t • u'⟫ = 0 := fun t => by rw [inner_smul_right, hun, mul_zero]
  have p₁ : t₁ • u' ∈ Sg := (D.hC₀ _ (inn _)).mpr r₁
  have p₂ : t₂ • u' ∈ Sg := (D.hC₀ _ (inn _)).mpr r₂
  have s₁ : t₁ • u' ∈ Metric.sphere D.c D.R := (D.hSC₀ _ (inn _)).mpr r₁
  have s₂ : t₂ • u' ∈ Metric.sphere D.c D.R := (D.hSC₀ _ (inn _)).mpr r₂
  have hne : t₁ • u' ≠ t₂ • u' := fun h' => h12 (smul_left_injective ℝ hu h')
  have circ := h.circle hW (W.smul_mem t₁ hu'W) p₁ (W.smul_mem t₂ hu'W) p₂ hne
  have hZ1 : t₁ • u' ≠ D.Z := fun h' => D.hZ₀ (by rw [← h', inn])
  have hZ2 : t₂ • u' ≠ D.Z := fun h' => D.hZ₀ (by rw [← h', inn])
  have heq := section_eq_sphere hW circ D.hR.le (P₁ := t₁ • u') (P₂ := t₂ • u') (P₃ := D.Z)
    ⟨W.smul_mem t₁ hu'W, p₁⟩ ⟨W.smul_mem t₂ hu'W, p₂⟩ ⟨hZW, D.hZ⟩ hne hZ1 hZ2
    (Metric.mem_sphere.mp s₁) (Metric.mem_sphere.mp s₂) (Metric.mem_sphere.mp D.hZS)
  intro x hx
  have := Set.ext_iff.mp heq x
  simp only [Set.mem_inter_iff, SetLike.mem_coe] at this
  constructor
  · intro hxS; exact (this.mpr ⟨hx, hxS⟩).2
  · intro hxS; exact (this.mp ⟨hx, hxS⟩).2

/-- Steps 4 and 5: a point off the base plane lies in the set iff it lies on the sphere. -/
theorem SphereData.off_plane {Sg : Set E3} (D : SphereData Sg) (h : PlaneSections Sg) {Y : E3}
    (hY : ⟪D.n₀, Y⟫ ≠ 0) : Y ∈ Sg ↔ Y ∈ Metric.sphere D.c D.R := by
  obtain ⟨u₀, hu₀, hu₀n, hd⟩ := exists_secant_dir D.ha₀ D.hk₀ D.hn₀
  obtain ⟨v, hv0, hvn₀', hvu⟩ := exists_normal D.n₀ u₀
  have hvn₀ : ⟪D.n₀, v⟫ = 0 := by rw [real_inner_comm]; exact hvn₀'
  have hv : ∀ t : ℝ, v ≠ t • u₀ := by
    intro t ht
    have : t * ‖u₀‖ ^ 2 = 0 := by
      have := hvu; rw [ht, inner_smul_left, real_inner_self_eq_norm_sq] at this
      simpa using this
    have ht0 : t = 0 := (mul_eq_zero.mp this).resolve_right (by positivity)
    exact hv0 (by rw [ht, ht0, zero_smul])
  obtain ⟨t₁, t₂, h12, r₁, r₂, -⟩ := secant_roots hu₀ hd
  have inn : ∀ t : ℝ, ⟪D.n₀, t • u₀⟫ = 0 := fun t => by rw [inner_smul_right, hu₀n, mul_zero]
  have p₁ : t₁ • u₀ ∈ Sg := (D.hC₀ _ (inn _)).mpr r₁
  have p₂ : t₂ • u₀ ∈ Sg := (D.hC₀ _ (inn _)).mpr r₂
  have s₁ : t₁ • u₀ ∈ Metric.sphere D.c D.R := (D.hSC₀ _ (inn _)).mpr r₁
  have s₂ : t₂ • u₀ ∈ Metric.sphere D.c D.R := (D.hSC₀ _ (inn _)).mpr r₂
  have hne : t₁ • u₀ ≠ t₂ • u₀ := fun h' => h12 (smul_left_injective ℝ hu₀ h')
  obtain ⟨n, hn, hnu, hnY⟩ := exists_normal u₀ Y
  have hW := finrank_plane hn
  have inW : ∀ t : ℝ, t • u₀ ∈ (ℝ ∙ n)ᗮ := fun t => by
    rw [mem_plane, inner_smul_right, hnu, mul_zero]
  have hYW : Y ∈ (ℝ ∙ n)ᗮ := mem_plane.mpr hnY
  have circ := h.circle hW (inW t₁) p₁ (inW t₂) p₂ hne
  have hY1 : ∀ t : ℝ, t • u₀ ≠ Y := fun t h' => hY (by rw [← h', inn])
  have heq : ((ℝ ∙ n)ᗮ : Set E3) ∩ Metric.sphere D.c D.R = ((ℝ ∙ n)ᗮ : Set E3) ∩ Sg := by
    by_cases hZn : ⟪n, D.Z⟫ = 0
    · have hZW : D.Z ∈ (ℝ ∙ n)ᗮ := mem_plane.mpr hZn
      have hZ1 : t₁ • u₀ ≠ D.Z := fun h' => D.hZ₀ (by rw [← h', inn])
      have hZ2 : t₂ • u₀ ≠ D.Z := fun h' => D.hZ₀ (by rw [← h', inn])
      exact section_eq_sphere hW circ D.hR.le (P₁ := t₁ • u₀) (P₂ := t₂ • u₀) (P₃ := D.Z)
        ⟨inW t₁, p₁⟩ ⟨inW t₂, p₂⟩ ⟨hZW, D.hZ⟩ hne hZ1 hZ2
        (Metric.mem_sphere.mp s₁) (Metric.mem_sphere.mp s₂) (Metric.mem_sphere.mp D.hZS)
    · have hdb : 0 < ⟪D.c, u₀⟫ ^ 2 - (‖D.c‖ ^ 2 - D.R ^ 2) * ‖u₀‖ ^ 2 := by
        have e₁ := (mem_sphere_quad D.hR.le).mp s₁
        have e₂ := (mem_sphere_quad D.hR.le).mp s₂
        rw [quad_line] at e₁ e₂
        have := quad_roots_distinct (q := ‖u₀‖ ^ 2) (b := ⟪D.c, u₀⟫) (κ := ‖D.c‖ ^ 2 - D.R ^ 2)
          e₁ e₂ h12 (by positivity)
        nlinarith [this]
      have hnu' : ⟪n, u₀⟫ = 0 := hnu
      obtain ⟨u', hu'n, hu'0, hu'd, Q, hQn, ⟨α, β, hQ⟩, hQeq, hQnot⟩ :=
        exists_point_near hu₀n hvn₀ hv D.hZ₀ hnu' hZn hd hdb
      obtain ⟨n', hn', hn'u, hn'Z⟩ := exists_normal u' D.Z
      have hu'W : u' ∈ (ℝ ∙ n')ᗮ := mem_plane.mpr hn'u
      have hZW' : D.Z ∈ (ℝ ∙ n')ᗮ := mem_plane.mpr hn'Z
      have hQW' : Q ∈ (ℝ ∙ n')ᗮ := by
        rw [hQ]; exact add_mem (Submodule.smul_mem _ _ hu'W) (Submodule.smul_mem _ _ hZW')
      have hQS : Q ∈ Metric.sphere D.c D.R := (mem_sphere_quad D.hR.le).mpr hQeq
      have hQSg : Q ∈ Sg :=
        ((D.step3 h hu'0 hu'n hu'd (finrank_plane hn') hu'W hZW') Q hQW').mpr hQS
      have hQW : Q ∈ (ℝ ∙ n)ᗮ := mem_plane.mpr hQn
      exact section_eq_sphere hW circ D.hR.le (P₁ := t₁ • u₀) (P₂ := t₂ • u₀) (P₃ := Q)
        ⟨inW t₁, p₁⟩ ⟨inW t₂, p₂⟩ ⟨hQW, hQSg⟩ hne (fun h' => hQnot t₁ h'.symm)
        (fun h' => hQnot t₂ h'.symm)
        (Metric.mem_sphere.mp s₁) (Metric.mem_sphere.mp s₂) (Metric.mem_sphere.mp hQS)
  have := Set.ext_iff.mp heq Y
  simp only [Set.mem_inter_iff, SetLike.mem_coe] at this
  constructor
  · intro hxS; exact (this.mpr ⟨hYW, hxS⟩).2
  · intro hxS; exact (this.mp ⟨hYW, hxS⟩).2

theorem exists_sphereData {Sg : Set E3} (h : PlaneSections Sg) {A B : E3} (hA : A ∈ Sg) (hB : B ∈ Sg)
    (hAB : A ≠ B) : Nonempty (SphereData Sg) := by
  obtain ⟨n₀, hn₀, hnA, hnB⟩ := exists_normal A B
  have hW := finrank_plane hn₀
  have circ := h.circle hW (mem_plane.mpr hnA) hA (mem_plane.mpr hnB) hB hAB
  obtain ⟨a₀, ha₀W, k₀, hk₀, hC⟩ := isCircleIn_quadratic circ
  have ha₀ : ⟪n₀, a₀⟫ = 0 := mem_plane.mp ha₀W
  have hC₀ : ∀ x, ⟪n₀, x⟫ = 0 → (x ∈ Sg ↔ ‖x‖ ^ 2 - 2 * ⟪a₀, x⟫ + k₀ = 0) := by
    intro x hx
    have := hC x
    constructor
    · intro hxS; exact (this.mp ⟨mem_plane.mpr hx, hxS⟩).2
    · intro hq; exact (this.mpr ⟨mem_plane.mpr hx, hq⟩).2
  obtain ⟨Z, hZ, hZ₀⟩ := exists_off_plane h hn₀ ha₀ hk₀ hC₀
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (‖Z‖ ^ 2 - 2 * ⟪a₀, Z⟫ + k₀) / (2 * ⟪n₀, Z⟫) := ⟨_, rfl⟩
  have hrad : 0 < ‖a₀‖ ^ 2 - k₀ + lam ^ 2 * ‖n₀‖ ^ 2 := by
    have := mul_nonneg (sq_nonneg lam) (sq_nonneg ‖n₀‖)
    linarith
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt (‖a₀‖ ^ 2 - k₀ + lam ^ 2 * ‖n₀‖ ^ 2) := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; exact Real.sqrt_pos.mpr hrad
  have hR2 : R ^ 2 = ‖a₀‖ ^ 2 - k₀ + lam ^ 2 * ‖n₀‖ ^ 2 := by rw [hRdef]; exact Real.sq_sqrt hrad.le
  obtain ⟨c, hcdef⟩ : ∃ c : E3, c = a₀ + lam • n₀ := ⟨_, rfl⟩
  have hcc : ‖c‖ ^ 2 = ‖a₀‖ ^ 2 + lam ^ 2 * ‖n₀‖ ^ 2 := by
    rw [hcdef, norm_add_sq_real, inner_smul_right, real_inner_comm n₀ a₀, ha₀, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hcx : ∀ x, ⟪c, x⟫ = ⟪a₀, x⟫ + lam * ⟪n₀, x⟫ := fun x => by
    rw [hcdef, inner_add_left, inner_smul_left]; simp
  refine ⟨⟨n₀, a₀, k₀, Z, c, R, hn₀, ha₀, hk₀, hC₀, hZ, hZ₀, hR, ?_, ?_⟩⟩
  · intro x hx
    rw [mem_sphere_quad hR.le, hcx, hx, hcc, hR2]
    constructor <;> intro h' <;> linarith
  · rw [mem_sphere_quad hR.le, hcx, hcc, hR2]
    have : lam * (2 * ⟪n₀, Z⟫) = ‖Z‖ ^ 2 - 2 * ⟪a₀, Z⟫ + k₀ := by
      rw [hlam]; field_simp
    linarith

/-- **Petrunin, Lemma 16.9, direction "if".** Let `Σ` be a subset of Euclidean space `ℝ³` with at least two
points, and suppose that every plane through the origin `O` meets `Σ` in the empty set, a single point, or a
circle (`PlaneSections`). Then `Σ` is a sphere (of positive radius). Here planes are the 2-dimensional
linear subspaces (planes through `O = 0`; a general `O` is obtained by translation) and circles are as in
`IsCircleIn`. The book leaves this direction to the reader. -/
@[kb "petrunin2025" "Lemma 16.9 (if), p. 136"]
theorem sphere_of_plane_sections {Sg : Set E3} (hSg : ∃ A ∈ Sg, ∃ B ∈ Sg, A ≠ B)
    (h : PlaneSections Sg) : ∃ (c : E3) (R : ℝ), 0 < R ∧ Sg = Metric.sphere c R := by
  obtain ⟨A, hA, B, hB, hAB⟩ := hSg
  obtain ⟨D⟩ := exists_sphereData h hA hB hAB
  refine ⟨D.c, D.R, D.hR, ?_⟩
  ext x
  by_cases hx : ⟪D.n₀, x⟫ = 0
  · rw [D.hC₀ x hx, D.hSC₀ x hx]
  · exact D.off_plane h hx

/-- **Petrunin, Lemma 16.9** (with `O` the origin): a subset of `ℝ³` with at least two points is a sphere
if and only if every plane through `O` meets it in `∅`, a point or a circle. -/
@[kb "petrunin2025" "Lemma 16.9, p. 136"]
theorem sphere_iff_plane_sections {Sg : Set E3} (hSg : ∃ A ∈ Sg, ∃ B ∈ Sg, A ≠ B) :
    (∃ (c : E3) (R : ℝ), 0 < R ∧ Sg = Metric.sphere c R) ↔ PlaneSections Sg := by
  constructor
  · rintro ⟨c, R, hR, rfl⟩ W _
    exact plane_inter_sphere c hR.le W
  · exact sphere_of_plane_sections hSg

/-- Lemma 16.9 for an arbitrary point `O`: the sections of `Σ` by planes through `O` are the translates by `O`
of the sections of `Σ - O` by planes through the origin, so the hypothesis is `PlaneSections` of the
translated set `{x - O | x ∈ Σ}`. -/
@[kb "petrunin2025" "Lemma 16.9 (if, general O), p. 136"]
theorem sphere_of_plane_sections_at (O : E3) {Sg : Set E3} (hSg : ∃ A ∈ Sg, ∃ B ∈ Sg, A ≠ B)
    (h : PlaneSections ((fun x => x - O) '' Sg)) : ∃ (c : E3) (R : ℝ), 0 < R ∧ Sg = Metric.sphere c R := by
  obtain ⟨A, hA, B, hB, hAB⟩ := hSg
  obtain ⟨c, R, hR, hT⟩ := sphere_of_plane_sections (Sg := (fun x => x - O) '' Sg)
    ⟨A - O, ⟨A, hA, rfl⟩, B - O, ⟨B, hB, rfl⟩, fun h' => hAB (sub_left_injective h')⟩ h
  refine ⟨c + O, R, hR, ?_⟩
  ext x
  have hx : x ∈ Sg ↔ x - O ∈ (fun x => x - O) '' Sg :=
    ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => by rwa [sub_left_inj.mp hyx] at hy⟩
  rw [hx, hT, Metric.mem_sphere, Metric.mem_sphere, dist_eq_norm, dist_eq_norm]
  rw [show x - O - c = x - (c + O) by abel]

end Main

end UndergradKB.Geometry
