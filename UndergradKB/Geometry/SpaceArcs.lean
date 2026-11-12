import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Analysis.Convex.Side
import Mathlib.Analysis.Convex.StrictConvexBetween
import UndergradKB.Common.Attr

/-! # Inversion maps arcs to arcs in space (Petrunin, Theorem 16.5(d), p. 135; arcs: Chapter 9)

Arcs of circles in a real inner product space (in particular `ℝ³`), defined as in the plane: the arc
`ABC` is the part of the circle through `A, B, C` on the same side of the line `(AC)` as `B`.  We
characterize the arc by a Ptolemy equality (`mem_arcSpace_iff_ptolemy`; proof by inversion at `A`
and the equality case of the triangle inequality) and deduce that an inversion maps an arc onto an
arc whenever the circle does not pass through the centre.  The book's degenerate arcs (segments and
pairs of half-lines on a line) are added in `arcSpace'`; for it the Ptolemy characterization and the
invariance under inversion hold for all distinct `A, B, C` (arcs through the centre included), the
centre `O` itself (`∞` of the inversive space) being left out. -/

namespace UndergradKB.Geometry

open EuclideanGeometry AffineSubspace

namespace SpaceArcs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma arcs_mem_line_iff {A C X : V} : X ∈ line[ℝ, A, C] ↔ ∃ τ : ℝ, X - A = τ • (C - A) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp [AffineMap.lineMap_apply]⟩
  · rintro ⟨τ, h⟩
    exact ⟨τ, by simp [AffineMap.lineMap_apply, ← h]⟩

/-- Coordinates of a point strictly on the same side of `(AC)` as `B`. -/
lemma exists_of_sSameSide {A B C X : V} (h : line[ℝ, A, C].SSameSide X B) :
    ∃ s t : ℝ, 0 < s ∧ X - A = s • (B - A) + t • (C - A) := by
  obtain ⟨⟨p₁, hp₁, p₂, hp₂, hr⟩, hX, hB⟩ := h
  obtain ⟨τ₁, h₁⟩ := arcs_mem_line_iff.1 hp₁
  obtain ⟨τ₂, h₂⟩ := arcs_mem_line_iff.1 hp₂
  have hv : X -ᵥ p₁ ≠ 0 := by
    intro h0
    rw [vsub_eq_zero_iff_eq] at h0
    exact hX (h0 ▸ hp₁)
  have hw : B -ᵥ p₂ ≠ 0 := by
    intro h0
    rw [vsub_eq_zero_iff_eq] at h0
    exact hB (h0 ▸ hp₂)
  obtain ⟨r, hr0, hr1⟩ := hr.exists_pos_right hv hw
  refine ⟨r, τ₁ - r * τ₂, hr0, ?_⟩
  simp only [vsub_eq_sub] at hr1
  have e1 : X - p₁ = X - A - (p₁ - A) := by abel
  have e2 : B - p₂ = B - A - (p₂ - A) := by abel
  rw [e1, h₁, e2, h₂] at hr1
  have : X - A = r • (B - A - τ₂ • (C - A)) + τ₁ • (C - A) := by rw [← hr1]; abel
  rw [this]
  module

lemma sSameSide_of_coords {A B C X : V} (hB : B ∉ line[ℝ, A, C]) (hX : X ∉ line[ℝ, A, C])
    {s t : ℝ} (hs : 0 < s) (h : X - A = s • (B - A) + t • (C - A)) :
    line[ℝ, A, C].SSameSide X B := by
  refine ⟨⟨A + t • (C - A), ?_, A, left_mem_affineSpan_pair ℝ A C, ?_⟩, hX, hB⟩
  · exact arcs_mem_line_iff.2 ⟨t, by simp⟩
  · have : X -ᵥ (A + t • (C - A)) = s • (B -ᵥ A) := by
      simp only [vsub_eq_sub]
      rw [sub_add_eq_sub_sub, h]; abel
    rw [this]
    exact SameRay.sameRay_pos_smul_left _ hs

lemma not_mem_line_of_coords {A B C X : V} (hB : B ∉ line[ℝ, A, C]) {s t : ℝ} (hs : s ≠ 0)
    (h : X - A = s • (B - A) + t • (C - A)) : X ∉ line[ℝ, A, C] := by
  intro hX
  obtain ⟨τ, hτ⟩ := arcs_mem_line_iff.1 hX
  apply hB
  rw [arcs_mem_line_iff]
  refine ⟨(τ - t) / s, ?_⟩
  have h1 : s • (B - A) = (τ - t) • (C - A) := by
    rw [hτ] at h
    rw [sub_smul]
    rw [eq_sub_iff_add_eq]
    exact h.symm
  have h2 : B - A = s⁻¹ • (s • (B - A)) := by rw [inv_smul_smul₀ hs]
  rw [h2, h1, smul_smul]
  congr 1
  field_simp

lemma not_mem_line_of_not_collinear {A B C : V} (h : ¬ Collinear ℝ {A, B, C}) :
    B ∉ line[ℝ, A, C] := fun hB => by
  have := collinear_insert_of_mem_affineSpan_pair hB
  rw [Set.insert_comm] at this
  exact h this

lemma exists_center {A B C : V} (h : ¬ Collinear ℝ {A, B, C}) :
    ∃ y : V, dist A y = dist B y ∧ dist A y = dist C y := by
  have hind : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.2 h
  let T : Affine.Triangle ℝ V := ⟨![A, B, C], hind⟩
  have h0 : dist A T.circumcenter = T.circumradius := T.dist_circumcenter_eq_circumradius 0
  have h1 : dist B T.circumcenter = T.circumradius := T.dist_circumcenter_eq_circumradius 1
  have h2 : dist C T.circumcenter = T.circumradius := T.dist_circumcenter_eq_circumradius 2
  exact ⟨T.circumcenter, by rw [h0, h1], by rw [h0, h2]⟩

lemma inv_sub (A U : V) (R : ℝ) :
    inversion A R U - A = (R / ‖U - A‖) ^ 2 • (U - A) := by
  have := inversion_vsub_center A R U
  simpa [dist_eq_norm] using this

lemma wbtw_inv_eq2 {A B C X : V} (hB : B ≠ A) (hC : C ≠ A) (hX : X ≠ A) :
    Wbtw ℝ (inversion A 1 C) (inversion A 1 X) (inversion A 1 B) ↔
      dist A X * dist B C = dist A B * dist C X + dist A C * dist B X := by
  rw [← dist_add_dist_eq_iff, dist_inversion_inversion hC hX, dist_inversion_inversion hX hB,
    dist_inversion_inversion hC hB]
  have hb : 0 < dist B A := dist_pos.2 hB
  have hc : 0 < dist C A := dist_pos.2 hC
  have hx : 0 < dist X A := dist_pos.2 hX
  rw [dist_comm A X, dist_comm A B, dist_comm A C, dist_comm X B, dist_comm B C]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

lemma wbtw_inv_eq3 {A B C X : V} (hB : B ≠ A) (hC : C ≠ A) (hX : X ≠ A) :
    Wbtw ℝ (inversion A 1 C) (inversion A 1 B) (inversion A 1 X) ↔
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X := by
  rw [← dist_add_dist_eq_iff, dist_inversion_inversion hC hB, dist_inversion_inversion hB hX,
    dist_inversion_inversion hC hX]
  have hb : 0 < dist B A := dist_pos.2 hB
  have hc : 0 < dist C A := dist_pos.2 hC
  have hx : 0 < dist X A := dist_pos.2 hX
  rw [dist_comm A X, dist_comm A B, dist_comm A C, dist_comm C B]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

lemma inv_coord {A U : V} : inversion A 1 U - A = (‖U - A‖ ^ 2)⁻¹ • (U - A) := by
  rw [inv_sub, one_div, inv_pow]

lemma sphere_iff {A p y : V} :
    dist p y = dist A y ↔ ‖p - A‖ ^ 2 = 2 * inner ℝ (p - A) (y - A) := by
  have h1 : dist p y ^ 2 = ‖p - A‖ ^ 2 - 2 * inner ℝ (p - A) (y - A) + ‖y - A‖ ^ 2 := by
    have : p - y = (p - A) - (y - A) := by abel
    rw [dist_eq_norm, this, norm_sub_sq_real]
  have h2 : dist A y ^ 2 = ‖y - A‖ ^ 2 := by
    rw [dist_eq_norm, ← norm_neg, neg_sub]
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, h1, h2]
  constructor <;> intro h <;> linarith

lemma ne_of_not_collinear {A B C : V} (h : ¬ Collinear ℝ {A, B, C}) :
    B ≠ A ∧ C ≠ A ∧ B ≠ C := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    exact h (by simpa using collinear_pair ℝ B C)
  · rintro rfl
    exact h (by simpa using collinear_pair ℝ B C)
  · rintro rfl
    exact h (by simpa using collinear_pair ℝ A B)

lemma real_aux {nb nc nx s t : ℝ} (hnb : 0 < nb) (hnc : 0 < nc) (hnx : 0 < nx)
    (hxx : nx = s * nb + t * nc) :
    (nx⁻¹ * s * nb) * nb⁻¹ = nx⁻¹ * s ∧ (1 - nx⁻¹ * s * nb) * nc⁻¹ = nx⁻¹ * t := by
  constructor
  · field_simp
  · field_simp
    linarith

lemma real_aux2 {nb nc nx : ℝ} (α : ℝ) (hnb : nb ≠ 0) (hnc : nc ≠ 0) :
    nx = (nx * α * nb⁻¹) * nb + (nx * (1 - α) * nc⁻¹) * nc := by
  field_simp
  ring

lemma arc_fwd {A B C X : V} (hcol : ¬ Collinear ℝ {A, B, C}) (hXA : X ≠ A)
    (h : Cospherical ({A, B, C, X} : Set V) ∧ line[ℝ, A, C].SSameSide X B) :
    dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X := by
  obtain ⟨hBA, hCA, hBC⟩ := ne_of_not_collinear hcol
  obtain ⟨⟨y, r, hy⟩, hside⟩ := h
  obtain ⟨s, t, hs, hst⟩ := exists_of_sSameSide hside
  have hyA := hy A (by simp)
  have eB := sphere_iff.1 ((hy B (by simp)).trans hyA.symm)
  have eC := sphere_iff.1 ((hy C (by simp)).trans hyA.symm)
  have eX := sphere_iff.1 ((hy X (by simp)).trans hyA.symm)
  have hnb : 0 < ‖B - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hBA)]
  have hnc : 0 < ‖C - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hCA)]
  have hnx : 0 < ‖X - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hXA)]
  have hxx : ‖X - A‖ ^ 2 = s * ‖B - A‖ ^ 2 + t * ‖C - A‖ ^ 2 := by
    rw [eX, hst, inner_add_left, real_inner_smul_left, real_inner_smul_left, eB, eC]
    ring
  set α : ℝ := (‖X - A‖ ^ 2)⁻¹ * s * ‖B - A‖ ^ 2 with hα
  have hα0 : 0 < α := by positivity
  obtain ⟨e1, e2⟩ := real_aux hnb hnc hnx hxx
  have key : inversion A 1 X - A =
      (1 - α) • (inversion A 1 C - A) + α • (inversion A 1 B - A) := by
    rw [inv_coord, inv_coord, inv_coord]
    have h3 : (‖X - A‖ ^ 2)⁻¹ • (X - A) = (‖X - A‖ ^ 2)⁻¹ • (s • (B - A) + t • (C - A)) := by
      rw [← hst]
    rw [h3, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, e1, e2]
    abel
  have hlm : AffineMap.lineMap (inversion A 1 C) (inversion A 1 B) α = inversion A 1 X := by
    rw [AffineMap.lineMap_apply_module]
    linear_combination (norm := module) -key
  rcases le_or_gt α 1 with hα1 | hα1
  · left
    exact (wbtw_inv_eq2 hBA hCA hXA).1 ⟨α, ⟨hα0.le, hα1⟩, hlm⟩
  · right
    refine (wbtw_inv_eq3 hBA hCA hXA).1 ⟨α⁻¹, ⟨by positivity, inv_le_one_of_one_le₀ hα1.le⟩, ?_⟩
    rw [← hlm, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    have hαα : α⁻¹ * α = 1 := inv_mul_cancel₀ hα0.ne'
    linear_combination (norm := module) hαα • (inversion A 1 B - inversion A 1 C)

lemma alpha_of_ptolemy {A B C X : V} (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C) (hXA : X ≠ A)
    (hXC : X ≠ C)
    (h : dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) :
    ∃ α : ℝ, 0 < α ∧
      AffineMap.lineMap (inversion A 1 C) (inversion A 1 B) α = inversion A 1 X := by
  have hinj := inversion_injective A (R := 1) one_ne_zero
  rcases h with h | h
  · obtain ⟨α, ⟨h0, h1⟩, hlm⟩ := (wbtw_inv_eq2 hBA hCA hXA).2 h
    refine ⟨α, lt_of_le_of_ne h0 ?_, hlm⟩
    rintro rfl
    rw [AffineMap.lineMap_apply_zero] at hlm
    exact hXC (hinj hlm).symm
  · obtain ⟨μ, ⟨h0, h1⟩, hlm⟩ := (wbtw_inv_eq3 hBA hCA hXA).2 h
    have hμ : μ ≠ 0 := by
      rintro rfl
      rw [AffineMap.lineMap_apply_zero] at hlm
      exact hBC (hinj hlm).symm
    have hμ0 : 0 < μ := lt_of_le_of_ne h0 (Ne.symm hμ)
    refine ⟨μ⁻¹, inv_pos.2 hμ0, ?_⟩
    have hμμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ
    rw [← hlm, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    linear_combination (norm := module) hμμ • (inversion A 1 X - inversion A 1 C)

lemma arc_bwd {A B C X : V} (hcol : ¬ Collinear ℝ {A, B, C}) (hXA : X ≠ A) (hXC : X ≠ C)
    (h : dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) :
    Cospherical ({A, B, C, X} : Set V) ∧ line[ℝ, A, C].SSameSide X B := by
  obtain ⟨hBA, hCA, hBC⟩ := ne_of_not_collinear hcol
  have hB := not_mem_line_of_not_collinear hcol
  have hinj := inversion_injective A (R := 1) one_ne_zero
  obtain ⟨α, hα0, hlm⟩ := alpha_of_ptolemy hBA hCA hBC hXA hXC h
  have key : inversion A 1 X - A =
      (1 - α) • (inversion A 1 C - A) + α • (inversion A 1 B - A) := by
    rw [← hlm, AffineMap.lineMap_apply_module]
    module
  rw [inv_coord, inv_coord, inv_coord] at key
  have hnb : 0 < ‖B - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hBA)]
  have hnc : 0 < ‖C - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hCA)]
  have hnx : 0 < ‖X - A‖ ^ 2 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hXA)]
  set s : ℝ := ‖X - A‖ ^ 2 * α * (‖B - A‖ ^ 2)⁻¹ with hs
  set t : ℝ := ‖X - A‖ ^ 2 * (1 - α) * (‖C - A‖ ^ 2)⁻¹ with ht
  have hx : X - A = s • (B - A) + t • (C - A) := by
    calc X - A = ‖X - A‖ ^ 2 • ((‖X - A‖ ^ 2)⁻¹ • (X - A)) := by
          rw [smul_inv_smul₀ hnx.ne']
      _ = s • (B - A) + t • (C - A) := by rw [key, hs, ht]; module
  have hs0 : 0 < s := by positivity
  have hsum : ‖X - A‖ ^ 2 = s * ‖B - A‖ ^ 2 + t * ‖C - A‖ ^ 2 := by
    rw [hs, ht]; exact real_aux2 α hnb.ne' hnc.ne'
  obtain ⟨y, hyB, hyC⟩ := exists_center hcol
  have eB := sphere_iff.1 (hyB.symm)
  have eC := sphere_iff.1 (hyC.symm)
  have eX : dist X y = dist A y := by
    rw [sphere_iff]
    calc ‖X - A‖ ^ 2 = s * ‖B - A‖ ^ 2 + t * ‖C - A‖ ^ 2 := hsum
      _ = 2 * (s * inner ℝ (B - A) (y - A) + t * inner ℝ (C - A) (y - A)) := by
          rw [eB, eC]; ring
      _ = 2 * inner ℝ (X - A) (y - A) := by
          rw [hx, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  refine ⟨⟨y, dist A y, ?_⟩, sSameSide_of_coords hB (not_mem_line_of_coords hB hs0.ne' hx) hs0 hx⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h <;> rw [h]
  · exact hyB.symm
  · exact hyC.symm
  · exact eX

theorem arc_iff_ptolemy {A B C X : V} (hcol : ¬ Collinear ℝ {A, B, C}) (hXA : X ≠ A)
    (hXC : X ≠ C) :
    (Cospherical ({A, B, C, X} : Set V) ∧ line[ℝ, A, C].SSameSide X B) ↔
      (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
        dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) :=
  ⟨arc_fwd hcol hXA, arc_bwd hcol hXA hXC⟩

/-! ### The collinear (degenerate) case -/

lemma wbtw_line_iff {A C : V} (hAC : A ≠ C) {r s t : ℝ} :
    Wbtw ℝ (AffineMap.lineMap A C r) (AffineMap.lineMap A C s) (AffineMap.lineMap A C t) ↔
      s ∈ Set.uIcc r t := by
  rw [(AffineMap.lineMap_injective ℝ hAC).wbtw_map_iff (f := AffineMap.lineMap A C),
    ← segment_eq_uIcc, mem_segment_iff_wbtw]

lemma lineMap_of_sub {A C X : V} {ξ : ℝ} (h : X - A = ξ • (C - A)) :
    X = AffineMap.lineMap A C ξ := by
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← h]; abel

lemma inv_line {A C X : V} (hCA : C ≠ A) (hXA : X ≠ A) {ξ : ℝ} (h : X - A = ξ • (C - A)) :
    inversion A 1 X = AffineMap.lineMap A (inversion A 1 C) ξ⁻¹ := by
  have hc : ‖C - A‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hCA)
  have hξ : ξ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact hXA (sub_eq_zero.1 h)
  have h1 := inv_coord (A := A) (U := X)
  have h2 := inv_coord (A := A) (U := C)
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, h2, ← sub_eq_iff_eq_add, h1, h,
    norm_smul, smul_smul, smul_smul]
  congr 1
  rw [Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

lemma sign_lemma {u v : ℝ} (hu : u ≠ 1) (hv : v ≠ 1) :
    (u ∈ Set.uIcc 1 v ∨ v ∈ Set.uIcc 1 u) ↔ ((1 < u ∧ 1 < v) ∨ (u < 1 ∧ v < 1)) := by
  constructor
  · rintro (h | h) <;> simp only [Set.mem_uIcc] at h <;>
      rcases lt_or_gt_of_ne hu with hu' | hu' <;> rcases lt_or_gt_of_ne hv with hv' | hv' <;>
      first
        | exact Or.inl ⟨hu', hv'⟩
        | exact Or.inr ⟨hu', hv'⟩
        | (exfalso; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases le_total u v with h | h <;>
      simp only [Set.mem_uIcc] <;>
      first
        | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
        | exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
        | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

lemma mem_Ioo_iff_inv {x : ℝ} (_h0 : x ≠ 0) (h1 : x ≠ 1) :
    (x ∈ Set.Ioo (0 : ℝ) 1 ↔ 1 < x⁻¹) ∧ (¬ x ∈ Set.Ioo (0 : ℝ) 1 ↔ x⁻¹ < 1) := by
  have e : x ∈ Set.Ioo (0 : ℝ) 1 ↔ 1 < x⁻¹ := by
    rw [one_lt_inv_iff₀, Set.mem_Ioo]
  refine ⟨e, ?_⟩
  rw [e, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h (inv_eq_one.not.2 h1), fun h => h.le⟩

lemma ptolemy_collinear {A B C X : V} {β ξ : ℝ} (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C)
    (hXA : X ≠ A) (hXC : X ≠ C) (hB : B - A = β • (C - A)) (hX : X - A = ξ • (C - A)) :
    (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) ↔
      (ξ ∈ Set.Ioo (0 : ℝ) 1 ↔ β ∈ Set.Ioo (0 : ℝ) 1) := by
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_smul] at hB; exact hBA (sub_eq_zero.1 hB)
  have hβ1 : β ≠ 1 := by
    rintro rfl; rw [one_smul] at hB; exact hBC (sub_left_injective hB)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_smul] at hX; exact hXA (sub_eq_zero.1 hX)
  have hξ1 : ξ ≠ 1 := by
    rintro rfl; rw [one_smul] at hX; exact hXC (sub_left_injective hX)
  have hAC' : A ≠ inversion A 1 C := fun h => hCA ((center_eq_inversion one_ne_zero).1 h)
  rw [← wbtw_inv_eq2 hBA hCA hXA, ← wbtw_inv_eq3 hBA hCA hXA]
  have e := wbtw_line_iff hAC' (r := 1) (s := ξ⁻¹) (t := β⁻¹)
  have e' := wbtw_line_iff hAC' (r := 1) (s := β⁻¹) (t := ξ⁻¹)
  rw [AffineMap.lineMap_apply_one, ← inv_line hCA hXA hX, ← inv_line hCA hBA hB] at e e'
  rw [e, e', sign_lemma (inv_eq_one.not.2 hξ1) (inv_eq_one.not.2 hβ1)]
  have i1 := mem_Ioo_iff_inv hξ0 hξ1
  have i2 := mem_Ioo_iff_inv hβ0 hβ1
  rw [← i1.1, ← i2.1, ← i1.2, ← i2.2]
  clear e e' i1 i2
  generalize (ξ ∈ Set.Ioo (0 : ℝ) 1) = P
  generalize (β ∈ Set.Ioo (0 : ℝ) 1) = Q
  tauto

lemma wbtw_coord_iff {A C P : V} (hAC : A ≠ C) {t : ℝ} (hP : P - A = t • (C - A))
    (h0 : t ≠ 0) (h1 : t ≠ 1) : Wbtw ℝ A P C ↔ t ∈ Set.Ioo (0 : ℝ) 1 := by
  have := wbtw_line_iff hAC (r := 0) (s := t) (t := 1)
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← lineMap_of_sub hP,
    Set.uIcc_of_le zero_le_one] at this
  rw [this, Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm h0), lt_of_le_of_ne b h1⟩
  · rintro ⟨a, b⟩; exact ⟨a.le, b.le⟩

lemma arc_branch_iff {A B C X : V} {β ξ : ℝ} (hAC : A ≠ C) (hBA : B ≠ A)
    (hBC : B ≠ C) (hXA : X ≠ A) (hXC : X ≠ C) (hB : B - A = β • (C - A))
    (hX : X - A = ξ • (C - A)) :
    ((Wbtw ℝ A B C ∧ Wbtw ℝ A X C) ∨ (¬ Wbtw ℝ A B C ∧ X ∈ line[ℝ, A, C] ∧ ¬ Sbtw ℝ A X C)) ↔
      (ξ ∈ Set.Ioo (0 : ℝ) 1 ↔ β ∈ Set.Ioo (0 : ℝ) 1) := by
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_smul] at hB; exact hBA (sub_eq_zero.1 hB)
  have hβ1 : β ≠ 1 := by
    rintro rfl; rw [one_smul] at hB; exact hBC (sub_left_injective hB)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_smul] at hX; exact hXA (sub_eq_zero.1 hX)
  have hξ1 : ξ ≠ 1 := by
    rintro rfl; rw [one_smul] at hX; exact hXC (sub_left_injective hX)
  have wB := wbtw_coord_iff hAC hB hβ0 hβ1
  have wX := wbtw_coord_iff hAC hX hξ0 hξ1
  have sX : Sbtw ℝ A X C ↔ ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [← wX]; exact ⟨fun h => h.1, fun h => ⟨h, hXA, hXC⟩⟩
  have hl : X ∈ line[ℝ, A, C] := arcs_mem_line_iff.2 ⟨ξ, hX⟩
  rw [wB, wX, sX]
  simp only [hl, true_and]
  generalize (ξ ∈ Set.Ioo (0 : ℝ) 1) = P
  generalize (β ∈ Set.Ioo (0 : ℝ) 1) = Q
  tauto

lemma mem_line_of_ptolemy {A B C X : V} {β : ℝ} (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C)
    (hXA : X ≠ A) (hXC : X ≠ C) (hB : B - A = β • (C - A))
    (h : dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) :
    X ∈ line[ℝ, A, C] := by
  obtain ⟨α, hα0, hlm⟩ := alpha_of_ptolemy hBA hCA hBC hXA hXC h
  have k1 : inversion A 1 X - A =
      (1 - α) • (inversion A 1 C - A) + α • (inversion A 1 B - A) := by
    rw [← hlm, AffineMap.lineMap_apply_module]
    module
  rw [inv_coord, inv_coord, inv_coord] at k1
  have hnx : ‖X - A‖ ^ 2 ≠ 0 := by positivity [norm_pos_iff.2 (sub_ne_zero.2 hXA)]
  have e : X - A = ‖X - A‖ ^ 2 • ((‖X - A‖ ^ 2)⁻¹ • (X - A)) := (smul_inv_smul₀ hnx _).symm
  rw [k1, hB] at e
  rw [arcs_mem_line_iff]
  refine ⟨‖X - A‖ ^ 2 * ((1 - α) * (‖C - A‖ ^ 2)⁻¹ +
    α * ((‖β • (C - A)‖ ^ 2)⁻¹ * β)), ?_⟩
  exact e.trans (by module)

end SpaceArcs

open SpaceArcs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The circular arc `ABC` in a real inner product space `V` (for instance `EuclideanSpace ℝ (Fin 3)`):
for non-collinear `A, B, C` it consists of the endpoints `A, C` and of the points `X` of the circle
through `A, B, C` that lie strictly on the same side of the line `(AC)` as `B`.  Here "`X` is on the
circle through `A, B, C`" is expressed as `Cospherical {A, B, C, X}` together with the fact that `X`
lies in the half-plane of `(AC)` containing `B` (which forces `X` into the plane `ABC`), and the side
condition is `AffineSubspace.SSameSide`.  This is the book's definition of an arc (Chapter 9, p. 70)
transported to space; degenerate arcs (collinear `A, B, C`) are not covered by this definition. -/
@[kb "petrunin2025" "Circular arcs (definition), p. 70"]
def arcSpace (A B C : V) : Set V :=
  {X | X = A ∨ X = C ∨ (Cospherical ({A, B, C, X} : Set V) ∧ line[ℝ, A, C].SSameSide X B)}

/-- **Ptolemy characterization of an arc.**  For non-collinear `A, B, C` and a point `X ≠ A, C`,
`X` lies on the arc `ABC` iff one of the two Ptolemy equalities `AX·BC = AB·CX + AC·BX` (cyclic
order `A, B, X, C`) or `AB·CX = AX·BC + AC·BX` (cyclic order `A, X, B, C`) holds.  The proof inverts
at `A`: the circle becomes a line and the equalities become `Wbtw`. -/
theorem mem_arcSpace_iff_ptolemy {A B C X : V} (hcol : ¬ Collinear ℝ {A, B, C}) (hXA : X ≠ A)
    (hXC : X ≠ C) :
    X ∈ arcSpace A B C ↔
      (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
        dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) := by
  simp only [arcSpace, Set.mem_ofPred_eq, hXA, hXC, false_or]
  exact arc_iff_ptolemy hcol hXA hXC

section Invariance

variable {O : V} {R : ℝ}

lemma ptolemy_inv_iff (hR : R ≠ 0) {A B C X : V} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O)
    (hX : X ≠ O) :
    (dist (inversion O R A) (inversion O R X) * dist (inversion O R B) (inversion O R C) =
        dist (inversion O R A) (inversion O R B) * dist (inversion O R C) (inversion O R X) +
          dist (inversion O R A) (inversion O R C) * dist (inversion O R B) (inversion O R X) ∨
      dist (inversion O R A) (inversion O R B) * dist (inversion O R C) (inversion O R X) =
        dist (inversion O R A) (inversion O R X) * dist (inversion O R B) (inversion O R C) +
          dist (inversion O R A) (inversion O R C) * dist (inversion O R B) (inversion O R X)) ↔
    (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
      dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) := by
  have oa : 0 < dist A O := dist_pos.2 hA
  have ob : 0 < dist B O := dist_pos.2 hB
  have oc : 0 < dist C O := dist_pos.2 hC
  have ox : 0 < dist X O := dist_pos.2 hX
  set K : ℝ := R ^ 4 / (dist A O * dist B O * dist C O * dist X O) with hK
  have hK0 : K ≠ 0 := by positivity
  have p1 : dist (inversion O R A) (inversion O R X) * dist (inversion O R B) (inversion O R C) =
      K * (dist A X * dist B C) := by
    rw [dist_inversion_inversion hA hX, dist_inversion_inversion hB hC, hK]
    field_simp
  have p2 : dist (inversion O R A) (inversion O R B) * dist (inversion O R C) (inversion O R X) =
      K * (dist A B * dist C X) := by
    rw [dist_inversion_inversion hA hB, dist_inversion_inversion hC hX, hK]
    field_simp
  have p3 : dist (inversion O R A) (inversion O R C) * dist (inversion O R B) (inversion O R X) =
      K * (dist A C * dist B X) := by
    rw [dist_inversion_inversion hA hC, dist_inversion_inversion hB hX, hK]
    field_simp
  rw [p1, p2, p3, ← mul_add, ← mul_add, mul_right_inj' hK0, mul_right_inj' hK0]

/-- **Inversion maps arcs to arcs** (Petrunin, Theorem 16.5(d), p. 135), pointwise form.  Let `A, B, C`
be non-collinear points of a real inner product space `V` (e.g. `ℝ³`), different from the centre
`O` of an inversion of radius `R ≠ 0`, whose inverses `A', B', C'` are again non-collinear (i.e. the
circle `ABC` does not pass through `O`).  Then for every point `X ≠ O`, `X` lies on the arc `ABC` iff
its inverse lies on the arc `A'B'C'`. -/
@[kb "petrunin2025" "Theorem 16.5(d), p. 135"]
theorem mem_arcSpace_inversion_iff (hR : R ≠ 0) {A B C X : V} (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hcol : ¬ Collinear ℝ {A, B, C})
    (hcol' : ¬ Collinear ℝ {inversion O R A, inversion O R B, inversion O R C}) (hX : X ≠ O) :
    X ∈ arcSpace A B C ↔ inversion O R X ∈ arcSpace (inversion O R A) (inversion O R B)
      (inversion O R C) := by
  have hinj := inversion_injective O hR
  by_cases hXA : X = A
  · subst hXA
    simp [arcSpace]
  by_cases hXC : X = C
  · subst hXC
    simp [arcSpace]
  have hXA' : inversion O R X ≠ inversion O R A := fun h => hXA (hinj h)
  have hXC' : inversion O R X ≠ inversion O R C := fun h => hXC (hinj h)
  rw [mem_arcSpace_iff_ptolemy hcol hXA hXC, mem_arcSpace_iff_ptolemy hcol' hXA' hXC',
    ptolemy_inv_iff hR hA hB hC hX]

/-- **Inversion maps arcs onto arcs** (Petrunin, Theorem 16.5(d), p. 135), set form.  Under the
hypotheses of `mem_arcSpace_inversion_iff`, the inversion maps the arc `ABC` (without the centre `O`,
which it need not contain) onto the arc `A'B'C'` (without `O`).  The general case (arcs through the
centre, lines) is `image_inversion_arcSpace'`. -/
@[kb "petrunin2025" "Theorem 16.5(d), p. 135"]
theorem image_inversion_arcSpace (hR : R ≠ 0) {A B C : V} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O)
    (hcol : ¬ Collinear ℝ {A, B, C})
    (hcol' : ¬ Collinear ℝ {inversion O R A, inversion O R B, inversion O R C}) :
    inversion O R '' (arcSpace A B C \ {O}) =
      arcSpace (inversion O R A) (inversion O R B) (inversion O R C) \ {O} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hXO⟩, rfl⟩
    exact ⟨(mem_arcSpace_inversion_iff hR hA hB hC hcol hcol' hXO).1 hX,
      by simpa [inversion_eq_center hR] using hXO⟩
  · rintro ⟨hY, hYO⟩
    have hYO' : Y ≠ O := hYO
    refine ⟨inversion O R Y, ⟨?_, by simpa [inversion_eq_center hR] using hYO'⟩,
      inversion_inversion O hR Y⟩
    rw [mem_arcSpace_inversion_iff hR hA hB hC hcol hcol'
      (by simpa [inversion_eq_center hR] using hYO'), inversion_inversion O hR Y]
    exact hY

end Invariance

section Degenerate

variable {O : V} {R : ℝ}

/-- The circline arc `ABC` for any three distinct points of a real inner product space, following the
book's convention (Chapter 9, p. 70): for non-collinear `A, B, C` it is `arcSpace A B C`; for
collinear `A, B, C` it is the segment `[AC]` if `B` lies between `A` and `C`, and otherwise the
union of the two closed half-lines of the line `(AC)` bounded by `A` and `C` and not meeting the open
segment `(AC)`. -/
@[kb "petrunin2025" "Circline arcs, degenerate arcs (definition), p. 70"]
def arcSpace' (A B C : V) : Set V :=
  {X | (¬ Collinear ℝ {A, B, C} ∧ X ∈ arcSpace A B C) ∨
    (Collinear ℝ {A, B, C} ∧ ((Wbtw ℝ A B C ∧ Wbtw ℝ A X C) ∨
      (¬ Wbtw ℝ A B C ∧ X ∈ line[ℝ, A, C] ∧ ¬ Sbtw ℝ A X C)))}

/-- For non-collinear points `arcSpace'` is `arcSpace`. -/
theorem arcSpace'_eq_of_not_collinear {A B C : V} (h : ¬ Collinear ℝ {A, B, C}) :
    arcSpace' A B C = arcSpace A B C := by
  ext X
  simp [arcSpace', h]

/-- The endpoint `A` lies on the arc. -/
theorem left_mem_arcSpace' {A B C : V} : A ∈ arcSpace' A B C := by
  by_cases h : Collinear ℝ {A, B, C}
  · by_cases hw : Wbtw ℝ A B C
    · exact Or.inr ⟨h, Or.inl ⟨hw, wbtw_self_left ℝ A C⟩⟩
    · exact Or.inr ⟨h, Or.inr ⟨hw, left_mem_affineSpan_pair ℝ A C, fun hs => hs.ne_left rfl⟩⟩
  · exact Or.inl ⟨h, Or.inl rfl⟩

/-- The endpoint `C` lies on the arc. -/
theorem right_mem_arcSpace' {A B C : V} : C ∈ arcSpace' A B C := by
  by_cases h : Collinear ℝ {A, B, C}
  · by_cases hw : Wbtw ℝ A B C
    · exact Or.inr ⟨h, Or.inl ⟨hw, wbtw_self_right ℝ A C⟩⟩
    · exact Or.inr ⟨h, Or.inr ⟨hw, right_mem_affineSpan_pair ℝ A C, fun hs => hs.ne_right rfl⟩⟩
  · exact Or.inl ⟨h, Or.inr (Or.inl rfl)⟩

/-- **Ptolemy characterization of a circline arc** (all cases, including degenerate arcs): for
distinct `A, B, C` and `X ≠ A, C`, `X` lies on the arc `ABC` iff one of the two Ptolemy equalities
holds.  (For collinear points these equalities are the `Wbtw` distance identities.) -/
theorem mem_arcSpace'_iff_ptolemy {A B C X : V} (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C)
    (hXA : X ≠ A) (hXC : X ≠ C) :
    X ∈ arcSpace' A B C ↔
      (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
        dist A B * dist C X = dist A X * dist B C + dist A C * dist B X) := by
  by_cases hcol : Collinear ℝ {A, B, C}
  · have hBl : B ∈ line[ℝ, A, C] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hCA.symm
    obtain ⟨β, hB⟩ := arcs_mem_line_iff.1 hBl
    have key : X ∈ line[ℝ, A, C] →
        (((Wbtw ℝ A B C ∧ Wbtw ℝ A X C) ∨
          (¬ Wbtw ℝ A B C ∧ X ∈ line[ℝ, A, C] ∧ ¬ Sbtw ℝ A X C)) ↔
        (dist A X * dist B C = dist A B * dist C X + dist A C * dist B X ∨
          dist A B * dist C X = dist A X * dist B C + dist A C * dist B X)) := by
      intro hX
      obtain ⟨ξ, hξ⟩ := arcs_mem_line_iff.1 hX
      rw [arc_branch_iff hCA.symm hBA hBC hXA hXC hB hξ,
        ptolemy_collinear hBA hCA hBC hXA hXC hB hξ]
    have hmem : X ∈ arcSpace' A B C ↔ ((Wbtw ℝ A B C ∧ Wbtw ℝ A X C) ∨
        (¬ Wbtw ℝ A B C ∧ X ∈ line[ℝ, A, C] ∧ ¬ Sbtw ℝ A X C)) := by
      simp [arcSpace', hcol]
    rw [hmem]
    constructor
    · intro h
      have hX : X ∈ line[ℝ, A, C] := by
        rcases h with ⟨_, h⟩ | ⟨_, h, _⟩
        · exact h.mem_affineSpan
        · exact h
      exact (key hX).1 h
    · intro h
      exact (key (mem_line_of_ptolemy hBA hCA hBC hXA hXC hB h)).2 h
  · rw [arcSpace'_eq_of_not_collinear hcol]
    exact mem_arcSpace_iff_ptolemy hcol hXA hXC

/-- **Inversion maps circline arcs to circline arcs** (Petrunin, Theorem 16.5(d), p. 135), pointwise
form, without any collinearity hypothesis: for distinct `A, B, C` different from the centre `O`, and
`X ≠ O`, `X` lies on the arc `ABC` iff `X'` lies on the arc `A'B'C'`.  Arcs through the centre `O`
(which become lines or half-lines, in the book's inversive space completed by `∞`) and lines are
covered; the points `O` and `∞` are simply left out. -/
@[kb "petrunin2025" "Theorem 16.5(d), p. 135"]
theorem mem_arcSpace'_inversion_iff (hR : R ≠ 0) {A B C X : V} (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C) (hX : X ≠ O) :
    X ∈ arcSpace' A B C ↔ inversion O R X ∈ arcSpace' (inversion O R A) (inversion O R B)
      (inversion O R C) := by
  have hinj := inversion_injective O hR
  have hBA' : inversion O R B ≠ inversion O R A := fun h => hBA (hinj h)
  have hCA' : inversion O R C ≠ inversion O R A := fun h => hCA (hinj h)
  have hBC' : inversion O R B ≠ inversion O R C := fun h => hBC (hinj h)
  by_cases hXA : X = A
  · subst hXA
    exact ⟨fun _ => left_mem_arcSpace', fun _ => left_mem_arcSpace'⟩
  by_cases hXC : X = C
  · subst hXC
    exact ⟨fun _ => right_mem_arcSpace', fun _ => right_mem_arcSpace'⟩
  have hXA' : inversion O R X ≠ inversion O R A := fun h => hXA (hinj h)
  have hXC' : inversion O R X ≠ inversion O R C := fun h => hXC (hinj h)
  rw [mem_arcSpace'_iff_ptolemy hBA hCA hBC hXA hXC,
    mem_arcSpace'_iff_ptolemy hBA' hCA' hBC' hXA' hXC', ptolemy_inv_iff hR hA hB hC hX]

/-- **Inversion maps circline arcs onto circline arcs** (Petrunin, Theorem 16.5(d), p. 135), set form
for arbitrary distinct `A, B, C ≠ O`: the inversion maps the arc `ABC` minus `O` onto the arc `A'B'C'`
minus `O`.  The only point of the inversive space not accounted for is `O ↔ ∞`: an arc through `O`
becomes an unbounded arc (line or half-line) and vice versa. -/
@[kb "petrunin2025" "Theorem 16.5(d), p. 135"]
theorem image_inversion_arcSpace' (hR : R ≠ 0) {A B C : V} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O)
    (hBA : B ≠ A) (hCA : C ≠ A) (hBC : B ≠ C) :
    inversion O R '' (arcSpace' A B C \ {O}) =
      arcSpace' (inversion O R A) (inversion O R B) (inversion O R C) \ {O} := by
  ext Y
  constructor
  · rintro ⟨X, ⟨hX, hXO⟩, rfl⟩
    exact ⟨(mem_arcSpace'_inversion_iff hR hA hB hC hBA hCA hBC hXO).1 hX,
      by simpa [inversion_eq_center hR] using hXO⟩
  · rintro ⟨hY, hYO⟩
    have hYO' : Y ≠ O := hYO
    have hYO'' : inversion O R Y ≠ O := by simpa [inversion_eq_center hR] using hYO'
    refine ⟨inversion O R Y, ⟨?_, hYO''⟩, inversion_inversion O hR Y⟩
    rw [mem_arcSpace'_inversion_iff hR hA hB hC hBA hCA hBC hYO'', inversion_inversion O hR Y]
    exact hY

end Degenerate

end UndergradKB.Geometry
