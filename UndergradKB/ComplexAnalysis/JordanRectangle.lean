import UndergradKB.ComplexAnalysis.Rectangle

/-!
# The Jordan curve theorem for rectangles (row CX-161, special case)

Beck et al. assume the Jordan curve theorem in Section 4.4: a simple closed path divides the plane
into exactly two connected open sets, a bounded inside and an unbounded outside, and the path is
the boundary of each. The general theorem is not in Mathlib. Here it is proved for the boundary of
a rectangle traversed by `rectPath`: the complement of the path is the disjoint union of the open
rectangle and the complement of the closed rectangle, these are its two connected components, the
first is bounded and the second unbounded, and the path is the frontier of both.
-/

open Set Metric Complex Topology

namespace UndergradKB.ComplexAnalysis

variable {x₀ x₁ y₀ y₁ : ℝ}

/-- The trace of the rectangular path is the closed rectangle minus the open rectangle. -/
theorem pathImage_rectPath (hx : x₀ < x₁) (hy : y₀ < y₁) :
    pathImage (rectPath x₀ x₁ y₀ y₁) = closedRect x₀ x₁ y₀ y₁ \ openRect x₀ x₁ y₀ y₁ := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact rectPath_mem_boundary hx hy ht
  · rintro z ⟨hz, hz'⟩
    exact mem_pathImage_rectPath hx hy hz hz'

lemma openRect_subset_closedRect : openRect x₀ x₁ y₀ y₁ ⊆ closedRect x₀ x₁ y₀ y₁ := by
  intro z hz
  simp only [mem_reProdIm, mem_Icc, mem_Ioo] at hz ⊢
  exact ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2.1.le, hz.2.2.le⟩

lemma convex_openRect : Convex ℝ (openRect x₀ x₁ y₀ y₁) :=
  ((convex_Ioo x₀ x₁).linear_preimage reLm).inter ((convex_Ioo y₀ y₁).linear_preimage imLm)

lemma closure_openRect (hx : x₀ < x₁) (hy : y₀ < y₁) :
    closure (openRect x₀ x₁ y₀ y₁) = closedRect x₀ x₁ y₀ y₁ := by
  rw [closure_reProdIm, closure_Ioo hx.ne, closure_Ioo hy.ne]

lemma interior_closedRect : interior (closedRect x₀ x₁ y₀ y₁) = openRect x₀ x₁ y₀ y₁ := by
  rw [interior_reProdIm, interior_Icc, interior_Icc]

/-- The complement of the closed rectangle is connected: it is the union of four open half planes,
each meeting the next. -/
theorem isConnected_compl_closedRect : IsConnected (closedRect x₀ x₁ y₀ y₁)ᶜ := by
  have e : (closedRect x₀ x₁ y₀ y₁)ᶜ =
      ({z : ℂ | x₁ < z.re} ∪ {z : ℂ | y₁ < z.im}) ∪ ({z : ℂ | z.re < x₀} ∪ {z : ℂ | z.im < y₀}) := by
    ext z
    simp only [mem_compl_iff, mem_reProdIm, mem_Icc, mem_union, mem_ofPred_eq]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      exact h ⟨⟨h'.2.1, h'.1.1⟩, h'.2.2, h'.1.2⟩
    · rintro ((h | h) | (h | h)) ⟨⟨h1, h2⟩, h3, h4⟩ <;> linarith
  have hre : ∀ a : ℝ, IsPreconnected {z : ℂ | a < z.re} := fun a =>
    (convex_halfSpace_re_gt a).isPreconnected
  have hre' : ∀ a : ℝ, IsPreconnected {z : ℂ | z.re < a} := fun a =>
    (convex_halfSpace_re_lt a).isPreconnected
  have him : ∀ a : ℝ, IsPreconnected {z : ℂ | a < z.im} := fun a =>
    (convex_halfSpace_im_gt a).isPreconnected
  have him' : ∀ a : ℝ, IsPreconnected {z : ℂ | z.im < a} := fun a =>
    (convex_halfSpace_im_lt a).isPreconnected
  rw [e]
  refine ⟨⟨⟨x₁ + 1, 0⟩, Or.inl (Or.inl (by simp))⟩, ?_⟩
  have hA : IsPreconnected ({z : ℂ | x₁ < z.re} ∪ {z : ℂ | y₁ < z.im}) :=
    (hre x₁).union ⟨x₁ + 1, y₁ + 1⟩ (by simp) (by simp) (him y₁)
  have hB : IsPreconnected ({z : ℂ | z.re < x₀} ∪ {z : ℂ | z.im < y₀}) :=
    (hre' x₀).union ⟨x₀ - 1, y₀ - 1⟩ (by simp) (by simp) (him' y₀)
  refine hA.union ⟨x₀ - 1, y₁ + 1⟩ (Or.inr (by simp)) (Or.inl (by simp)) hB

lemma not_isBounded_compl_closedRect : ¬ Bornology.IsBounded (closedRect x₀ x₁ y₀ y₁)ᶜ := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall 0
  have hmem : ((|M| + |x₁| + 1 : ℝ) : ℂ) ∈ (closedRect x₀ x₁ y₀ y₁)ᶜ := by
    simp only [mem_compl_iff, mem_reProdIm, mem_Icc, ofReal_re, not_and]
    intro _ h
    linarith [le_abs_self x₁, abs_nonneg M]
  have := hM hmem
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
  rw [abs_of_nonneg (by positivity)] at this
  linarith [le_abs_self M, abs_nonneg x₁]

/-- **The Jordan curve theorem for rectangles** (Beck, Section 4.4, assumed there in general):
the complement of the rectangular path is the union of the open rectangle and the complement of
the closed rectangle; these are disjoint, open and connected, the first is bounded and the second
is not, and the path is the frontier of each. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem jordan_curve_rectPath (hx : x₀ < x₁) (hy : y₀ < y₁) :
    (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ = openRect x₀ x₁ y₀ y₁ ∪ (closedRect x₀ x₁ y₀ y₁)ᶜ ∧
    Disjoint (openRect x₀ x₁ y₀ y₁) (closedRect x₀ x₁ y₀ y₁)ᶜ ∧
    IsOpen (openRect x₀ x₁ y₀ y₁) ∧ IsOpen (closedRect x₀ x₁ y₀ y₁)ᶜ ∧
    IsConnected (openRect x₀ x₁ y₀ y₁) ∧ IsConnected (closedRect x₀ x₁ y₀ y₁)ᶜ ∧
    Bornology.IsBounded (openRect x₀ x₁ y₀ y₁) ∧ ¬ Bornology.IsBounded (closedRect x₀ x₁ y₀ y₁)ᶜ ∧
    frontier (openRect x₀ x₁ y₀ y₁) = pathImage (rectPath x₀ x₁ y₀ y₁) ∧
    frontier (closedRect x₀ x₁ y₀ y₁)ᶜ = pathImage (rectPath x₀ x₁ y₀ y₁) := by
  have hP := pathImage_rectPath hx hy
  refine ⟨?_, ?_, isOpen_Ioo.reProdIm isOpen_Ioo, (isClosed_Icc.reProdIm isClosed_Icc).isOpen_compl,
    ?_, isConnected_compl_closedRect,
    (isCompact_Icc.reProdIm isCompact_Icc).isBounded.subset openRect_subset_closedRect,
    not_isBounded_compl_closedRect, ?_, ?_⟩
  · rw [hP]
    ext z
    simp only [mem_compl_iff, mem_sdiff, not_and, not_not, mem_union]
    constructor
    · intro h
      by_cases hc : z ∈ closedRect x₀ x₁ y₀ y₁
      · exact Or.inl (h hc)
      · exact Or.inr hc
    · rintro (h | h) hc
      · exact h
      · exact absurd hc h
  · rw [Set.disjoint_compl_right_iff_subset]
    exact openRect_subset_closedRect
  · refine ⟨⟨⟨(x₀ + x₁) / 2, (y₀ + y₁) / 2⟩, ?_⟩,
      convex_openRect.isPreconnected⟩
    simp only [mem_reProdIm, mem_Ioo]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rw [frontier, closure_openRect hx hy, (isOpen_Ioo.reProdIm isOpen_Ioo).interior_eq, hP]
  · rw [frontier_compl, frontier, (isClosed_Icc.reProdIm isClosed_Icc).closure_eq,
      interior_closedRect, hP]

/-- The connected component of a point of the open rectangle in the complement of the path is the
open rectangle (the inside). -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem connectedComponentIn_compl_rectPath_of_mem (hx : x₀ < x₁) (hy : y₀ < y₁) {z : ℂ}
    (h : z ∈ openRect x₀ x₁ y₀ y₁) :
    connectedComponentIn (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ z = openRect x₀ x₁ y₀ y₁ := by
  obtain ⟨hU, -, hO1, -, hC1, -, -, -, -, -⟩ := jordan_curve_rectPath hx hy
  have hP := pathImage_rectPath hx hy
  have hz' : z ∈ (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ := hU ▸ Or.inl h
  refine Subset.antisymm ?_ (hC1.isPreconnected.subset_connectedComponentIn h
    (hU ▸ subset_union_left))
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hO1
    ⟨z, mem_connectedComponentIn hz', h⟩ ?_
  rintro y ⟨hy1, hy2⟩
  rw [closure_openRect hx hy] at hy1
  by_contra hyo
  exact connectedComponentIn_subset _ _ hy2 (hP ▸ ⟨hy1, hyo⟩)

/-- The connected component of a point outside the closed rectangle in the complement of the path
is the complement of the closed rectangle (the outside). -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem connectedComponentIn_compl_rectPath_of_not_mem (hx : x₀ < x₁) (hy : y₀ < y₁) {z : ℂ}
    (hzo : z ∉ closedRect x₀ x₁ y₀ y₁) :
    connectedComponentIn (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ z = (closedRect x₀ x₁ y₀ y₁)ᶜ := by
  obtain ⟨hU, -, -, hO2, -, hC2, -, -, -, -⟩ := jordan_curve_rectPath hx hy
  have hP := pathImage_rectPath hx hy
  have hz' : z ∈ (pathImage (rectPath x₀ x₁ y₀ y₁))ᶜ := hU ▸ Or.inr hzo
  refine Subset.antisymm ?_ (hC2.isPreconnected.subset_connectedComponentIn hzo
    (hU ▸ subset_union_right))
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hO2
    ⟨z, mem_connectedComponentIn hz', hzo⟩ ?_
  rintro y ⟨hy1, hy2⟩
  rw [closure_compl, interior_closedRect] at hy1
  intro hyc
  exact connectedComponentIn_subset _ _ hy2 (hP ▸ ⟨hyc, hy1⟩)

end UndergradKB.ComplexAnalysis
