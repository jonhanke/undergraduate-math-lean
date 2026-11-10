import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.Convex.Side
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import UndergradKB.Common.Attr

/-! # Lines, half-planes and Pasch (Petrunin, chapters 1-3)

The discrete metric (p. 11), motions of the real line (Exercise 1.6), points on a half-line
(Exercise 1.12), two lines meet in at most one point (Proposition 2.2), doubled angles and collinearity
(Exercise 2.10), sides of a line and signs of oriented angles (Proposition 3.10, Corollary 3.11,
Exercise 3.14), Pasch's theorem (3.13) and crossing cevians (Exercise 3.15). Lines in the plane are
affine subspaces with one-dimensional direction. -/

namespace UndergradKB.Geometry

open EuclideanGeometry AffineSubspace

section Plane

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a 2-dimensional space, two points off a line are strictly on the same side or strictly on
opposite sides. -/
theorem sSameSide_or_sOppSide [Fact (Module.finrank ℝ V = 2)] {ℓ : AffineSubspace ℝ P}
    (hℓ : Module.finrank ℝ ℓ.direction = 1) {x y : P} (hx : x ∉ ℓ) (hy : y ∉ ℓ) :
    ℓ.SSameSide x y ∨ ℓ.SOppSide x y := by
  have hne : ℓ ≠ ⊥ := by
    rintro rfl
    rw [direction_bot, finrank_bot] at hℓ
    exact absurd hℓ (by norm_num)
  have : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (n := 1) (Fact.out (p := Module.finrank ℝ V = 2))
  obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot ℓ).2 hne
  have hv : y -ᵥ p ∉ ℓ.direction := fun h =>
    hy (by simpa using AffineSubspace.vadd_mem_of_mem_direction h hp)
  have htop : ℓ.direction ⊔ (ℝ ∙ (y -ᵥ p)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hv, hℓ, Fact.out (p := Module.finrank ℝ V = 2)]
  have hx' : x -ᵥ p ∈ ℓ.direction ⊔ (ℝ ∙ (y -ᵥ p)) := by rw [htop]; trivial
  obtain ⟨d, hd, w, hw, hdw⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hp' : d +ᵥ p ∈ ℓ := AffineSubspace.vadd_mem_of_mem_direction hd hp
  have hxe : x -ᵥ (d +ᵥ p) = a • (y -ᵥ p) := by
    rw [vsub_vadd_eq_vsub_sub, ← hdw]; abel
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    have : x = d +ᵥ p := by simpa using hxe
    rw [this]; exact hp'
  rcases lt_or_gt_of_ne ha with h | h
  · right
    refine ⟨⟨_, hp', p, hp, Or.inr (Or.inr ⟨1, -a, one_pos, by linarith, ?_⟩)⟩, hx, hy⟩
    rw [hxe, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]; simp
  · left
    refine ⟨⟨_, hp', p, hp, Or.inr (Or.inr ⟨1, a, one_pos, h, ?_⟩)⟩, hx, hy⟩
    rw [hxe]; simp

/-- The line `ℓ` meets the closed segment `[XY]`. -/
def LineMeetsSegment (ℓ : AffineSubspace ℝ P) (X Y : P) : Prop :=
  ∃ Z ∈ ℓ, Z ∈ affineSegment ℝ X Y

/-- A segment between two points off a line meets the line iff the points are strictly on opposite
sides of it. -/
theorem segment_meets_iff_sOppSide {ℓ : AffineSubspace ℝ P} {x y : P} (hx : x ∉ ℓ) (hy : y ∉ ℓ) :
    LineMeetsSegment ℓ x y ↔ ℓ.SOppSide x y := by
  rw [SOppSide, wOppSide_iff_exists_wbtw]
  simp only [hx, hy, not_false_eq_true, and_self, and_true]
  exact Iff.rfl

/-- **Pasch's theorem** (Petrunin, Theorem 3.13): a line `ℓ` passing through no vertex of a triangle
`ABC` in the plane meets either none or exactly two of the three sides (closed segments).
(The nondegeneracy of the triangle is not needed.) -/
@[kb "petrunin2025" "Pasch's theorem 3.13, p. 27"]
theorem pasch [Fact (Module.finrank ℝ V = 2)] {ℓ : AffineSubspace ℝ P}
    (hℓ : Module.finrank ℝ ℓ.direction = 1) {A B C : P} (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ) :
    (¬LineMeetsSegment ℓ A B ∧ ¬LineMeetsSegment ℓ B C ∧ ¬LineMeetsSegment ℓ C A) ∨
    (LineMeetsSegment ℓ A B ∧ LineMeetsSegment ℓ B C ∧ ¬LineMeetsSegment ℓ C A) ∨
    (LineMeetsSegment ℓ A B ∧ ¬LineMeetsSegment ℓ B C ∧ LineMeetsSegment ℓ C A) ∨
    (¬LineMeetsSegment ℓ A B ∧ LineMeetsSegment ℓ B C ∧ LineMeetsSegment ℓ C A) := by
  rw [segment_meets_iff_sOppSide hA hB, segment_meets_iff_sOppSide hB hC,
    segment_meets_iff_sOppSide hC hA]
  rcases sSameSide_or_sOppSide hℓ hA hB with h1 | h1 <;>
    rcases sSameSide_or_sOppSide hℓ hB hC with h2 | h2 <;>
    rcases sSameSide_or_sOppSide hℓ hC hA with h3 | h3
  · exact Or.inl ⟨h1.not_sOppSide, h2.not_sOppSide, h3.not_sOppSide⟩
  · exact absurd h3.symm (h1.trans h2).not_sOppSide
  · exact absurd h3.symm (h1.trans_sOppSide h2).not_sSameSide
  · exact Or.inr (Or.inr (Or.inr ⟨h1.not_sOppSide, h2, h3⟩))
  · exact absurd h3.symm (h1.trans_sSameSide h2).not_sSameSide
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.not_sOppSide, h3⟩))
  · exact Or.inr (Or.inl ⟨h1, h2, h3.not_sOppSide⟩)
  · exact absurd h3.symm (h1.trans h2).not_sOppSide

end Plane

section Cevians

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Vector from `A` to a point of the segment `[BC]`, written in terms of `B -ᵥ A` and `C -ᵥ A`. -/
theorem lineMap_vsub_aux (A B C : P) (s : ℝ) :
    AffineMap.lineMap B C s -ᵥ A = (1 - s) • (B -ᵥ A) + s • (C -ᵥ A) := by
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right C B A]
  module

/-- **Crossing cevians** (Petrunin, Exercise 3.15): if `A'` lies on the segment `[BC]` and `B'` on the
segment `[AC]`, then the segments `[AA']` and `[BB']` have a common point. (Nondegeneracy of the
triangle is not needed.) -/
@[kb "petrunin2025" "Exercise 3.15, p. 28"]
theorem exists_wbtw_cevians {A B C A' B' : P} (hA' : Wbtw ℝ B A' C) (hB' : Wbtw ℝ A B' C) :
    ∃ X, Wbtw ℝ A X A' ∧ Wbtw ℝ B X B' := by
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hA'
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hB'
  by_cases hD : s + t - s * t = 0
  · have hs : s = 0 := by nlinarith
    have ht : t = 0 := by subst hs; linarith
    subst hs ht
    exact ⟨A, by simp, by simp⟩
  · have hDpos : 0 < s + t - s * t := by
      rcases lt_or_gt_of_ne hD with h | h
      · nlinarith
      · exact h
    refine ⟨AffineMap.lineMap A (AffineMap.lineMap B C s) (t / (s + t - s * t)), ⟨_, ⟨?_, ?_⟩, rfl⟩,
      ⟨s / (s + t - s * t), ⟨?_, ?_⟩, ?_⟩⟩
    · positivity
    · rw [div_le_one hDpos]; nlinarith
    · positivity
    · rw [div_le_one hDpos]; nlinarith
    · apply vsub_left_cancel (p := A)
      have h1 : AffineMap.lineMap A (AffineMap.lineMap B C s) (t / (s + t - s * t)) -ᵥ A =
          (t / (s + t - s * t)) • ((1 - s) • (B -ᵥ A) + s • (C -ᵥ A)) := by
        rw [AffineMap.lineMap_vsub_left, lineMap_vsub_aux]
      have h2 : AffineMap.lineMap B (AffineMap.lineMap A C t) (s / (s + t - s * t)) -ᵥ A =
          (s / (s + t - s * t)) • (t • (C -ᵥ A) - (B -ᵥ A)) + (B -ᵥ A) := by
        rw [← vsub_add_vsub_cancel _ B A, AffineMap.lineMap_vsub_left,
          ← vsub_sub_vsub_cancel_right _ B A, AffineMap.lineMap_vsub_left]
      rw [h1, h2]
      match_scalars
      all_goals field_simp
      ring

end Cevians

section Lines

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Two lines meet in at most one point** (Petrunin, Proposition 2.2): lines are the affine
subspaces with one-dimensional direction; two distinct ones share at most one point. -/
@[kb "petrunin2025" "Proposition 2.2, p. 20"]
theorem eq_of_mem_inter_of_ne {ℓ₁ ℓ₂ : AffineSubspace ℝ P} (h₁ : Module.finrank ℝ ℓ₁.direction = 1)
    (h₂ : Module.finrank ℝ ℓ₂.direction = 1) (hne : ℓ₁ ≠ ℓ₂) {x y : P} (hx₁ : x ∈ ℓ₁)
    (hx₂ : x ∈ ℓ₂) (hy₁ : y ∈ ℓ₁) (hy₂ : y ∈ ℓ₂) : x = y := by
  by_contra hxy
  have hv : y -ᵥ x ≠ 0 := vsub_ne_zero.2 (Ne.symm hxy)
  apply hne
  apply AffineSubspace.ext_of_direction_eq _ ⟨x, hx₁, hx₂⟩
  rw [eq_span_singleton_of_mem_of_finrank_eq_one h₁ (AffineSubspace.vsub_mem_direction hy₁ hx₁) hv,
    eq_span_singleton_of_mem_of_finrank_eq_one h₂ (AffineSubspace.vsub_mem_direction hy₂ hx₂) hv]

/-- The line through two distinct points has a one-dimensional direction. -/
theorem finrank_direction_line {P₁ P₂ : P} (h : P₁ ≠ P₂) :
    Module.finrank ℝ (line[ℝ, P₁, P₂]).direction = 1 := by
  rw [direction_affineSpan]
  have := (affineIndependent_of_ne ℝ h).finrank_vectorSpan (n := 1) (by simp)
  have hr : Set.range ![P₁, P₂] = {P₁, P₂} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]; simp [Set.pair_comm]
  rwa [hr] at this

end Lines

section Oriented

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Collinearity via doubled angles** (Petrunin, Exercise 2.10): for points `A, B, C` different
from `O` in an oriented plane, `B, O, C` are collinear iff `2∡AOB = 2∡AOC`. -/
@[kb "petrunin2025" "Exercise 2.10, p. 22"]
theorem collinear_iff_two_zsmul_oangle_eq {O A B C : P} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O) :
    Collinear ℝ ({B, O, C} : Set P) ↔ (2 : ℤ) • ∡ A O B = (2 : ℤ) • ∡ A O C := by
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff,
    ← oangle_add hB hA hC, oangle_rev B O A, smul_add, smul_neg]
  exact neg_eq_iff_add_eq_zero.symm

/-- For a point off the line `PQ`, the sign of the angle `∡PXQ` is nonzero. -/
theorem oangle_sign_ne_zero_of_notMem {P₁ P₂ X : P} (h : X ∉ line[ℝ, P₁, P₂]) (h₁₂ : P₁ ≠ P₂) :
    (∡ P₁ X P₂).sign ≠ 0 := by
  intro h0
  rw [Real.Angle.sign_eq_zero_iff, oangle_eq_zero_or_eq_pi_iff_collinear] at h0
  exact h (h0.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h₁₂)

/-- **Same side iff same sign of `∡PXQ`** (Petrunin, Exercise 3.14). -/
@[kb "petrunin2025" "Exercise 3.14, p. 28"]
theorem sSameSide_iff_oangle_sign_eq {P₁ P₂ X Y : P} (h₁₂ : P₁ ≠ P₂) (hX : X ∉ line[ℝ, P₁, P₂])
    (hY : Y ∉ line[ℝ, P₁, P₂]) :
    line[ℝ, P₁, P₂].SSameSide X Y ↔ (∡ P₁ X P₂).sign = (∡ P₁ Y P₂).sign := by
  constructor
  · intro h
    exact (h.oangle_sign_eq (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)).symm
  · intro h
    rcases sSameSide_or_sOppSide (finrank_direction_line h₁₂) hX hY with h' | h'
    · exact h'
    · exfalso
      have h2 := h'.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ P₁ P₂)
        (right_mem_affineSpan_pair ℝ P₁ P₂)
      have h3 := oangle_sign_ne_zero_of_notMem hX h₁₂
      rw [← h] at h2
      revert h2 h3
      generalize (∡ P₁ X P₂).sign = z
      decide +revert

/-- **Half-planes and the sign of `∡PQX`** (Petrunin, Proposition 3.10, Corollary 3.11): for points
`X, Y` off the line `PQ`, the following are equivalent: the angles `∡PQX`, `∡PQY` have the same
sign; the segment `[XY]` does not meet the line; `X` and `Y` lie strictly on the same side. -/
@[kb "petrunin2025" "Proposition 3.10, p. 26"]
theorem oangle_sign_eq_iff_not_meets {P₁ P₂ X Y : P} (h₁₂ : P₁ ≠ P₂) (hX : X ∉ line[ℝ, P₁, P₂])
    (hY : Y ∉ line[ℝ, P₁, P₂]) :
    (∡ P₁ P₂ X).sign = (∡ P₁ P₂ Y).sign ↔ ¬LineMeetsSegment line[ℝ, P₁, P₂] X Y := by
  have key : ∀ Z : P, (∡ P₁ P₂ Z).sign = -(∡ P₁ Z P₂).sign := fun Z => by
    rw [oangle_swap₁₃_sign P₁ Z P₂]
    exact (oangle_rotate_sign P₁ P₂ Z).symm
  rw [key X, key Y, neg_inj, ← sSameSide_iff_oangle_sign_eq h₁₂ hX hY,
    segment_meets_iff_sOppSide hX hY]
  rcases sSameSide_or_sOppSide (finrank_direction_line h₁₂) hX hY with h | h
  · simp [h, h.not_sOppSide]
  · simp [h, h.not_sSameSide]

/-- **Half-planes** (Petrunin, Corollary 3.11): for `X, Y` off the line `PQ`, they lie strictly on the
same side iff `∡PQX` and `∡PQY` have the same sign. -/
@[kb "petrunin2025" "Corollary 3.11, p. 27"]
theorem sSameSide_iff_oangle_sign_eq_left {P₁ P₂ X Y : P} (h₁₂ : P₁ ≠ P₂)
    (hX : X ∉ line[ℝ, P₁, P₂]) (hY : Y ∉ line[ℝ, P₁, P₂]) :
    line[ℝ, P₁, P₂].SSameSide X Y ↔ (∡ P₁ P₂ X).sign = (∡ P₁ P₂ Y).sign := by
  rw [oangle_sign_eq_iff_not_meets h₁₂ hX hY, segment_meets_iff_sOppSide hX hY]
  rcases sSameSide_or_sOppSide (finrank_direction_line h₁₂) hX hY with h | h
  · simp [h, h.not_sOppSide]
  · simp [h, h.not_sSameSide]

end Oriented

section Misc

/-- A type synonym carrying the discrete metric. -/
def DiscreteMetricSpace (X : Type*) : Type _ := X

open Classical in
/-- **The discrete metric** (Petrunin, Example on p. 11): the distance is `0` between equal points
and `1` otherwise. -/
@[kb "petrunin2025" "Discrete metric, p. 11"]
noncomputable instance DiscreteMetricSpace.instMetricSpace (X : Type*) :
    MetricSpace (DiscreteMetricSpace X) where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by simp only [eq_comm]
  dist_triangle x y z := by
    by_cases hxy : x = y <;> by_cases hyz : y = z <;> by_cases hxz : x = z <;> simp_all
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    simp [hne] at h

open Classical in
theorem DiscreteMetricSpace.dist_def {X : Type*} (x y : DiscreteMetricSpace X) :
    dist x y = if x = y then 0 else 1 := rfl

/-- **Motions of the real line** (Petrunin, Exercise 1.6): every motion `f` of `ℝ` is either
`x ↦ f 0 + x` or `x ↦ f 0 - x`. -/
@[kb "petrunin2025" "Exercise 1.6, p. 12"]
theorem isometryEquiv_real (f : ℝ ≃ᵢ ℝ) :
    (∀ x, f x = f 0 + x) ∨ (∀ x, f x = f 0 - x) := by
  have hd : ∀ x y, (f x - f y) ^ 2 = (x - y) ^ 2 := fun x y => by
    rw [← sq_abs, ← Real.dist_eq, f.dist_eq, Real.dist_eq, sq_abs]
  have h0 : ∀ x, (f x - f 0) = x ∨ (f x - f 0) = -x := fun x => by
    have := hd x 0
    rw [sub_zero] at this
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  have h1 := hd 1
  rcases h0 1 with e | e
  · left
    intro x
    rcases h0 x with ex | ex
    · linarith
    · have := h1 x
      have hx : x = 0 := by nlinarith
      subst hx; linarith
  · right
    intro x
    rcases h0 x with ex | ex
    · have := h1 x
      have hx : x = 0 := by nlinarith
      subst hx; linarith
    · linarith

end Misc

section HalfLine

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Unique point on a half-line at a given distance** (Petrunin, Exercise 1.12): on the half-line
`[PQ)` (the points `lineMap P Q t`, `t ≥ 0`) with `P ≠ Q`, for each `r ≥ 0` there is exactly one
point `X` with `PX = r`. -/
@[kb "petrunin2025" "Exercise 1.12, p. 13"]
theorem existsUnique_halfLine_dist {P₁ Q : P} (h : P₁ ≠ Q) {r : ℝ} (hr : 0 ≤ r) :
    ∃! X : P, (∃ t : ℝ, 0 ≤ t ∧ X = AffineMap.lineMap P₁ Q t) ∧ dist P₁ X = r := by
  have hd : 0 < dist P₁ Q := dist_pos.2 h
  refine ⟨AffineMap.lineMap P₁ Q (r / dist P₁ Q), ⟨⟨_, by positivity, rfl⟩, ?_⟩, ?_⟩
  · rw [dist_left_lineMap, Real.norm_of_nonneg (by positivity)]
    field_simp
  · rintro X ⟨⟨t, ht, rfl⟩, hX⟩
    rw [dist_left_lineMap, Real.norm_of_nonneg ht] at hX
    have : t = r / dist P₁ Q := by field_simp; linarith
    rw [this]

end HalfLine

end UndergradKB.Geometry
