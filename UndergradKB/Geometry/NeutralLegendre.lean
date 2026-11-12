import UndergradKB.Geometry.NeutralCongruence
import UndergradKB.Common.Attr

/-! # Neutral plane V: Saccheri-Legendre theory (Petrunin, Chapter 11, Sections A-C)

For every neutral plane (Axioms I-IV): hypotenuse-leg congruence (11.1), side-angle-angle (11.7),
Exercise 11.8, the hinge proposition (11.9), Legendre's theorem that the angle sum of a triangle is at most `π`
(11.10), the quadrangle inequality of Exercise 11.11 (in a general form), additivity of the defect (11.12),
Exercise 11.13 and Exercise 11.14 (opposite sides of a rectangle are equal).

The inequality `AB ≤ CD` for a quadrangle with right angles at `A` and `B` (Exercise 11.11) is proved by the
reflection trick of Legendre's proof: the reflections across the perpendiculars at `A` and `B` compose to a map
moving `(AB)` along itself by `2·AB`, and moving `D` by at most `2·CD`. -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-! ### Small helpers -/

private theorem degenerate_map (f : P ≃ᵢ P) {A B C : P} (h : IsTriangle.Degenerate A B C) :
    IsTriangle.Degenerate (f A) (f B) (f C) := by
  obtain ⟨L, ⟨g, hg, rfl⟩, hA, hB, hC⟩ := h
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  exact ⟨Set.range (f ∘ g), ⟨f ∘ g, f.isometry.comp hg, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩

private theorem degenerate_unrotate {A B C : P} (h : IsTriangle.Degenerate B C A) :
    IsTriangle.Degenerate A B C := by
  obtain ⟨L, hL, hB, hC, hA⟩ := h
  exact ⟨L, hL, hA, hB, hC⟩

private theorem isBetween_map (f : P ≃ᵢ P) {A B C : P} (h : IsBetween A B C) :
    IsBetween (f A) (f B) (f C) := by
  refine ⟨fun e => h.1 (f.injective e), fun e => h.2.1 (f.injective e), ?_, degenerate_map f h.degenerate⟩
  rw [f.dist_eq, f.dist_eq, f.dist_eq]
  exact h.dist_add

include N in
/-- Two points between `A` and `B` at the same distance from `A` coincide. -/
private theorem isBetween_unique {A M M' B : P} (h : IsBetween A M B) (h' : IsBetween A M' B)
    (hd : dist A M = dist A M') : M = M' := by
  refine (N.isLine_line h.ne).eq_of_dist_eq (N.left_mem_line _ _) (N.right_mem_line _ _)
    (N.mem_line_of_isBetween h) (N.mem_line_of_isBetween h') h.ne hd ?_
  have e1 := h.dist_add
  have e2 := h'.dist_add
  rw [dist_comm B M, dist_comm B M']
  linarith

include N in
/-- Reflecting `A` across the line `(CB)`, where `∠ACB` is right. -/
private theorem right_reflect {A B C : P} (hAB : A ≠ B) (hA : A ≠ C) (hB : B ≠ C)
    (h : N.uangle A C B = π / 2) :
    ∃ D, IsBetween A C D ∧ dist C D = dist C A ∧ dist B D = dist B A ∧ B ≠ D := by
  have hL := N.isLine_line hB.symm
  have hBL : B ∈ N.line C B := N.right_mem_line C B
  have hCL : C ∈ N.line C B := N.left_mem_line C B
  have hr : N.uangle B C A = π / 2 := by rw [N.uangle_comm hB hA]; exact h
  obtain ⟨h1, h2⟩ := N.isBetween_lineRefl_of_perp hL hBL hCL hB hA hr
  refine ⟨N.lineRefl hL A, h1, h2, ?_, ?_⟩
  · have := (N.lineRefl hL).dist_eq B A
    rw [N.lineRefl_fix hL hBL] at this
    exact this
  · intro e
    have : N.lineRefl hL B = N.lineRefl hL A := by rw [N.lineRefl_fix hL hBL]; exact e
    exact hAB ((N.lineRefl hL).injective this).symm

/-- **Theorem 11.1 (hypotenuse-leg).** Right triangles with equal hypotenuses and one pair of equal legs are
congruent. -/
@[kb "petrunin2025" "Theorem 11.1, p. 83"]
theorem hypotenuse_leg {A B C A' B' C' : P} (hT : IsTriangle A B C) (hT' : IsTriangle A' B' C')
    (hC : N.uangle A C B = π / 2) (hC' : N.uangle A' C' B' = π / 2) (h₁ : dist A B = dist A' B')
    (h₂ : dist A C = dist A' C') : TriangleCongruent A B C A' B' C' := by
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := N.right_reflect hT.1 (fun e => hT.2.2 e.symm) hT.2.1 hC
  obtain ⟨D', hD1', hD2', hD3', hD4'⟩ :=
    N.right_reflect hT'.1 (fun e => hT'.2.2 e.symm) hT'.2.1 hC'
  have hAD : dist A D = dist A' D' := by
    have e1 := hD1.dist_add
    have e2 := hD1'.dist_add
    rw [hD2] at e1
    rw [hD2'] at e2
    rw [← e1, ← e2, dist_comm C A, dist_comm C' A', h₂]
  have hcong : TriangleCongruent A B D A' B' D' := by
    refine N.sss ⟨hT.1, hD4, hD1.ne.symm⟩ ⟨hT'.1, hD4', hD1'.ne.symm⟩ h₁.symm ?_ ?_
    · rw [hD3, hD3', dist_comm B' A', dist_comm B A, h₁]
    · rw [dist_comm D' A', dist_comm D A, hAD]
  obtain ⟨f, hfA, hfB, hfD⟩ := hcong
  refine ⟨f, hfA, hfB, ?_⟩
  have hm := isBetween_map f hD1
  rw [hfA, hfD] at hm
  refine N.isBetween_unique hm hD1' ?_
  rw [← hfA, f.dist_eq, h₂, hfA]

/-- A principal value of absolute value `0` or `π` is a degenerate (straight or zero) angle. -/
private theorem abs_toReal_eq_zero_or_pi (x : Real.Angle) :
    (|x.toReal| = 0 ∨ |x.toReal| = π) ↔ (x = 0 ∨ x = π) := by
  constructor
  · rintro (h | h)
    · left
      exact Real.Angle.toReal_eq_zero_iff.1 (abs_eq_zero.1 h)
    · right
      rcases (abs_eq Real.pi_pos.le).1 h with h | h
      · exact Real.Angle.toReal_eq_pi_iff.1 h
      · exfalso
        have := Real.Angle.neg_pi_lt_toReal x
        linarith
  · rintro (rfl | rfl)
    · left
      simp
    · right
      rw [Real.Angle.toReal_pi, abs_of_pos Real.pi_pos]

include N in
private theorem uangle_zero_or_pi_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    (N.uangle A O B = 0 ∨ N.uangle A O B = π) ↔ IsTriangle.Degenerate A O B := by
  rw [N.degenerate_iff_angle hA hB, ← abs_toReal_eq_zero_or_pi]
  rfl

include N in
private theorem isBetween_of_mem_ray_of_dist_lt {B X Z : P} (hBZ : B ≠ Z) (hX : X ∈ metricHalfLine B Z)
    (hXB : X ≠ B) (hd : dist B X < dist B Z) : IsBetween B X Z := by
  have h1 : dist Z X = |dist B Z - dist B X| := N.dist_of_mem_metricHalfLine hBZ hX
  have hpos : 0 < dist B X := dist_pos.2 hXB.symm
  have h2 : dist X Z = dist B Z - dist B X := by
    rw [dist_comm, h1, abs_of_nonneg (by linarith)]
  exact N.isBetween_of_mem_line hBZ (N.metricHalfLine_subset_line hBZ hX) hXB
    (fun e => by rw [e] at hd; exact lt_irrefl _ hd) hd (by rw [h2]; linarith)

/-- The far angle is smaller than the near one (exterior angle). -/
private theorem uangle_far_lt_near {A B X Y : P} (hXY : IsBetween B X Y) (hA : A ∉ N.line B Y) :
    N.uangle A Y B < N.uangle A X B := by
  have hAY : A ≠ Y := fun e => hA (by rw [e]; exact N.right_mem_line B Y)
  have h := N.uangle_lt_exterior (A := Y) (B := A) (C := B) (D := X) hXY.symm
    (by rw [N.line_comm]; exact hA)
  have e : N.uangle X Y A = N.uangle A Y B := by
    have hr := (IsBetween.mem_metricHalfLine N hXY.symm).1
    have : N.angle X Y A = N.angle B Y A := N.angle_ray_left hXY.ne hr hXY.2.1 hAY
    unfold NeutralPlane.uangle
    rw [this]
    exact N.uangle_comm hXY.ne hAY
  rw [e] at h
  exact h

/-- **Exercise 11.7 (side-angle-angle).** -/
@[kb "petrunin2025" "Exercise 11.7, p. 85"]
theorem saa {A B C A' B' C' : P} (hT : IsTriangle A B C) (hT' : IsTriangle A' B' C')
    (hnd' : ¬ IsTriangle.Degenerate A' B' C') (h₁ : dist A B = dist A' B')
    (h₂ : N.uangle A B C = N.uangle A' B' C') (h₃ : N.uangle B C A = N.uangle B' C' A') :
    TriangleCongruent A B C A' B' C' := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hAB', hBC', hCA'⟩ := hT'
  have hnd : ¬ IsTriangle.Degenerate A B C := by
    intro hd
    apply hnd'
    rw [← N.uangle_zero_or_pi_iff hAB' hBC'.symm, ← h₂]
    exact (N.uangle_zero_or_pi_iff hAB hBC.symm).2 hd
  have hAnl : A ∉ N.line B C := fun h =>
    hnd (degenerate_unrotate ((N.degenerate_iff_mem_line hBC).2 h))
  obtain ⟨C'', ⟨hC''r, hd⟩, huniq⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hBC (dist_nonneg : 0 ≤ dist B' C')
  have hC''B : C'' ≠ B := by
    intro e
    rw [e, dist_self] at hd
    exact hBC' (dist_eq_zero.1 hd.symm)
  have hC''l : C'' ∈ N.line B C := N.metricHalfLine_subset_line hBC hC''r
  have hAC'' : A ≠ C'' := fun e => hAnl (by rw [e]; exact hC''l)
  have hang : N.uangle C'' B A = N.uangle C B A := by
    unfold NeutralPlane.uangle
    rw [N.angle_ray_left hBC.symm hC''r hC''B hAB]
  have hcong : TriangleCongruent B A C'' B' A' C' := by
    refine N.sas hAB.symm hC''B.symm hAC'' hAB'.symm hBC' hCA'.symm ?_ hd.symm ?_
    · rw [dist_comm B' A', dist_comm B A]
      exact h₁.symm
    · rw [N.uangle_comm hBC'.symm hAB', ← h₂, N.uangle_comm hAB hBC.symm, hang]
  obtain ⟨f, hfB, hfA, hfC⟩ := hcong
  have hu : N.uangle A' C' B' = N.uangle A C'' B := by
    rw [← hfA, ← hfB, ← hfC]
    exact N.uangle_isometryEquiv f hAC'' hC''B.symm
  have key : N.uangle A C'' B = N.uangle A C B := by
    rw [← hu, N.uangle_comm hCA'.symm hBC', ← h₃, N.uangle_comm hBC hCA.symm]
  have hCC : C'' = C := by
    by_contra hne
    rcases lt_trichotomy (dist B C'') (dist B C) with hlt | heq | hgt
    · have hb : IsBetween B C'' C := N.isBetween_of_mem_ray_of_dist_lt hBC hC''r hC''B hlt
      have := N.uangle_far_lt_near hb hAnl
      linarith
    · exact hne (huniq C ⟨N.self_mem_metricHalfLine hBC, by rw [← heq]; exact hd⟩).symm
    · have hray : metricHalfLine B C'' = metricHalfLine B C := N.metricHalfLine_eq_of_mem hBC hC''r hC''B
      have hCr : C ∈ metricHalfLine B C'' := by
        rw [hray]
        exact N.self_mem_metricHalfLine hBC
      have hb : IsBetween B C C'' := N.isBetween_of_mem_ray_of_dist_lt hC''B.symm hCr hBC.symm hgt
      have hl : N.line B C'' = N.line B C :=
        N.line_eq_of_mem hBC (N.left_mem_line B C) hC''l hC''B.symm
      have := N.uangle_far_lt_near hb (by rw [hl]; exact hAnl)
      linarith
  exact ⟨f, hfA, hfB, hCC ▸ hfC⟩

private theorem nd_left {A B C D : P} (hD : IsBetween A D B) (hC : C ∉ N.line A B) :
    IsTriangle A D C ∧ ¬ IsTriangle.Degenerate A D C := by
  have hCA : C ≠ A := fun e => hC (by rw [e]; exact N.left_mem_line A B)
  have hCD : C ≠ D := fun e => hC (by rw [e]; exact N.mem_line_of_isBetween hD)
  refine ⟨⟨hD.1.symm, hCD.symm, hCA⟩, fun hd => hC ?_⟩
  have := (N.degenerate_iff_mem_line hD.1.symm).1 hd
  rwa [N.line_eq_of_mem hD.ne (N.left_mem_line A B) (N.mem_line_of_isBetween hD) hD.1.symm] at this

private theorem nd_right {A B C D : P} (hD : IsBetween A D B) (hC : C ∉ N.line A B) :
    IsTriangle B D C ∧ ¬ IsTriangle.Degenerate B D C := by
  have hCB : C ≠ B := fun e => hC (by rw [e]; exact N.right_mem_line A B)
  have hCD : C ≠ D := fun e => hC (by rw [e]; exact N.mem_line_of_isBetween hD)
  refine ⟨⟨hD.2.1.symm, hCD.symm, hCB⟩, fun hd => hC ?_⟩
  have := (N.degenerate_iff_mem_line hD.2.1.symm).1 hd
  rwa [N.line_eq_of_mem hD.ne (N.right_mem_line A B) (N.mem_line_of_isBetween hD) hD.2.1.symm] at this

include N in
/-- **Exercise 11.8.** If `D` lies between `A` and `B`, then `CD < CA` or `CD < CB`. -/
@[kb "petrunin2025" "Exercise 11.8, p. 85"]
theorem dist_lt_or_dist_lt_of_isBetween {A B C D : P} (hD : IsBetween A D B) :
    dist C D < dist C A ∨ dist C D < dist C B := by
  have hAB : A ≠ B := hD.ne
  by_cases hC : C ∈ N.line A B
  · obtain ⟨t, rfl⟩ := N.exists_linePt_eq hAB hC
    obtain ⟨s, hs⟩ := N.exists_linePt_eq hAB (N.mem_line_of_isBetween hD)
    have hB : N.linePt A B (dist A B) = B := N.linePt_dist hAB
    have hAD : dist A D = |s| := by rw [← hs]; exact N.dist_left_linePt hAB s
    have hDB : dist D B = |s - dist A B| := by
      have := N.dist_linePt hAB s (dist A B)
      rwa [hs, hB] at this
    have hCD : dist (N.linePt A B t) D = |t - s| := by
      have := N.dist_linePt hAB t s
      rwa [hs] at this
    have hCA : dist (N.linePt A B t) A = |t| := by
      rw [dist_comm, N.dist_left_linePt hAB]
    have hCB : dist (N.linePt A B t) B = |t - dist A B| := by
      have := N.dist_linePt hAB t (dist A B)
      rwa [hB] at this
    have h1 := hD.dist_add
    have p1 : 0 < dist A D := dist_pos.2 hD.1.symm
    have p2 : 0 < dist D B := dist_pos.2 hD.2.1
    rw [hAD, hDB] at h1
    rw [hAD] at p1
    rw [hDB] at p2
    rw [hCD, hCA, hCB]
    have hs0 : 0 < s ∧ s < dist A B := by
      rcases abs_cases s with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
        rcases abs_cases (s - dist A B) with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> constructor <;> linarith
    rcases le_or_gt t s with h | h
    · right
      rcases abs_cases (t - s) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
        rcases abs_cases (t - dist A B) with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> linarith [hs0.1, hs0.2]
    · left
      rcases abs_cases (t - s) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
        rcases abs_cases t with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> linarith [hs0.1, hs0.2]
  · have hq : π = N.uangle A D C + N.uangle C D B :=
      (N.uangle_add_uangle_of_isBetween hD hC).1.symm
    obtain ⟨hT1, hn1⟩ := N.nd_left hD hC
    obtain ⟨hT2, hn2⟩ := N.nd_right hD hC
    by_cases hh : π / 2 ≤ N.uangle A D C
    · left
      have h5 := (N.dist_lt_iff_uangle_lt hT1 hn1).2
      have h6 := N.uangle_add_uangle_lt_pi hT1 hn1
      rw [dist_comm C D, dist_comm C A]
      exact h5 (by linarith)
    · right
      have h5 := (N.dist_lt_iff_uangle_lt hT2 hn2).2
      have h6 := N.uangle_add_uangle_lt_pi hT2 hn2
      have e := N.uangle_comm hT2.1 hT2.2.1.symm
      rw [dist_comm C D, dist_comm C B]
      exact h5 (by linarith)

include N in
/-- A point at a prescribed positive distance and angle (Axiom IIIa and Exercise 1.12). -/
private theorem exists_pt' {O A : P} (hA : A ≠ O) {r : ℝ} (hr : 0 < r) (α : Real.Angle) :
    ∃ B, dist O B = r ∧ N.angle A O B = α := by
  obtain ⟨D, hD, hang, -⟩ := N.axiomIIIa O A hA α
  obtain ⟨B, ⟨hB, hd⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hD.symm hr.le
  have hBO : B ≠ O := by
    intro e
    rw [e, dist_self] at hd
    linarith
  exact ⟨B, hd, by rw [N.angle_ray_right hA hD hB hBO, hang]⟩

include N in
/-- Two points at the same distance from `C` making the same angle with a half-line coincide. -/
private theorem eq_of_angle_dist {A C B0 B1 : P} (hA : A ≠ C) (hB0 : B0 ≠ C) (hB1 : B1 ≠ C)
    (hd : dist C B0 = dist C B1) (h : N.angle A C B0 = N.angle A C B1) : B0 = B1 := by
  have h0 : N.angle B1 C B0 = 0 := by
    have := N.axiomIIIb C B1 A B0 hB1 hA hB0
    rw [N.angle_rev hB1 hA, ← h, neg_add_cancel] at this
    exact this.symm
  have hray : B0 ∈ metricHalfLine C B1 := N.mem_ray_of_angle_eq_zero hB1 hB0 h0
  obtain ⟨x, -, huniq⟩ := N.existsUnique_mem_metricHalfLine_dist hB1.symm (dist_nonneg : 0 ≤ dist C B1)
  exact (huniq B0 ⟨hray, hd⟩).trans (huniq B1 ⟨N.self_mem_metricHalfLine hB1.symm, rfl⟩).symm

include N in
/-- Replacing `B` by its mirror image in `(AC)` if necessary, the angle `∡ACB` becomes nonnegative. -/
private theorem exists_normal {A C B : P} (hA : A ≠ C) (hB : B ≠ C) :
    ∃ B0, B0 ≠ C ∧ dist C B0 = dist C B ∧ dist A B0 = dist A B ∧
      N.angle A C B0 = ((N.uangle A C B : ℝ) : Real.Angle) := by
  by_cases hs : 0 ≤ (N.angle A C B).sign
  · exact ⟨B, hB, rfl, rfl, (Real.Angle.coe_abs_toReal_of_sign_nonneg hs).symm⟩
  · have hs' : (N.angle A C B).sign ≤ 0 := (not_le.1 hs).le
    have hL := N.isLine_line hA
    obtain ⟨σ, hfix, -, -, hang⟩ := N.exists_lineRefl hL
    have hσA : σ A = A := hfix A (N.left_mem_line A C)
    have hσC : σ C = C := hfix C (N.right_mem_line A C)
    refine ⟨σ B, ?_, ?_, ?_, ?_⟩
    · intro e
      apply hB
      apply σ.injective
      rw [hσC]
      exact e
    · have := σ.dist_eq C B
      rwa [hσC] at this
    · have := σ.dist_eq A B
      rwa [hσA] at this
    · have h := hang A C B hA hB
      rw [hσA, hσC] at h
      rw [h]
      have h2 := Real.Angle.neg_coe_abs_toReal_of_sign_nonpos hs'
      rw [N.uangle_def]
      exact neg_eq_iff_eq_neg.2 h2.symm

private theorem sign_coe_pos' {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π) : (θ : Real.Angle).sign = 1 := by
  rw [Real.Angle.sign, Real.Angle.sin_coe]
  exact sign_pos (Real.sin_pos_of_pos_of_lt_pi h0 h1)

include N in
/-- The core of the hinge theorem: the reflection trick across the bisector. -/
private theorem hinge_core {A C B0 B1 : P} {t0 t1 : ℝ} (hA : A ≠ C) (hB0 : B0 ≠ C) (hB1 : B1 ≠ C)
    (hd : dist C B0 = dist C B1) (h0 : N.angle A C B0 = (t0 : Real.Angle))
    (h1 : N.angle A C B1 = (t1 : Real.Angle)) (ht0 : 0 ≤ t0) (hlt : t0 < t1) (ht1 : t1 ≤ π) :
    dist A B0 < dist A B1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (t0 + t1) / 2 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (t1 - t0) / 2 := ⟨_, rfl⟩
  have hpi := Real.pi_pos
  have hm0 : 0 < m := by linarith
  have hmpi : m < π := by linarith
  have hh0 : 0 < h := by linarith
  have hhpi : h < π := by linarith
  obtain ⟨X, hXd, hAX⟩ := N.exists_pt' hA one_pos (m : Real.Angle)
  have hXC : X ≠ C := by
    intro e
    rw [e, dist_self] at hXd
    exact zero_ne_one hXd
  have hL := N.isLine_line hXC
  have hCl : C ∈ N.line X C := N.right_mem_line X C
  have hXl : X ∈ N.line X C := N.left_mem_line X C
  obtain ⟨σ, hfix, -, hσσ, hang⟩ := N.exists_lineRefl hL
  have hσC : σ C = C := hfix C hCl
  have hσX : σ X = X := hfix X hXl
  have eXA : N.angle X C A = ((-m : ℝ) : Real.Angle) := by
    rw [N.angle_rev hXC hA, hAX, Real.Angle.coe_neg]
  have eXB0 : N.angle X C B0 = ((-h : ℝ) : Real.Angle) := by
    have := N.axiomIIIb C X A B0 hXC hA hB0
    rw [eXA, h0, ← Real.Angle.coe_add] at this
    rw [← this]
    congr 1
    linarith
  have eXσ : N.angle X C (σ B0) = (h : Real.Angle) := by
    have := hang X C B0 hXC hB0
    rw [hσX, hσC, eXB0, ← Real.Angle.coe_neg, neg_neg] at this
    exact this
  have hσB0C : σ B0 ≠ C := by
    intro e
    apply hB0
    apply σ.injective
    rw [hσC]
    exact e
  have eAσ : N.angle A C (σ B0) = (t1 : Real.Angle) := by
    have := N.axiomIIIb C A X (σ B0) hA hXC hσB0C
    rw [hAX, eXσ, ← Real.Angle.coe_add] at this
    rw [← this]
    congr 1
    linarith
  have hσB0 : σ B0 = B1 := by
    refine N.eq_of_angle_dist hA hσB0C hB1 ?_ (eAσ.trans h1.symm)
    have := σ.dist_eq C B0
    rw [hσC] at this
    rw [this, hd]
  -- signs
  have sgnA : (N.angle X C A).sign = -1 := by
    rw [eXA, Real.Angle.coe_neg, Real.Angle.sign_neg, sign_coe_pos' hm0 hmpi]
  have sgnB0 : (N.angle X C B0).sign = -1 := by
    rw [eXB0, Real.Angle.coe_neg, Real.Angle.sign_neg, sign_coe_pos' hh0 hhpi]
  have sgnσA : (N.angle X C (σ A)).sign = 1 := by
    have := hang X C A hXC hA
    rw [hσX, hσC, eXA, ← Real.Angle.coe_neg, neg_neg] at this
    rw [this, sign_coe_pos' hm0 hmpi]
  have hAn : A ∉ N.line X C := fun hmem =>
    by
      have := (N.sign_angle_eq_zero_iff hXC hA).2 ((N.degenerate_iff_mem_line hXC).2 hmem)
      rw [sgnA] at this
      exact absurd this (by decide)
  have hB0n : B0 ∉ N.line X C := fun hmem =>
    by
      have := (N.sign_angle_eq_zero_iff hXC hB0).2 ((N.degenerate_iff_mem_line hXC).2 hmem)
      rw [sgnB0] at this
      exact absurd this (by decide)
  have hσAn : σ A ∉ N.line X C := fun hmem => by
    have h1 := hfix _ hmem
    rw [hσσ] at h1
    exact hAn (h1 ▸ hmem)
  have hSame : SameSide (N.line X C) A B0 :=
    (N.sameSide_iff_sign hXC hAn hB0n).2 (by rw [sgnA, sgnB0])
  have hNot : ¬ SameSide (N.line X C) (σ A) B0 := fun hs => by
    have := (N.sameSide_iff_sign hXC hσAn hB0n).1 hs
    rw [sgnσA, sgnB0] at this
    exact absurd this (by decide)
  obtain ⟨Z, hZl, hZb⟩ := N.exists_mem_line_of_not_sameSide hXC hσAn hB0n hNot
  have hZσ : σ Z = Z := hfix Z hZl
  have e1 : dist (σ A) Z = dist A Z := by
    have := σ.dist_eq (σ A) Z
    rw [hZσ, hσσ] at this
    exact this.symm
  have hsum := hZb.dist_add
  have hne : dist A Z + dist Z B0 ≠ dist A B0 := fun e => hSame.2.2 ⟨Z, hZl, e⟩
  have hle := dist_triangle A Z B0
  have e2 : dist (σ A) B0 = dist A B1 := by
    have := σ.dist_eq (σ A) B0
    rw [hσσ, hσB0] at this
    exact this.symm
  calc dist A B0 < dist A Z + dist Z B0 := lt_of_le_of_ne hle (fun e => hne e.symm)
    _ = dist (σ A) B0 := by rw [← hsum, e1]
    _ = dist A B1 := e2

include N in
/-- Transport a triangle with the same apex distance and angle onto the half-line `[CA)`. -/
private theorem exists_transport {A C A' C' B' : P} (hA : A ≠ C) (hA' : A' ≠ C') (hB' : B' ≠ C')
    (h₁ : dist A C = dist A' C') (hpos : 0 < N.uangle A' C' B') :
    ∃ B1, B1 ≠ C ∧ dist C B1 = dist C' B' ∧ dist A B1 = dist A' B' ∧
      N.angle A C B1 = ((N.uangle A' C' B' : ℝ) : Real.Angle) := by
  have hCB' : 0 < dist C' B' := dist_pos.2 hB'.symm
  obtain ⟨B1, hd, hang⟩ := N.exists_pt' hA hCB' ((N.uangle A' C' B' : ℝ) : Real.Angle)
  have hB1C : B1 ≠ C := by
    intro e
    rw [e, dist_self] at hd
    linarith
  have hu1 : N.uangle A C B1 = N.uangle A' C' B' := by
    rw [N.uangle_def, hang]
    exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨N.uangle_nonneg _ _ _, N.uangle_le_pi _ _ _⟩
  have hAB1 : A ≠ B1 := by
    intro e
    rw [← e] at hu1
    have : N.uangle A C A = 0 := by
      rw [N.uangle_def, N.angle_self hA]
      simp
    linarith
  have hA'B' : A' ≠ B' := by
    intro e
    rw [← e] at hpos
    have : N.uangle A' C' A' = 0 := by
      rw [N.uangle_def, N.angle_self hA']
      simp
    linarith
  have hcong : TriangleCongruent C A B1 C' A' B' := by
    refine N.sas hA.symm hB1C.symm hAB1 hA'.symm hB'.symm hA'B' ?_ hd.symm ?_
    · rw [dist_comm C' A', dist_comm C A]
      exact h₁.symm
    · rw [N.uangle_comm hB' hA', N.uangle_comm hB1C hA, hu1]
  exact ⟨B1, hB1C, hd, (TriangleCongruent.dist_eq hcong).2.1.symm, hang⟩

include N in
private theorem hinge_lt {A B C A' B' C' : P} (hA : A ≠ C) (hB : B ≠ C) (hA' : A' ≠ C') (hB' : B' ≠ C')
    (h₁ : dist A C = dist A' C') (h₂ : dist B C = dist B' C')
    (hlt : N.uangle A C B < N.uangle A' C' B') : dist A B < dist A' B' := by
  obtain ⟨B0, hB0C, hd0, hA0, hang0⟩ := N.exists_normal hA hB
  obtain ⟨B1, hB1C, hd1, hA1, hang1⟩ :=
    N.exists_transport hA hA' hB' h₁ ((N.uangle_nonneg A C B).trans_lt hlt)
  have := N.hinge_core hA hB0C hB1C (by rw [hd0, hd1, dist_comm C B, h₂, dist_comm B' C'])
    hang0 hang1 (N.uangle_nonneg A C B) hlt (N.uangle_le_pi A' C' B')
  rw [hA0, hA1] at this
  exact this

include N in
private theorem hinge_eq {A B C A' B' C' : P} (hA : A ≠ C) (hB : B ≠ C) (hA' : A' ≠ C') (hB' : B' ≠ C')
    (h₁ : dist A C = dist A' C') (h₂ : dist B C = dist B' C')
    (heq : N.uangle A C B = N.uangle A' C' B') : dist A B = dist A' B' := by
  rcases (N.uangle_nonneg A C B).eq_or_lt with h0 | hpos
  · have h0' : N.uangle A' C' B' = 0 := by rw [← heq, ← h0]
    have hB1 : B ∈ metricHalfLine C A := (N.uangle_eq_zero_iff hA hB).1 h0.symm
    have hB1' : B' ∈ metricHalfLine C' A' := (N.uangle_eq_zero_iff hA' hB').1 h0'
    rw [N.dist_of_mem_metricHalfLine hA.symm hB1, N.dist_of_mem_metricHalfLine hA'.symm hB1']
    rw [dist_comm C A, dist_comm C B, dist_comm C' A', dist_comm C' B', h₁, h₂]
  · obtain ⟨B0, hB0C, hd0, hA0, hang0⟩ := N.exists_normal hA hB
    obtain ⟨B1, hB1C, hd1, hA1, hang1⟩ := N.exists_transport hA hA' hB' h₁ (by rw [← heq]; exact hpos)
    have hB01 : B0 = B1 :=
      N.eq_of_angle_dist hA hB0C hB1C (by rw [hd0, hd1, dist_comm C B, h₂, dist_comm B' C'])
        (hang0.trans ((congrArg (fun x : ℝ => (x : Real.Angle)) heq).trans hang1.symm))
    rw [← hA0, ← hA1, hB01]

/-- **Proposition 11.9 (hinge).** If `AC = A'C'` and `BC = B'C'` (with `A, B ≠ C`, `A', B' ≠ C'`), then
`AB < A'B'` iff `|∡ACB| < |∡A'C'B'|`. -/
@[kb "petrunin2025" "Proposition 11.9, p. 85"]
theorem hinge {A B C A' B' C' : P} (hA : A ≠ C) (hB : B ≠ C) (hA' : A' ≠ C') (hB' : B' ≠ C')
    (h₁ : dist A C = dist A' C') (h₂ : dist B C = dist B' C') :
    dist A B < dist A' B' ↔ N.uangle A C B < N.uangle A' C' B' := by
  constructor
  · intro h
    by_contra hn
    rcases (not_lt.1 hn).lt_or_eq with h1 | h1
    · have := N.hinge_lt hA' hB' hA hB h₁.symm h₂.symm h1
      linarith
    · have := N.hinge_eq hA hB hA' hB' h₁ h₂ h1.symm
      linarith
  · exact N.hinge_lt hA hB hA' hB' h₁ h₂

theorem hinge_le {A B C A' B' C' : P} (hA : A ≠ C) (hB : B ≠ C) (hA' : A' ≠ C') (hB' : B' ≠ C')
    (h₁ : dist A C = dist A' C') (h₂ : dist B C = dist B' C') :
    dist A B ≤ dist A' B' ↔ N.uangle A C B ≤ N.uangle A' C' B' := by
  constructor
  · intro h
    by_contra hn
    have := N.hinge_lt hA' hB' hA hB h₁.symm h₂.symm (not_le.1 hn)
    linarith
  · intro h
    rcases h.lt_or_eq with h1 | h1
    · exact (N.hinge_lt hA hB hA' hB' h₁ h₂ h1).le
    · exact (N.hinge_eq hA hB hA' hB' h₁ h₂ h1).le

/-- Straight angles: if `B` lies between `A` and `C`, the angle at `B` is `π` and the others are `0`. -/
private theorem uangle_of_isBetween {A B C : P} (h : IsBetween A B C) :
    N.uangle A B C = π ∧ N.uangle B A C = 0 ∧ N.uangle A C B = 0 := by
  have hA : A ≠ B := h.1.symm
  have hC : C ≠ B := h.2.1.symm
  have hAC : A ≠ C := h.ne
  refine ⟨(N.uangle_eq_pi_iff hA hC).2 h, ?_, ?_⟩
  · exact (N.uangle_eq_zero_iff hA.symm hAC.symm).2 (IsBetween.mem_metricHalfLine N h).2
  · exact (N.uangle_eq_zero_iff hAC hC.symm).2 (IsBetween.mem_metricHalfLine N h.symm).1

/-- A degenerate triangle has zero defect (angles `0, 0, π`, Corollary 2.8). -/
theorem defect_eq_zero_of_degenerate {A B C : P} (hT : IsTriangle A B C)
    (h : IsTriangle.Degenerate A B C) : N.defect A B C = 0 := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  unfold NeutralPlane.defect
  rcases hL.isBetween_trichotomy hA hB hC hAB hBC hCA with h1 | h1 | h1
  · obtain ⟨e1, e2, e3⟩ := N.uangle_of_isBetween h1
    rw [N.uangle_comm hCA hAB.symm, e1, e2, e3]
    ring
  · obtain ⟨e1, e2, e3⟩ := N.uangle_of_isBetween h1
    rw [N.uangle_comm hBC hCA.symm, N.uangle_comm hCA hAB.symm, e1, e2, e3]
    ring
  · obtain ⟨e1, e2, e3⟩ := N.uangle_of_isBetween h1
    rw [N.uangle_comm hBC hCA.symm, e1, e2, e3]
    ring

theorem defect_rotate {A B C : P} (_hT : IsTriangle A B C) : N.defect B C A = N.defect A B C := by
  unfold NeutralPlane.defect
  ring

theorem defect_swap {A B C : P} (hT : IsTriangle A B C) : N.defect B A C = N.defect A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  unfold NeutralPlane.defect
  rw [N.uangle_comm hAB.symm hCA, N.uangle_comm hCA.symm hBC, N.uangle_comm hBC.symm hAB]
  ring

/-- The defect is invariant under motions. -/
theorem defect_isometryEquiv (f : P ≃ᵢ P) {A B C : P} (hT : IsTriangle A B C) :
    N.defect (f A) (f B) (f C) = N.defect A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  unfold NeutralPlane.defect
  rw [N.uangle_isometryEquiv f hAB hBC.symm, N.uangle_isometryEquiv f hBC hCA.symm,
    N.uangle_isometryEquiv f hCA hAB.symm]

theorem defect_congruent {A B C A' B' C' : P} (hT : IsTriangle A B C)
    (h : TriangleCongruent A B C A' B' C') : N.defect A' B' C' = N.defect A B C := by
  obtain ⟨f, rfl, rfl, rfl⟩ := h
  exact N.defect_isometryEquiv f hT

/-- **Exercise 11.12 (additivity of the defect).** If `D` lies between `A` and `B`, then
`defect ABC = defect ADC + defect DBC`. -/
@[kb "petrunin2025" "Exercise 11.12, p. 87"]
theorem defect_add {A B C D : P} (hD : IsBetween A D B) (hC : C ∉ N.line A B) :
    N.defect A B C = N.defect A D C + N.defect D B C := by
  have hAB : A ≠ B := hD.ne
  have hCA : C ≠ A := fun e => hC (by rw [e]; exact N.left_mem_line A B)
  have hCB : C ≠ B := fun e => hC (by rw [e]; exact N.right_mem_line A B)
  have hCD : C ≠ D := fun e => hC (by rw [e]; exact N.mem_line_of_isBetween hD)
  have e1 := (N.uangle_add_uangle_of_isBetween hD hC).1
  have e2 := (N.isBetween_angle_sign_and_uangle hD hC).2.2
  have e3 : N.uangle C A D = N.uangle C A B := by
    unfold NeutralPlane.uangle
    rw [N.angle_ray_right hCA hAB.symm (IsBetween.mem_metricHalfLine N hD).1 hD.1]
  have e4 : N.uangle D B C = N.uangle A B C := by
    unfold NeutralPlane.uangle
    rw [N.angle_ray_left hAB (IsBetween.mem_metricHalfLine N hD.symm).1 hD.2.1 hCB]
  have c1 := N.uangle_comm hCD.symm hCA.symm
  have c2 := N.uangle_comm hCB.symm hCD.symm
  have c3 := N.uangle_comm hCB.symm hCA.symm
  unfold NeutralPlane.defect
  linarith

include N in
/-- Reflecting `lp t` through `lp u` along the line `(AB)` gives `lp (2u - t)`. -/
private theorem pointRefl_linePt {A B : P} (hAB : A ≠ B) (u t : ℝ) :
    N.pointRefl (N.linePt A B u) (N.linePt A B t) = N.linePt A B (2 * u - t) := by
  by_cases htu : t = u
  · subst htu
    rw [N.pointRefl_apply, N.pointReflFun_self]
    congr 1
    ring
  · have hne : N.linePt A B u ≠ N.linePt A B t := fun e => htu (N.linePt_injective hAB e).symm
    have hne2 : N.linePt A B u ≠ N.linePt A B (2 * u - t) := fun e =>
      htu (by have := N.linePt_injective hAB e; linarith)
    have d1 := N.dist_linePt hAB t u
    have d2 := N.dist_linePt hAB u (2 * u - t)
    have d3 := N.dist_linePt hAB t (2 * u - t)
    have e1 : u - (2 * u - t) = t - u := by ring
    have e2 : t - (2 * u - t) = 2 * (t - u) := by ring
    have hb : IsBetween (N.linePt A B t) (N.linePt A B u) (N.linePt A B (2 * u - t)) := by
      refine ⟨hne, hne2, ?_, ⟨N.line A B, N.isLine_line hAB, N.linePt_mem_line A B t,
        N.linePt_mem_line A B u, N.linePt_mem_line A B _⟩⟩
      rw [d3, d1, d2, e1, e2, abs_mul, abs_two]
      ring
    exact N.pointRefl_eq_of_isBetween hb (by rw [d2, N.dist_linePt hAB u t, e1, abs_sub_comm])

include N in
private theorem perp_perp_aux {A B C D : P} (hAB : A ≠ B) (hD : D = A ∨ N.uangle D A B = π / 2)
    (hC : C = B ∨ N.uangle A B C = π / 2) : dist A B ≤ dist C D := by
  obtain ⟨Ea, hEa, hEaang⟩ := N.exists_angle_eq_pi_div_two hAB.symm one_pos
  obtain ⟨Eb, hEb, hEbang⟩ := N.exists_angle_eq_pi_div_two hAB one_pos
  have hEaA : Ea ≠ A := by
    intro e
    rw [e, dist_self] at hEa
    exact zero_ne_one hEa
  have hEbB : Eb ≠ B := by
    intro e
    rw [e, dist_self] at hEb
    exact zero_ne_one hEb
  have hra : N.uangle B A Ea = π / 2 := by
    rw [N.uangle_def, hEaang, Real.Angle.toReal_pi_div_two, abs_of_pos (by positivity)]
  have hrb : N.uangle A B Eb = π / 2 := by
    rw [N.uangle_def, hEbang, Real.Angle.toReal_pi_div_two, abs_of_pos (by positivity)]
  have hLa := N.isLine_line hEaA.symm
  have hLb := N.isLine_line hEbB.symm
  have hLab := N.isLine_line hAB
  have hDpA : D ∈ N.line A Ea := by
    by_cases hDA : D = A
    · rw [hDA]
      exact N.left_mem_line A Ea
    · have hDr : N.uangle D A B = π / 2 := hD.resolve_left hDA
      refine N.mem_line_of_perp hLab (N.right_mem_line A B) (N.left_mem_line A B) hAB.symm hEaA hDA hra ?_
      rw [N.uangle_comm hAB.symm hDA]
      exact hDr
  have hCpB : C ∈ N.line B Eb := by
    by_cases hCB : C = B
    · rw [hCB]
      exact N.left_mem_line B Eb
    · exact N.mem_line_of_perp hLab (N.left_mem_line A B) (N.right_mem_line A B) hAB hEbB hCB hrb
        (hC.resolve_left hCB)
  have hr_line : ∀ t, N.lineRefl hLa (N.linePt A B t) = N.pointRefl A (N.linePt A B t) := by
    intro t
    by_cases ht : N.linePt A B t = A
    · rw [ht, N.lineRefl_fix hLa (N.left_mem_line A Ea), N.pointRefl_apply, N.pointReflFun_self]
    · have hu : N.uangle Ea A (N.linePt A B t) = π / 2 := by
        rw [N.uangle_comm hEaA ht]
        exact N.uangle_eq_pi_div_two_of_mem_line hAB.symm hEaA hra (N.linePt_mem_line A B t) ht
      obtain ⟨hb, hd⟩ := N.isBetween_lineRefl_of_perp hLa (N.right_mem_line A Ea) (N.left_mem_line A Ea)
        hEaA ht hu
      exact (N.pointRefl_eq_of_isBetween hb hd).symm
  have hs_line : ∀ t, N.lineRefl hLb (N.linePt A B t) = N.pointRefl B (N.linePt A B t) := by
    intro t
    by_cases ht : N.linePt A B t = B
    · rw [ht, N.lineRefl_fix hLb (N.left_mem_line B Eb), N.pointRefl_apply, N.pointReflFun_self]
    · have hu : N.uangle Eb B (N.linePt A B t) = π / 2 := by
        rw [N.uangle_comm hEbB ht]
        refine N.uangle_eq_pi_div_two_of_mem_line hAB hEbB hrb ?_ ht
        rw [N.line_comm]
        exact N.linePt_mem_line A B t
      obtain ⟨hb, hd⟩ := N.isBetween_lineRefl_of_perp hLb (N.right_mem_line B Eb) (N.left_mem_line B Eb)
        hEbB ht hu
      exact (N.pointRefl_eq_of_isBetween hb hd).symm
  have hrD : N.lineRefl hLa D = D := N.lineRefl_fix hLa hDpA
  have hsC : N.lineRefl hLb C = C := N.lineRefl_fix hLb hCpB
  generalize N.lineRefl hLa = r at hr_line hrD
  generalize N.lineRefl hLb = s at hs_line hsC
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = dist A B := ⟨_, rfl⟩
  have hBc : N.linePt A B c = B := by rw [hc]; exact N.linePt_dist hAB
  let T : P ≃ᵢ P := r.trans s
  have hT : ∀ t, T (N.linePt A B t) = N.linePt A B (t + 2 * c) := by
    intro t
    have h1 := N.pointRefl_linePt hAB 0 t
    rw [N.linePt_zero] at h1
    have h2 := N.pointRefl_linePt hAB c (2 * 0 - t)
    rw [hBc] at h2
    show s (r (N.linePt A B t)) = _
    rw [hr_line, h1, hs_line, h2]
    congr 1
    ring
  have hTn : ∀ n : ℕ, (⇑T)^[n] A = N.linePt A B (2 * n * c) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hT]
      congr 1
      push_cast
      ring
  have hdistT : ∀ (n : ℕ) (x y : P), dist ((⇑T)^[n] x) ((⇑T)^[n] y) = dist x y := by
    intro n x y
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.dist_eq, ih]
  have hTD : dist D (T D) ≤ 2 * dist C D := by
    have e1 : T D = s D := by
      show s (r D) = _
      rw [hrD]
    have e2 : dist C (s D) = dist C D := by
      have := s.dist_eq C D
      rwa [hsC] at this
    rw [e1]
    have := dist_triangle D C (s D)
    rw [dist_comm D C] at this
    linarith
  have hDn : ∀ n : ℕ, dist D ((⇑T)^[n] D) ≤ n * dist D (T D) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := dist_triangle D ((⇑T)^[n] D) ((⇑T)^[n + 1] D)
      have h2 : dist ((⇑T)^[n] D) ((⇑T)^[n + 1] D) = dist D (T D) := by
        rw [Function.iterate_succ_apply]
        exact hdistT n D (T D)
      rw [h2] at h1
      push_cast
      linarith
  have hmain : ∀ n : ℕ, 2 * n * c ≤ 2 * dist A D + 2 * n * dist C D := by
    intro n
    have h1 := dist_triangle A D ((⇑T)^[n] A)
    have h2 := dist_triangle D ((⇑T)^[n] D) ((⇑T)^[n] A)
    have h3 : dist ((⇑T)^[n] D) ((⇑T)^[n] A) = dist D A := hdistT n D A
    have h4 : dist A ((⇑T)^[n] A) = 2 * n * c := by
      have hc0 : 0 ≤ c := by rw [hc]; exact dist_nonneg
      rw [hTn, N.dist_left_linePt hAB, abs_of_nonneg (mul_nonneg (mul_nonneg two_pos.le (Nat.cast_nonneg n)) hc0)]
    have h5 := hDn n
    have h6 : (n : ℝ) * dist D (T D) ≤ n * (2 * dist C D) :=
      mul_le_mul_of_nonneg_left hTD (Nat.cast_nonneg n)
    rw [dist_comm D A] at h3
    linarith
  by_contra hcon
  have hlt : dist C D < c := by rw [hc]; exact not_le.1 hcon
  obtain ⟨n, hn⟩ := exists_nat_gt (dist A D / (c - dist C D))
  have hpos : 0 < c - dist C D := by linarith
  have := (div_lt_iff₀ hpos).1 hn
  have := hmain n
  nlinarith
/-- **Exercise 11.11, general form.** If `D = A` or `∠DAB` is right, and `C = B` or `∠ABC` is right, then
`AB ≤ CD`. (No convexity of `ABCD` is needed: compose the reflections across the perpendiculars to `(AB)` at
`A` and at `B`.) -/
@[kb "petrunin2025" "Exercise 11.11, p. 86"]
theorem dist_le_of_perp_perp {A B C D : P} (hAB : A ≠ B) (hD : D = A ∨ N.uangle D A B = π / 2)
    (hC : C = B ∨ N.uangle A B C = π / 2) : dist A B ≤ dist C D :=
  N.perp_perp_aux hAB hD hC

private theorem degenerate_swap' {A B C : P} (h : IsTriangle.Degenerate A B C) :
    IsTriangle.Degenerate B A C := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  exact ⟨L, hL, hB, hA, hC⟩

include N in
/-- Right triangle case of Legendre's theorem (positive right angle): hinge plus Exercise 11.11. -/
private theorem rt_pos {A B C : P} (hT : IsTriangle A B C)
    (hang : N.angle A B C = ((π / 2 : ℝ) : Real.Angle)) :
    N.uangle B A C + N.uangle A C B ≤ π / 2 := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hpi := Real.pi_pos
  have hr : N.uangle A B C = π / 2 := by
    rw [N.uangle_def, hang, Real.Angle.toReal_pi_div_two, abs_of_pos (by positivity)]
  have hnd : ¬ IsTriangle.Degenerate A B C := N.not_degenerate_of_uangle_eq_pi_div_two hAB hBC.symm hr
  have hBA : B ≠ A := hAB.symm
  have hbpos : 0 < dist B C := dist_pos.2 hBC
  obtain ⟨D, hDd, hDang⟩ := N.exists_pt' hBA hbpos ((-π / 2 : ℝ) : Real.Angle)
  have hDA : D ≠ A := by
    intro e
    rw [e, dist_self] at hDd
    linarith
  have hDu : N.uangle B A D = π / 2 := by
    rw [N.uangle_def, hDang, Real.Angle.toReal_neg_pi_div_two, abs_of_neg (by linarith)]
    ring
  have hBD : B ≠ D := by
    intro e
    rw [← e] at hDu
    have : N.uangle B A B = 0 := by
      rw [N.uangle_def, N.angle_self hBA]
      simp
    linarith
  have hDu' : N.uangle D A B = π / 2 := by rw [N.uangle_comm hDA hBA]; exact hDu
  have hcong : TriangleCongruent A B D B A C := by
    refine N.sas hAB hDA.symm hBD hBA hBC hCA.symm (dist_comm B A) hDd.symm ?_
    rw [N.uangle_comm hBC.symm hAB, hDu', hr]
  obtain ⟨f, hfA, hfB, hfD⟩ := hcong
  have d1 : dist A C = dist B D := by
    have := f.dist_eq B D
    rwa [hfB, hfD] at this
  have a1 : N.uangle B A C = N.uangle A B D := by
    have := N.uangle_isometryEquiv f hAB hBD.symm
    rwa [hfA, hfB, hfD] at this
  have hndABD : ¬ IsTriangle.Degenerate A B D := fun h =>
    N.not_degenerate_of_uangle_eq_pi_div_two hBA hDA hDu (degenerate_swap' h)
  obtain ⟨hs1, hs2⟩ := N.sign_angle_triangle ⟨hAB, hBD, hDA⟩ hndABD
  have hDAB : N.angle D A B = ((π / 2 : ℝ) : Real.Angle) := by
    rw [N.angle_rev hDA hBA, hDang, ← Real.Angle.coe_neg]
    congr 1
    ring
  have hsign : (N.angle A B D).sign = 1 := by
    rw [hs1, hs2, hDAB, Real.Angle.sign_coe_pi_div_two]
  have hABD : N.angle A B D = ((N.uangle A B D : ℝ) : Real.Angle) :=
    (Real.Angle.coe_abs_toReal_of_sign_nonneg (by rw [hsign]; decide)).symm
  have hlt := N.uangle_add_uangle_lt_pi ⟨hAB, hBC, hCA⟩ hnd
  have hα : N.uangle A B D < π / 2 := by
    have := N.uangle_comm hCA hBA
    rw [← a1]
    linarith
  have hDBC : N.angle D B C = ((π / 2 - N.uangle A B D : ℝ) : Real.Angle) := by
    have h := N.axiomIIIb B D A C hBD.symm hAB hBC.symm
    rw [← h, N.angle_rev hBD.symm hAB, hABD, hang, ← Real.Angle.coe_neg, ← Real.Angle.coe_add]
    congr 1
    ring
  have hu : N.uangle D B C = π / 2 - N.uangle A B D := by
    have h0 := N.uangle_nonneg A B D
    rw [N.uangle_def, hDBC, Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩,
      abs_of_nonneg (by linarith)]
  have hh := N.hinge (A := D) (B := C) (C := B) (A' := A) (B' := B) (C' := C) hBD.symm hBC.symm
    hCA.symm hBC (by rw [dist_comm D B]; exact d1.symm) (dist_comm C B)
  have hp := N.dist_le_of_perp_perp hAB (Or.inr hDu') (Or.inr hr)
  have hn : ¬ dist D C < dist A B := by
    rw [dist_comm D C]
    exact not_lt.2 hp
  have hn2 : ¬ N.uangle D B C < N.uangle A C B := fun h => hn (hh.2 h)
  have := not_lt.1 hn2
  linarith

include N in
private theorem rt_defect {A B C : P} (hT : IsTriangle A B C) (hr : N.uangle A B C = π / 2) :
    0 ≤ N.defect A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have key : N.uangle B A C + N.uangle A C B ≤ π / 2 := by
    rcases Real.Angle.abs_toReal_eq_pi_div_two_iff.1 hr with h | h
    · exact N.rt_pos ⟨hAB, hBC, hCA⟩ h
    · have hL := N.isLine_line hAB
      obtain ⟨σ, hfix, -, -, hang⟩ := N.exists_lineRefl hL
      have hσA : σ A = A := hfix A (N.left_mem_line A B)
      have hσB : σ B = B := hfix B (N.right_mem_line A B)
      have h2 := hang A B C hAB hBC.symm
      rw [hσA, hσB, h, ← Real.Angle.coe_neg] at h2
      have hne1 : B ≠ σ C := fun e => hBC (σ.injective (by rw [hσB]; exact e))
      have hne2 : σ C ≠ A := fun e => hCA (σ.injective (by rw [hσA]; exact e))
      have := N.rt_pos (A := A) (B := B) (C := σ C) ⟨hAB, hne1, hne2⟩
        (h2.trans (by congr 1; ring))
      have u1 := N.uangle_isometryEquiv σ hAB.symm hCA
      have u2 := N.uangle_isometryEquiv σ hCA.symm hBC
      rw [hσA, hσB] at u1 u2
      rw [u1, u2] at this
      exact this
  have c1 := N.uangle_comm hBC hCA.symm
  have c2 := N.uangle_comm hCA hAB.symm
  unfold NeutralPlane.defect
  linarith

include N in
private theorem defect_nonneg_top {A B C : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C)
    (h1 : N.uangle C A B ≤ N.uangle B C A) (h2 : N.uangle A B C ≤ N.uangle B C A) :
    0 ≤ N.defect A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hT : IsTriangle A B C := ⟨hAB, hBC, hCA⟩
  have hCnl : C ∉ N.line A B := fun h => hnd ((N.degenerate_iff_mem_line hAB).2 h)
  have s1 := N.uangle_add_uangle_lt_pi hT hnd
  have s2 := N.uangle_add_uangle_lt_pi (A := B) (B := C) (C := A) ⟨hBC, hCA, hAB⟩
    (fun h => hnd (degenerate_unrotate h))
  have s3 := N.uangle_add_uangle_lt_pi (A := C) (B := A) (C := B) ⟨hCA, hAB, hBC⟩
    (fun h => hnd (degenerate_unrotate (degenerate_unrotate h)))
  have hA90 : N.uangle C A B < π / 2 := by linarith
  have hB90 : N.uangle A B C < π / 2 := by linarith
  obtain ⟨F, hFl, hF⟩ := N.exists_foot (N.isLine_line hAB) hCnl
  have hAl : A ∈ N.line A B := N.left_mem_line A B
  have hBl : B ∈ N.line A B := N.right_mem_line A B
  have hFA : F ≠ A := by
    intro e
    have := hF B hBl (by rw [e]; exact hAB.symm)
    rw [e] at this
    linarith
  have hFB : F ≠ B := by
    intro e
    have h3 := hF A hAl (by rw [e]; exact hAB)
    rw [e] at h3
    have h4 := N.uangle_comm hAB hBC.symm
    linarith
  have hCF : C ≠ F := fun e => hCnl (by rw [e]; exact hFl)
  have hAFC : N.uangle A F C = π / 2 := by
    rw [N.uangle_comm hFA.symm hCF]
    exact hF A hAl hFA.symm
  have hBFC : N.uangle B F C = π / 2 := by
    rw [N.uangle_comm hFB.symm hCF]
    exact hF B hBl hFB.symm
  have nd1 : ¬ IsTriangle.Degenerate A F C :=
    N.not_degenerate_of_uangle_eq_pi_div_two hFA.symm hCF hAFC
  have nd2 : ¬ IsTriangle.Degenerate B F C :=
    N.not_degenerate_of_uangle_eq_pi_div_two hFB.symm hCF hBFC
  have T1 : IsTriangle A F C := ⟨hFA.symm, hCF.symm, hCA⟩
  have T2 : IsTriangle B F C := ⟨hFB.symm, hCF.symm, hBC.symm⟩
  have lt1 := N.uangle_add_uangle_lt_pi T1 nd1
  have lt2 := N.uangle_add_uangle_lt_pi T2 nd2
  have hbt : IsBetween A F B := by
    rcases (N.isLine_line hAB).isBetween_trichotomy hAl hBl hFl hAB hFB.symm hFA with h | h | h
    · exfalso
      have hl : N.line B F = N.line A B := N.line_eq_of_mem hAB hBl hFl hFB.symm
      have h5 := (N.uangle_add_uangle_of_isBetween h (by rw [hl]; exact hCnl)).1
      have c := N.uangle_comm hAB.symm hCA
      linarith
    · exfalso
      have hl : N.line A F = N.line A B := N.line_eq_of_mem hAB hAl hFl hFA.symm
      have h5 := (N.uangle_add_uangle_of_isBetween h (by rw [hl]; exact hCnl)).1
      linarith
    · exact h
  rw [N.defect_add hbt hCnl, N.defect_swap T2]
  exact add_nonneg (N.rt_defect T1 hAFC) (N.rt_defect T2 hBFC)

include N in
private theorem defect_nonneg_aux {A B C : P} (hT : IsTriangle A B C) : 0 ≤ N.defect A B C := by
  by_cases hd : IsTriangle.Degenerate A B C
  · rw [N.defect_eq_zero_of_degenerate hT hd]
  · obtain ⟨hAB, hBC, hCA⟩ := hT
    have hT : IsTriangle A B C := ⟨hAB, hBC, hCA⟩
    have hT2 : IsTriangle B C A := ⟨hBC, hCA, hAB⟩
    have hT3 : IsTriangle C A B := ⟨hCA, hAB, hBC⟩
    have hd2 : ¬ IsTriangle.Degenerate B C A := fun h => hd (degenerate_unrotate h)
    have hd3 : ¬ IsTriangle.Degenerate C A B := fun h =>
      hd (degenerate_unrotate (degenerate_unrotate h))
    have r1 := N.defect_rotate hT
    have r2 := N.defect_rotate hT2
    rcases le_total (N.uangle C A B) (N.uangle B C A) with hac | hca
    · rcases le_total (N.uangle A B C) (N.uangle B C A) with hbc | hcb
      · exact N.defect_nonneg_top hT hd hac hbc
      · have := N.defect_nonneg_top hT3 hd3 hcb (hac.trans hcb)
        rwa [r2, r1] at this
    · rcases le_total (N.uangle A B C) (N.uangle C A B) with hba | hab
      · have := N.defect_nonneg_top hT2 hd2 hba hca
        rwa [r1] at this
      · have := N.defect_nonneg_top hT3 hd3 (hca.trans hab) hab
        rwa [r2, r1] at this

/-- **Theorem 11.10 (Saccheri-Legendre).** The angle sum of a triangle in a neutral plane is at most `π`. -/
@[kb "petrunin2025" "Theorem 11.10, p. 86"]
theorem uangle_sum_le_pi {A B C : P} (hT : IsTriangle A B C) :
    N.uangle A B C + N.uangle B C A + N.uangle C A B ≤ π := by
  have := N.defect_nonneg_aux hT
  unfold NeutralPlane.defect at this
  linarith

/-- The defect of every triangle is nonnegative (Theorem 11.10). -/
@[kb "petrunin2025" "Theorem 11.10, p. 86"]
theorem defect_nonneg {A B C : P} (hT : IsTriangle A B C) : 0 ≤ N.defect A B C :=
  N.defect_nonneg_aux hT

/-- Defect monotonicity: if `D` lies between `A` and `B`, then `defect ADC ≤ defect ABC`. -/
theorem defect_le_of_isBetween {A B C D : P} (hD : IsBetween A D B) (hC : C ∉ N.line A B) :
    N.defect A D C ≤ N.defect A B C := by
  have hCB : C ≠ B := fun e => hC (by rw [e]; exact N.right_mem_line A B)
  have hCD : C ≠ D := fun e => hC (by rw [e]; exact N.mem_line_of_isBetween hD)
  have := N.defect_nonneg (A := D) (B := B) (C := C) ⟨hD.2.1, hCB.symm, hCD⟩
  rw [N.defect_add hD hC]
  linarith

/-- Adding two angles of the same sign whose absolute values sum to less than `π`. -/
private theorem abs_toReal_add_of_sign_eq {x y : Real.Angle} (hs : x.sign = y.sign)
    (hlt : |x.toReal| + |y.toReal| < π) : |(x + y).toReal| = |x.toReal| + |y.toReal| := by
  have hpi := Real.pi_pos
  have hxy : x + y = ((x.toReal + y.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  by_cases h0 : 0 ≤ x.sign
  · have hx0 : 0 ≤ x.toReal := Real.Angle.toReal_nonneg_iff_sign_nonneg.2 h0
    have hy0 : 0 ≤ y.toReal :=
      Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [← hs]; exact h0)
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0] at hlt ⊢
    rw [hxy, Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩, abs_of_nonneg (by linarith)]
  · have hx0 : x.toReal < 0 := not_le.1 (fun h => h0 (Real.Angle.toReal_nonneg_iff_sign_nonneg.1 h))
    have hy0 : y.toReal < 0 := not_le.1 (fun h => h0 (by
      rw [hs]; exact Real.Angle.toReal_nonneg_iff_sign_nonneg.1 h))
    rw [abs_of_neg hx0, abs_of_neg hy0] at hlt ⊢
    rw [hxy, Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, by linarith⟩, abs_of_neg (by linarith)]
    ring

/-- **Exercise 11.13.** If `X` is the reflection of `C` across the midpoint `M` of `[AB]`, then
`defect ABC = defect AXC`. -/
@[kb "petrunin2025" "Exercise 11.13, p. 87"]
theorem defect_pointRefl_midpoint {A B C M : P} (hM : IsBetween A M B) (hMM : dist A M = dist M B)
    (hC : C ∉ N.line A B) : N.defect A B C = N.defect A (N.pointRefl M C) C := by
  have hAB : A ≠ B := hM.ne
  have hCA : C ≠ A := fun e => hC (by rw [e]; exact N.left_mem_line A B)
  have hCB : C ≠ B := fun e => hC (by rw [e]; exact N.right_mem_line A B)
  have hCM : C ≠ M := fun e => hC (by rw [e]; exact N.mem_line_of_isBetween hM)
  have hnd : ¬ IsTriangle.Degenerate A B C := fun hd => hC ((N.degenerate_iff_mem_line hAB).1 hd)
  obtain ⟨X, hX⟩ : ∃ X, X = N.pointRefl M C := ⟨_, rfl⟩
  rw [← hX]
  have hCMX : IsBetween C M X := by
    rw [hX, N.pointRefl_apply]
    exact N.isBetween_pointReflFun hCM
  have hdMX : dist M X = dist M C := by
    rw [hX, N.pointRefl_apply]
    exact N.dist_pointReflFun M C
  have hfA : N.pointRefl M A = B :=
    N.pointRefl_eq_of_isBetween hM (by rw [dist_comm M A]; exact hMM.symm)
  have hfB : N.pointRefl M B = A :=
    N.pointRefl_eq_of_isBetween hM.symm (by rw [dist_comm M A]; exact hMM)
  have hfX : N.pointRefl M X = C := N.pointRefl_eq_of_isBetween hCMX.symm hdMX.symm
  have hXC : X ≠ C := hCMX.ne.symm
  have hAX : A ≠ X := by
    intro e
    have := congrArg (N.pointRefl M) e
    rw [hfA, hfX] at this
    exact hCB this.symm
  have e1 := N.uangle_isometryEquiv (N.pointRefl M) hAX hXC.symm
  rw [hfA, hfX, ← hX] at e1
  have hXr : X ∈ metricHalfLine C M := (IsBetween.mem_metricHalfLine N hCMX).2
  have e2 : N.uangle B C X = N.uangle B C M := by
    unfold NeutralPlane.uangle
    rw [N.angle_ray_right hCB.symm hCM.symm hXr hXC]
  have e3 : N.uangle A C X = N.uangle A C M := by
    unfold NeutralPlane.uangle
    rw [N.angle_ray_right hCA.symm hCM.symm hXr hXC]
  have e4 := (N.isBetween_angle_sign_and_uangle hM hC).2.2
  have c1 := N.uangle_comm hXC hCA.symm
  have c2 := N.uangle_comm hCM.symm hCB.symm
  have c3 := N.uangle_comm hCB.symm hCA.symm
  obtain ⟨hs1, hs2⟩ := N.sign_angle_triangle ⟨hAB, hCB.symm, hCA⟩ hnd
  have hlt := N.uangle_add_uangle_lt_pi ⟨hAB, hCB.symm, hCA⟩ hnd
  have eBAX : N.angle B A X = N.angle A B C := by
    have := N.angle_pointRefl M hAB hCB
    rwa [hfA, hfB, ← hX] at this
  have eCAX : N.angle C A X = N.angle C A B + N.angle A B C := by
    have := N.axiomIIIb A C B X hCA hAB.symm hAX.symm
    rw [eBAX] at this
    exact this.symm
  have hsum : N.uangle C A X = N.uangle C A B + N.uangle A B C := by
    unfold NeutralPlane.uangle at hlt ⊢
    rw [eCAX]
    exact abs_toReal_add_of_sign_eq (hs1.trans hs2).symm hlt
  unfold NeutralPlane.defect
  linarith

/-- **Exercise 11.14.** Opposite sides of a rectangle are equal. -/
@[kb "petrunin2025" "Exercise 11.14, p. 87"]
theorem IsRectangle.dist_eq {A B C D : P} (h : N.IsRectangle A B C D) :
    dist A B = dist C D ∧ dist B C = dist D A := by
  obtain ⟨hAB, hAC, hAD, hBC, hBD, hCD, hB, hC, hD, hA⟩ := h
  have h1 := N.dist_le_of_perp_perp hAB (Or.inr hA) (Or.inr hB)
  have h2 := N.dist_le_of_perp_perp (A := D) (B := C) (D := A) (C := B) hCD.symm
    (Or.inr ((N.uangle_comm hAD hCD).trans hD)) (Or.inr ((N.uangle_comm hCD.symm hBC).trans hC))
  have h3 := N.dist_le_of_perp_perp (A := B) (B := C) (D := A) (C := D) hBC (Or.inr hB) (Or.inr hC)
  have h4 := N.dist_le_of_perp_perp (A := A) (B := D) (D := B) (C := C) hAD
    (Or.inr ((N.uangle_comm hAB.symm hAD.symm).trans hA))
    (Or.inr ((N.uangle_comm hAD hCD).trans hD))
  rw [dist_comm D C, dist_comm B A] at h2
  rw [dist_comm A D, dist_comm C B] at h4
  exact ⟨le_antisymm h1 h2, le_antisymm h3 h4⟩

end NeutralPlane

end Neutral

end UndergradKB.Geometry
