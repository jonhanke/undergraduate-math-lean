import UndergradKB.Geometry.NeutralHalfPlanes
import UndergradKB.Common.Attr

/-! # Neutral plane IV: congruent triangles and perpendicular lines (Petrunin, Chapters 4-5)

Derived from Axioms I-IV of `NeutralPlane`: the congruence conditions ASA (4.1), SSS (4.4), isosceles
triangles (4.2), Corollary 4.5 (`AB + BC = AC` puts `B` on `[AC]`), the perpendicular bisector (5.2),
existence and uniqueness of perpendiculars (5.6), the reflection across a line as an angle-reversing motion
(5.8, 5.10), the perpendicular as the shortest path to a line (5.13), and Exercise 5.4 (the larger side lies
opposite the larger angle). All of these are marked in the book as valid in every neutral plane. -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

theorem TriangleCongruent.dist_eq {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C') :
    dist A' B' = dist A B ∧ dist B' C' = dist B C ∧ dist C' A' = dist C A := by
  obtain ⟨f, hA, hB, hC⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← hA, ← hB, f.dist_eq]
  · rw [← hB, ← hC, f.dist_eq]
  · rw [← hC, ← hA, f.dist_eq]

/-- Motions compose and invert, so congruence of triangles is symmetric and transitive. -/
private theorem TriangleCongruent.symm' {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C') :
    TriangleCongruent A' B' C' A B C := by
  obtain ⟨f, hA, hB, hC⟩ := h
  exact ⟨f.symm, by rw [← hA]; exact f.symm_apply_apply A, by rw [← hB]; exact f.symm_apply_apply B,
    by rw [← hC]; exact f.symm_apply_apply C⟩

private theorem TriangleCongruent.trans' {A B C A' B' C' A'' B'' C'' : P}
    (h : TriangleCongruent A B C A' B' C') (h' : TriangleCongruent A' B' C' A'' B'' C'') :
    TriangleCongruent A B C A'' B'' C'' := by
  obtain ⟨f, hA, hB, hC⟩ := h
  obtain ⟨g, gA, gB, gC⟩ := h'
  exact ⟨f.trans g, by simp [hA, gA], by simp [hB, gB], by simp [hC, gC]⟩

private theorem degenerate_swap {A B C : P} (h : IsTriangle.Degenerate A B C) :
    IsTriangle.Degenerate B A C := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  exact ⟨L, hL, hB, hA, hC⟩

private theorem degenerate_rotate {A B C : P} (h : IsTriangle.Degenerate A B C) :
    IsTriangle.Degenerate B C A := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  exact ⟨L, hL, hB, hC, hA⟩

/-- A real-valued sign equal to its own negative is zero. -/
private theorem signType_eq_zero_of_eq_neg {s : SignType} (h : s = -s) : s = 0 := by
  revert h
  revert s
  decide

/-- Two angles with equal absolute values of their principal values are equal or opposite. -/
private theorem angle_eq_or_neg_of_abs {x y : Real.Angle} (h : |x.toReal| = |y.toReal|) :
    x = y ∨ x = -y := by
  rcases abs_eq_abs.1 h with h | h
  · left
    calc x = ((x.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal x).symm
      _ = ((y.toReal : ℝ) : Real.Angle) := by rw [h]
      _ = y := Real.Angle.coe_toReal y
  · right
    calc x = ((x.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal x).symm
      _ = ((-y.toReal : ℝ) : Real.Angle) := by rw [h]
      _ = -y := by rw [Real.Angle.coe_neg, Real.Angle.coe_toReal]

private theorem abs_toReal_eq_of_eq_or_neg {x y : Real.Angle} (h : x = y ∨ x = -y) :
    |x.toReal| = |y.toReal| := by
  rcases h with h | h
  · rw [h]
  · rw [h, Real.Angle.abs_toReal_neg]

/-- A right angle has measure `±π/2`. -/
private theorem angle_eq_half_or_neg {x : Real.Angle} (h : |x.toReal| = π / 2) :
    x = ((π / 2 : ℝ) : Real.Angle) ∨ x = -((π / 2 : ℝ) : Real.Angle) := by
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ π / 2)).1 h with e | e
  · left
    calc x = ((x.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal x).symm
      _ = _ := by rw [e]
  · right
    calc x = ((x.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal x).symm
      _ = _ := by rw [e, Real.Angle.coe_neg]

namespace NeutralPlane

/-- Congruent triangles (by a motion) have equal angles up to sign at corresponding vertices. -/
theorem TriangleCongruent.angle_eq {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C')
    (hAB : A ≠ B) (hCB : C ≠ B) :
    N.angle A' B' C' = N.angle A B C ∨ N.angle A' B' C' = -N.angle A B C := by
  by_cases hAC : A = C
  · obtain ⟨f, hA, hB, hC⟩ := h
    have hA'B' : A' ≠ B' := fun e => hAB (f.injective (hA.trans (e.trans hB.symm)))
    have hAC' : A' = C' := by rw [← hA, ← hC, hAC]
    left
    rw [← hAC', ← hAC, N.angle_self hA'B', N.angle_self hAB]
  · obtain ⟨f, hA, hB, hC⟩ := h
    have hA'B' : A' ≠ B' := fun e => hAB (f.injective (hA.trans (e.trans hB.symm)))
    have hC'B' : C' ≠ B' := fun e => hCB (f.injective (hC.trans (e.trans hB.symm)))
    have hA'C' : A' ≠ C' := fun e => hAC (f.injective (hA.trans (e.trans hC.symm)))
    have := (N.axiomIV B C A B' C' A' hCB.symm (Ne.symm hAC) hAB hC'B'.symm hA'C'.symm hA'B').1
      ⟨f, hB, hC, hA⟩
    exact this.2.2

theorem TriangleCongruent.uangle_eq {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C')
    (hAB : A ≠ B) (hCB : C ≠ B) : N.uangle A' B' C' = N.uangle A B C := by
  have := TriangleCongruent.angle_eq N h hAB hCB
  exact abs_toReal_eq_of_eq_or_neg this

/-- SAS (Axiom IV) in the unsigned form: `A'B' = AB`, `A'C' = AC`, `|∡C'A'B'| = |∡CAB|`. -/
theorem sas {A B C A' B' C' : P} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hAB' : A' ≠ B')
    (hAC' : A' ≠ C') (hBC' : B' ≠ C') (h₁ : dist A' B' = dist A B) (h₂ : dist A' C' = dist A C)
    (h₃ : N.uangle C' A' B' = N.uangle C A B) : TriangleCongruent A B C A' B' C' :=
  (N.axiomIV A B C A' B' C' hAB hBC hAC.symm hAB' hBC' hAC'.symm).2
    ⟨h₁, h₂, angle_eq_or_neg_of_abs h₃⟩

/-- A point at a prescribed positive distance and angle (Axiom IIIa and Exercise 1.12). -/
private theorem exists_pt {O A : P} (hA : A ≠ O) {r : ℝ} (hr : 0 < r) (α : Real.Angle) :
    ∃ B, dist O B = r ∧ N.angle A O B = α := by
  obtain ⟨D, hD, hang, -⟩ := N.axiomIIIa O A hA α
  obtain ⟨B, ⟨hB, hd⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hD.symm hr.le
  have hBO : B ≠ O := by
    intro e
    rw [e, dist_self] at hd
    linarith
  exact ⟨B, hd, by rw [N.angle_ray_right hA hD hB hBO, hang]⟩

/-- Two points with the same angle from a given half-line lie on a common half-line (Axiom IIIa). -/
private theorem mem_ray_of_angle_eq_aux {O A B C : P} (hA : A ≠ O) (hB : B ≠ O) (hC : C ≠ O)
    (h : N.angle A O B = N.angle A O C) : B ∈ metricHalfLine O C := by
  obtain ⟨D, hD, hang, huniq⟩ := N.axiomIIIa O A hA (N.angle A O C)
  have h1 := huniq B hB h
  have h2 := huniq C hC rfl
  rw [N.metricHalfLine_eq_of_mem hD.symm h2 hC]
  exact h1

include N in
/-- Two points of one half-line at the same distance from its vertex coincide. -/
private theorem eq_of_mem_ray_of_dist_eq {O A X Y : P} (hOA : O ≠ A) (hX : X ∈ metricHalfLine O A)
    (hY : Y ∈ metricHalfLine O A) (h : dist O X = dist O Y) : X = Y := by
  obtain ⟨Z, -, hZ⟩ := N.existsUnique_mem_metricHalfLine_dist hOA (dist_nonneg : 0 ≤ dist O Y)
  rw [hZ X ⟨hX, h⟩, hZ Y ⟨hY, rfl⟩]

include N in
/-- A point strictly inside a nondegenerate configuration: if `C'' ∈ [AC)` and the triangle `ABC` is nondegenerate
then `C''` (different from `A`) is not `B`. -/
private theorem ray_pt_ne {A B C C'' : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (hC'' : C'' ∈ metricHalfLine A C) (hC''A : C'' ≠ A) : C'' ≠ B := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hs := N.sign_angle_triangle ⟨hAB, hBC, hCA⟩ hnd
  have hne := N.sign_angle_ne_zero ⟨hAB, hBC, hCA⟩ hnd
  have hang : N.angle C'' A B = N.angle C A B := N.angle_ray_left hCA hC'' hC''A hAB.symm
  intro e
  rw [e, N.angle_self hAB.symm] at hang
  apply hne
  rw [hs.1, hs.2, ← hang]
  exact Real.Angle.sign_zero

include N in
/-- Two half-lines `[AC)`, `[BC)` of a nondegenerate triangle meet only at `C`. -/
private theorem eq_of_mem_rays {A B C X : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (h1 : X ∈ metricHalfLine A C) (h2 : X ∈ metricHalfLine B C) :
    X = C := by
  by_contra hXC
  have hAC : A ≠ C := hT.2.2.symm
  have hBC : B ≠ C := hT.2.1
  have e1 : N.line C X = N.line A C :=
    N.line_eq_of_mem hAC (N.right_mem_line A C) (N.metricHalfLine_subset_line hAC h1) (Ne.symm hXC)
  have e2 : N.line C X = N.line B C :=
    N.line_eq_of_mem hBC (N.right_mem_line B C) (N.metricHalfLine_subset_line hBC h2) (Ne.symm hXC)
  have hA : A ∈ N.line B C := by
    have : A ∈ N.line A C := N.left_mem_line A C
    rw [← e1, e2] at this
    exact this
  exact hnd (degenerate_rotate (degenerate_rotate ((N.degenerate_iff_mem_line hBC).2 hA)))

/-- A point `C''` of `[AC)` seen from `B` under the same unsigned angle as `C` is `C` itself. -/
private theorem ray_pt_unique {A B C C'' : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hC'' : C'' ∈ metricHalfLine A C) (hC''A : C'' ≠ A)
    (h : N.uangle A B C'' = N.uangle A B C) : C'' = C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hs := N.sign_angle_triangle ⟨hAB, hBC, hCA⟩ hnd
  have hne := N.sign_angle_ne_zero ⟨hAB, hBC, hCA⟩ hnd
  have hang : N.angle C'' A B = N.angle C A B := N.angle_ray_left hCA hC'' hC''A hAB.symm
  have hC''B := N.ray_pt_ne ⟨hAB, hBC, hCA⟩ hnd hC'' hC''A
  have hs0 : (N.angle C'' A B).sign ≠ 0 := by
    rw [hang, ← hs.2, ← hs.1]
    exact hne
  have hnd2 : ¬ IsTriangle.Degenerate A B C'' := by
    intro hd
    exact hs0 ((N.sign_angle_eq_zero_iff hC''A hAB.symm).2
      (degenerate_rotate (degenerate_rotate hd)))
  have hs2 := N.sign_angle_triangle ⟨hAB, hC''B.symm, hC''A⟩ hnd2
  have hsign : (N.angle A B C'').sign = (N.angle A B C).sign := by
    rw [hs2.1, hs2.2, hang, ← hs.2, ← hs.1]
  have hcases := angle_eq_or_neg_of_abs h
  have heq : N.angle A B C'' = N.angle A B C := by
    rcases hcases with h1 | h1
    · exact h1
    · exfalso
      rw [h1, Real.Angle.sign_neg] at hsign
      exact hne (signType_eq_zero_of_eq_neg hsign.symm)
  have hray : C'' ∈ metricHalfLine B C := N.mem_ray_of_angle_eq_aux hAB hC''B hBC.symm heq
  exact N.eq_of_mem_rays ⟨hAB, hBC, hCA⟩ hnd hC'' hray

/-- **ASA condition 4.1.** -/
@[kb "petrunin2025" "Theorem 4.1, p. 31"]
theorem asa {A B C A' B' C' : P} (hT : IsTriangle A B C) (hT' : IsTriangle A' B' C')
    (hnd' : ¬ IsTriangle.Degenerate A' B' C') (h₁ : dist A B = dist A' B')
    (h₂ : N.uangle A B C = N.uangle A' B' C') (h₃ : N.uangle C A B = N.uangle C' A' B') :
    TriangleCongruent A B C A' B' C' := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hAB', hBC', hCA'⟩ := hT'
  obtain ⟨C'', ⟨hC''r, hd⟩, -⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hCA'.symm (dist_nonneg : 0 ≤ dist A C)
  have hC''A' : C'' ≠ A' := by
    intro e
    rw [e, dist_self] at hd
    exact hCA.symm (dist_eq_zero.1 hd.symm)
  have hang : N.angle C'' A' B' = N.angle C' A' B' := N.angle_ray_left hCA' hC''r hC''A' hAB'.symm
  have hB'C'' := (N.ray_pt_ne ⟨hAB', hBC', hCA'⟩ hnd' hC''r hC''A').symm
  have hcong : TriangleCongruent A B C A' B' C'' :=
    N.sas hAB hCA.symm hBC hAB' hC''A'.symm hB'C'' h₁.symm hd
      (by
        have : N.uangle C'' A' B' = N.uangle C' A' B' := by
          unfold NeutralPlane.uangle
          rw [hang]
        rw [this, ← h₃])
  have hu := TriangleCongruent.uangle_eq N hcong hAB hBC.symm
  have hC''eq : C'' = C' :=
    N.ray_pt_unique ⟨hAB', hBC', hCA'⟩ hnd' hC''r hC''A' (by rw [hu, h₂])
  rw [hC''eq] at hcong
  exact hcong

/-- **Theorem 4.2.** In an isosceles triangle with base `[AB]`, `∡ABC = -∡BAC`. -/
@[kb "petrunin2025" "Theorem 4.2, p. 32"]
theorem isosceles {A B C : P} (hT : IsTriangle A B C) (h : dist C A = dist C B) :
    N.angle A B C = -N.angle B A C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hcong : TriangleCongruent C A B C B A :=
    (N.axiomIV C A B C B A hCA hAB hBC hBC.symm hAB.symm hCA.symm).2
      ⟨h.symm, h, Or.inr (N.angle_rev hCA.symm hBC)⟩
  have hang := TriangleCongruent.angle_eq N hcong hCA hAB.symm
  have r1 : N.angle A B C = -N.angle C B A := N.angle_rev hAB hBC.symm
  have r2 : N.angle B A C = -N.angle C A B := N.angle_rev hAB.symm hCA
  by_cases hd : IsTriangle.Degenerate A B C
  · have hC : C ∈ N.line A B := (N.degenerate_iff_mem_line hAB).1 hd
    have hCr1 : C ∈ metricHalfLine A B := by
      rcases N.mem_metricHalfLine_or_isBetween hAB hC with h1 | h1
      · exact h1
      · exfalso
        have := h1.dist_add
        have := dist_pos.2 hAB
        linarith [dist_comm A B, dist_comm C B, dist_comm C A]
    have hC' : C ∈ N.line B A := by rw [N.line_comm]; exact hC
    have hCr2 : C ∈ metricHalfLine B A := by
      rcases N.mem_metricHalfLine_or_isBetween hAB.symm hC' with h1 | h1
      · exact h1
      · exfalso
        have := h1.dist_add
        have := dist_pos.2 hAB
        linarith [dist_comm A B, dist_comm C B, dist_comm C A]
    rw [N.angle_eq_zero_of_mem_ray hAB.symm hCr1 hCA, N.angle_eq_zero_of_mem_ray hAB hCr2 hBC.symm]
    simp
  · have hs := N.sign_angle_triangle ⟨hAB, hBC, hCA⟩ hd
    have hne := N.sign_angle_ne_zero ⟨hAB, hBC, hCA⟩ hd
    rw [r1, r2]
    rcases hang with h1 | h1
    · exfalso
      have e1 : (N.angle A B C).sign = -(N.angle C A B).sign := by
        rw [r1, Real.Angle.sign_neg, h1]
      have e2 : (N.angle A B C).sign = (N.angle C A B).sign := by rw [hs.1, hs.2]
      rw [e2] at e1
      exact hne (by rw [e2]; exact signType_eq_zero_of_eq_neg e1)
    · rw [h1]

/-- **Theorem 4.2, converse.** -/
@[kb "petrunin2025" "Theorem 4.2, p. 32"]
theorem isosceles_converse {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (h : N.angle A B C = -N.angle B A C) : dist C A = dist C B := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have r1 : N.angle A B C = -N.angle C B A := N.angle_rev hAB hBC.symm
  have r2 : N.angle B A C = -N.angle C A B := N.angle_rev hAB.symm hCA
  have hcong : TriangleCongruent A B C B A C := by
    refine N.asa ⟨hAB, hBC, hCA⟩ ⟨hAB.symm, hCA.symm, hBC.symm⟩ (fun hd => hnd (degenerate_swap hd))
      (dist_comm A B) (abs_toReal_eq_of_eq_or_neg (Or.inr h)) ?_
    apply abs_toReal_eq_of_eq_or_neg
    right
    rw [r1, r2] at h
    rw [neg_neg] at h
    exact h.symm
  exact (TriangleCongruent.dist_eq hcong).2.2.symm

theorem uangle_eq_of_dist_eq {A B C : P} (hT : IsTriangle A B C) (h : dist C A = dist C B) :
    N.uangle A B C = N.uangle B A C :=
  abs_toReal_eq_of_eq_or_neg (Or.inr (N.isosceles hT h))

include N in
/-- **SSS condition 4.4.** -/
@[kb "petrunin2025" "Theorem 4.4, p. 33"]
theorem sss {A B C A' B' C' : P} (hT : IsTriangle A B C) (hT' : IsTriangle A' B' C')
    (h₁ : dist A' B' = dist A B) (h₂ : dist B' C' = dist B C) (h₃ : dist C' A' = dist C A) :
    TriangleCongruent A B C A' B' C' := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hAB', hBC', hCA'⟩ := hT'
  obtain ⟨C'', hd, hang⟩ :=
    N.exists_pt (O := A') (A := B') hAB'.symm (dist_pos.2 hCA'.symm) (N.angle B A C)
  have hC''A' : C'' ≠ A' := by
    intro e
    rw [e, dist_self] at hd
    exact hCA'.symm (dist_eq_zero.1 hd.symm)
  have hd3 : dist A' C' = dist A C := by rw [dist_comm A' C', h₃, dist_comm]
  have hB'C'' : B' ≠ C'' := by
    intro e
    have h0 : N.angle B A C = 0 := by
      rw [← hang, ← e]
      exact N.angle_self hAB'.symm
    have hCr : C ∈ metricHalfLine A B := N.mem_ray_of_angle_eq_zero hAB.symm hCA h0
    have : dist A B = dist A C := by
      rw [← h₁, e, hd, hd3]
    exact hBC (N.eq_of_mem_ray_of_dist_eq hAB (N.self_mem_metricHalfLine hAB) hCr this)
  have hcong1 : TriangleCongruent A B C A' B' C'' :=
    (N.axiomIV A B C A' B' C'' hAB hBC hCA hAB' hB'C'' hC''A').2
      ⟨h₁, hd.trans hd3, Or.inl (by
        rw [N.angle_rev hC''A' hAB'.symm, hang, N.angle_rev hAB.symm hCA, neg_neg])⟩
  have hdB := (TriangleCongruent.dist_eq hcong1).2.1
  by_cases hc : C'' = C'
  · rw [hc] at hcong1
    exact hcong1
  replace hc : C'' ≠ C' := hc
  have hdB' : dist B' C'' = dist B' C' := by rw [hdB, h₂]
  have i1 := N.isosceles (A := C') (B := C'') (C := A') ⟨hc.symm, hC''A', hCA'.symm⟩ hd.symm
  have i2 := N.isosceles (A := C') (B := C'') (C := B') ⟨hc.symm, hB'C''.symm, hBC'⟩ hdB'.symm
  have e1 := N.axiomIIIb C'' A' C' B' hC''A'.symm hc.symm hB'C''
  have e2 := N.axiomIIIb C' A' C'' B' hCA'.symm hc hBC'
  have r1 : N.angle A' C'' C' = N.angle C'' C' A' := by
    rw [N.angle_rev hC''A'.symm hc.symm, i1, neg_neg]
  have r3 : N.angle A' C' C'' = -N.angle C'' C' A' := N.angle_rev hCA'.symm hc
  have hrev : N.angle A' C'' B' = -N.angle A' C' B' := by
    rw [← e1, ← e2, r1, i2, r3]
    abel
  have hcong2 : TriangleCongruent C' A' B' C'' A' B' :=
    (N.axiomIV C' A' B' C'' A' B' hCA' hAB' hBC' hC''A' hAB' hB'C'').2
      ⟨by rw [dist_comm C'' A', dist_comm C' A']; exact hd,
       by rw [dist_comm C'' B', dist_comm C' B']; exact hdB',
       Or.inr (by
        rw [N.angle_rev hB'C'' hC''A'.symm, N.angle_rev hBC' hCA'.symm, hrev])⟩
  obtain ⟨g, gC, gA, gB⟩ := hcong2
  exact hcong1.trans' (TriangleCongruent.symm' ⟨g, gA, gB, gC⟩)

/-- **Corollary 4.5.** If `AB + BC = AC` then `B ∈ [AC]`; in particular `B ∈ (AC)`. -/
@[kb "petrunin2025" "Corollary 4.5, p. 33"]
theorem mem_line_of_dist_add {A B C : P} (hAC : A ≠ C) (h : dist A B + dist B C = dist A C) :
    B ∈ N.line A C := by
  by_cases hAB : A = B
  · rw [← hAB]
    exact N.left_mem_line A C
  by_cases hBC : B = C
  · rw [hBC]
    exact N.right_mem_line A C
  obtain ⟨B', ⟨hB'r, hB'd⟩, -⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hAC (dist_nonneg : 0 ≤ dist A B)
  have hAB0 : 0 < dist A B := dist_pos.2 hAB
  have hBC0 : 0 < dist B C := dist_pos.2 hBC
  have hB'A : B' ≠ A := by
    intro e
    rw [e, dist_self] at hB'd
    linarith
  have hdist : dist B' C = dist B C := by
    have := N.dist_of_mem_metricHalfLine hAC hB'r
    rw [dist_comm B' C, this, hB'd, abs_of_nonneg (by linarith : (0 : ℝ) ≤ dist A C - dist A B)]
    linarith
  have hB'C : B' ≠ C := by
    intro e
    rw [e, dist_self] at hdist
    linarith
  have hbet : IsBetween A B' C :=
    N.isBetween_of_mem_line hAC (N.metricHalfLine_subset_line hAC hB'r) hB'A hB'C
      (by rw [hB'd]; linarith) (by rw [hdist]; linarith)
  have hpi : N.angle A B' C = π := (N.angle_eq_pi_iff hB'A.symm hB'C.symm).2 hbet
  have hcong : TriangleCongruent A B' C A B C :=
    N.sss ⟨hB'A.symm, hB'C, hAC.symm⟩ ⟨hAB, hBC, hAC.symm⟩ hB'd.symm hdist.symm rfl
  have hang := TriangleCongruent.angle_eq N hcong hB'A.symm hB'C.symm
  have hABC : N.angle A B C = π := by
    rcases hang with h1 | h1
    · rw [h1, hpi]
    · rw [h1, hpi, Real.Angle.neg_coe_pi]
  obtain ⟨L, hL, hA, hB, hC⟩ := (N.degenerate_iff_angle hAB (Ne.symm hBC)).2 (Or.inr hABC)
  rw [← N.eq_line hL hA hC hAC]
  exact hB

include N in
/-- Every point lies on some line. -/
private theorem exists_isLine_mem (A : P) : ∃ L : Set P, IsLine L ∧ A ∈ L := by
  obtain ⟨X, Y, hXY⟩ := N.axiomI
  by_cases hAX : A = X
  · rw [hAX]
    exact ⟨N.line X Y, N.isLine_line hXY, N.left_mem_line X Y⟩
  · exact ⟨N.line A X, N.isLine_line hAX, N.left_mem_line A X⟩

include N in
/-- The triangle inequality is strict for nondegenerate triangles (from Corollary 4.5). -/
theorem dist_lt_add_of_not_degenerate {A B C : P} (hnd : ¬ IsTriangle.Degenerate A B C) :
    dist A C < dist A B + dist B C := by
  rcases (dist_triangle A B C).lt_or_eq with h | h
  · exact h
  exfalso
  by_cases hAC : A = C
  · rw [← hAC, dist_self, dist_comm B A] at h
    have hAB : A = B := dist_eq_zero.1 (by linarith [dist_nonneg (x := A) (y := B)])
    obtain ⟨L, hL, hAL⟩ := N.exists_isLine_mem A
    exact hnd ⟨L, hL, hAL, by rw [← hAB]; exact hAL, by rw [← hAC]; exact hAL⟩
  · exact hnd ⟨N.line A C, N.isLine_line hAC, N.left_mem_line A C,
      N.mem_line_of_dist_add hAC h.symm, N.right_mem_line A C⟩

/-- If `B` lies between `A` and `C` then `∡ABC = π` and `B ∈ (AC)`. -/
theorem IsBetween.mem_line {A B C : P} (h : IsBetween A B C) : B ∈ N.line A C :=
  N.mem_line_of_isBetween h

theorem IsBetween.angle_eq_pi {A B C : P} (h : IsBetween A B C) : N.angle A B C = π :=
  (N.angle_eq_pi_iff h.1.symm h.2.1.symm).2 h

include N in
/-- If `B` lies between `A` and `C`, then `B ∈ [AC)` and `C ∈ [AB)`. -/
theorem IsBetween.mem_metricHalfLine {A B C : P} (h : IsBetween A B C) :
    B ∈ metricHalfLine A C ∧ C ∈ metricHalfLine A B := by
  have hAC := h.ne
  have hAB : A ≠ B := h.1.symm
  have hd := h.dist_add
  have hpos := dist_pos.2 hAB
  constructor
  · rcases N.mem_metricHalfLine_or_isBetween hAC (N.mem_line_of_isBetween h) with h1 | h1
    · exact h1
    · exfalso
      have := h1.dist_add
      linarith [dist_comm B A, dist_comm A C, dist_comm B C]
  · have hl : N.line A B = N.line A C :=
      N.line_eq_of_mem hAC (N.left_mem_line A C) (N.mem_line_of_isBetween h) hAB
    have hC : C ∈ N.line A B := by
      rw [hl]
      exact N.right_mem_line A C
    rcases N.mem_metricHalfLine_or_isBetween hAB hC with h1 | h1
    · exact h1
    · exfalso
      have := h1.dist_add
      linarith [dist_comm B A, dist_comm A C, dist_comm B C, dist_comm C A, dist_comm C B]

/-! ### Perpendicular lines (Chapter 5) -/

/-- An angle has `|θ| = π/2` exactly when `θ + θ = π`. -/
private theorem abs_toReal_eq_half_iff (x : Real.Angle) : |x.toReal| = π / 2 ↔ x + x = π := by
  constructor
  · intro h
    rcases angle_eq_half_or_neg h with h1 | h1
    · rw [h1, ← Real.Angle.coe_add]
      congr 1
      ring
    · rw [h1, ← neg_add, ← Real.Angle.coe_add, show π / 2 + π / 2 = π by ring]
      exact Real.Angle.neg_coe_pi
  · intro h
    have h2 : (2 : ℕ) • x = π := by rw [two_nsmul]; exact h
    rcases Real.Angle.two_nsmul_eq_pi_iff.1 h2 with h3 | h3
    · rw [h3, Real.Angle.toReal_pi_div_two, abs_of_pos (by positivity)]
    · rw [h3, Real.Angle.toReal_neg_pi_div_two, abs_of_neg (by linarith [Real.pi_pos])]
      ring

private theorem two_zsmul_eq_zero_of_eq_neg {θ : Real.Angle} (h : θ = -θ) : (2 : ℤ) • θ = 0 := by
  rw [two_zsmul]
  exact add_eq_zero_iff_eq_neg.2 h

private theorem eq_neg_of_two_zsmul_eq_zero {θ : Real.Angle} (h : (2 : ℤ) • θ = 0) : θ = -θ := by
  rw [two_zsmul] at h
  exact add_eq_zero_iff_eq_neg.1 h

private theorem degenerate_reverse {A B C : P} (h : IsTriangle.Degenerate A B C) :
    IsTriangle.Degenerate C B A := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  exact ⟨L, hL, hC, hB, hA⟩

/-- A line has a point different from any given one of its points. -/
private theorem exists_ne_of_mem_line {L : Set P} (hL : IsLine L) {F : P} (hF : F ∈ L) :
    ∃ Y ∈ L, Y ≠ F := by
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨t, rfl⟩ := hF
  refine ⟨g (t + 1), ⟨_, rfl⟩, fun e => ?_⟩
  have := hg.injective e
  linarith

include N in
/-- Two distinct points of a line, with a degenerate triple through them, put the third on the line. -/
private theorem mem_of_degenerate {L : Set P} (hL : IsLine L) {A B X : P} (hA : A ∈ L) (hB : B ∈ L)
    (hAB : A ≠ B) (hd : IsTriangle.Degenerate A B X) : X ∈ L := by
  obtain ⟨L', hL', hA', hB', hX'⟩ := hd
  have := (N.eq_line hL' hA' hB' hAB).trans (N.eq_line hL hA hB hAB).symm
  rw [this] at hX'
  exact hX'

/-- For `A ≠ B` on a line `L` and `X ≠ A`: `X ∈ L` iff `∡BAX = -∡BAX`. -/
private theorem mem_iff_angle_eq_neg {L : Set P} (hL : IsLine L) {A B X : P} (hA : A ∈ L) (hB : B ∈ L)
    (hAB : A ≠ B) (hX : X ≠ A) : X ∈ L ↔ N.angle B A X = -N.angle B A X := by
  constructor
  · intro hXL
    have hd : IsTriangle.Degenerate B A X := ⟨L, hL, hB, hA, hXL⟩
    exact eq_neg_of_two_zsmul_eq_zero ((N.degenerate_iff_two_zsmul hAB.symm hX).1 hd)
  · intro h
    have hd := (N.degenerate_iff_two_zsmul hAB.symm hX).2 (two_zsmul_eq_zero_of_eq_neg h)
    exact N.mem_of_degenerate hL hB hA hAB.symm hd

include N in
/-- A midpoint of two distinct points. -/
private theorem exists_midpoint {P₁ P₂ : P} (h : P₁ ≠ P₂) :
    ∃ M, IsBetween P₁ M P₂ ∧ dist P₁ M = dist M P₂ := by
  obtain ⟨d, hd⟩ : ∃ d, d = dist P₁ P₂ := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ dist_pos.2 h
  have hPd : N.linePt P₁ P₂ d = P₂ := by rw [hd]; exact N.linePt_dist h
  obtain ⟨M, hM⟩ : ∃ M, M = N.linePt P₁ P₂ (d / 2) := ⟨_, rfl⟩
  have h1 : dist P₁ M = d / 2 := by
    rw [hM, N.dist_left_linePt h, abs_of_pos (by linarith)]
  have h2 : dist M P₂ = d / 2 := by
    have := N.dist_linePt h (d / 2) d
    rw [hPd] at this
    rw [hM, this, abs_of_neg (by linarith)]
    ring
  refine ⟨M, ⟨?_, ?_, ?_, ⟨N.line P₁ P₂, N.isLine_line h, N.left_mem_line _ _, ?_,
    N.right_mem_line _ _⟩⟩, by rw [h1, h2]⟩
  · intro e
    rw [e, dist_self] at h1
    linarith
  · intro e
    rw [e, dist_self] at h2
    linarith
  · rw [h1, h2, hd]
    ring
  · rw [hM]
    exact N.linePt_mem_line _ _ _

/-- Two right angles `∠XMA`, `∠XMB` on the same arm `[MX)` put `A, M, B` on a line. -/
private theorem degenerate_of_right_right {A B M X : P} (hA : A ≠ M) (hB : B ≠ M) (hX : X ≠ M)
    (h₁ : N.uangle X M A = π / 2) (h₂ : N.uangle X M B = π / 2) : IsTriangle.Degenerate A M B := by
  have ha := (abs_toReal_eq_half_iff _).1 h₁
  have hb := (abs_toReal_eq_half_iff _).1 h₂
  rw [N.degenerate_iff_two_zsmul hA hB, two_zsmul, ← N.axiomIIIb M A X B hA hX hB,
    N.angle_rev hA hX]
  calc (-N.angle X M A + N.angle X M B) + (-N.angle X M A + N.angle X M B)
      = -(N.angle X M A + N.angle X M A) + (N.angle X M B + N.angle X M B) := by abel
    _ = 0 := by
      rw [ha, hb, Real.Angle.neg_coe_pi, Real.Angle.coe_pi_add_coe_pi]


/-! #### The mirror map across a line, built from a base point `A` and a second point `B` -/

open Classical in
/-- The mirror image of `X`: same distance from `A`, opposite angle `∡BAX` (and `A ↦ A`). -/
private noncomputable def mirrorFun (A B : P) (hBA : B ≠ A) (X : P) : P :=
  if h : X = A then A else
    Classical.choose (N.exists_pt hBA (dist_pos.2 (Ne.symm h)) (-N.angle B A X))

private theorem mirrorFun_self (A B : P) (hBA : B ≠ A) : N.mirrorFun A B hBA A = A := by
  unfold mirrorFun
  rw [dif_pos rfl]

private theorem mirrorFun_spec {A B : P} (hBA : B ≠ A) {X : P} (hX : X ≠ A) :
    dist A (N.mirrorFun A B hBA X) = dist A X ∧
      N.angle B A (N.mirrorFun A B hBA X) = -N.angle B A X := by
  unfold mirrorFun
  rw [dif_neg hX]
  exact Classical.choose_spec (N.exists_pt hBA (dist_pos.2 (Ne.symm hX)) (-N.angle B A X))

private theorem mirrorFun_ne {A B : P} (hBA : B ≠ A) {X : P} (hX : X ≠ A) :
    N.mirrorFun A B hBA X ≠ A := by
  intro e
  have := (N.mirrorFun_spec hBA hX).1
  rw [e, dist_self] at this
  exact hX (dist_eq_zero.1 this.symm).symm

private theorem mirror_unique {A B Y Y' : P} (hBA : B ≠ A) (hY : Y ≠ A) (hY' : Y' ≠ A)
    (hd : dist A Y = dist A Y') (hang : N.angle B A Y = N.angle B A Y') : Y = Y' :=
  N.eq_of_mem_ray_of_dist_eq hY'.symm (N.mem_ray_of_angle_eq_aux hBA hY hY' hang)
    (N.self_mem_metricHalfLine hY'.symm) hd

private theorem mirrorFun_invol {A B : P} (hBA : B ≠ A) (X : P) :
    N.mirrorFun A B hBA (N.mirrorFun A B hBA X) = X := by
  by_cases hX : X = A
  · rw [hX, N.mirrorFun_self, N.mirrorFun_self]
  · have h1 := N.mirrorFun_spec hBA hX
    have h1' := N.mirrorFun_ne hBA hX
    have h2 := N.mirrorFun_spec hBA h1'
    exact N.mirror_unique hBA (N.mirrorFun_ne hBA h1') hX (by rw [h2.1, h1.1])
      (by rw [h2.2, h1.2, neg_neg])

private theorem mirrorFun_angle_base {A B : P} (hBA : B ≠ A) {X Y : P} (hX : X ≠ A) (hY : Y ≠ A) :
    N.angle (N.mirrorFun A B hBA X) A (N.mirrorFun A B hBA Y) = -N.angle X A Y := by
  have hX' := N.mirrorFun_ne hBA hX
  have hY' := N.mirrorFun_ne hBA hY
  have e1 : N.angle (N.mirrorFun A B hBA X) A (N.mirrorFun A B hBA Y) =
      -N.angle B A (N.mirrorFun A B hBA X) + N.angle B A (N.mirrorFun A B hBA Y) := by
    rw [← N.axiomIIIb A _ B _ hX' hBA hY', N.angle_rev hX' hBA]
  have e2 : N.angle X A Y = -N.angle B A X + N.angle B A Y := by
    rw [← N.axiomIIIb A X B Y hX hBA hY, N.angle_rev hX hBA]
  rw [e1, e2, (N.mirrorFun_spec hBA hX).2, (N.mirrorFun_spec hBA hY).2]
  abel

private theorem mirrorFun_dist {A B : P} (hBA : B ≠ A) (X Y : P) :
    dist (N.mirrorFun A B hBA X) (N.mirrorFun A B hBA Y) = dist X Y := by
  by_cases hX : X = A
  · rw [hX, N.mirrorFun_self]
    by_cases hY : Y = A
    · rw [hY, N.mirrorFun_self]
    · exact (N.mirrorFun_spec hBA hY).1
  by_cases hY : Y = A
  · rw [hY, N.mirrorFun_self, dist_comm, (N.mirrorFun_spec hBA hX).1, dist_comm]
  by_cases hXY : X = Y
  · rw [hXY, dist_self, dist_self]
  have hX' := N.mirrorFun_ne hBA hX
  have hY' := N.mirrorFun_ne hBA hY
  have hne : N.mirrorFun A B hBA X ≠ N.mirrorFun A B hBA Y := by
    intro e
    apply hXY
    rw [← N.mirrorFun_invol hBA X, ← N.mirrorFun_invol hBA Y, e]
  have hiv := (N.axiomIV A X Y A (N.mirrorFun A B hBA X) (N.mirrorFun A B hBA Y) (Ne.symm hX) hXY hY
      (Ne.symm hX') hne hY').2 ⟨(N.mirrorFun_spec hBA hX).1, (N.mirrorFun_spec hBA hY).1,
      Or.inr (N.mirrorFun_angle_base hBA hY hX)⟩
  exact (TriangleCongruent.dist_eq hiv).2.1

/-- The mirror map as a motion. -/
private noncomputable def mirrorEquiv (A B : P) (hBA : B ≠ A) : P ≃ᵢ P where
  toFun := N.mirrorFun A B hBA
  invFun := N.mirrorFun A B hBA
  left_inv := N.mirrorFun_invol hBA
  right_inv := N.mirrorFun_invol hBA
  isometry_toFun := Isometry.of_dist_eq fun X Y => N.mirrorFun_dist hBA X Y

private theorem mirrorEquiv_apply (A B : P) (hBA : B ≠ A) (X : P) :
    N.mirrorEquiv A B hBA X = N.mirrorFun A B hBA X := rfl

/-- Angles at a point `O` with one side towards the base point `A` are reversed. -/
private theorem mirror_angle_rev_aux {A B : P} (hBA : B ≠ A) {O Z : P} (hO : O ≠ A) (hZO : Z ≠ O) :
    N.angle A (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA Z) = -N.angle A O Z := by
  have hO' := N.mirrorFun_ne hBA hO
  by_cases hZ : Z = A
  · rw [hZ, N.mirrorFun_self, N.angle_self (Ne.symm hO'), N.angle_self (Ne.symm hO), neg_zero]
  have hT : IsTriangle A O Z := ⟨Ne.symm hO, Ne.symm hZO, hZ⟩
  have hZ' := N.mirrorFun_ne hBA hZ
  have hang := N.angle_isometryEquiv (N.mirrorEquiv A B hBA) (Ne.symm hO) hZO
  simp only [mirrorEquiv_apply, N.mirrorFun_self] at hang
  by_cases hd : IsTriangle.Degenerate A O Z
  · have h2 := eq_neg_of_two_zsmul_eq_zero ((N.degenerate_iff_two_zsmul (Ne.symm hO) hZO).1 hd)
    rcases hang with h | h
    · rw [h]
      exact h2
    · exact h
  · have hne : N.mirrorFun A B hBA O ≠ N.mirrorFun A B hBA Z := fun e => hZO (by
      have := congrArg (N.mirrorFun A B hBA) e
      rw [N.mirrorFun_invol, N.mirrorFun_invol] at this
      exact this.symm)
    have hT' : IsTriangle A (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA Z) :=
      ⟨Ne.symm hO', hne, hZ'⟩
    have hd' : ¬ IsTriangle.Degenerate A (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA Z) := by
      intro hd'
      apply hd
      have hx := eq_neg_of_two_zsmul_eq_zero ((N.degenerate_iff_two_zsmul (Ne.symm hO')
        (fun e => hne e.symm)).1 hd')
      refine (N.degenerate_iff_two_zsmul (Ne.symm hO) hZO).2 (two_zsmul_eq_zero_of_eq_neg ?_)
      rcases hang with h | h
      · rw [h] at hx
        exact hx
      · rw [h, neg_neg] at hx
        exact hx.symm
    have s1 := N.sign_angle_triangle hT hd
    have s2 := N.sign_angle_triangle hT' hd'
    have e := N.mirrorFun_angle_base hBA hZ hO
    have hsign : (N.angle A (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA Z)).sign =
        -(N.angle A O Z).sign := by
      rw [s2.1, s2.2, e, Real.Angle.sign_neg, ← s1.2, ← s1.1]
    have hne0 := N.sign_angle_ne_zero hT hd
    rcases hang with h | h
    · exfalso
      rw [h] at hsign
      exact hne0 (signType_eq_zero_of_eq_neg hsign)
    · exact h

/-- The mirror map reverses all angles. -/
private theorem mirror_angle_rev {A B : P} (hBA : B ≠ A) {X O Y : P} (hX : X ≠ O) (hY : Y ≠ O) :
    N.angle (N.mirrorFun A B hBA X) (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA Y) =
      -N.angle X O Y := by
  by_cases hO : O = A
  · rw [hO] at hX hY ⊢
    rw [N.mirrorFun_self]
    exact N.mirrorFun_angle_base hBA hX hY
  · have hO' := N.mirrorFun_ne hBA hO
    have hXσ : N.mirrorFun A B hBA X ≠ N.mirrorFun A B hBA O := fun e => hX (by
      have := congrArg (N.mirrorFun A B hBA) e
      rwa [N.mirrorFun_invol, N.mirrorFun_invol] at this)
    have hYσ : N.mirrorFun A B hBA Y ≠ N.mirrorFun A B hBA O := fun e => hY (by
      have := congrArg (N.mirrorFun A B hBA) e
      rwa [N.mirrorFun_invol, N.mirrorFun_invol] at this)
    have e1 := N.axiomIIIb (N.mirrorFun A B hBA O) (N.mirrorFun A B hBA X) A
      (N.mirrorFun A B hBA Y) hXσ (Ne.symm hO') hYσ
    have e2 := N.axiomIIIb O X A Y hX (Ne.symm hO) hY
    rw [← e1, ← e2, N.angle_rev hXσ (Ne.symm hO'), N.angle_rev hX (Ne.symm hO),
      N.mirror_angle_rev_aux hBA hO hX, N.mirror_angle_rev_aux hBA hO hY]
    abel

/-- The reflection across a line, as a motion (the content of `exists_lineRefl`). -/
private theorem exists_lineRefl_aux {L : Set P} (hL : IsLine L) :
    ∃ σ : P ≃ᵢ P, (∀ X ∈ L, σ X = X) ∧ (∀ X, X ∉ L → σ X ≠ X) ∧ (∀ X, σ (σ X) = X) ∧
      (∀ A O B : P, A ≠ O → B ≠ O → N.angle (σ A) (σ O) (σ B) = -N.angle A O B) := by
  obtain ⟨A, hA⟩ : ∃ A, A ∈ L := by
    obtain ⟨g, hg, rfl⟩ := hL
    exact ⟨g 0, 0, rfl⟩
  obtain ⟨B, hB, hBA⟩ := exists_ne_of_mem_line hL hA
  refine ⟨N.mirrorEquiv A B hBA, ?_, ?_, ?_, ?_⟩
  · intro X hX
    show N.mirrorFun A B hBA X = X
    by_cases hXA : X = A
    · rw [hXA, N.mirrorFun_self]
    · have h1 := N.mirrorFun_spec hBA hXA
      have h2 := (N.mem_iff_angle_eq_neg hL hA hB hBA.symm hXA).1 hX
      exact N.mirror_unique hBA (N.mirrorFun_ne hBA hXA) hXA h1.1 (by rw [h1.2]; exact h2.symm)
  · intro X hX h
    have hXA : X ≠ A := fun e => hX (e ▸ hA)
    have h1 := (N.mirrorFun_spec hBA hXA).2
    have h' : N.mirrorFun A B hBA X = X := h
    rw [h'] at h1
    exact hX ((N.mem_iff_angle_eq_neg hL hA hB hBA.symm hXA).2 h1)
  · intro X
    exact N.mirrorFun_invol hBA X
  · intro X O Y hXO hYO
    exact N.mirror_angle_rev hBA hXO hYO

/-- **Theorem 5.2.** Let `M` be the midpoint of `[AB]` (`A ≠ B`) and `X ≠ M`. Then `XA = XB` iff `∠AMX` is
right. -/
@[kb "petrunin2025" "Theorem 5.2, p. 37"]
theorem dist_eq_iff_uangle_eq_pi_div_two {A B M X : P} (hM : IsBetween A M B)
    (hMM : dist A M = dist M B) (hX : X ≠ M) :
    dist X A = dist X B ↔ N.uangle A M X = π / 2 := by
  have hAM : A ≠ M := hM.1.symm
  have hBM : B ≠ M := hM.2.1.symm
  have hAB : A ≠ B := hM.ne
  have hMX : M ≠ X := hX.symm
  have hpi : N.angle A M B = π := (N.angle_eq_pi_iff hAM hBM).2 hM
  have hsum : N.angle A M X + N.angle X M B = π := by
    rw [N.axiomIIIb M A X B hAM hX hBM, hpi]
  constructor
  · intro h
    have hXA : X ≠ A := by
      intro e
      rw [e, dist_self] at h
      exact hAB (dist_eq_zero.1 h.symm)
    have hXB : X ≠ B := by
      intro e
      rw [e, dist_self] at h
      exact hAB (dist_eq_zero.1 h).symm
    have hcong : TriangleCongruent A M X B M X :=
      N.sss ⟨hAM, hMX, hXA⟩ ⟨hBM, hMX, hXB⟩ (by rw [dist_comm B M, hMM]) rfl h.symm
    have hang := TriangleCongruent.angle_eq N hcong hAM hX
    have hrev := N.angle_rev hX hBM
    rcases hang with h1 | h1
    · exfalso
      rw [hrev, h1, add_neg_cancel] at hsum
      exact Real.Angle.pi_ne_zero hsum.symm
    · rw [hrev, h1, neg_neg] at hsum
      exact (abs_toReal_eq_half_iff _).2 hsum
  · intro h
    have ha := (abs_toReal_eq_half_iff _).1 h
    have hXMB : N.angle X M B = N.angle A M X := by
      have : N.angle A M X + N.angle X M B = N.angle A M X + N.angle A M X := by rw [hsum, ha]
      exact add_left_cancel this
    have hXA : X ≠ A := by
      intro e
      rw [e, N.angle_self hAM, add_zero] at ha
      exact Real.Angle.pi_ne_zero ha.symm
    have hXB : X ≠ B := by
      intro e
      rw [e, hpi, Real.Angle.coe_pi_add_coe_pi] at ha
      exact Real.Angle.pi_ne_zero ha.symm
    have hcong : TriangleCongruent M A X M B X :=
      (N.axiomIV M A X M B X hAM.symm hXA.symm hX hBM.symm hXB.symm hX).2
        ⟨by rw [dist_comm M A]; exact hMM.symm, rfl,
         Or.inr (by rw [hXMB, N.angle_rev hX hAM, neg_neg])⟩
    have := (TriangleCongruent.dist_eq hcong).2.1
    rw [dist_comm X A, dist_comm X B]
    exact this.symm

/-- A right angle has a sign `±1`; in particular, its sides are not on one line. -/
theorem not_degenerate_of_uangle_eq_pi_div_two {A O B : P} (hA : A ≠ O) (hB : B ≠ O)
    (h : N.uangle A O B = π / 2) : ¬ IsTriangle.Degenerate A O B := by
  intro hd
  rw [N.degenerate_iff_angle hA hB] at hd
  have h' : N.angle A O B + N.angle A O B = π := (abs_toReal_eq_half_iff _).1 h
  rcases hd with h0 | h0
  · rw [h0, add_zero] at h'
    exact Real.Angle.pi_ne_zero h'.symm
  · rw [h0, Real.Angle.coe_pi_add_coe_pi] at h'
    exact Real.Angle.pi_ne_zero h'.symm

/-- Right angles are kept when a side is moved along its line: if `∠AOB` is right, `A' ∈ (OA)`, `A' ≠ O`,
then `∠A'OB` is right. -/
theorem uangle_eq_pi_div_two_of_mem_line {A O B A' : P} (hA : A ≠ O) (hB : B ≠ O)
    (h : N.uangle A O B = π / 2) (hA' : A' ∈ N.line O A) (hA'O : A' ≠ O) : N.uangle A' O B = π / 2 := by
  rcases N.mem_metricHalfLine_or_isBetween hA.symm hA' with hm | hb
  · show |(N.angle A' O B).toReal| = π / 2
    rw [N.angle_ray_left hA hm hA'O hB]
    exact h
  · have hpi : N.angle A' O A = π := (N.angle_eq_pi_iff hA'O hA).2 hb
    have hsum := N.axiomIIIb O A' A B hA'O hA hB
    rw [hpi] at hsum
    have ha := (abs_toReal_eq_half_iff _).1 h
    refine (abs_toReal_eq_half_iff _).2 ?_
    rw [← hsum, add_add_add_comm, Real.Angle.coe_pi_add_coe_pi, ha, zero_add]

/-- Existence of a right angle at a given point on a given side (Axiom IIIa): for `A ≠ O` there is `B` with
`∡AOB = π/2` at any prescribed distance `r > 0` from `O`. -/
theorem exists_angle_eq_pi_div_two {O A : P} (hA : A ≠ O) {r : ℝ} (hr : 0 < r) :
    ∃ B, dist O B = r ∧ N.angle A O B = ((π / 2 : ℝ) : Real.Angle) :=
  N.exists_pt hA hr _

/-! #### Angle sums and the exterior angle (auxiliary forms, used before their public statements) -/

/-- `|∡CAB| + |∡ABC| < π` (Proposition 11.5), via the reflection of `C` across the midpoint of `[AB]`. -/
private theorem aux_lt_pi {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    N.uangle C A B + N.uangle A B C < π := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨M, hM, hMd⟩ := N.exists_midpoint hAB
  have hAM : A ≠ M := hM.1.symm
  have hBM : B ≠ M := hM.2.1.symm
  have hMl : M ∈ N.line A B := N.mem_line_of_isBetween hM
  have hCl : C ∉ N.line A B := fun h => hnd ((N.degenerate_iff_mem_line hAB).2 h)
  have hCM : C ≠ M := fun e => hCl (e ▸ hMl)
  have hbet : IsBetween C M (N.pointRefl M C) := by
    rw [N.pointRefl_apply]
    exact N.isBetween_pointReflFun hCM
  obtain ⟨Xr, hXr⟩ : ∃ Xr, Xr = N.pointRefl M C := ⟨_, rfl⟩
  rw [← hXr] at hbet
  have RA : N.pointRefl M A = B :=
    N.pointRefl_eq_of_isBetween hM (by rw [dist_comm M A]; exact hMd.symm)
  have RB : N.pointRefl M B = A :=
    N.pointRefl_eq_of_isBetween hM.symm (by rw [dist_comm M A]; exact hMd)
  have h76 := N.angle_pointRefl M hAB hBC.symm (C := C)
  rw [RA, RB, ← hXr] at h76
  have hCXr : C ≠ Xr := hbet.ne
  have hAnl : A ∉ N.line C Xr := by
    intro hA
    have hMl' : M ∈ N.line C Xr := N.mem_line_of_isBetween hbet
    have hBl : B ∈ N.line A M := (N.degenerate_iff_mem_line hAM).1 hM.degenerate
    have hl : N.line C Xr = N.line A M := N.eq_line (N.isLine_line hCXr) hA hMl' hAM
    exact hnd ⟨N.line C Xr, N.isLine_line hCXr, hA, by rw [hl]; exact hBl, N.left_mem_line C Xr⟩
  have hXrA : Xr ≠ A := fun e => hAnl (e ▸ N.right_mem_line C Xr)
  have h38 := (N.isBetween_angle_sign_and_uangle hbet hAnl).2.2
  have hray := IsBetween.mem_metricHalfLine N hM
  have e1 : N.uangle C A M = N.uangle C A B := by
    show |(N.angle C A M).toReal| = |(N.angle C A B).toReal|
    rw [N.angle_ray_right hCA hAB.symm hray.1 hAM.symm]
  have e2 : N.uangle M A Xr = N.uangle B A Xr := by
    show |(N.angle M A Xr).toReal| = |(N.angle B A Xr).toReal|
    rw [N.angle_ray_left hAB.symm hray.1 hAM.symm hXrA]
  have e3 : N.uangle B A Xr = N.uangle A B C := by
    show |(N.angle B A Xr).toReal| = |(N.angle A B C).toReal|
    rw [h76]
  have hne : N.uangle C A Xr ≠ π := by
    intro h
    exact hAnl (N.mem_line_of_isBetween ((N.uangle_eq_pi_iff hCA hXrA).1 h))
  have hle := N.uangle_le_pi C A Xr
  rw [e1, e2, e3] at h38
  rw [h38]
  exact lt_of_le_of_ne hle hne

/-- Exterior angle (auxiliary form of `uangle_lt_exterior`). -/
private theorem aux_exterior {A B C D : P} (hD : IsBetween A D C) (hB : B ∉ N.line A C) :
    N.uangle D A B < N.uangle B D C := by
  have hAD : A ≠ D := hD.1.symm
  have hAC : A ≠ C := hD.ne
  have hDl : D ∈ N.line A C := N.mem_line_of_isBetween hD
  have hl : N.line A D = N.line A C := N.line_eq_of_mem hAC (N.left_mem_line A C) hDl hAD
  have hBA : B ≠ A := fun e => hB (e ▸ N.left_mem_line A C)
  have hBD : B ≠ D := fun e => hB (e ▸ hDl)
  have hnd : ¬ IsTriangle.Degenerate A D B := fun hd => hB (by
    rw [← hl]
    exact (N.degenerate_iff_mem_line hAD).1 hd)
  have h1 := N.aux_lt_pi (A := A) (B := D) (C := B) ⟨hAD, hBD.symm, hBA⟩ hnd
  have h2 := (N.uangle_add_uangle_of_isBetween hD hB).1
  have h3 := N.uangle_comm hBA (Ne.symm hAD)
  linarith

/-- The unsigned angle of a nondegenerate triangle is positive. -/
private theorem aux_uangle_pos {A O B : P} (hA : A ≠ O) (hB : B ≠ O)
    (h : ¬ IsTriangle.Degenerate A O B) : 0 < N.uangle A O B := by
  rcases (N.uangle_nonneg A O B).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    apply h
    rw [N.degenerate_iff_angle hA hB]
    left
    exact Real.Angle.toReal_eq_zero_iff.1 (abs_eq_zero.1 h1.symm)

/-- Larger side opposite larger angle (one implication of Exercise 5.4). -/
private theorem aux_dist_lt {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (h : dist B C < dist A C) : N.uangle C A B < N.uangle A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨D, ⟨hDr, hDd⟩, -⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hCA (dist_nonneg : 0 ≤ dist B C)
  have hBCpos : 0 < dist B C := dist_pos.2 hBC
  have hDC : D ≠ C := by
    intro e
    rw [e, dist_self] at hDd
    linarith
  have hDA : D ≠ A := by
    intro e
    rw [e] at hDd
    linarith [dist_comm C A]
  have hBl : B ∉ N.line C A := fun hb => hnd (degenerate_rotate ((N.degenerate_iff_mem_line hCA).2 hb))
  have hDl : D ∈ N.line C A := N.metricHalfLine_subset_line hCA hDr
  have hAD' := N.dist_of_mem_metricHalfLine hCA hDr
  have hbet : IsBetween C D A := by
    refine N.isBetween_of_mem_line hCA hDl hDC hDA (by linarith [dist_comm C A]) ?_
    rw [dist_comm D A, hAD', abs_of_nonneg (by linarith [dist_comm C A])]
    linarith [dist_comm C A]
  have hDray : D ∈ metricHalfLine A C := (IsBetween.mem_metricHalfLine N hbet.symm).1
  have u1 : N.uangle D A B = N.uangle C A B := by
    show |(N.angle D A B).toReal| = |(N.angle C A B).toReal|
    rw [N.angle_ray_left hCA hDray hDA hAB.symm]
  have hBl' : B ∉ N.line A C := by
    rw [N.line_comm]
    exact hBl
  have ext := N.aux_exterior hbet.symm hBl'
  have hDB : D ≠ B := by
    rintro rfl
    exact hBl hDl
  have iso := N.uangle_eq_of_dist_eq (A := D) (B := B) (C := C) ⟨hDB, hBC, hDC.symm⟩
    (by rw [hDd, dist_comm])
  have h38 := (N.isBetween_angle_sign_and_uangle hbet hBl).2.2
  have hndD : ¬ IsTriangle.Degenerate D B A := by
    rintro ⟨L', hL', hD', hB', hA'⟩
    apply hBl
    have e1 := N.eq_line hL' hD' hA' hDA
    have e2 : N.line D A = N.line C A :=
      N.line_eq_of_mem hCA hDl (N.right_mem_line C A) hDA
    rw [e1, e2] at hB'
    exact hB'
  have hpos := N.aux_uangle_pos hDB hAB hndD
  have c1 := N.uangle_comm hBC.symm hDB
  have c2 := N.uangle_comm hBC.symm hAB
  linarith

/-- Exercise 5.4 (auxiliary form). -/
private theorem aux_dist_lt_iff {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    dist B C < dist A C ↔ N.uangle C A B < N.uangle A B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  refine ⟨N.aux_dist_lt ⟨hAB, hBC, hCA⟩ hnd, fun h => ?_⟩
  by_contra hn
  have hn' : dist A C ≤ dist B C := not_lt.1 hn
  have c1 := N.uangle_comm hBC.symm hAB
  have c2 := N.uangle_comm hAB.symm hCA
  rcases hn'.lt_or_eq with h1 | h1
  · have := N.aux_dist_lt (A := B) (B := A) (C := C) ⟨hAB.symm, hCA.symm, hBC.symm⟩
      (fun hd => hnd (degenerate_swap hd)) h1
    linarith
  · have := N.uangle_eq_of_dist_eq ⟨hAB, hBC, hCA⟩ (by rw [dist_comm C A, dist_comm C B]; exact h1)
    linarith

/-- The hypotenuse of a right triangle is longer than a leg (auxiliary form of `dist_lt_hypotenuse`). -/
private theorem aux_hyp {A B C : P} (hA : A ≠ C) (hB : B ≠ C) (h : N.uangle A C B = π / 2) :
    dist A C < dist A B := by
  have hAB : A ≠ B := by
    intro e
    have h' := (abs_toReal_eq_half_iff _).1 h
    rw [← e, N.angle_self hA, add_zero] at h'
    exact Real.Angle.pi_ne_zero h'.symm
  have hnd0 := N.not_degenerate_of_uangle_eq_pi_div_two hA hB h
  have hnd1 : ¬ IsTriangle.Degenerate B C A := fun hd => hnd0 (degenerate_reverse hd)
  have hnd2 : ¬ IsTriangle.Degenerate C B A := fun hd =>
    hnd0 (degenerate_rotate (degenerate_rotate hd))
  have key := (N.aux_dist_lt_iff (A := B) (B := C) (C := A) ⟨hB, hA.symm, hAB⟩ hnd1).2
  have hlt := N.aux_lt_pi (A := C) (B := B) (C := A) ⟨hB.symm, hAB.symm, hA⟩ hnd2
  have c1 := N.uangle_comm hB hA
  have c2 := N.uangle_comm hB.symm hAB
  have hlt' : dist C A < dist B A := key (by linarith)
  rw [dist_comm C A, dist_comm B A] at hlt'
  exact hlt'

/-- **Theorem 5.6** (existence). From a point `X` off a line `L` there is a footpoint `F ∈ L` with
`(XF) ⊥ L`. -/
@[kb "petrunin2025" "Theorem 5.6, p. 38"]
theorem exists_foot {L : Set P} (hL : IsLine L) {X : P} (hX : X ∉ L) :
    ∃ F ∈ L, ∀ Y ∈ L, Y ≠ F → N.uangle X F Y = π / 2 := by
  obtain ⟨σ, hfix, hmove, -, -⟩ := N.exists_lineRefl_aux hL
  obtain ⟨A, hA⟩ : ∃ A, A ∈ L := by
    obtain ⟨g, hg, rfl⟩ := hL
    exact ⟨g 0, 0, rfl⟩
  obtain ⟨B, hB, hBA⟩ := exists_ne_of_mem_line hL hA
  have hXσ : X ≠ σ X := (hmove X hX).symm
  obtain ⟨M, hM, hMd⟩ := N.exists_midpoint hXσ
  have hXM : X ≠ M := hM.1.symm
  have hdist : ∀ Z ∈ L, dist Z X = dist Z (σ X) := by
    intro Z hZ
    have := σ.dist_eq Z X
    rw [hfix Z hZ] at this
    exact this.symm
  have hright : ∀ Z ∈ L, Z ≠ M → N.uangle X M Z = π / 2 := by
    intro Z hZ hZM
    exact (N.dist_eq_iff_uangle_eq_pi_div_two hM hMd hZM).1 (hdist Z hZ)
  have key : ∃ Z ∈ L, M ∈ L ∧ Z ≠ M ∧ N.uangle X M Z = π / 2 := by
    by_cases hAM : A = M
    · exact ⟨B, hB, hAM ▸ hA, fun e => hBA (e.trans hAM.symm), hright B hB (fun e => hBA (e.trans hAM.symm))⟩
    by_cases hBM : B = M
    · exact ⟨A, hA, hBM ▸ hB, hAM, hright A hA hAM⟩
    · have hd := N.degenerate_of_right_right hAM hBM hXM (hright A hA hAM) (hright B hB hBM)
      obtain ⟨L', hL', hA', hM', hB'⟩ := hd
      exact ⟨A, hA, N.mem_of_degenerate hL hA hB hBA.symm ⟨L', hL', hA', hB', hM'⟩, hAM,
        hright A hA hAM⟩
  obtain ⟨Z, hZ, hM, hZM, hr⟩ := key
  refine ⟨M, hM, fun Y hY hYM => ?_⟩
  have hl : L = N.line M Z := N.eq_line hL hM hZ hZM.symm
  have hYl : Y ∈ N.line M Z := by
    rw [← hl]
    exact hY
  have h1 : N.uangle Z M X = π / 2 := by
    rw [N.uangle_comm hZM hXM]
    exact hr
  have h2 := N.uangle_eq_pi_div_two_of_mem_line hZM hXM h1 hYl hYM
  rw [N.uangle_comm hXM hYM]
  exact h2

/-- **Theorem 5.6** (uniqueness). -/
@[kb "petrunin2025" "Theorem 5.6, p. 38"]
theorem foot_unique {L : Set P} (hL : IsLine L) {X F F' : P} (hX : X ∉ L) (hF : F ∈ L) (hF' : F' ∈ L)
    (h : ∀ Y ∈ L, Y ≠ F → N.uangle X F Y = π / 2) (h' : ∀ Y ∈ L, Y ≠ F' → N.uangle X F' Y = π / 2) :
    F = F' := by
  by_contra hne
  have hXF : X ≠ F := fun e => hX (e ▸ hF)
  have hXF' : X ≠ F' := fun e => hX (e ▸ hF')
  have h1 := N.aux_hyp hXF (fun e => hne e.symm) (h F' hF' (fun e => hne e.symm))
  have h2 := N.aux_hyp hXF' hne (h' F hF hne)
  linarith

/-- Through a point `F` of a line `L` there is a unique perpendicular line: two points `X, Y ∉ L` with right
angles `∠XFA`, `∠YFA` (`A ∈ L`, `A ≠ F`) lie on one line through `F`. -/
theorem mem_line_of_perp {L : Set P} (hL : IsLine L) {A F X Y : P} (hA : A ∈ L) (hF : F ∈ L) (hAF : A ≠ F)
    (hX : X ≠ F) (hY : Y ≠ F) (hXr : N.uangle A F X = π / 2) (hYr : N.uangle A F Y = π / 2) :
    Y ∈ N.line F X := by
  have hd := N.degenerate_of_right_right hX hY hAF.symm.symm hXr hYr
  rw [N.line_comm]
  exact (N.degenerate_iff_mem_line hX).1 hd

/-! ### Reflection across a line -/

/-- **Proposition 5.8 / Corollary 5.10.** For every line `L` there is a motion `σ` (the reflection across
`L`) fixing `L` pointwise, moving every point off `L`, keeping distances to the points of `L`, and reversing
angles. -/
@[kb "petrunin2025" "Corollary 5.10, p. 40"]
theorem exists_lineRefl {L : Set P} (hL : IsLine L) :
    ∃ σ : P ≃ᵢ P, (∀ X ∈ L, σ X = X) ∧ (∀ X, X ∉ L → σ X ≠ X) ∧ (∀ X, σ (σ X) = X) ∧
      (∀ A O B : P, A ≠ O → B ≠ O → N.angle (σ A) (σ O) (σ B) = -N.angle A O B) :=
  N.exists_lineRefl_aux hL

/-- The reflection across `L` (chosen by `exists_lineRefl`). -/
noncomputable def lineRefl {L : Set P} (hL : IsLine L) : P ≃ᵢ P :=
  Classical.choose (N.exists_lineRefl hL)

theorem lineRefl_fix {L : Set P} (hL : IsLine L) {X : P} (hX : X ∈ L) : N.lineRefl hL X = X :=
  (Classical.choose_spec (N.exists_lineRefl hL)).1 X hX

theorem lineRefl_ne {L : Set P} (hL : IsLine L) {X : P} (hX : X ∉ L) : N.lineRefl hL X ≠ X :=
  (Classical.choose_spec (N.exists_lineRefl hL)).2.1 X hX

theorem lineRefl_lineRefl {L : Set P} (hL : IsLine L) (X : P) : N.lineRefl hL (N.lineRefl hL X) = X :=
  (Classical.choose_spec (N.exists_lineRefl hL)).2.2.1 X

theorem angle_lineRefl {L : Set P} (hL : IsLine L) {A O B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.angle (N.lineRefl hL A) (N.lineRefl hL O) (N.lineRefl hL B) = -N.angle A O B :=
  (Classical.choose_spec (N.exists_lineRefl hL)).2.2.2 A O B hA hB

/-- The reflection across `L` maps a line perpendicular to `L` at `F` to itself, reversing it: a point at
signed distance `t` from `F` goes to the point at signed distance `-t`. Stated: if `∠XFA` is right
(`A, F ∈ L`, `A ≠ F`), then `F` is the midpoint of `[X σX]`. -/
theorem isBetween_lineRefl_of_perp {L : Set P} (hL : IsLine L) {A F X : P} (hA : A ∈ L) (hF : F ∈ L)
    (hAF : A ≠ F) (hX : X ≠ F) (hr : N.uangle A F X = π / 2) :
    IsBetween X F (N.lineRefl hL X) ∧ dist F (N.lineRefl hL X) = dist F X := by
  have hσX : N.lineRefl hL X ≠ F := by
    intro e
    apply hX
    rw [← N.lineRefl_lineRefl hL X, e, N.lineRefl_fix hL hF]
  have hang := N.angle_lineRefl hL hAF hX
  rw [N.lineRefl_fix hL hA, N.lineRefl_fix hL hF] at hang
  have ha := (abs_toReal_eq_half_iff _).1 hr
  have hsum := N.axiomIIIb F X A (N.lineRefl hL X) hX hAF hσX
  rw [N.angle_rev hX hAF, hang] at hsum
  have hpi : N.angle X F (N.lineRefl hL X) = π := by
    rw [← hsum, ← neg_add, ha, Real.Angle.neg_coe_pi]
  refine ⟨(N.angle_eq_pi_iff hX hσX).1 hpi, ?_⟩
  have := (N.lineRefl hL).dist_eq F X
  rwa [N.lineRefl_fix hL hF] at this

/-- The footpoint of `X ∉ L` is the midpoint of `[X σX]`. -/
theorem foot_isBetween_lineRefl {L : Set P} (hL : IsLine L) {X F : P} (hX : X ∉ L) (hF : F ∈ L)
    (h : ∀ Y ∈ L, Y ≠ F → N.uangle X F Y = π / 2) :
    IsBetween X F (N.lineRefl hL X) ∧ dist F (N.lineRefl hL X) = dist F X := by
  obtain ⟨Y, hY, hYF⟩ := exists_ne_of_mem_line hL hF
  have hXF : X ≠ F := fun e => hX (e ▸ hF)
  exact N.isBetween_lineRefl_of_perp hL hY hF hYF hXF ((N.uangle_comm hYF hXF).trans (h Y hY hYF))

/-- **Lemma 5.13.** The perpendicular is the shortest path from a point to a line. -/
@[kb "petrunin2025" "Lemma 5.13, p. 41"]
theorem dist_foot_lt {L : Set P} (hL : IsLine L) {X F Y : P} (hF : F ∈ L) (hY : Y ∈ L) (hYF : Y ≠ F)
    (h : ∀ Z ∈ L, Z ≠ F → N.uangle X F Z = π / 2) : dist X F < dist X Y := by
  by_cases hXF : X = F
  · rw [hXF, dist_self]
    exact dist_pos.2 hYF.symm
  · exact N.aux_hyp hXF hYF (h Y hY hYF)

/-- A right triangle: if `∠ACB` is right then `AC < AB` (Lemma 5.13 for the line `(CB)`). -/
theorem dist_lt_hypotenuse {A B C : P} (hA : A ≠ C) (hB : B ≠ C) (h : N.uangle A C B = π / 2) :
    dist A C < dist A B :=
  N.aux_hyp hA hB h

/-- **Proposition 11.5.** In a nondegenerate triangle `|∡CAB| + |∡ABC| < π`. (Book's proof: reflect `C`
across the midpoint `M` of `[AB]` to `X`; then `|∡CAX| = |∡CAB| + |∡ABC|` by Exercise 3.8 and Proposition 7.6,
and `∡CAX ≠ π`.) -/
@[kb "petrunin2025" "Proposition 11.5, p. 84"]
theorem uangle_add_uangle_lt_pi {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    N.uangle C A B + N.uangle A B C < π :=
  N.aux_lt_pi hT hnd

/-- Exterior angle: if `D` lies between `A` and `C` and `B ∉ (AC)`, then `|∡DAB| < |∡BDC|`. -/
theorem uangle_lt_exterior {A B C D : P} (hD : IsBetween A D C) (hB : B ∉ N.line A C) :
    N.uangle D A B < N.uangle B D C :=
  N.aux_exterior hD hB

/-- **Exercise 5.4.** In a nondegenerate triangle, `AC > BC` iff `|∡ABC| > |∡CAB|`. -/
@[kb "petrunin2025" "Exercise 5.4, p. 38"]
theorem dist_lt_iff_uangle_lt {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    dist B C < dist A C ↔ N.uangle C A B < N.uangle A B C :=
  N.aux_dist_lt_iff hT hnd

end NeutralPlane

end Neutral

end UndergradKB.Geometry
