import UndergradKB.Geometry.NeutralLegendre
import UndergradKB.Common.Attr

/-! # Neutral plane VI: zero defect, rectangles and parallels (Petrunin, Theorem 11.16 (a), (b), (e), (f))

Let `Z` be the statement that every triangle has zero defect (`NeutralPlane.AllZeroDefect`). For every neutral
plane we prove:

* (e) ⇒ (f): a zero-defect triangle is cut along an altitude into a zero-defect right triangle, and two copies of
  it make a rectangle;
* (f) ⇒ `Z` (Exercise 11.15): rectangles are doubled by reflections until they contain any given right
  triangle;
* if no triangle has zero defect, then Axiom h-V holds (the book's remark after Theorem 11.16): on a line `ℓ`
  the angles `∡PRQ` tend to `0` as `R` runs away (Legendre's halving), while the defect of `PQR` stays bounded
  below;
* `Z` ⇒ uniqueness of parallels, hence (a), and (a) ⇒ (e);
* (b) ⇒ (a): the circumcentre of `Q`, its reflection `X` across `ℓ` and the reflection of `X` across another
  line through `Q` lies on both lines; and `Z` ⇒ (b). -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- Every triangle has zero defect. -/
def AllZeroDefect : Prop := ∀ A B C : P, IsTriangle A B C → N.defect A B C = 0


/-! ### Small helpers -/

include N in
theorem ne_of_not_degenerate {A O B : P} (hA : A ≠ O) (h : ¬ IsTriangle.Degenerate A O B) : A ≠ B := by
  rintro rfl
  exact h ⟨N.line O A, N.isLine_line hA.symm, N.right_mem_line O A, N.left_mem_line O A,
    N.right_mem_line O A⟩

theorem uangle_pos_of_nondeg {A O B : P} (hA : A ≠ O) (hB : B ≠ O) (h : ¬ IsTriangle.Degenerate A O B) :
    0 < N.uangle A O B := by
  rcases (N.uangle_nonneg A O B).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    apply h
    rw [N.degenerate_iff_angle hA hB]
    left
    have h2 := h1.symm
    rw [N.uangle_def] at h2
    exact Real.Angle.toReal_eq_zero_iff.1 (abs_eq_zero.1 h2)

theorem uangle_of_angle_eq_coe {A O B : P} {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ π)
    (h : N.angle A O B = (γ : Real.Angle)) : N.uangle A O B = γ := by
  rw [N.uangle_def, h]
  exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨h0, h1⟩

/-- Triangle inequality for unsigned angles. -/
theorem uangle_le_add {A B X O : P} (hA : A ≠ O) (hB : B ≠ O) (hX : X ≠ O) :
    N.uangle A O B ≤ N.uangle A O X + N.uangle X O B := by
  have h := N.axiomIIIb O A X B hA hX hB
  rw [N.uangle_def, N.uangle_def, N.uangle_def, ← h]
  set a := N.angle A O X
  set b := N.angle X O B
  have hab : ((a.toReal + b.toReal : ℝ) : Real.Angle) = a + b := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  by_cases hc : -π < a.toReal + b.toReal ∧ a.toReal + b.toReal ≤ π
  · rw [← hab, Real.Angle.toReal_coe_eq_self_iff.2 hc]
    exact abs_add_le _ _
  · have h3 : π ≤ |a.toReal + b.toReal| := by
      by_contra hlt
      push Not at hlt
      exact hc ⟨by linarith [neg_abs_le (a.toReal + b.toReal)], by linarith [le_abs_self (a.toReal + b.toReal)]⟩
    calc |(a + b).toReal| ≤ π := Real.Angle.abs_toReal_le_pi _
      _ ≤ |a.toReal + b.toReal| := h3
      _ ≤ _ := abs_add_le _ _

include N in
theorem exists_midpoint {A B : P} (h : A ≠ B) : ∃ M, IsBetween A M B ∧ dist A M = dist M B := by
  have hd := dist_pos.2 h
  set M := N.linePt A B (dist A B / 2) with hM
  have h1 : dist A M = dist A B / 2 := by
    rw [hM, N.dist_left_linePt h, abs_of_pos (by linarith)]
  have h2 : dist M B = dist A B / 2 := by
    have := N.dist_linePt h (dist A B / 2) (dist A B)
    rw [N.linePt_dist h] at this
    rw [hM, this, abs_of_neg (by linarith)]
    ring
  refine ⟨M, ⟨?_, ?_, ?_, ?_⟩, by rw [h1, h2]⟩
  · intro e
    rw [e, dist_self] at h1
    linarith
  · intro e
    rw [e, dist_self] at h2
    linarith
  · rw [h1, h2]
    ring
  · exact ⟨N.line A B, N.isLine_line h, N.left_mem_line A B, N.linePt_mem_line A B _, N.right_mem_line A B⟩

theorem exists_ne_mem {L : Set P} (hL : IsLine L) {x : P} (hx : x ∈ L) : ∃ y ∈ L, y ≠ x := by
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨a, rfl⟩ := hx
  refine ⟨g (a + 1), ⟨a + 1, rfl⟩, fun e => ?_⟩
  have := hg.injective e
  linarith

theorem not_mem_line_of_perp {A O B : P} (hA : A ≠ O) (hB : B ≠ O) (h : N.uangle A O B = π / 2) :
    A ∉ N.line O B := by
  intro hm
  apply N.not_degenerate_of_uangle_eq_pi_div_two hA hB h
  obtain ⟨L, hL, h1, h2, h3⟩ := (N.degenerate_iff_mem_line hB.symm).2 hm
  exact ⟨L, hL, h3, h1, h2⟩

/-- Degeneracy is invariant under rotating the vertices. -/
theorem deg_rotate {A B C : P} (h : IsTriangle.Degenerate A B C) : IsTriangle.Degenerate B C A := by
  obtain ⟨L, hL, h1, h2, h3⟩ := h
  exact ⟨L, hL, h2, h3, h1⟩

theorem nondeg_rotate {A B C : P} (h : ¬ IsTriangle.Degenerate A B C) : ¬ IsTriangle.Degenerate B C A :=
  fun h' => h (deg_rotate (deg_rotate h'))

/-- The defect is unchanged by any permutation of the vertices. -/
theorem defect_perm1 {A B C : P} (hT : IsTriangle A B C) : N.defect A C B = N.defect A B C := by
  have h1 := N.defect_swap hT
  have h2 := N.defect_rotate (A := B) (B := A) (C := C) ⟨hT.1.symm, hT.2.2.symm, hT.2.1.symm⟩
  rw [h2, h1]

theorem defect_perm2 {A B C : P} (hT : IsTriangle A B C) : N.defect C A B = N.defect A B C := by
  have h1 := N.defect_rotate hT
  have h2 := N.defect_rotate (A := B) (B := C) (C := A) ⟨hT.2.1, hT.2.2, hT.1⟩
  rw [h2, h1]

include N in
/-- A point strictly between `A` and `C` lies on the rays `[AC)` and `[CA)`; here as `B ∈ [AC)`,
`C ∈ [AB)`. -/
theorem isBetween_rays {A B C : P} (h : IsBetween A B C) :
    B ∈ metricHalfLine A C ∧ C ∈ metricHalfLine A B := by
  have hAB : A ≠ B := h.1.symm
  have hAC : A ≠ C := h.ne
  have hd := h.dist_add
  refine ⟨?_, ?_⟩
  · rcases N.mem_metricHalfLine_or_isBetween hAC (N.mem_line_of_isBetween h) with h1 | h1
    · exact h1
    · exfalso
      have := h1.dist_add
      linarith [dist_comm B A, dist_comm C B, dist_pos.2 hAB, dist_comm C A]
  · have hC : C ∈ N.line A B := (N.degenerate_iff_mem_line hAB).1 h.degenerate
    rcases N.mem_metricHalfLine_or_isBetween hAB hC with h1 | h1
    · exact h1
    · exfalso
      have := h1.dist_add
      have := dist_pos.2 hAB
      rw [dist_comm C A, dist_comm B C] at *
      linarith

theorem uangle_ray_right {A O B B' : P} (hA : A ≠ O) (hB : B ≠ O) (hB' : B' ∈ metricHalfLine O B)
    (hB'O : B' ≠ O) : N.uangle A O B' = N.uangle A O B := by
  rw [N.uangle_def, N.uangle_def, N.angle_ray_right hA hB hB' hB'O]

theorem uangle_ray_left {A A' O B : P} (hA : A ≠ O) (hA' : A' ∈ metricHalfLine O A) (hA'O : A' ≠ O)
    (hB : B ≠ O) : N.uangle A' O B = N.uangle A O B := by
  rw [N.uangle_def, N.uangle_def, N.angle_ray_left hA hA' hA'O hB]

/-! ### Footpoints and right triangles -/

/-- Seen from the foot `F` of a perpendicular from `C`, a point `X` strictly between `Y` and `F` on the line
sees `Y` under an obtuse angle. -/
theorem foot_obtuse {L : Set P} (hL : IsLine L) {C Y X F : P} (hY : Y ∈ L) (hX : X ∈ L) (hF : F ∈ L)
    (hC : C ∉ L) (hFr : ∀ Z ∈ L, Z ≠ F → N.uangle C F Z = π / 2) (hb : IsBetween Y X F) :
    π / 2 < N.uangle Y X C := by
  have hYF : Y ≠ F := hb.ne
  have hXF : X ≠ F := hb.2.1
  have hCX : C ≠ X := by
    rintro rfl
    exact hC hX
  have hCF : C ≠ F := by
    rintro rfl
    exact hC hF
  have hLine : N.line Y F = L := (N.eq_line hL hY hF hYF).symm
  have hC' : C ∉ N.line Y F := by rw [hLine]; exact hC
  obtain ⟨h1, -⟩ := N.uangle_add_uangle_of_isBetween hb hC'
  have hr := hFr X hX hXF
  have hnd : ¬ IsTriangle.Degenerate C F X := N.not_degenerate_of_uangle_eq_pi_div_two hCF hXF hr
  have h2 := N.uangle_add_uangle_lt_pi (A := F) (B := X) (C := C) ⟨hXF.symm, hCX.symm, hCF⟩
    (nondeg_rotate hnd)
  have h3 := N.uangle_comm (A := F) (O := X) (B := C) hXF.symm hCX
  linarith

/-- If the base angles at `A` and `B` are acute, the foot of `C` on `(AB)` lies between `A` and `B`. -/
theorem foot_isBetween_of_acute {A B C F : P} (hAB : A ≠ B) (hC : C ∉ N.line A B)
    (hA : N.uangle C A B < π / 2) (hB : N.uangle A B C < π / 2) (hF : F ∈ N.line A B)
    (hFr : ∀ Y ∈ N.line A B, Y ≠ F → N.uangle C F Y = π / 2) : IsBetween A F B := by
  have hL := N.isLine_line hAB
  have hAm := N.left_mem_line A B
  have hBm := N.right_mem_line A B
  have hCA : C ≠ A := by
    rintro rfl
    exact hC hAm
  have hCB : C ≠ B := by
    rintro rfl
    exact hC hBm
  have hFA : F ≠ A := by
    intro e
    have h := hFr B hBm (by intro h; exact hAB (e.symm.trans h.symm))
    rw [e] at h
    linarith
  have hFB : F ≠ B := by
    intro e
    have h := hFr A hAm (by intro h; exact hAB (h.trans e))
    rw [e] at h
    have := N.uangle_comm (A := C) (O := B) (B := A) hCB hAB
    linarith
  rcases hL.isBetween_trichotomy hAm hBm hF hAB hFB.symm hFA with h | h | h
  · have := N.foot_obtuse hL hBm hAm hF hC hFr h
    rw [N.uangle_comm hAB.symm hCA] at this
    linarith
  · have := N.foot_obtuse hL hAm hBm hF hC hFr h
    linarith
  · exact h

/-- Two perpendiculars to one line do not meet (Proposition 11.5): if `∠XAB` and `∠YBA` are right
(`A ≠ B`), then the lines `(AX)` and `(BY)` are disjoint. -/
theorem disjoint_of_perp_perp {A B X Y : P} (hAB : A ≠ B) (hX : X ≠ A) (hY : Y ≠ B)
    (hXr : N.uangle X A B = π / 2) (hYr : N.uangle Y B A = π / 2) :
    Disjoint (N.line A X) (N.line B Y) := by
  rw [Set.disjoint_left]
  intro Z hZ1 hZ2
  have hZA : Z ≠ A := by
    intro e
    rw [e] at hZ2
    have := N.uangle_eq_pi_div_two_of_mem_line hY hAB hYr hZ2 hAB
    rw [N.uangle_def, N.angle_self hAB] at this
    simp at this
    linarith [Real.pi_pos]
  have hZB : Z ≠ B := by
    intro e
    rw [e] at hZ1
    have := N.uangle_eq_pi_div_two_of_mem_line hX hAB.symm hXr hZ1 hAB.symm
    rw [N.uangle_def, N.angle_self hAB.symm] at this
    simp at this
    linarith [Real.pi_pos]
  have h1 := N.uangle_eq_pi_div_two_of_mem_line hX hAB.symm hXr hZ1 hZA
  have h2 := N.uangle_eq_pi_div_two_of_mem_line hY hAB hYr hZ2 hZB
  have hnd : ¬ IsTriangle.Degenerate Z A B := N.not_degenerate_of_uangle_eq_pi_div_two hZA hAB.symm h1
  have h3 := N.uangle_add_uangle_lt_pi (A := A) (B := B) (C := Z) ⟨hAB, hZB.symm, hZA⟩
    (nondeg_rotate hnd)
  have h4 := N.uangle_comm (A := Z) (O := B) (B := A) hZB hAB
  linarith

private theorem nondeg_swap' {A B C : P} (h : ¬ IsTriangle.Degenerate A B C) :
    ¬ IsTriangle.Degenerate A C B := by
  rintro ⟨L, hL, hA, hC, hB⟩
  exact h ⟨L, hL, hA, hB, hC⟩

include N in
/-- Splitting a triangle along the altitude from the vertex `C` with the largest angle. -/
private theorem split_largest {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (hA : N.uangle C A B ≤ N.uangle B C A) (hB : N.uangle A B C ≤ N.uangle B C A) :
    ∃ F, IsBetween A F B ∧ N.uangle C F A = π / 2 ∧ N.uangle C F B = π / 2 ∧
      C ∉ N.line A B ∧ N.defect A B C = N.defect A F C + N.defect F B C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hC : C ∉ N.line A B := fun h => hnd ((N.degenerate_iff_mem_line hAB).2 h)
  have hsum := N.uangle_sum_le_pi (A := A) (B := B) (C := C) ⟨hAB, hBC, hCA⟩
  have pA : 0 < N.uangle C A B :=
    N.uangle_pos_of_nondeg hCA hAB.symm (nondeg_rotate (nondeg_rotate hnd))
  have pB : 0 < N.uangle A B C := N.uangle_pos_of_nondeg hAB hBC.symm hnd
  have a1 : N.uangle C A B < π / 2 := by
    by_contra hh
    push Not at hh
    linarith
  have a2 : N.uangle A B C < π / 2 := by
    by_contra hh
    push Not at hh
    linarith
  obtain ⟨F, hFL, hF⟩ := N.exists_foot (N.isLine_line hAB) hC
  have hbt := N.foot_isBetween_of_acute hAB hC a1 a2 hFL hF
  refine ⟨F, hbt, ?_, ?_, hC, N.defect_add hbt hC⟩
  · exact hF A (N.left_mem_line A B) hbt.1.symm
  · exact hF B (N.right_mem_line A B) hbt.2.1.symm

include N in
private theorem exists_split {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    ∃ X Y Z F : P, IsTriangle X Y Z ∧ ¬ IsTriangle.Degenerate X Y Z ∧ N.defect X Y Z = N.defect A B C ∧
      IsBetween X F Y ∧ N.uangle Z F X = π / 2 ∧ N.uangle Z F Y = π / 2 ∧ Z ∉ N.line X Y ∧
      N.defect X Y Z = N.defect X F Z + N.defect F Y Z := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hT0 : IsTriangle A B C := ⟨hAB, hBC, hCA⟩
  have caseC : N.uangle C A B ≤ N.uangle B C A → N.uangle A B C ≤ N.uangle B C A →
      ∃ X Y Z F : P, IsTriangle X Y Z ∧ ¬ IsTriangle.Degenerate X Y Z ∧ N.defect X Y Z = N.defect A B C ∧
        IsBetween X F Y ∧ N.uangle Z F X = π / 2 ∧ N.uangle Z F Y = π / 2 ∧ Z ∉ N.line X Y ∧
        N.defect X Y Z = N.defect X F Z + N.defect F Y Z := by
    intro h1 h2
    obtain ⟨F, a, b, c, d, e⟩ := N.split_largest hT0 hnd h1 h2
    exact ⟨A, B, C, F, hT0, hnd, rfl, a, b, c, d, e⟩
  have caseA : N.uangle A B C ≤ N.uangle C A B → N.uangle B C A ≤ N.uangle C A B →
      ∃ X Y Z F : P, IsTriangle X Y Z ∧ ¬ IsTriangle.Degenerate X Y Z ∧ N.defect X Y Z = N.defect A B C ∧
        IsBetween X F Y ∧ N.uangle Z F X = π / 2 ∧ N.uangle Z F Y = π / 2 ∧ Z ∉ N.line X Y ∧
        N.defect X Y Z = N.defect X F Z + N.defect F Y Z := by
    intro h1 h2
    have hT1 : IsTriangle B C A := ⟨hBC, hCA, hAB⟩
    obtain ⟨F, a, b, c, d, e⟩ := N.split_largest hT1 (nondeg_rotate hnd) h1 h2
    exact ⟨B, C, A, F, hT1, nondeg_rotate hnd, N.defect_rotate hT0, a, b, c, d, e⟩
  have caseB : N.uangle B C A ≤ N.uangle A B C → N.uangle C A B ≤ N.uangle A B C →
      ∃ X Y Z F : P, IsTriangle X Y Z ∧ ¬ IsTriangle.Degenerate X Y Z ∧ N.defect X Y Z = N.defect A B C ∧
        IsBetween X F Y ∧ N.uangle Z F X = π / 2 ∧ N.uangle Z F Y = π / 2 ∧ Z ∉ N.line X Y ∧
        N.defect X Y Z = N.defect X F Z + N.defect F Y Z := by
    intro h1 h2
    have hT1 : IsTriangle C A B := ⟨hCA, hAB, hBC⟩
    obtain ⟨F, a, b, c, d, e⟩ := N.split_largest hT1 (nondeg_rotate (nondeg_rotate hnd)) h1 h2
    exact ⟨C, A, B, F, hT1, nondeg_rotate (nondeg_rotate hnd), N.defect_perm2 hT0, a, b, c, d, e⟩
  rcases le_total (N.uangle A B C) (N.uangle B C A) with h1 | h1
  · rcases le_total (N.uangle B C A) (N.uangle C A B) with h2 | h2
    · exact caseA (h1.trans h2) h2
    · exact caseC h2 h1
  · rcases le_total (N.uangle A B C) (N.uangle C A B) with h3 | h3
    · exact caseA h3 (h1.trans h3)
    · exact caseB h1 h3

include N in
private theorem tri_of_split {X Y Z F : P} (hbt : IsBetween X F Y) (hZ : Z ∉ N.line X Y) :
    IsTriangle X F Z ∧ IsTriangle F Y Z := by
  have hZF : Z ≠ F := by
    rintro rfl
    exact hZ (N.mem_line_of_isBetween hbt)
  have hZX : Z ≠ X := by
    rintro rfl
    exact hZ (N.left_mem_line _ _)
  have hZY : Z ≠ Y := by
    rintro rfl
    exact hZ (N.right_mem_line _ _)
  exact ⟨⟨hbt.1.symm, hZF.symm, hZX⟩, ⟨hbt.2.1, hZY.symm, hZF⟩⟩

/-- A triangle with zero defect contains a right triangle with zero defect: the altitude from the vertex with
the largest angle (Proposition 11.5 and Exercise 11.12). -/
theorem exists_right_zeroDefect (h : N.ZeroDefectTriangle) :
    ∃ A B C : P, IsTriangle A B C ∧ ¬ IsTriangle.Degenerate A B C ∧ N.uangle A C B = π / 2 ∧
      N.defect A B C = 0 := by
  obtain ⟨A, B, C, hT, hnd, h0⟩ := h
  obtain ⟨X, Y, Z, F, hT', hnd', hd, hbt, hr1, hr2, hZ, hsplit⟩ := N.exists_split hT hnd
  obtain ⟨t1, t2⟩ := N.tri_of_split hbt hZ
  have d1 := N.defect_nonneg t1
  have d2 := N.defect_nonneg t2
  have z1 : N.defect X F Z = 0 := by linarith
  have hXF : X ≠ F := t1.1
  have hZF : Z ≠ F := t1.2.1.symm
  have hr : N.uangle X F Z = π / 2 := (N.uangle_comm hXF hZF).trans hr1
  refine ⟨X, Z, F, ⟨t1.2.2.symm, t1.2.1.symm, hXF.symm⟩, ?_, hr, ?_⟩
  · exact nondeg_swap' (N.not_degenerate_of_uangle_eq_pi_div_two hXF hZF hr)
  · rw [N.defect_perm1 t1]
    exact z1

include N in
private theorem pointRefl_ends {A B M : P} (hM : IsBetween A M B) (hMM : dist A M = dist M B) :
    N.pointRefl M A = B ∧ N.pointRefl M B = A := by
  constructor
  · exact N.pointRefl_eq_of_isBetween hM (by linarith [dist_comm A M])
  · exact N.pointRefl_eq_of_isBetween hM.symm (by linarith [dist_comm A M])

include N in
private theorem rect_corner {A B C M : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (hC : N.uangle A C B = π / 2) (h0 : N.defect A B C = 0)
    (hM : IsBetween A M B) (hMM : dist A M = dist M B) :
    N.uangle (N.pointRefl M C) A C = π / 2 := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hfA, hfB⟩ := N.pointRefl_ends hM hMM
  have hCL : C ∉ N.line A B := fun h => hnd ((N.degenerate_iff_mem_line hAB).2 h)
  have hML : M ∈ N.line A B := N.mem_line_of_isBetween hM
  have hMC : C ≠ M := by
    intro e
    exact hCL (e ▸ hML)
  have hCMD : IsBetween C M (N.pointRefl M C) := by
    rw [N.pointRefl_apply]
    exact N.isBetween_pointReflFun hMC
  set D := N.pointRefl M C with hD
  have hDA : D ≠ A := by
    intro e
    rw [← hfB, hD] at e
    exact hBC (((N.pointRefl M).injective e).symm)
  have hCD : C ≠ D := hCMD.ne
  have hMA : M ≠ A := hM.1
  have hrays := N.isBetween_rays hM
  have hBline : B ∈ N.line A M := N.metricHalfLine_subset_line hMA.symm hrays.2
  have hAD : A ∉ N.line C D := by
    intro hA
    have e : N.line A M = N.line C D :=
      N.line_eq_of_mem hCD hA (N.mem_line_of_isBetween hCMD) hMA.symm
    apply hnd
    exact ⟨N.line C D, N.isLine_line hCD, hA, e ▸ hBline, N.left_mem_line C D⟩
  have hsum := (N.isBetween_angle_sign_and_uangle hCMD hAD).2.2
  have e1 : N.uangle C A M = N.uangle C A B :=
    N.uangle_ray_right hCA hAB.symm hrays.1 hMA
  have e2 : N.uangle M A D = N.uangle B A D :=
    N.uangle_ray_left hAB.symm hrays.1 hMA hDA
  have e3 : N.uangle B A D = N.uangle D A B := N.uangle_comm hAB.symm hDA
  have e4 : N.uangle D A B = N.uangle C B A := by
    have := N.uangle_isometryEquiv (N.pointRefl M) (A := C) (O := B) (B := A) hBC.symm hAB
    rw [hfA, hfB] at this
    exact this
  have e5 : N.uangle A B C = N.uangle C B A := N.uangle_comm hAB hBC.symm
  have e6 : N.uangle B C A = π / 2 := (N.uangle_comm hBC hCA.symm).trans hC
  have hdef : N.uangle A B C + N.uangle B C A + N.uangle C A B = π := by
    unfold NeutralPlane.defect at h0
    linarith
  have : N.uangle C A D = π / 2 := by
    rw [← hsum, e1, e2, e3, e4]
    linarith
  rw [N.uangle_comm hDA hCA]
  exact this

/-- Two copies of a zero-defect right triangle `ACB` (right angle at `C`) make a rectangle: reflect `C` across
the midpoint `M` of the hypotenuse. -/
theorem isRectangle_of_right_zeroDefect {A B C M : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hC : N.uangle A C B = π / 2) (h0 : N.defect A B C = 0)
    (hM : IsBetween A M B) (hMM : dist A M = dist M B) :
    N.IsRectangle A C B (N.pointRefl M C) := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hfA, hfB⟩ := N.pointRefl_ends hM hMM
  have hCL : C ∉ N.line A B := fun h => hnd ((N.degenerate_iff_mem_line hAB).2 h)
  have hMC : C ≠ M := by
    intro e
    exact hCL (e ▸ N.mem_line_of_isBetween hM)
  have hCMD : IsBetween C M (N.pointRefl M C) := by
    rw [N.pointRefl_apply]
    exact N.isBetween_pointReflFun hMC
  set D := N.pointRefl M C with hD
  have hDA : D ≠ A := by
    intro e
    rw [← hfB, hD] at e
    exact hBC (((N.pointRefl M).injective e).symm)
  have hDB : D ≠ B := by
    intro e
    rw [← hfA, hD] at e
    exact hCA ((N.pointRefl M).injective e)
  have h1 := N.rect_corner ⟨hAB, hBC, hCA⟩ hnd hC h0 hM hMM
  have h2 := N.rect_corner (A := B) (B := A) (C := C) (M := M) ⟨hAB.symm, hCA.symm, hBC.symm⟩
    (not_degenerate_swap hnd) ((N.uangle_comm hBC hCA.symm).symm ▸ hC)
    (by rw [N.defect_swap ⟨hAB, hBC, hCA⟩]; exact h0) hM.symm
    (by linarith [dist_comm B M, dist_comm M A])
  have h3 : N.uangle B D A = π / 2 := by
    have := N.uangle_isometryEquiv (N.pointRefl M) (A := A) (O := C) (B := B) hCA.symm hBC
    rw [hfA, hfB] at this
    exact this.trans hC
  refine ⟨hCA.symm, hAB, hDA.symm, hBC.symm, hCMD.ne, hDB.symm, hC, ?_, h3, ?_⟩
  · rw [N.uangle_comm hBC.symm hDB]
    exact h2
  · exact h1

/-- **(e) ⇒ (f).** -/
theorem hasRectangle_of_zeroDefectTriangle (h : N.ZeroDefectTriangle) : N.HasRectangle := by
  obtain ⟨A, B, C, hT, hnd, hC, h0⟩ := N.exists_right_zeroDefect h
  obtain ⟨M, hM, hMM⟩ := N.exists_midpoint hT.1
  exact ⟨_, _, _, _, N.isRectangle_of_right_zeroDefect hT hnd hC h0 hM hMM⟩

/-! ### Rectangles ⇒ zero defect (Exercise 11.15) -/

theorem IsRectangle.rotate {A B C D : P} (h : N.IsRectangle A B C D) : N.IsRectangle B C D A := by
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := h
  exact ⟨h4, h5, h1.symm, h6, h2.symm, h3.symm, a2, a3, a4, a1⟩

theorem IsRectangle.reverse {A B C D : P} (h : N.IsRectangle A B C D) : N.IsRectangle A D C B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := h
  refine ⟨h3, h2, h1, h6.symm, h5.symm, h4.symm, ?_, ?_, ?_, ?_⟩
  · exact (N.uangle_comm h3 h6).trans a3
  · exact (N.uangle_comm h6.symm h4).trans a2
  · exact (N.uangle_comm h4.symm h1).trans a1
  · exact (N.uangle_comm h1.symm h3.symm).trans a4

private theorem rect_defect_aux {A B C D : P} (h : N.IsRectangle A B C D) :
    N.defect A B C = 0 ∧ N.defect C D A = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := h
  have d1 := N.defect_nonneg (A := A) (B := B) (C := C) ⟨h1, h4, h2.symm⟩
  have d2 := N.defect_nonneg (A := C) (B := D) (C := A) ⟨h6, h3.symm, h2⟩
  have t1 := N.uangle_le_add (A := B) (B := D) (X := A) (O := C) h4 h6.symm h2
  have t2 := N.uangle_le_add (A := D) (B := B) (X := C) (O := A) h3.symm h1.symm h2.symm
  unfold NeutralPlane.defect at d1 d2 ⊢
  constructor <;> linarith

theorem IsRectangle.defect_eq_zero {A B C D : P} (h : N.IsRectangle A B C D) : N.defect A B D = 0 := by
  have h' := (N.rect_defect_aux h.rotate).2
  have := N.defect_perm2 (A := A) (B := B) (C := D) ⟨h.1, h.2.2.2.2.1, h.2.2.1.symm⟩
  rw [← this]
  exact h'

/-- A motion maps rectangles to rectangles. -/
theorem IsRectangle.isometryEquiv (f : P ≃ᵢ P) {A B C D : P} (h : N.IsRectangle A B C D) :
    N.IsRectangle (f A) (f B) (f C) (f D) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := h
  refine ⟨f.injective.ne h1, f.injective.ne h2, f.injective.ne h3, f.injective.ne h4, f.injective.ne h5,
    f.injective.ne h6, ?_, ?_, ?_, ?_⟩
  · exact (N.uangle_isometryEquiv f h1 h4.symm).trans a1
  · exact (N.uangle_isometryEquiv f h4 h6.symm).trans a2
  · exact (N.uangle_isometryEquiv f h6 h3).trans a3
  · exact (N.uangle_isometryEquiv f h3.symm h1.symm).trans a4

/-- Doubling a rectangle `ABCD` across the side `(BC)`: there is a rectangle `A A' D' D` with `AA' = 2·AB`
(`B` the midpoint of `[AA']`, `C` the midpoint of `[DD']`). -/
theorem IsRectangle.double {A B C D : P} (h : N.IsRectangle A B C D) :
    ∃ A' D' : P, N.IsRectangle A A' D' D ∧ IsBetween A B A' ∧ dist A A' = 2 * dist A B := by
  have hR := h
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := h
  have hL := N.isLine_line h4
  have hBL : B ∈ N.line B C := N.left_mem_line B C
  have hCL : C ∈ N.line B C := N.right_mem_line B C
  have hfB := N.lineRefl_fix hL hBL
  have hfC := N.lineRefl_fix hL hCL
  have hcA : N.uangle C B A = π / 2 := (N.uangle_comm h4.symm h1).trans a1
  obtain ⟨hb1, hd1⟩ := N.isBetween_lineRefl_of_perp hL hCL hBL h4.symm h1 hcA
  obtain ⟨hb2, hd2⟩ := N.isBetween_lineRefl_of_perp hL hBL hCL h4 h6.symm a2
  have hR' := IsRectangle.isometryEquiv N (N.lineRefl hL) hR
  rw [hfB, hfC] at hR'
  set A' := N.lineRefl hL A with hA'
  set D' := N.lineRefl hL D with hD'
  obtain ⟨g1, g2, g3, g4, g5, g6, b1, b2, b3, b4⟩ := hR'
  -- rays
  have hA'ray : A' ∈ metricHalfLine A B := (N.isBetween_rays hb1).2
  have hAray : A ∈ metricHalfLine A' B := (N.isBetween_rays hb1.symm).2
  have hDray : D ∈ metricHalfLine D' C := (N.isBetween_rays hb2.symm).2
  have hD'ray : D' ∈ metricHalfLine D C := (N.isBetween_rays hb2).2
  have hAA' : A ≠ A' := hb1.ne
  have hDD' : D ≠ D' := hb2.ne
  have hA'B : A' ≠ B := hb1.2.1.symm
  have hD'C : D' ≠ C := hb2.2.1.symm
  have hDnot : D ∉ N.line A B := N.not_mem_line_of_perp h3.symm h1.symm a4
  have hA'line : A' ∈ N.line A B := N.metricHalfLine_subset_line h1 hA'ray
  have hAD' : A ≠ D' := by
    intro e
    have : N.lineRefl hL A = D := by
      have := congrArg (N.lineRefl hL) e
      rw [N.lineRefl_lineRefl] at this
      exact this
    apply hDnot
    rw [← this]
    exact hA'line
  have hA'D : A' ≠ D := by
    intro e
    apply hDnot
    rw [← e]
    exact hA'line
  refine ⟨A', D', ⟨hAA', hAD', h3, g3, hA'D, hDD'.symm, ?_, ?_, ?_, ?_⟩, hb1, ?_⟩
  · calc N.uangle A A' D' = N.uangle D' A' A := N.uangle_comm hAA' g3.symm
      _ = N.uangle D' A' B := N.uangle_ray_right g3.symm g1.symm hAray hAA'
      _ = π / 2 := b4
  · calc N.uangle A' D' D = N.uangle A' D' C := N.uangle_ray_right g3 g6 hDray hDD'
      _ = N.uangle C D' A' := N.uangle_comm g3 g6
      _ = π / 2 := b3
  · calc N.uangle D' D A = N.uangle C D A := N.uangle_ray_left h6 hD'ray hDD'.symm h3
      _ = π / 2 := a3
  · calc N.uangle D A A' = N.uangle D A B := N.uangle_ray_right h3.symm h1.symm hA'ray hAA'.symm
      _ = π / 2 := a4
  · have := hb1.dist_add
    have h7 : dist B A' = dist B A := hd1
    rw [dist_comm B A] at h7
    linarith

include N in
private theorem grow_aux (n : ℕ) : ∀ {A B C D : P}, N.IsRectangle A B C D →
    ∃ A' B' C' D' : P, N.IsRectangle A' B' C' D' ∧ 2 ^ n * dist A B ≤ dist A' B' ∧
      dist A D ≤ dist A' D' := by
  induction n with
  | zero =>
    intro A B C D h
    exact ⟨A, B, C, D, h, by simp, le_rfl⟩
  | succ n ih =>
    intro A B C D h
    obtain ⟨A', D', hR, hb, hd⟩ := h.double
    obtain ⟨A2, B2, C2, D2, hR2, k1, k2⟩ := ih hR
    refine ⟨A2, B2, C2, D2, hR2, ?_, k2⟩
    have : (2 : ℝ) ^ (n + 1) * dist A B = 2 ^ n * dist A A' := by
      rw [hd]
      ring
    rw [this]
    exact k1

/-- With one rectangle there are rectangles with both sides as long as we like. -/
theorem exists_rectangle_ge (h : N.HasRectangle) (a b : ℝ) :
    ∃ A B C D : P, N.IsRectangle A B C D ∧ a ≤ dist A B ∧ b ≤ dist A D := by
  obtain ⟨A, B, C, D, hR⟩ := h
  have d1 : 0 < dist A B := dist_pos.2 hR.1
  have d2 : 0 < dist A D := dist_pos.2 hR.2.2.1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a / dist A B) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (b / dist A D) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ d1] at hn
  rw [div_lt_iff₀ d2] at hm
  obtain ⟨A1, B1, C1, D1, hR1, h1, h1'⟩ := N.grow_aux n hR
  obtain ⟨A2, B2, C2, D2, hR2, h2, h2'⟩ := N.grow_aux m hR1.reverse
  refine ⟨A2, D2, C2, B2, hR2.reverse, ?_, ?_⟩
  · linarith
  · have := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ 2 ^ m)
    linarith

/-- With one rectangle, any right angle `∠PQR` is the corner of a rectangle `QXYW` with `X ∈ [QP)`,
`W ∈ [QR)`, `QX ≥ QP`, `QW ≥ QR`. -/
theorem exists_rectangle_at (h : N.HasRectangle) {P₀ Q R : P} (hP : P₀ ≠ Q) (hR : R ≠ Q)
    (hr : N.uangle P₀ Q R = π / 2) :
    ∃ X Y W : P, N.IsRectangle Q X Y W ∧ X ∈ metricHalfLine Q P₀ ∧ W ∈ metricHalfLine Q R ∧
      dist Q P₀ ≤ dist Q X ∧ dist Q R ≤ dist Q W := by
  obtain ⟨A, B, C, D, hRc, hAB, hAD⟩ := N.exists_rectangle_ge h (dist Q P₀) (dist Q R)
  obtain ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩ := hRc
  have hRc : N.IsRectangle A B C D := ⟨h1, h2, h3, h4, h5, h6, a1, a2, a3, a4⟩
  obtain ⟨X, ⟨hXr, hXd⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hP.symm (dist_nonneg : 0 ≤ dist A B)
  obtain ⟨W, ⟨hWr, hWd⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hR.symm (dist_nonneg : 0 ≤ dist A D)
  have hXQ : X ≠ Q := by
    intro e
    rw [e, dist_self] at hXd
    exact h1 (dist_eq_zero.1 hXd.symm)
  have hWQ : W ≠ Q := by
    intro e
    rw [e, dist_self] at hWd
    exact h3 (dist_eq_zero.1 hWd.symm)
  have hang : N.uangle W Q X = π / 2 := by
    rw [N.uangle_ray_left hR hWr hWQ hXQ, N.uangle_ray_right hR hP hXr hXQ, N.uangle_comm hR hP]
    exact hr
  have hXW : X ≠ W := by
    intro e
    rw [e, N.uangle_def, N.angle_self hWQ] at hang
    simp at hang
    linarith [Real.pi_pos]
  obtain ⟨f, hfA, hfB, hfD⟩ := N.sas h1 h3 h5 hXQ.symm hWQ.symm hXW hXd hWd (by rw [hang, a4])
  have hR2 := IsRectangle.isometryEquiv N f hRc
  rw [hfA, hfB, hfD] at hR2
  refine ⟨X, f C, W, hR2, hXr, hWr, ?_, ?_⟩
  · rw [hXd]
    exact hAB
  · rw [hWd]
    exact hAD

/-- If every right triangle has zero defect, then every triangle has (altitude from the largest angle). -/
theorem allZeroDefect_of_right (h : ∀ A B C : P, IsTriangle A B C → N.uangle A C B = π / 2 →
    N.defect A B C = 0) : N.AllZeroDefect := by
  intro A B C hT
  by_cases hd : IsTriangle.Degenerate A B C
  · exact N.defect_eq_zero_of_degenerate hT hd
  obtain ⟨X, Y, Z, F, hT', hnd', hdef, hbt, hr1, hr2, hZ, hsplit⟩ := N.exists_split hT hd
  obtain ⟨t1, t2⟩ := N.tri_of_split hbt hZ
  have hXF : X ≠ F := t1.1
  have hZF : Z ≠ F := t1.2.1.symm
  have hYF : Y ≠ F := t2.1.symm
  have z1 : N.defect X F Z = 0 := by
    have := h X Z F ⟨t1.2.2.symm, t1.2.1.symm, hXF.symm⟩ ((N.uangle_comm hXF hZF).trans hr1)
    rw [← N.defect_perm1 t1]
    exact this
  have z2 : N.defect F Y Z = 0 := by
    have := h Y Z F ⟨t2.2.1, t2.2.2, t2.1⟩ ((N.uangle_comm hYF hZF).trans hr2)
    rw [← N.defect_rotate t2]
    exact this
  rw [← hdef, hsplit, z1, z2]
  norm_num

include N in
/-- If `X` lies on the ray `[CA)` at least as far as `A`, then the defect of `CXW` is at least that of `CAW`. -/
private theorem defect_le_of_ray {C A X W : P} (hCA : C ≠ A) (hX : X ∈ metricHalfLine C A)
    (hle : dist C A ≤ dist C X) (hW : W ∉ N.line C A) : N.defect C A W ≤ N.defect C X W := by
  by_cases hAX : A = X
  · rw [hAX]
  have hdA := dist_pos.2 hCA
  have hXC : X ≠ C := by
    intro e
    rw [e, dist_self] at hle
    linarith
  have hlineEq : N.line C X = N.line C A :=
    N.line_eq_of_mem hCA (N.left_mem_line C A) (N.metricHalfLine_subset_line hCA hX) hXC.symm
  have hAl : A ∈ N.line C X := by
    rw [hlineEq]
    exact N.right_mem_line C A
  have hlt : dist C A < dist C X := by
    refine lt_of_le_of_ne hle (fun e => hAX ?_)
    exact (N.existsUnique_mem_metricHalfLine_dist hCA dist_nonneg).unique
      ⟨N.self_mem_metricHalfLine hCA, rfl⟩ ⟨hX, e.symm⟩
  have hd := N.dist_of_mem_metricHalfLine hCA hX
  have hlt2 : dist A X < dist C X := by
    rw [hd, abs_of_nonpos (by linarith)]
    linarith
  have hbt : IsBetween C A X := N.isBetween_of_mem_line hXC.symm hAl hCA.symm hAX hlt hlt2
  exact N.defect_le_of_isBetween hbt (by rw [hlineEq]; exact hW)

/-- **Exercise 11.15, (f) ⇒ Z.** If the neutral plane has a rectangle, then all its triangles have zero
defect. -/
@[kb "petrunin2025" "Exercise 11.15, p. 87"]
theorem allZeroDefect_of_hasRectangle (h : N.HasRectangle) : N.AllZeroDefect := by
  apply N.allZeroDefect_of_right
  intro A B C hT hC
  have hAC : A ≠ C := hT.2.2.symm
  have hBC : B ≠ C := hT.2.1
  obtain ⟨X, Y, W, hRect, hXr, hWr, hX, hW⟩ := N.exists_rectangle_at h hAC hBC hC
  have hdef0 := hRect.defect_eq_zero
  obtain ⟨r1, r2, r3, r4, r5, r6, a1, a2, a3, a4⟩ := hRect
  have hXC : X ≠ C := r1.symm
  have hWC : W ≠ C := r3.symm
  have hWA : N.uangle W C A = π / 2 := by
    rw [← N.uangle_ray_right hWC hAC hXr hXC]
    exact a4
  have hWnot : W ∉ N.line C A := N.not_mem_line_of_perp hWC hAC hWA
  have hAnot : A ∉ N.line C B := N.not_mem_line_of_perp hAC hBC hC
  have s1 := N.defect_le_of_ray hAC.symm hXr hX hWnot
  have s2 := N.defect_le_of_ray hBC.symm hWr hW hAnot
  have hAW : A ≠ W := fun e => hWnot (e ▸ N.right_mem_line C A)
  have e1 := N.defect_perm1 (A := C) (B := A) (C := W) ⟨hAC.symm, hAW, hWC⟩
  have d0 := N.defect_nonneg (A := C) (B := B) (C := A) ⟨hBC.symm, hT.1.symm, hAC⟩
  have e2 := N.defect_perm2 hT
  have e3 := N.defect_perm1 (A := C) (B := A) (C := B) ⟨hAC.symm, hT.1, hBC⟩
  linarith

/-- **Z ⇒ (e).** -/
theorem zeroDefectTriangle_of_allZeroDefect (h : N.AllZeroDefect) : N.ZeroDefectTriangle := by
  obtain ⟨A, B, C, hT, hnd⟩ := N.exists_nondegenerate
  exact ⟨A, B, C, hT, hnd, h A B C hT⟩

/-! ### Legendre's halving and parallels -/

/-- Halving: if `R` lies between `P` and `R'` with `RR' = RQ`, then `|∡PR'Q| ≤ |∡PRQ| / 2`. -/
theorem uangle_le_half {P₀ Q R R' : P} (hR : IsBetween P₀ R R') (hRR' : dist R R' = dist R Q)
    (hQ : Q ∉ N.line P₀ R) : N.uangle P₀ R' Q ≤ N.uangle P₀ R Q / 2 := by
  have hP0R : P₀ ≠ R := hR.1.symm
  have hRR'ne : R ≠ R' := hR.2.1
  have hR'in : R' ∈ N.line P₀ R := N.metricHalfLine_subset_line hP0R (N.isBetween_rays hR).2
  have hline : N.line P₀ R' = N.line P₀ R :=
    N.line_eq_of_mem hP0R (N.left_mem_line _ _) hR'in hR.ne
  have hQ' : Q ∉ N.line P₀ R' := by
    rw [hline]
    exact hQ
  have hRQ : R ≠ Q := fun e => hQ (e ▸ N.right_mem_line _ _)
  have hR'Q : R' ≠ Q := fun e => hQ (e ▸ hR'in)
  have hsupp := (N.uangle_add_uangle_of_isBetween hR hQ').1
  have hT : IsTriangle Q R R' := ⟨hRQ.symm, hRR'ne, hR'Q⟩
  have hsum := N.uangle_sum_le_pi hT
  have hiso := N.uangle_eq_of_dist_eq (A := R') (B := Q) (C := R) ⟨hR'Q, hRQ.symm, hRR'ne⟩ hRR'
  have hcomm := N.uangle_comm (A := Q) (O := R') (B := R) hR'Q.symm hRR'ne
  have hray := N.uangle_ray_left (A := R) (A' := P₀) (O := R') (B := Q) hRR'ne
    (N.isBetween_rays hR.symm).2 hR.ne hR'Q.symm
  linarith

/-- The angles `∡PRQ` tend to `0` as `R` runs along a half-line of `ℓ` from `P`: for every `ε > 0` there is
`R ∈ [P R₀)`, `R ≠ P`, with `|∡PRQ| < ε` (any `Q ∉ (PR₀)`). -/
theorem exists_uangle_lt {P₀ Q R₀ : P} (hR₀ : R₀ ≠ P₀) (hQ : Q ∉ N.line P₀ R₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ R, R ∈ metricHalfLine P₀ R₀ ∧ R ≠ P₀ ∧ N.uangle P₀ R Q < ε := by
  have hne : P₀ ≠ R₀ := hR₀.symm
  have hpos : ∀ s : ℝ, 0 < s → N.linePt P₀ R₀ s ≠ P₀ := by
    intro s hs e
    have := N.dist_left_linePt hne s
    rw [e, dist_self, abs_of_pos hs] at this
    linarith
  have key : ∀ n : ℕ, ∃ s : ℝ, 0 < s ∧ N.uangle P₀ (N.linePt P₀ R₀ s) Q ≤ π * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_pos, by simpa using N.uangle_le_pi _ _ _⟩
    | succ n ih =>
      obtain ⟨s, hs, hle⟩ := ih
      have hRL : N.linePt P₀ R₀ s ∈ N.line P₀ R₀ := N.linePt_mem_line _ _ _
      have hRQ : N.linePt P₀ R₀ s ≠ Q := fun e => hQ (e ▸ hRL)
      have hd : 0 < dist (N.linePt P₀ R₀ s) Q := dist_pos.2 hRQ
      refine ⟨s + dist (N.linePt P₀ R₀ s) Q, by linarith, ?_⟩
      have d1 : dist (N.linePt P₀ R₀ s) (N.linePt P₀ R₀ (s + dist (N.linePt P₀ R₀ s) Q))
          = dist (N.linePt P₀ R₀ s) Q := by
        rw [N.dist_linePt hne, abs_of_nonpos (by linarith)]
        ring
      have d2 := N.dist_left_linePt hne s
      have d3 := N.dist_left_linePt hne (s + dist (N.linePt P₀ R₀ s) Q)
      rw [abs_of_pos hs] at d2
      rw [abs_of_pos (by linarith)] at d3
      have hbt : IsBetween P₀ (N.linePt P₀ R₀ s) (N.linePt P₀ R₀ (s + dist (N.linePt P₀ R₀ s) Q)) := by
        refine ⟨hpos s hs, ?_, ?_, ?_⟩
        · intro e
          rw [← e, dist_self] at d1
          linarith
        · linarith
        · exact ⟨N.line P₀ R₀, N.isLine_line hne, N.left_mem_line _ _, hRL, N.linePt_mem_line _ _ _⟩
      have hQ' : Q ∉ N.line P₀ (N.linePt P₀ R₀ s) := by
        rw [N.line_eq_of_mem hne (N.left_mem_line _ _) hRL (hpos s hs).symm]
        exact hQ
      have hh := N.uangle_le_half hbt d1 hQ'
      rw [pow_succ]
      nlinarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε Real.pi_pos) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨s, hs, hle⟩ := key n
  refine ⟨N.linePt P₀ R₀ s, ?_, hpos s hs, ?_⟩
  · rw [N.metricHalfLine_eq_linePt hne]
    exact ⟨s, le_of_lt hs, rfl⟩
  · rw [lt_div_iff₀ Real.pi_pos] at hn
    nlinarith

/-- If `∡A` and `∡C` have the same nonzero sign, `|∡A| < |∡C| < π`, then `∡C - ∡A` has that sign too. -/
private theorem sign_sub_of_lt {a c : Real.Angle} (h : a.sign = c.sign) (h0 : c.sign ≠ 0)
    (hlt : |a.toReal| < |c.toReal|) (hc : |c.toReal| < π) : (c - a).sign = c.sign := by
  have e : c - a = ((c.toReal - a.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  have hapi := Real.Angle.abs_toReal_le_pi a
  rcases lt_trichotomy c.toReal 0 with hy | hy | hy
  · have hcs : c.sign = -1 := Real.Angle.toReal_neg_iff_sign_neg.1 hy
    have hx : a.toReal < 0 := by
      rcases lt_trichotomy a.toReal 0 with hx | hx | hx
      · exact hx
      · exfalso
        apply h0
        rw [← h, (Real.Angle.toReal_eq_zero_iff).1 hx, Real.Angle.sign_zero]
      · exfalso
        have := (Real.Angle.toReal_nonneg_iff_sign_nonneg).1 hx.le
        rw [h, hcs] at this
        exact absurd this (by decide)
    rw [abs_of_neg hy, abs_of_neg hx] at hlt
    rw [abs_of_neg hy] at hc
    have hr : (c - a).toReal = c.toReal - a.toReal := by
      rw [e, Real.Angle.toReal_coe_eq_self_iff]
      constructor <;> linarith
    rw [hcs]
    exact Real.Angle.toReal_neg_iff_sign_neg.1 (by rw [hr]; linarith)
  · exfalso
    apply h0
    rw [(Real.Angle.toReal_eq_zero_iff).1 hy, Real.Angle.sign_zero]
  · have hcs : 0 ≤ c.sign := (Real.Angle.toReal_nonneg_iff_sign_nonneg).1 hy.le
    have hx : 0 < a.toReal := by
      rcases lt_trichotomy a.toReal 0 with hx | hx | hx
      · exfalso
        have := Real.Angle.toReal_neg_iff_sign_neg.1 hx
        rw [h] at this
        rw [this] at hcs
        exact absurd hcs (by decide)
      · exfalso
        apply h0
        rw [← h, (Real.Angle.toReal_eq_zero_iff).1 hx, Real.Angle.sign_zero]
      · exact hx
    rw [abs_of_pos hy, abs_of_pos hx] at hlt
    rw [abs_of_pos hy] at hc
    have hr : (c - a).toReal = c.toReal - a.toReal := by
      rw [e, Real.Angle.toReal_coe_eq_self_iff]
      constructor <;> linarith [Real.pi_pos]
    have hne : c - a ≠ (π : Real.Angle) := by
      intro hh
      rw [hh, Real.Angle.toReal_pi] at hr
      linarith
    have h1 := Real.Angle.sign_toReal hne
    rw [hr, sign_pos (by linarith)] at h1
    have h2 : c.sign = 1 := by
      have h3 := Real.Angle.sign_toReal (θ := c) (by
        intro hh
        have : c.toReal = π := by rw [hh, Real.Angle.toReal_pi]
        linarith)
      rw [sign_pos hy] at h3
      exact h3.symm
    rw [h2, ← h1]

include N in
private theorem nondeg_FQR {ℓ : Set P} (hℓ : IsLine ℓ) {Q F R : P} (hQ : Q ∉ ℓ) (hF : F ∈ ℓ) (hR : R ∈ ℓ)
    (hRF : R ≠ F) : IsTriangle F Q R ∧ ¬ IsTriangle.Degenerate F Q R := by
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  have hRQ : R ≠ Q := fun e => hQ (e ▸ hR)
  refine ⟨⟨hFQ, hRQ.symm, hRF⟩, ?_⟩
  have e : ℓ = N.line F R := N.eq_line hℓ hF hR hRF.symm
  have : ¬ IsTriangle.Degenerate F R Q := by
    rw [N.degenerate_iff_mem_line hRF.symm, ← e]
    exact hQ
  exact nondeg_swap' this

private theorem signType_pick : ∀ a b c : SignType, b = -a → a ≠ 0 → c ≠ 0 → c = a ∨ c = b := by
  decide

include N in
/-- Under `Z`, a parallel to `ℓ` through `Q` is perpendicular to the perpendicular `(QF)`: otherwise it makes
an acute angle with `[QF)` and, by Legendre's halving, a ray inside it meets `ℓ`. -/
private theorem perp_of_parallel_zero (h : N.AllZeroDefect) {ℓ : Set P} (hℓ : IsLine ℓ) {Q F : P}
    (hQ : Q ∉ ℓ) (hF : F ∈ ℓ) (hFr : ∀ Y ∈ ℓ, Y ≠ F → N.uangle Q F Y = π / 2)
    {m : Set P} (hm : IsLine.ParallelThrough ℓ m Q) {Y : P} (hY : Y ∈ m) (hYQ : Y ≠ Q) :
    N.uangle F Q Y = π / 2 := by
  obtain ⟨hmL, hQm, hdisj⟩ := hm
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  have hFm : F ∉ m := fun hh => Set.disjoint_left.1 hdisj hF hh
  have offline : ∀ Y ∈ m, Y ≠ Q → Y ∉ N.line Q F := by
    intro Y hY hYQ hYl
    have e1 : m = N.line Q Y := N.eq_line hmL hQm hY hYQ.symm
    have e2 : N.line Q Y = N.line Q F :=
      N.line_eq_of_mem hFQ.symm (N.left_mem_line Q F) hYl hYQ.symm
    apply hFm
    rw [e1, e2]
    exact N.right_mem_line Q F
  by_contra hne
  have acute : ∃ Y' ∈ m, Y' ≠ Q ∧ N.uangle F Q Y' < π / 2 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨Y, hY, hYQ, hlt⟩
    · have hb : IsBetween Y Q (N.pointRefl Q Y) := by
        rw [N.pointRefl_apply]
        exact N.isBetween_pointReflFun hYQ
      have e1 : m = N.line Q Y := N.eq_line hmL hQm hY hYQ.symm
      have hY'm : N.pointRefl Q Y ∈ m := by
        have := N.metricHalfLine_subset_line hYQ (N.isBetween_rays hb).2
        rw [e1, N.line_comm]
        exact this
      have hF' : F ∉ N.line Y (N.pointRefl Q Y) := by
        rw [← N.eq_line hmL hY hY'm hb.ne]
        exact hFm
      have hs := (N.uangle_add_uangle_of_isBetween hb hF').1
      have hcomm := N.uangle_comm hYQ hFQ
      exact ⟨_, hY'm, hb.2.1.symm, by linarith⟩
  obtain ⟨Y, hY, hYQ, hα⟩ := acute
  have hYoff := offline Y hY hYQ
  have hmeq : m = N.line Q Y := N.eq_line hmL hQm hY hYQ.symm
  have hYF : Y ≠ F := fun e => hFm (e ▸ hY)
  obtain ⟨R₁, hR₁, hR₁F⟩ := exists_ne_mem hℓ hF
  have hb2 : IsBetween R₁ F (N.pointRefl F R₁) := by
    rw [N.pointRefl_apply]
    exact N.isBetween_pointReflFun hR₁F
  have hR₂ℓ : N.pointRefl F R₁ ∈ ℓ := by
    have := N.metricHalfLine_subset_line hR₁F (N.isBetween_rays hb2).2
    rw [N.eq_line hℓ hR₁ hF hR₁F]
    exact this
  have hR₂F : N.pointRefl F R₁ ≠ F := hb2.2.1.symm
  have nd1 : ∀ R ∈ ℓ, R ≠ F → ¬ IsTriangle.Degenerate R F Q := fun R hR hRF =>
    N.not_degenerate_of_uangle_eq_pi_div_two hRF hFQ.symm
      ((N.uangle_comm hRF hFQ.symm).trans (hFr R hR hRF))
  have s1 : (N.angle R₁ F Q).sign ≠ 0 :=
    N.sign_angle_ne_zero ⟨hR₁F, hFQ, fun e => hQ (e ▸ hR₁)⟩ (nd1 R₁ hR₁ hR₁F)
  have s2 : (N.angle (N.pointRefl F R₁) F Q).sign = -(N.angle R₁ F Q).sign :=
    N.sign_angle_of_angle_eq_pi hR₁F hR₂F hFQ.symm ((N.angle_eq_pi_iff hR₁F hR₂F).2 hb2)
  have hndFQY : ¬ IsTriangle.Degenerate F Q Y := by
    rw [N.degenerate_iff_mem_line hFQ, N.line_comm]
    exact hYoff
  have sY : (N.angle F Q Y).sign ≠ 0 := N.sign_angle_ne_zero ⟨hFQ, hYQ.symm, hYF⟩ hndFQY
  obtain ⟨R₀, hR₀, hR₀F, hsg⟩ : ∃ R₀ ∈ ℓ, R₀ ≠ F ∧ (N.angle R₀ F Q).sign = (N.angle F Q Y).sign := by
    rcases signType_pick _ _ _ s2 s1 sY with e | e
    · exact ⟨R₁, hR₁, hR₁F, e.symm⟩
    · exact ⟨_, hR₂ℓ, hR₂F, e.symm⟩
  have hQline : Q ∉ N.line F R₀ := by
    rw [← N.eq_line hℓ hF hR₀ hR₀F.symm]
    exact hQ
  obtain ⟨R, hRray, hRF, hRε⟩ := N.exists_uangle_lt hR₀F hQline (ε := π / 2 - N.uangle F Q Y)
    (by linarith)
  have hRℓ : R ∈ ℓ := by
    have := N.metricHalfLine_subset_line hR₀F.symm hRray
    rwa [← N.eq_line hℓ hF hR₀ hR₀F.symm] at this
  obtain ⟨hT, hnd⟩ := N.nondeg_FQR hℓ hQ hF hRℓ hRF
  have hRQ : R ≠ Q := hT.2.1.symm
  have hsgn := (N.sign_angle_triangle (A := R) (B := F) (C := Q) ⟨hRF, hFQ, hRQ.symm⟩ (nd1 R hRℓ hRF)).1
  have hsR : (N.angle R F Q).sign = (N.angle R₀ F Q).sign := by
    rw [N.angle_ray_left hR₀F hRray hRF hFQ.symm]
  have hs1 : (N.angle F Q R).sign = (N.angle F Q Y).sign := by
    rw [← hsgn, hsR, hsg]
  have hdef := h F Q R hT
  unfold NeutralPlane.defect at hdef
  have q1 : N.uangle R F Q = π / 2 := (N.uangle_comm hRF hFQ.symm).trans (hFr R hRℓ hRF)
  have q2 : N.uangle Q R F = N.uangle F R Q := N.uangle_comm hRQ.symm hRF.symm
  have q3 := N.uangle_nonneg F R Q
  have hlt' : |(N.angle F Q Y).toReal| < |(N.angle F Q R).toReal| := by
    rw [← N.uangle_def, ← N.uangle_def]
    linarith
  have hc' : |(N.angle F Q R).toReal| < π := by
    rw [← N.uangle_def]
    linarith [Real.pi_pos]
  have hadd := N.axiomIIIb Q F Y R hFQ hYQ hRQ
  have hYQR : N.angle Y Q R = N.angle F Q R - N.angle F Q Y := by
    rw [← hadd]
    abel
  have hs2 : (N.angle Y Q R).sign = (N.angle F Q R).sign := by
    rw [hYQR]
    refine sign_sub_of_lt (by rw [hs1]) ?_ hlt' hc'
    rw [hs1]
    exact sY
  have hs1' : (N.angle F Q Y).sign = (N.angle F Q R).sign := hs1.symm
  obtain ⟨Z, hZray, hZb⟩ := N.crossbar hT hnd hYQ hs1.symm hs2
  have hZm : Z ∈ m := by
    rw [hmeq]
    exact N.metricHalfLine_subset_line hYQ.symm hZray
  have hZℓ : Z ∈ ℓ := by
    rw [N.eq_line hℓ hF hRℓ hRF.symm]
    exact N.mem_line_of_isBetween hZb
  exact Set.disjoint_left.1 hdisj hZℓ hZm

/-- **Z ⇒ uniqueness of parallels** (Playfair): through a point off a line there is at most one parallel. -/
theorem parallel_unique_of_allZeroDefect (h : N.AllZeroDefect) {ℓ : Set P} (hℓ : IsLine ℓ) {Q : P}
    (hQ : Q ∉ ℓ) {m m' : Set P} (hm : IsLine.ParallelThrough ℓ m Q) (hm' : IsLine.ParallelThrough ℓ m' Q) :
    m = m' := by
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hℓ hQ
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  obtain ⟨Y₁, hY₁, hY₁Q⟩ := exists_ne_mem hm.1 hm.2.1
  obtain ⟨Y₂, hY₂, hY₂Q⟩ := exists_ne_mem hm'.1 hm'.2.1
  have p1 := N.perp_of_parallel_zero h hℓ hQ hF hFr hm hY₁ hY₁Q
  have p2 := N.perp_of_parallel_zero h hℓ hQ hF hFr hm' hY₂ hY₂Q
  have hmem : Y₂ ∈ N.line Q Y₁ :=
    N.mem_line_of_perp (N.isLine_line hFQ) (N.left_mem_line F Q) (N.right_mem_line F Q) hFQ hY₁Q hY₂Q p1 p2
  have e1 : m = N.line Q Y₁ := N.eq_line hm.1 hm.2.1 hY₁ hY₁Q.symm
  have e2 : m' = N.line Q Y₂ := N.eq_line hm'.1 hm'.2.1 hY₂ hY₂Q.symm
  rw [e1, e2]
  exact (N.line_eq_of_mem hY₁Q.symm (N.left_mem_line Q Y₁) hmem hY₂Q.symm).symm

include N in
/-- Through a point off a line, the perpendicular to the perpendicular is parallel. -/
private theorem exists_parallel_perp {ℓ : Set P} (hℓ : IsLine ℓ) {Q F : P} (hQ : Q ∉ ℓ) (hF : F ∈ ℓ)
    (hFr : ∀ Y ∈ ℓ, Y ≠ F → N.uangle Q F Y = π / 2) :
    ∃ m, IsLine.ParallelThrough ℓ m Q ∧ ∀ Y ∈ m, Y ≠ Q → N.uangle F Q Y = π / 2 := by
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  obtain ⟨Y, hY, hYF⟩ := exists_ne_mem hℓ hF
  obtain ⟨X, hXd, hXa⟩ := N.exists_angle_eq_pi_div_two hFQ one_pos
  have hXQ : X ≠ Q := by
    intro e
    rw [e, dist_self] at hXd
    exact absurd hXd (by norm_num)
  have hXr : N.uangle F Q X = π / 2 :=
    N.uangle_of_angle_eq_coe (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hXa
  have hXr' : N.uangle X Q F = π / 2 := (N.uangle_comm hXQ hFQ).trans hXr
  have hYr : N.uangle Y F Q = π / 2 := (N.uangle_comm hYF hFQ.symm).trans (hFr Y hY hYF)
  have hd := N.disjoint_of_perp_perp hFQ.symm hXQ hYF hXr' hYr
  have e : ℓ = N.line F Y := N.eq_line hℓ hF hY hYF.symm
  refine ⟨N.line Q X, ⟨N.isLine_line hXQ.symm, N.left_mem_line Q X, ?_⟩, ?_⟩
  · rw [e]
    exact hd.symm
  · intro Y' hY' hY'Q
    have := N.uangle_eq_pi_div_two_of_mem_line hXQ hFQ hXr' hY' hY'Q
    exact (N.uangle_comm hFQ hY'Q).trans this

include N in
/-- Through a point off a line there is a parallel (the perpendicular to the perpendicular). -/
theorem exists_parallel {ℓ : Set P} (hℓ : IsLine ℓ) {Q : P} (hQ : Q ∉ ℓ) :
    ∃ m, IsLine.ParallelThrough ℓ m Q := by
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hℓ hQ
  obtain ⟨m, hm, -⟩ := N.exists_parallel_perp hℓ hQ hF hFr
  exact ⟨m, hm⟩

/-- **Z ⇒ (a).** -/
theorem onlyOneParallel_of_allZeroDefect (h : N.AllZeroDefect) : N.OnlyOneParallel := by
  obtain ⟨A, B, C, hT, hnd⟩ := N.exists_nondegenerate
  have hC : C ∉ N.line A B := fun hh => hnd ((N.degenerate_iff_mem_line hT.1).2 hh)
  obtain ⟨m, hm⟩ := N.exists_parallel (N.isLine_line hT.1) hC
  exact ⟨N.line A B, N.isLine_line hT.1, C, hC, m, hm, fun m' hm' =>
    N.parallel_unique_of_allZeroDefect h (N.isLine_line hT.1) hC hm' hm⟩

include N in
private theorem isBetween_linePt {A B : P} (hne : A ≠ B) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IsBetween A (N.linePt A B s) (N.linePt A B t) := by
  have d1 : dist (N.linePt A B s) (N.linePt A B t) = t - s := by
    rw [N.dist_linePt hne, abs_of_nonpos (by linarith)]
    ring
  have d2 := N.dist_left_linePt hne s
  have d3 := N.dist_left_linePt hne t
  rw [abs_of_pos hs] at d2
  rw [abs_of_pos (by linarith)] at d3
  refine ⟨?_, ?_, ?_, ⟨N.line A B, N.isLine_line hne, N.left_mem_line _ _, N.linePt_mem_line _ _ _,
    N.linePt_mem_line _ _ _⟩⟩
  · intro e
    rw [e, dist_self] at d2
    linarith
  · intro e
    rw [e, dist_self] at d1
    linarith
  · linarith

include N in
private theorem uangle_of_degenerate {A O B : P} (hA : A ≠ O) (hB : B ≠ O) (h : IsTriangle.Degenerate A O B) :
    N.uangle A O B = 0 ∨ N.uangle A O B = π := by
  rcases (N.degenerate_iff_angle hA hB).1 h with h0 | h0
  · left
    rw [N.uangle_def, h0]
    simp
  · right
    rw [N.uangle_def, h0, Real.Angle.toReal_pi, abs_of_pos Real.pi_pos]

/-- **If no triangle has zero defect, Axiom h-V holds** (the remark after Theorem 11.16). -/
@[kb "petrunin2025" "Remark after Theorem 11.16, p. 88"]
theorem axiomHV_of_not_zeroDefectTriangle (h : ¬ N.ZeroDefectTriangle) : N.AxiomHV := by
  intro ℓ hℓ Q hQ
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hℓ hQ
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  obtain ⟨m0, hm0, hperp0⟩ := N.exists_parallel_perp hℓ hQ hF hFr
  obtain ⟨R₀, hR₀, hR₀F⟩ := exists_ne_mem hℓ hF
  have hne : F ≠ R₀ := hR₀F.symm
  have hℓeq : ℓ = N.line F R₀ := N.eq_line hℓ hF hR₀ hne
  have hLℓ : ∀ t, N.linePt F R₀ t ∈ ℓ := fun t => by
    rw [hℓeq]
    exact N.linePt_mem_line _ _ _
  have hLne : ∀ t : ℝ, t ≠ 0 → N.linePt F R₀ t ≠ F := by
    intro t ht e
    have := N.dist_left_linePt hne t
    rw [e, dist_self] at this
    exact ht (abs_eq_zero.1 this.symm)
  have hQL : ∀ t, N.linePt F R₀ t ≠ Q := fun t e => hQ (e ▸ hLℓ t)
  have hrt : ∀ t : ℝ, t ≠ 0 → N.uangle (N.linePt F R₀ t) F Q = π / 2 := fun t ht =>
    (N.uangle_comm (hLne t ht) hFQ.symm).trans (hFr _ (hLℓ t) (hLne t ht))
  have hQn : ∀ t : ℝ, t ≠ 0 → Q ∉ N.line F (N.linePt F R₀ t) := by
    intro t ht
    rw [← N.eq_line hℓ hF (hLℓ t) (hLne t ht).symm]
    exact hQ
  have hnd : ∀ t : ℝ, t ≠ 0 → ¬ IsTriangle.Degenerate F Q (N.linePt F R₀ t) := fun t ht =>
    (N.nondeg_FQR hℓ hQ hF (hLℓ t) (hLne t ht)).2
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ t, φ t = N.uangle F Q (N.linePt F R₀ t) := ⟨_, fun _ => rfl⟩
  have hsymm : ∀ t : ℝ, t ≠ 0 → φ (-t) = φ t := by
    intro t ht
    have hcong : TriangleCongruent F Q (N.linePt F R₀ t) F Q (N.linePt F R₀ (-t)) :=
      N.sas hFQ (hLne t ht).symm (hQL t).symm hFQ (hLne (-t) (neg_ne_zero.2 ht)).symm (hQL (-t)).symm rfl
        (by rw [N.dist_left_linePt hne, N.dist_left_linePt hne, abs_neg])
        ((hrt (-t) (neg_ne_zero.2 ht)).trans (hrt t ht).symm)
    rw [hφ, hφ]
    exact TriangleCongruent.uangle_eq N hcong hFQ (hQL t)
  have hφ0 : φ 0 = 0 := by
    rw [hφ, N.linePt_zero, N.uangle_def, N.angle_self hFQ]
    simp
  have hφpos : ∀ t : ℝ, t ≠ 0 → 0 < φ t := fun t ht => by
    rw [hφ]
    exact N.uangle_pos_of_nondeg hFQ (hQL t) (hnd t ht)
  have hmono : ∀ s t : ℝ, 0 ≤ s → s < t → φ s < φ t := by
    intro s t hs hst
    have ht : 0 < t := by linarith
    rcases hs.eq_or_lt with h0 | hs'
    · rw [← h0, hφ0]
      exact hφpos t ht.ne'
    · have hb := N.isBetween_linePt hne hs' hst
      have hsum := (N.isBetween_angle_sign_and_uangle hb (hQn t ht.ne')).2.2
      have hLsLt : N.linePt F R₀ t ≠ N.linePt F R₀ s := fun e => hst.ne' (N.linePt_injective hne e)
      have hpos := N.uangle_pos_of_nondeg (hQL s) (hQL t)
        (N.nondeg_FQR hℓ hQ (hLℓ s) (hLℓ t) hLsLt).2
      rw [hφ, hφ]
      linarith
  have hodd : ∀ t : ℝ, φ t = φ |t| := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      by_cases h0 : t = 0
      · rw [h0]
        simp
      · have := hsymm (-t) (neg_ne_zero.2 h0)
        rwa [neg_neg] at this
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = N.defect F (N.linePt F R₀ 1) Q := ⟨_, rfl⟩
  have hT1 : IsTriangle F (N.linePt F R₀ 1) Q := ⟨(hLne 1 one_ne_zero).symm, hQL 1, hFQ.symm⟩
  have hδ : 0 < δ := by
    have h0 := N.defect_nonneg hT1
    rcases (hδdef ▸ h0 : 0 ≤ δ).eq_or_lt with e | e
    · exfalso
      exact h ⟨F, N.linePt F R₀ 1, Q, hT1, nondeg_swap' (hnd 1 one_ne_zero), by rw [← hδdef]; exact e.symm⟩
    · exact e
  have hbound1 : ∀ T : ℝ, 1 ≤ T → φ T ≤ π / 2 - δ := by
    intro T hT
    have hT0 : T ≠ 0 := by positivity
    have hdefT : δ ≤ N.defect F (N.linePt F R₀ T) Q := by
      rcases hT.eq_or_lt with e | e
      · rw [hδdef, ← e]
      · rw [hδdef]
        exact N.defect_le_of_isBetween (N.isBetween_linePt hne one_pos e) (hQn T hT0)
    have hTri : IsTriangle F Q (N.linePt F R₀ T) := (N.nondeg_FQR hℓ hQ hF (hLℓ T) (hLne T hT0)).1
    have hperm := N.defect_perm1 hTri
    have q := N.uangle_nonneg Q (N.linePt F R₀ T) F
    have q2 := hrt T hT0
    unfold NeutralPlane.defect at hperm hdefT
    rw [hφ]
    linarith
  have hlt : ∀ t : ℝ, φ t < φ (|t| + 1) := by
    intro t
    rw [hodd t]
    exact hmono |t| (|t| + 1) (abs_nonneg t) (by linarith)
  have hub : ∀ t : ℝ, φ t ≤ π / 2 - δ := fun t =>
    (hlt t).le.trans (hbound1 _ (by linarith [abs_nonneg t]))
  have hbdd : BddAbove (Set.range φ) := ⟨π / 2 - δ, by
    rintro _ ⟨t, rfl⟩
    exact hub t⟩
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = sSup (Set.range φ) := ⟨_, rfl⟩
  have hφθ : ∀ t, φ t ≤ θ := fun t => hθdef ▸ le_csSup hbdd ⟨t, rfl⟩
  have hθlt : ∀ t, φ t < θ := fun t => lt_of_lt_of_le (hlt t) (hφθ _)
  have hθle : θ ≤ π / 2 - δ := hθdef ▸ csSup_le (Set.range_nonempty φ) (by
    rintro _ ⟨t, rfl⟩
    exact hub t)
  have hθpos : 0 < θ := by
    have := hθlt 0
    rwa [hφ0] at this
  obtain ⟨Y, hYQ, hYa, -⟩ := N.axiomIIIa Q F hFQ (θ : Real.Angle)
  have hYr : N.uangle F Q Y = θ :=
    N.uangle_of_angle_eq_coe hθpos.le (by linarith [Real.pi_pos]) hYa
  have hFn : F ∉ N.line Q Y := by
    intro hh
    have e : N.line Q F = N.line Q Y := N.line_eq_of_mem hYQ.symm (N.left_mem_line Q Y) hh hFQ.symm
    have hYl : Y ∈ N.line Q F := by
      rw [e]
      exact N.right_mem_line Q Y
    have hdeg : IsTriangle.Degenerate F Q Y :=
      ⟨N.line Q F, N.isLine_line hFQ.symm, N.right_mem_line Q F, N.left_mem_line Q F, hYl⟩
    rcases N.uangle_of_degenerate hFQ hYQ hdeg with h0 | h0
    · linarith
    · linarith [Real.pi_pos]
  refine ⟨m0, N.line Q Y, ?_, hm0, ⟨N.isLine_line hYQ.symm, N.left_mem_line Q Y, ?_⟩⟩
  · intro e
    have := hperp0 Y (by rw [e]; exact N.right_mem_line Q Y) hYQ
    linarith
  · rw [Set.disjoint_left]
    intro Z hZ hZm
    obtain ⟨t, rfl⟩ : ∃ t, N.linePt F R₀ t = Z := N.exists_linePt_eq hne (by rw [← hℓeq]; exact hZ)
    have hZQ := hQL t
    have h1 := hθlt t
    rw [hφ] at h1
    rcases N.mem_metricHalfLine_or_isBetween hYQ.symm hZm with hray | hb
    · have := N.uangle_ray_right hFQ hYQ hray hZQ
      linarith
    · have hFn' : F ∉ N.line (N.linePt F R₀ t) Y := by
        rw [N.line_eq_of_mem hYQ.symm hZm (N.right_mem_line Q Y) hb.ne]
        exact hFn
      have hsum := (N.uangle_add_uangle_of_isBetween hb hFn').1
      have hcomm := N.uangle_comm hZQ hFQ
      linarith

/-- **(a) ⇒ (e).** -/
theorem zeroDefectTriangle_of_onlyOneParallel (h : N.OnlyOneParallel) : N.ZeroDefectTriangle := by
  by_contra hn
  obtain ⟨ℓ, hℓ, Q, hQ, m, hm, huniq⟩ := h
  obtain ⟨m1, m2, hne, h1, h2⟩ := N.axiomHV_of_not_zeroDefectTriangle hn ℓ hℓ Q hQ
  exact hne ((huniq m1 h1).trans (huniq m2 h2).symm)

/-! ### Circumscribed triangles -/

/-- A point equidistant from `A ≠ B` lies on the perpendicular bisector: if `OA = OB`, `M` the midpoint, `L` a
line through `M` with a right angle `∠AMX` for some `X ∈ L`, then `O ∈ L`. -/
theorem mem_perpBisector {A B M X O : P} (hM : IsBetween A M B) (hMM : dist A M = dist M B) (hX : X ≠ M)
    (hr : N.uangle A M X = π / 2) (hO : dist O A = dist O B) : O ∈ N.line M X := by
  by_cases hOM : O = M
  · rw [hOM]
    exact N.left_mem_line M X
  have h1 := (N.dist_eq_iff_uangle_eq_pi_div_two hM hMM hOM).1 hO
  exact N.mem_line_of_perp (N.isLine_line hM.ne) (N.left_mem_line A B)
    (N.mem_line_of_isBetween hM) hM.1.symm hX hOM hr h1

/-- If all triangles can be circumscribed, a parallel to `ℓ` through `Q` is perpendicular to `(QF)`: otherwise
the circumcentre of `Q`, its reflection `X` across `ℓ` and the reflection of `X` across the parallel lies on
both `ℓ` and the parallel. -/
private theorem perp_of_parallel_circ (h : N.AllTrianglesCircumscribable) {ℓ : Set P} (hℓ : IsLine ℓ)
    {Q F : P} (hQ : Q ∉ ℓ) (hF : F ∈ ℓ) (hFr : ∀ Y ∈ ℓ, Y ≠ F → N.uangle Q F Y = π / 2)
    {m : Set P} (hm : IsLine.ParallelThrough ℓ m Q) {Y : P} (hY : Y ∈ m) (hYQ : Y ≠ Q) :
    N.uangle F Q Y = π / 2 := by
  obtain ⟨hmL, hQm, hdisj⟩ := hm
  have hFQ : F ≠ Q := fun e => hQ (e ▸ hF)
  have hFm : F ∉ m := fun hh => Set.disjoint_left.1 hdisj hF hh
  obtain ⟨hb, hbd⟩ := N.foot_isBetween_lineRefl hℓ hQ hF hFr
  set X := N.lineRefl hℓ Q with hXdef
  have hQX : Q ≠ X := hb.ne
  have hXm : X ∉ m := by
    intro hXm
    have e : m = N.line Q X := N.eq_line hmL hQm hXm hQX
    apply hFm
    rw [e]
    exact N.mem_line_of_isBetween hb
  obtain ⟨F', hF'm, hF'r⟩ := N.exists_foot hmL hXm
  by_cases hF'Q : F' = Q
  · rw [hF'Q] at hF'r
    have := hF'r Y hY hYQ
    exact N.uangle_eq_pi_div_two_of_mem_line hQX.symm hYQ this (N.mem_line_of_isBetween hb) hFQ
  · exfalso
    have hF'Q' : Q ≠ F' := fun e => hF'Q e.symm
    obtain ⟨hb', hbd'⟩ := N.foot_isBetween_lineRefl hmL hXm hF'm hF'r
    set X' := N.lineRefl hmL X with hX'def
    have hXX' : X ≠ X' := hb'.ne
    have hX'Q : X' ≠ Q := by
      intro e
      have h1 : N.lineRefl hmL Q = Q := N.lineRefl_fix hmL hQm
      have h2 : N.lineRefl hmL X = N.lineRefl hmL Q := by rw [h1]; exact e
      exact hQX ((N.lineRefl hmL).injective h2).symm
    have hT : IsTriangle Q X X' := ⟨hQX, hXX', hX'Q⟩
    have hnd : ¬ IsTriangle.Degenerate Q X X' := by
      intro hdeg
      have hX'l : X' ∈ N.line Q X := (N.degenerate_iff_mem_line hQX).1 hdeg
      have e1 : N.line X X' = N.line Q X :=
        N.line_eq_of_mem hQX (N.right_mem_line Q X) hX'l hXX'
      have hF'l : F' ∈ N.line Q X := by
        rw [← e1]
        exact N.mem_line_of_isBetween hb'
      have hne : m ≠ N.line Q X := by
        intro e
        exact hXm (e ▸ N.right_mem_line Q X)
      exact hF'Q (N.eq_of_mem_line_of_mem_line hmL (N.isLine_line hQX) hne hF'm hF'l hQm
        (N.left_mem_line Q X)).symm.symm
    obtain ⟨O, r, hOQ, hOX, hOX'⟩ := h Q X X' hT hnd
    obtain ⟨Y₀, hY₀, hY₀F⟩ := exists_ne_mem hℓ hF
    have hOℓ : O ∈ ℓ := by
      have := N.mem_perpBisector hb (by linarith [dist_comm F Q, dist_comm F X]) hY₀F
        (hFr Y₀ hY₀ hY₀F) (hOQ.trans hOX.symm)
      rw [N.eq_line hℓ hF hY₀ hY₀F.symm]
      exact this
    have hOm : O ∈ m := by
      have := N.mem_perpBisector hb' (by linarith [dist_comm F' X, dist_comm F' X']) hF'Q'
        (hF'r Q hQm hF'Q') (hOX.trans hOX'.symm)
      rw [N.eq_line hmL hF'm hQm hF'Q]
      exact this
    exact Set.disjoint_left.1 hdisj hOℓ hOm

/-- **(b) ⇒ (a).** If every nondegenerate triangle can be circumscribed, through a point off a line there is
only one parallel. -/
theorem onlyOneParallel_of_allTrianglesCircumscribable (h : N.AllTrianglesCircumscribable) :
    N.OnlyOneParallel := by
  obtain ⟨A, B, C, hT, hnd⟩ := N.exists_nondegenerate
  have hC : C ∉ N.line A B := fun hh => hnd ((N.degenerate_iff_mem_line hT.1).2 hh)
  have hℓ := N.isLine_line hT.1
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hℓ hC
  have hFQ : F ≠ C := fun e => hC (e ▸ hF)
  obtain ⟨m0, hm0, hperp0⟩ := N.exists_parallel_perp hℓ hC hF hFr
  refine ⟨N.line A B, hℓ, C, hC, m0, hm0, fun m' hm' => ?_⟩
  obtain ⟨Y₁, hY₁, hY₁Q⟩ := exists_ne_mem hm0.1 hm0.2.1
  obtain ⟨Y₂, hY₂, hY₂Q⟩ := exists_ne_mem hm'.1 hm'.2.1
  have p1 := hperp0 Y₁ hY₁ hY₁Q
  have p2 := N.perp_of_parallel_circ h hℓ hC hF hFr hm' hY₂ hY₂Q
  have hmem : Y₂ ∈ N.line C Y₁ :=
    N.mem_line_of_perp (N.isLine_line hFQ) (N.left_mem_line F C) (N.right_mem_line F C) hFQ hY₁Q hY₂Q p1 p2
  have e1 : m0 = N.line C Y₁ := N.eq_line hm0.1 hm0.2.1 hY₁ hY₁Q.symm
  have e2 : m' = N.line C Y₂ := N.eq_line hm'.1 hm'.2.1 hY₂ hY₂Q.symm
  rw [e1, e2]
  exact N.line_eq_of_mem hY₁Q.symm (N.left_mem_line C Y₁) hmem hY₂Q.symm

include N in
private theorem exists_perp_dir {A M : P} (hAM : A ≠ M) : ∃ X, X ≠ M ∧ N.uangle A M X = π / 2 := by
  obtain ⟨X, hXd, hXa⟩ := N.exists_angle_eq_pi_div_two hAM one_pos
  have hXM : X ≠ M := by
    intro e
    rw [e, dist_self] at hXd
    exact absurd hXd (by norm_num)
  exact ⟨X, hXM, N.uangle_of_angle_eq_coe (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hXa⟩

include N in
private theorem dist_eq_of_mem_perp {A B M X O : P} (hM : IsBetween A M B) (hMM : dist A M = dist M B)
    (hX : X ≠ M) (hr : N.uangle A M X = π / 2) (hO : O ∈ N.line M X) : dist O A = dist O B := by
  by_cases hOM : O = M
  · rw [hOM]
    linarith [dist_comm M A, dist_comm M B]
  · have hAM : A ≠ M := hM.1.symm
    have h1 := N.uangle_eq_pi_div_two_of_mem_line hX hAM ((N.uangle_comm hAM hX).symm.trans hr) hO hOM
    exact (N.dist_eq_iff_uangle_eq_pi_div_two hM hMM hOM).2 ((N.uangle_comm hAM hOM).trans h1)

/-- **Z ⇒ (b).** The perpendicular bisectors of two sides meet. -/
theorem allTrianglesCircumscribable_of_allZeroDefect (h : N.AllZeroDefect) :
    N.AllTrianglesCircumscribable := by
  intro A B C hT hnd
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨M1, hM1, hM1d⟩ := N.exists_midpoint hAB
  obtain ⟨M2, hM2, hM2d⟩ := N.exists_midpoint hCA.symm
  obtain ⟨X1, hX1, hr1⟩ := N.exists_perp_dir hM1.1.symm
  obtain ⟨X2, hX2, hr2⟩ := N.exists_perp_dir hM2.1.symm
  have hAM1 : A ≠ M1 := hM1.1.symm
  have hAM2 : A ≠ M2 := hM2.1.symm
  have key : ∃ O, O ∈ N.line M1 X1 ∧ O ∈ N.line M2 X2 := by
    by_contra hno
    have hm1 := N.isLine_line hX1.symm
    have hdisj : Disjoint (N.line M1 X1) (N.line M2 X2) :=
      Set.disjoint_left.2 fun O h1 h2 => hno ⟨O, h1, h2⟩
    have hM2n : M2 ∉ N.line M1 X1 := fun hh => Set.disjoint_left.1 hdisj hh (N.left_mem_line M2 X2)
    obtain ⟨F, hF, hFr⟩ := N.exists_foot hm1 hM2n
    obtain ⟨p, hp, hpperp⟩ := N.exists_parallel_perp hm1 hM2n hF hFr
    have hm2par : IsLine.ParallelThrough (N.line M1 X1) (N.line M2 X2) M2 :=
      ⟨N.isLine_line hX2.symm, N.left_mem_line _ _, hdisj⟩
    have hpm : N.line M2 X2 = p := N.parallel_unique_of_allZeroDefect h hm1 hM2n hm2par hp
    have hFM2 : F ≠ M2 := fun e => hM2n (e ▸ hF)
    have hFX2 : N.uangle F M2 X2 = π / 2 :=
      hpperp X2 (by rw [← hpm]; exact N.right_mem_line M2 X2) hX2
    have hFl : F ∈ N.line M2 A :=
      N.mem_line_of_perp (N.isLine_line hX2.symm) (N.right_mem_line M2 X2) (N.left_mem_line M2 X2) hX2
        hAM2 hFM2 ((N.uangle_comm hX2 hAM2).trans hr2) ((N.uangle_comm hX2 hFM2).trans hFX2)
    have hAC : A ≠ C := hCA.symm
    have e : N.line A M2 = N.line A C :=
      N.line_eq_of_mem hAC (N.left_mem_line A C) (N.mem_line_of_isBetween hM2) hAM2
    have hFAC : F ∈ N.line A C := by
      rw [← e, N.line_comm]
      exact hFl
    have hAm1 : A ∉ N.line M1 X1 := N.not_mem_line_of_perp hAM1 hX1 hr1
    have hAF : A ≠ F := fun e => hAm1 (e ▸ hF)
    have foot1 : ∀ Y ∈ N.line M1 X1, Y ≠ M1 → N.uangle A M1 Y = π / 2 := by
      intro Y hY hYM
      have := N.uangle_eq_pi_div_two_of_mem_line (A := X1) (O := M1) (B := A) (A' := Y) hX1 hAM1
        ((N.uangle_comm hX1 hAM1).trans hr1) hY hYM
      exact (N.uangle_comm hAM1 hYM).trans this
    have e3 : N.line M2 F = N.line M2 A :=
      N.line_eq_of_mem hAM2.symm (N.left_mem_line M2 A) hFl hFM2.symm
    have hAl : A ∈ N.line F M2 := by
      rw [N.line_comm, e3]
      exact N.right_mem_line M2 A
    have foot2 : ∀ Y ∈ N.line M1 X1, Y ≠ F → N.uangle A F Y = π / 2 := by
      intro Y hY hYF
      exact N.uangle_eq_pi_div_two_of_mem_line (A := M2) (O := F) (B := Y) (A' := A) hFM2.symm hYF
        (hFr Y hY hYF) hAl hAF
    have hFM1 : F = M1 := N.foot_unique hm1 hAm1 hF (N.left_mem_line M1 X1) foot2 foot1
    have hM1AC : M1 ∈ N.line A C := hFM1 ▸ hFAC
    have e4 : N.line A M1 = N.line A C := N.line_eq_of_mem hAC (N.left_mem_line A C) hM1AC hAM1
    have hBl : B ∈ N.line A M1 := N.metricHalfLine_subset_line hAM1 (N.isBetween_rays hM1).2
    rw [e4] at hBl
    exact nondeg_swap' hnd ((N.degenerate_iff_mem_line hAC).2 hBl)
  obtain ⟨O, hO1, hO2⟩ := key
  have d1 := N.dist_eq_of_mem_perp hM1 hM1d hX1 hr1 hO1
  have d2 := N.dist_eq_of_mem_perp hM2 hM2d hX2 hr2 hO2
  exact ⟨O, dist O A, rfl, d1.symm, d2.symm⟩

end NeutralPlane

end Neutral

end UndergradKB.Geometry
