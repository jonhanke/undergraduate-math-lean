import UndergradKB.Geometry.NeutralAngles
import UndergradKB.Geometry.NeutralConditions
import UndergradKB.Common.Attr

/-! # Neutral plane III: signs of angles and half-planes (Petrunin, Chapter 3)

Derived from Axioms I-IV of `NeutralPlane`. The sign of an angle (`Real.Angle.sign`: `1` for a positive angle,
`-1` for a negative one, `0` for `0` and `π`) splits the complement of a line into two half-planes
(Corollary 3.11); the continuity Axiom IIIc enters through the intermediate value theorem (Corollary 3.5).
We also prove Pasch's theorem (3.13), the crossbar property, and that the reflection across a point preserves
angles (Proposition 7.6, which the book proves without Axiom V). -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- `|∡AOB|` unfolds to `|(∡AOB).toReal|`. -/
theorem uangle_def (A O B : P) : N.uangle A O B = |(N.angle A O B).toReal| := rfl

theorem uangle_nonneg (A O B : P) : 0 ≤ N.uangle A O B := abs_nonneg _

theorem uangle_le_pi (A O B : P) : N.uangle A O B ≤ π :=
  Real.Angle.abs_toReal_le_pi _

theorem uangle_comm {A O B : P} (hA : A ≠ O) (hB : B ≠ O) : N.uangle A O B = N.uangle B O A := by
  unfold uangle
  rw [N.angle_rev hA hB, Real.Angle.abs_toReal_neg]

/-- Motions keep unsigned angles (Axiom IV). -/
theorem uangle_isometryEquiv (f : P ≃ᵢ P) {A O B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.uangle (f A) (f O) (f B) = N.uangle A O B := by
  unfold uangle
  rcases N.angle_isometryEquiv f hA hB with h | h
  · rw [h]
  · rw [h, Real.Angle.abs_toReal_neg]

/-- `|∡AOB| = π` iff `O` lies between `A` and `B`. -/
theorem uangle_eq_pi_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.uangle A O B = π ↔ IsBetween A O B := by
  rw [← N.angle_eq_pi_iff hA hB]
  unfold uangle
  constructor
  · intro h
    rcases (abs_eq Real.pi_pos.le).1 h with h | h
    · exact Real.Angle.toReal_eq_pi_iff.1 h
    · exfalso
      have := (Real.Angle.toReal_mem_Ioc (N.angle A O B)).1
      linarith
  · intro h
    rw [h, Real.Angle.toReal_pi, abs_of_pos Real.pi_pos]

/-- `|∡AOB| = 0` iff `B ∈ [OA)`. -/
theorem uangle_eq_zero_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.uangle A O B = 0 ↔ B ∈ metricHalfLine O A := by
  rw [← N.angle_eq_zero_iff hA hB]
  unfold uangle
  rw [abs_eq_zero, Real.Angle.toReal_eq_zero_iff]

/-! ### Signs of angles -/

/-- **Lemma 3.2.** If `∠AOB` is straight, then `∠AOX` and `∠BOX` have opposite signs. -/
@[kb "petrunin2025" "Lemma 3.2, p. 24"]
theorem sign_angle_of_angle_eq_pi {O A B X : P} (hA : A ≠ O) (hB : B ≠ O) (hX : X ≠ O)
    (h : N.angle A O B = π) : (N.angle B O X).sign = -(N.angle A O X).sign := by
  have h1 := N.axiomIIIb O A X B hA hX hB
  rw [h] at h1
  have e : N.angle X O B = (π : Real.Angle) - N.angle A O X := by rw [← h1]; abel
  have h2 : N.angle B O X = N.angle A O X - π := by
    rw [N.angle_rev hB hX, e]; abel
  rw [h2, Real.Angle.sign_sub_pi]

/-- Nondegeneracy is symmetric in the three points. -/
theorem not_degenerate_rotate {A B C : P} (h : ¬ IsTriangle.Degenerate A B C) :
    ¬ IsTriangle.Degenerate B C A := by
  rintro ⟨L, hL, hB, hC, hA⟩
  exact h ⟨L, hL, hA, hB, hC⟩

theorem not_degenerate_swap {A B C : P} (h : ¬ IsTriangle.Degenerate A B C) :
    ¬ IsTriangle.Degenerate B A C := by
  rintro ⟨L, hL, hB, hA, hC⟩
  exact h ⟨L, hL, hA, hB, hC⟩

theorem not_degenerate_swap_right {A B C : P} (h : ¬ IsTriangle.Degenerate A B C) :
    ¬ IsTriangle.Degenerate A C B :=
  not_degenerate_swap (not_degenerate_rotate (not_degenerate_rotate h))

/-- A point off the line `(AB)` makes a nondegenerate triple. -/
theorem nd_of_notin {A B X : P} (h : A ≠ B) (hX : X ∉ N.line A B) : ¬ IsTriangle.Degenerate A B X :=
  fun hd => hX ((N.degenerate_iff_mem_line h).1 hd)

include N in
/-- If `A` lies between `O` and `Z`, then `Z` is on the half-line `[OA)`. -/
theorem ray_of_between_outer {O A Z : P} (h : IsBetween O A Z) : Z ∈ metricHalfLine O A := by
  have hOA : O ≠ A := h.1.symm
  have hl : Z ∈ N.line O A := (N.degenerate_iff_mem_line hOA).1 h.degenerate
  rcases N.mem_metricHalfLine_or_isBetween hOA hl with h1 | h1
  · exact h1
  · exfalso
    have e1 := h.dist_add
    have e2 := h1.dist_add
    have := dist_pos.2 hOA
    linarith [dist_comm O A, dist_comm Z O, dist_comm Z A, dist_comm O Z, dist_comm A Z]

include N in
/-- If `A` lies between `O` and `Z`, then `A` is on the half-line `[OZ)`. -/
theorem ray_of_between_inner {O A Z : P} (h : IsBetween O A Z) : A ∈ metricHalfLine O Z := by
  have hOZ : O ≠ Z := h.ne
  have hl : A ∈ N.line O Z := N.mem_line_of_isBetween h
  rcases N.mem_metricHalfLine_or_isBetween hOZ hl with h1 | h1
  · exact h1
  · exfalso
    have e1 := h.dist_add
    have e2 := h1.dist_add
    have := dist_pos.2 h.1.symm
    linarith [dist_comm O A, dist_comm A O, dist_comm Z O, dist_comm A Z]

theorem linePt_ne_left {A B : P} (h : A ≠ B) {u : ℝ} (hu : u ≠ 0) : N.linePt A B u ≠ A := by
  intro e
  apply hu
  exact N.linePt_injective h (by rw [e, N.linePt_zero])

theorem not_degenerate_linePt {A B X : P} (h : A ≠ B) (hX : X ∉ N.line A B) {u : ℝ} (hu : u ≠ 0) :
    ¬ IsTriangle.Degenerate A (N.linePt A B u) X := by
  intro hd
  rw [N.degenerate_iff_mem_line (Ne.symm (N.linePt_ne_left h hu))] at hd
  rw [N.line_eq_of_mem h (N.left_mem_line A B) (N.linePt_mem_line A B u)
    (Ne.symm (N.linePt_ne_left h hu))] at hd
  exact hX hd

/-- **Corollary 3.5.** Along a continuous family of nondegenerate triangles the sign of the angle is
constant. -/
@[kb "petrunin2025" "Corollary 3.5, p. 25"]
theorem sign_angle_eq_of_continuousOn {O A B : ℝ → P} (hO : ContinuousOn O (Set.Icc 0 1))
    (hA : ContinuousOn A (Set.Icc 0 1)) (hB : ContinuousOn B (Set.Icc 0 1))
    (hAO : ∀ t ∈ Set.Icc (0 : ℝ) 1, A t ≠ O t) (hBO : ∀ t ∈ Set.Icc (0 : ℝ) 1, B t ≠ O t)
    (hnd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ¬ IsTriangle.Degenerate (A t) (O t) (B t)) :
    (N.angle (A 0) (O 0) (B 0)).sign = (N.angle (A 1) (O 1) (B 1)).sign := by
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, N.angle (A t) (O t) (B t) ≠ 0 ∧ N.angle (A t) (O t) (B t) ≠ π := by
    intro t ht
    have := hnd t ht
    rw [N.degenerate_iff_angle (hAO t ht) (hBO t ht)] at this
    exact not_or.1 this
  have hc : ContinuousOn (fun t => N.angle (A t) (O t) (B t)) (Set.Icc 0 1) := by
    intro t ht
    have h1 := N.axiomIIIc (A t) (O t) (B t) (hAO t ht) (hBO t ht) (hne t ht).2
    have h2 : ContinuousWithinAt (fun t => (A t, O t, B t)) (Set.Icc 0 1) t :=
      (hA t ht).prodMk ((hO t ht).prodMk (hB t ht))
    exact ContinuousAt.comp_continuousWithinAt (f := fun t => (A t, O t, B t)) h1 h2
  exact (Real.Angle.sign_eq_of_continuousOn (isConnected_Icc zero_le_one) hc hne
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).symm

/-- **Lemma 3.6.** Moving the vertex `Q` along `[PQ)` does not change the sign of `∠PQX`. -/
@[kb "petrunin2025" "Lemma 3.6, p. 25"]
theorem sign_angle_eq_of_mem_ray {P₀ Q Q' X : P} (hPQ : P₀ ≠ Q) (hQ' : Q' ∈ metricHalfLine P₀ Q)
    (hQ'P : Q' ≠ P₀) (hX : X ∉ N.line P₀ Q) :
    (N.angle P₀ Q' X).sign = (N.angle P₀ Q X).sign := by
  rw [N.metricHalfLine_eq_linePt hPQ] at hQ'
  obtain ⟨s, hs, hsQ⟩ := hQ'
  have hs : 0 ≤ s := hs
  have hs0 : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hQ'P
      rw [← hsQ, ← h]
      exact N.linePt_zero P₀ Q
  have hq : 0 < dist P₀ Q := dist_pos.2 hPQ
  set q := dist P₀ Q with hqdef
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (1 - t) * q + t * s := by
    intro t ht
    have : min q s ≤ (1 - t) * q + t * s := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 (min_le_left q s)),
        mul_nonneg ht.1 (sub_nonneg.2 (min_le_right q s))]
    exact lt_of_lt_of_le (lt_min hq hs0) this
  have key := N.sign_angle_eq_of_continuousOn (O := fun t => N.linePt P₀ Q ((1 - t) * q + t * s))
    (A := fun _ => P₀) (B := fun _ => X)
    ((N.continuous_linePt hPQ).comp (by fun_prop)).continuousOn continuousOn_const continuousOn_const
    (fun t ht => (N.linePt_ne_left hPQ (hpos t ht).ne').symm)
    (fun t ht h => hX (h ▸ N.linePt_mem_line P₀ Q _))
    (fun t ht => N.not_degenerate_linePt hPQ hX (hpos t ht).ne')
  have e0 : (1 - (0 : ℝ)) * q + 0 * s = q := by ring
  have e1 : (1 - (1 : ℝ)) * q + 1 * s = s := by ring
  have eq : N.linePt P₀ Q q = Q := N.linePt_dist hPQ
  simp only [e0, e1, eq, hsQ] at key
  exact key.symm

/-- **Theorem 3.7.** The three angles of a nondegenerate triangle have the same sign. -/
@[kb "petrunin2025" "Theorem 3.7, p. 25"]
theorem sign_angle_triangle {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    (N.angle A B C).sign = (N.angle B C A).sign ∧ (N.angle B C A).sign = (N.angle C A B).sign := by
  have main : ∀ {A B C : P}, IsTriangle A B C → ¬ IsTriangle.Degenerate A B C →
      (N.angle A B C).sign = (N.angle C A B).sign := by
    intro A B C hT hnd
    obtain ⟨hAB, hBC, hCA⟩ := hT
    have hZ := N.isBetween_pointReflFun (O := A) (X := B) hAB.symm
    set Z := N.pointReflFun A B with hZdef
    have hZA : Z ≠ A := hZ.2.1.symm
    have hZB : Z ≠ B := hZ.ne.symm
    have hCl : C ∉ N.line Z B := by
      intro hC
      have hZl : Z ∈ N.line B A := (N.degenerate_iff_mem_line hAB.symm).1 hZ.degenerate
      have hBl : B ∈ N.line B A := N.left_mem_line B A
      rw [N.line_eq_of_mem hAB.symm hZl hBl hZB] at hC
      exact hnd ((N.degenerate_iff_mem_line hAB).2 (by rw [N.line_comm]; exact hC))
    have h1 : N.angle Z B C = N.angle A B C :=
      N.angle_ray_left hAB (N.ray_of_between_outer hZ) hZB hBC.symm
    have h2 := N.sign_angle_eq_of_mem_ray hZB (N.ray_of_between_inner hZ.symm) hZA.symm hCl
    have h3 := N.axiomIIIb A Z C B hZA hCA hAB.symm
    rw [(N.angle_eq_pi_iff hZA hAB.symm).2 hZ.symm] at h3
    have h4 : N.angle C A B = (π : Real.Angle) - N.angle Z A C := by rw [← h3]; abel
    rw [h4, Real.Angle.sign_pi_sub, h2, ← h1]
  have t1 := main hT hnd
  have hT2 : IsTriangle B C A := ⟨hT.2.1, hT.2.2, hT.1⟩
  have hT3 : IsTriangle C A B := ⟨hT.2.2, hT.1, hT.2.1⟩
  have t2 := main hT2 (not_degenerate_rotate hnd)
  have t3 := main hT3 (not_degenerate_rotate (not_degenerate_rotate hnd))
  exact ⟨t2.symm, t3.symm⟩

/-- The angles of a nondegenerate triangle have nonzero sign. -/
theorem sign_angle_ne_zero {A B C : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) :
    (N.angle A B C).sign ≠ 0 := by
  rw [Ne, N.sign_angle_eq_zero_iff hT.1 hT.2.1.symm]
  exact hnd


/-- A signed sum of two angles of one nonzero sign, with the sign kept, adds the absolute values. -/
theorem uangle_add_aux (O A B X : P) (hA : A ≠ O) (hB : B ≠ O) (hX : X ≠ O)
    (h₁ : (N.angle A O X).sign = (N.angle A O B).sign) (h₂ : (N.angle X O B).sign = (N.angle A O B).sign)
    (h₀ : (N.angle A O B).sign ≠ 0) : N.uangle A O X + N.uangle X O B = N.uangle A O B := by
  have hsum := N.axiomIIIb O A X B hA hX hB
  have ha0 : (N.angle A O X).sign ≠ 0 := by rw [h₁]; exact h₀
  have hb0 : (N.angle X O B).sign ≠ 0 := by rw [h₂]; exact h₀
  have hapi : N.angle A O X ≠ π := fun e => ha0 (by rw [e, Real.Angle.sign_coe_pi])
  have hbpi : N.angle X O B ≠ π := fun e => hb0 (by rw [e, Real.Angle.sign_coe_pi])
  have hts := Real.Angle.toReal_add_eq_toReal_add_toReal hapi hbpi
    (Or.inr (by rw [hsum, h₁]))
  unfold uangle
  rw [← hsum, hts]
  rcases (N.angle A O X).sign.trichotomy with h | h | h
  · have hx : (N.angle A O X).toReal < 0 := Real.Angle.toReal_neg_iff_sign_neg.2 h
    have hy : (N.angle X O B).toReal < 0 :=
      Real.Angle.toReal_neg_iff_sign_neg.2 (by rw [h₂, ← h₁, h])
    rw [abs_of_neg hx, abs_of_neg hy, abs_of_neg (by linarith)]
    ring
  · exact absurd h ha0
  · have hx : 0 ≤ (N.angle A O X).toReal :=
      Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [h]; decide)
    have hy : 0 ≤ (N.angle X O B).toReal :=
      Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [h₂, ← h₁, h]; decide)
    rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (by linarith)]

/-- A point off the line `(PQ)` lies off the line spanned by... the apex angle has the opposite sign of the
base angle at the other end. -/
theorem sign_swap_vertex {Q Z W : P} (hQZ : Q ≠ Z) (hW : W ∉ N.line Q Z) :
    (N.angle Z Q W).sign = -(N.angle Q Z W).sign := by
  have hWQ : W ≠ Q := fun e => hW (e ▸ N.left_mem_line Q Z)
  have hWZ : W ≠ Z := fun e => hW (e ▸ N.right_mem_line Q Z)
  have hnd : ¬ IsTriangle.Degenerate Q Z W := fun hd => hW ((N.degenerate_iff_mem_line hQZ).1 hd)
  have h := N.sign_angle_triangle ⟨hQZ, hWZ.symm, hWQ⟩ hnd
  rw [N.angle_rev hQZ.symm hWQ, Real.Angle.sign_neg, ← h.2, ← h.1]

/-- **Exercise 3.8.** If `B` lies between `A` and `C` and `X ∉ (AC)`, then `∠AXB`, `∠BXC`, `∠AXC` have the
same sign and `|∡AXB| + |∡BXC| = |∡AXC|`. -/
@[kb "petrunin2025" "Exercise 3.8, p. 26"]
theorem isBetween_angle_sign_and_uangle {A B C X : P} (hB : IsBetween A B C) (hX : X ∉ N.line A C) :
    (N.angle A X B).sign = (N.angle B X C).sign ∧ (N.angle A X B).sign = (N.angle A X C).sign ∧
      N.uangle A X B + N.uangle B X C = N.uangle A X C := by
  have hAB : A ≠ B := hB.1.symm
  have hBC : B ≠ C := hB.2.1
  have hAC : A ≠ C := hB.ne
  have hAl := N.left_mem_line A C
  have hBl := N.mem_line_of_isBetween hB
  have hCl := N.right_mem_line A C
  have hXA : X ≠ A := fun e => hX (e ▸ hAl)
  have hXB : X ≠ B := fun e => hX (e ▸ hBl)
  have hXC : X ≠ C := fun e => hX (e ▸ hCl)
  have hlAB : N.line A B = N.line A C := N.line_eq_of_mem hAC hAl hBl hAB
  have hlBC : N.line B C = N.line A C := N.line_eq_of_mem hAC hBl hCl hBC
  have hnd1 : ¬ IsTriangle.Degenerate A X B :=
    not_degenerate_swap_right (N.nd_of_notin hAB (by rw [hlAB]; exact hX))
  have hnd2 : ¬ IsTriangle.Degenerate B X C :=
    not_degenerate_swap_right (N.nd_of_notin hBC (by rw [hlBC]; exact hX))
  have hnd3 : ¬ IsTriangle.Degenerate A X C :=
    not_degenerate_swap_right (N.nd_of_notin hAC hX)
  have T1 := N.sign_angle_triangle ⟨hXA.symm, hXB, hAB.symm⟩ hnd1
  have T2 := N.sign_angle_triangle ⟨hXB.symm, hXC, hBC.symm⟩ hnd2
  have T3 := N.sign_angle_triangle ⟨hXA.symm, hXC, hAC.symm⟩ hnd3
  -- the straight angle at `B`
  have hstr := N.sign_angle_of_angle_eq_pi (O := B) (A := A) (B := C) (X := X) hAB hBC.symm hXB
    ((N.angle_eq_pi_iff hAB hBC.symm).2 hB)
  have hCBX : (N.angle C B X).sign = (N.angle X B A).sign := by
    rw [hstr, N.angle_rev hXB hAB, Real.Angle.sign_neg]
  have hray : N.angle C A X = N.angle B A X :=
    N.angle_ray_left hAB.symm (N.ray_of_between_outer hB) hAC.symm hXA
  have e1 : (N.angle B X C).sign = (N.angle A X B).sign := by
    rw [T2.1, T2.2, hCBX, ← T1.1]
  have e2 : (N.angle A X C).sign = (N.angle A X B).sign := by
    rw [T3.1, T3.2, hray, ← T1.2, ← T1.1]
  refine ⟨e1.symm, e2.symm, ?_⟩
  have hne : (N.angle A X C).sign ≠ 0 := N.sign_angle_ne_zero ⟨hXA.symm, hXC, hAC.symm⟩ hnd3
  exact N.uangle_add_aux X A C B hXA.symm hXC.symm hXB.symm e2.symm (e1.trans e2.symm) hne

/-- Supplementary angles: if `O` lies between `A` and `B` and `X ∉ (AB)`, then
`|∡AOX| + |∡XOB| = π` and `∠AOX`, `∠XOB` have the same sign. -/
theorem uangle_add_uangle_of_isBetween {A O B X : P} (hO : IsBetween A O B) (hX : X ∉ N.line A B) :
    N.uangle A O X + N.uangle X O B = π ∧ (N.angle A O X).sign = (N.angle X O B).sign := by
  have hAO : A ≠ O := hO.1.symm
  have hBO : B ≠ O := hO.2.1.symm
  have hOl := N.mem_line_of_isBetween hO
  have hXO : X ≠ O := fun e => hX (e ▸ hOl)
  have hpi := (N.angle_eq_pi_iff hAO hBO).2 hO
  have hsum := N.axiomIIIb O A X B hAO hXO hBO
  rw [hpi] at hsum
  have e : N.angle X O B = (π : Real.Angle) - N.angle A O X := by rw [← hsum]; abel
  have hsg : (N.angle A O X).sign = (N.angle X O B).sign := by
    rw [e, Real.Angle.sign_pi_sub]
  have hnd : ¬ IsTriangle.Degenerate A O X := by
    intro hd
    apply hX
    have h1 : X ∈ N.line A O := (N.degenerate_iff_mem_line hAO).1 hd
    have h2 : N.line A O = N.line A B := N.line_eq_of_mem hO.ne (N.left_mem_line A B) hOl hAO
    rw [h2] at h1
    exact h1
  have h0 : (N.angle A O X).sign ≠ 0 := fun h => hnd ((N.sign_angle_eq_zero_iff hAO hXO).1 h)
  refine ⟨?_, hsg⟩
  unfold uangle
  apply Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq _ hsg h0
  rw [hsum, Real.Angle.two_zsmul_coe_pi]

/-- Angle addition with signs: if `∠AOX` and `∠XOB` have the same nonzero sign as `∠AOB`, then
`|∡AOX| + |∡XOB| = |∡AOB|`. -/
theorem uangle_add_of_sign_eq {O A B X : P} (hA : A ≠ O) (hB : B ≠ O) (hX : X ≠ O)
    (h₁ : (N.angle A O X).sign = (N.angle A O B).sign) (h₂ : (N.angle X O B).sign = (N.angle A O B).sign)
    (h₀ : (N.angle A O B).sign ≠ 0) : N.uangle A O X + N.uangle X O B = N.uangle A O B :=
  N.uangle_add_aux O A B X hA hB hX h₁ h₂ h₀

/-! ### Half-planes -/

theorem sign_eq_zero_of_eq_neg' {s : SignType} (h : s = -s) : s = 0 := by
  revert h
  revert s
  decide

theorem sign_eq_zero_of_neg_eq_zero' {s : SignType} (h : -s = 0) : s = 0 := by
  revert h
  revert s
  decide

/-! #### Corollary 4.5 inside this file

The metric criterion `AB + BC = AC ⟹ B ∈ (AC)` (Corollary 4.5) is needed already for the half-plane statements
below, which are phrased with distances. It follows from SSS; to keep the files acyclic we re-derive the small
part of Chapter 4 that is needed (isosceles triangles and SSS). The later file `NeutralCongruence` has the same
results in their public form. -/

private theorem tc_symm {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C') :
    TriangleCongruent A' B' C' A B C := by
  obtain ⟨f, hA, hB, hC⟩ := h
  exact ⟨f.symm, by rw [← hA]; exact f.symm_apply_apply A, by rw [← hB]; exact f.symm_apply_apply B,
    by rw [← hC]; exact f.symm_apply_apply C⟩

private theorem tc_trans {A B C A' B' C' A'' B'' C'' : P}
    (h : TriangleCongruent A B C A' B' C') (h' : TriangleCongruent A' B' C' A'' B'' C'') :
    TriangleCongruent A B C A'' B'' C'' := by
  obtain ⟨f, hA, hB, hC⟩ := h
  obtain ⟨g, gA, gB, gC⟩ := h'
  exact ⟨f.trans g, by simp [hA, gA], by simp [hB, gB], by simp [hC, gC]⟩

private theorem tc_dist {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C') :
    dist A' B' = dist A B ∧ dist B' C' = dist B C ∧ dist C' A' = dist C A := by
  obtain ⟨f, hA, hB, hC⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← hA, ← hB, f.dist_eq]
  · rw [← hB, ← hC, f.dist_eq]
  · rw [← hC, ← hA, f.dist_eq]

/-- Congruent triangles (by a motion) have equal angles up to sign at corresponding vertices. -/
private theorem tc_angle {A B C A' B' C' : P} (h : TriangleCongruent A B C A' B' C')
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

include N in
private theorem tc_eq_of_mem_ray_of_dist_eq {O A X Y : P} (hOA : O ≠ A) (hX : X ∈ metricHalfLine O A)
    (hY : Y ∈ metricHalfLine O A) (h : dist O X = dist O Y) : X = Y := by
  obtain ⟨Z, -, hZ⟩ := N.existsUnique_mem_metricHalfLine_dist hOA (dist_nonneg : 0 ≤ dist O Y)
  rw [hZ X ⟨hX, h⟩, hZ Y ⟨hY, rfl⟩]

private theorem tc_exists_pt {O A : P} (hA : A ≠ O) {r : ℝ} (hr : 0 < r) (α : Real.Angle) :
    ∃ B, dist O B = r ∧ N.angle A O B = α := by
  obtain ⟨D, hD, hang, -⟩ := N.axiomIIIa O A hA α
  obtain ⟨B, ⟨hB, hd⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hD.symm hr.le
  have hBO : B ≠ O := by
    intro e
    rw [e, dist_self] at hd
    linarith
  exact ⟨B, hd, by rw [N.angle_ray_right hA hD hB hBO, hang]⟩

private theorem tc_isosceles {A B C : P} (hT : IsTriangle A B C) (h : dist C A = dist C B) :
    N.angle A B C = -N.angle B A C := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  have hcong : TriangleCongruent C A B C B A :=
    (N.axiomIV C A B C B A hCA hAB hBC hBC.symm hAB.symm hCA.symm).2
      ⟨h.symm, h, Or.inr (N.angle_rev hCA.symm hBC)⟩
  have hang := N.tc_angle hcong hCA hAB.symm
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
      exact hne (by rw [e2]; exact sign_eq_zero_of_eq_neg' e1)
    · rw [h1]

include N in
private theorem tc_sss {A B C A' B' C' : P} (hT : IsTriangle A B C) (hT' : IsTriangle A' B' C')
    (h₁ : dist A' B' = dist A B) (h₂ : dist B' C' = dist B C) (h₃ : dist C' A' = dist C A) :
    TriangleCongruent A B C A' B' C' := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨hAB', hBC', hCA'⟩ := hT'
  obtain ⟨C'', hd, hang⟩ :=
    N.tc_exists_pt (O := A') (A := B') hAB'.symm (dist_pos.2 hCA'.symm) (N.angle B A C)
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
    exact hBC (N.tc_eq_of_mem_ray_of_dist_eq hAB (N.self_mem_metricHalfLine hAB) hCr this)
  have hcong1 : TriangleCongruent A B C A' B' C'' :=
    (N.axiomIV A B C A' B' C'' hAB hBC hCA hAB' hB'C'' hC''A').2
      ⟨h₁, hd.trans hd3, Or.inl (by
        rw [N.angle_rev hC''A' hAB'.symm, hang, N.angle_rev hAB.symm hCA, neg_neg])⟩
  have hdB := (tc_dist hcong1).2.1
  by_cases hc : C'' = C'
  · rw [hc] at hcong1
    exact hcong1
  replace hc : C'' ≠ C' := hc
  have hdB' : dist B' C'' = dist B' C' := by rw [hdB, h₂]
  have i1 := N.tc_isosceles (A := C') (B := C'') (C := A') ⟨hc.symm, hC''A', hCA'.symm⟩ hd.symm
  have i2 := N.tc_isosceles (A := C') (B := C'') (C := B') ⟨hc.symm, hB'C''.symm, hBC'⟩ hdB'.symm
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
  exact tc_trans hcong1 (tc_symm ⟨g, gA, gB, gC⟩)

/-- **Corollary 4.5** (derived here from SSS): `AB + BC = AC` puts `B` on `(AC)`. -/
theorem mem_line_of_dist_add_aux {A B C : P} (hAC : A ≠ C) (h : dist A B + dist B C = dist A C) :
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
    N.tc_sss ⟨hB'A.symm, hB'C, hAC.symm⟩ ⟨hAB, hBC, hAC.symm⟩ hB'd.symm hdist.symm rfl
  have hang := N.tc_angle hcong hB'A.symm hB'C.symm
  have hABC : N.angle A B C = π := by
    rcases hang with h1 | h1
    · rw [h1, hpi]
    · rw [h1, hpi, Real.Angle.neg_coe_pi]
  obtain ⟨L, hL, hA, hB, hC⟩ := (N.degenerate_iff_angle hAB (Ne.symm hBC)).2 (Or.inr hABC)
  rw [← N.eq_line hL hA hC hAC]
  exact hB

include N in
theorem isBetween_of_cross {L : Set P} {X Y Z : P} (hX : X ∉ L) (hY : Y ∉ L) (hZ : Z ∈ L)
    (hd : dist X Z + dist Z Y = dist X Y) : IsBetween X Z Y := by
  have hZX : Z ≠ X := fun e => hX (e ▸ hZ)
  have hZY : Z ≠ Y := fun e => hY (e ▸ hZ)
  have hXY : X ≠ Y := by
    rintro rfl
    have := dist_pos.2 hZX
    rw [dist_self] at hd
    linarith [dist_comm X Z]
  exact ⟨hZX, hZY, hd, ⟨N.line X Y, N.isLine_line hXY, N.left_mem_line X Y,
    N.mem_line_of_dist_add_aux hXY hd, N.right_mem_line X Y⟩⟩

theorem ne_left_of_notin {A B X : P} (hX : X ∉ N.line A B) : X ≠ A :=
  fun e => hX (e ▸ N.left_mem_line A B)

theorem ne_right_of_notin {A B X : P} (hX : X ∉ N.line A B) : X ≠ B :=
  fun e => hX (e ▸ N.right_mem_line A B)

theorem exists_points_of_isLine {L : Set P} (hL : IsLine L) : ∃ P₀ Q : P, P₀ ≠ Q ∧ L = N.line P₀ Q := by
  obtain ⟨f, hf, rfl⟩ := hL
  have hne : f 0 ≠ f 1 := by
    intro e
    have := hf.dist_eq 0 1
    rw [e, dist_self, Real.dist_eq] at this
    norm_num at this
  exact ⟨f 0, f 1, hne, N.eq_line ⟨f, hf, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ hne⟩

/-- Lemma 3.9: if the segment `[XY]` misses the line then the signs agree. -/
theorem sign_eq_of_no_cross {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q)
    (hY : Y ∉ N.line P₀ Q) (h : ¬ ∃ Z ∈ N.line P₀ Q, dist X Z + dist Z Y = dist X Y) :
    (N.angle P₀ Q X).sign = (N.angle P₀ Q Y).sign := by
  by_cases hXY : X = Y
  · rw [hXY]
  have hd0 : 0 < dist X Y := dist_pos.2 hXY
  have hY' : N.linePt X Y (dist X Y) = Y := N.linePt_dist hXY
  have hBnot : ∀ t ∈ Set.Icc (0 : ℝ) 1, N.linePt X Y (t * dist X Y) ∉ N.line P₀ Q := by
    intro t ht hmem
    apply h
    refine ⟨_, hmem, ?_⟩
    have h1 : dist X (N.linePt X Y (t * dist X Y)) = t * dist X Y := by
      rw [N.dist_left_linePt hXY, abs_of_nonneg (mul_nonneg ht.1 hd0.le)]
    have h2 : dist (N.linePt X Y (t * dist X Y)) Y = (1 - t) * dist X Y := by
      have := N.dist_linePt hXY (t * dist X Y) (dist X Y)
      rw [hY'] at this
      rw [this, abs_of_nonpos (by nlinarith [ht.2, hd0])]
      ring
    rw [h1, h2]
    ring
  have key := N.sign_angle_eq_of_continuousOn (O := fun _ => Q) (A := fun _ => P₀)
    (B := fun t => N.linePt X Y (t * dist X Y)) continuousOn_const continuousOn_const
    ((N.continuous_linePt hXY).comp (by fun_prop)).continuousOn
    (fun _ _ => hPQ) (fun t ht e => hBnot t ht (by rw [e]; exact N.right_mem_line P₀ Q))
    (fun t ht hdeg => hBnot t ht ((N.degenerate_iff_mem_line hPQ).1 hdeg))
  simp only [zero_mul, one_mul, N.linePt_zero, hY'] at key
  exact key

/-- If `Z` on the line separates `X` and `Y` then the angles `∠PQX`, `∠PQY` have opposite signs. -/
theorem sign_flip {P₀ Q X Y Z : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q) (hY : Y ∉ N.line P₀ Q)
    (hZ : Z ∈ N.line P₀ Q) (hb : IsBetween X Z Y) :
    (N.angle P₀ Q Y).sign = -(N.angle P₀ Q X).sign := by
  have hXQ : X ≠ Q := N.ne_right_of_notin hX
  have hYQ : Y ≠ Q := N.ne_right_of_notin hY
  by_cases hZQ : Z = Q
  · rw [hZQ] at hb
    have hpi := (N.angle_eq_pi_iff hXQ hYQ).2 hb
    have h1 := N.sign_angle_of_angle_eq_pi hXQ hYQ hPQ hpi
    rw [N.angle_rev hPQ hYQ, N.angle_rev hPQ hXQ, Real.Angle.sign_neg, Real.Angle.sign_neg, h1]
  · have hl : N.line Q Z = N.line P₀ Q := N.line_eq_of_mem hPQ (N.right_mem_line P₀ Q) hZ (Ne.symm hZQ)
    have hXl : X ∉ N.line Q Z := by rw [hl]; exact hX
    have hYl : Y ∉ N.line Q Z := by rw [hl]; exact hY
    have sx := N.sign_swap_vertex (Ne.symm hZQ) hXl
    have sy := N.sign_swap_vertex (Ne.symm hZQ) hYl
    have hXZ : X ≠ Z := hb.1.symm
    have hYZ : Y ≠ Z := hb.2.1.symm
    have hstr := N.sign_angle_of_angle_eq_pi (X := Q) hXZ hYZ (Ne.symm hZQ)
      ((N.angle_eq_pi_iff hXZ hYZ).2 hb)
    have hQZY : (N.angle Q Z Y).sign = -(N.angle Q Z X).sign := by
      rw [N.angle_rev (Ne.symm hZQ) hYZ, N.angle_rev (Ne.symm hZQ) hXZ, Real.Angle.sign_neg,
        Real.Angle.sign_neg, hstr, neg_neg]
    have hmain : (N.angle Z Q Y).sign = -(N.angle Z Q X).sign := by
      rw [sx, sy, hQZY]
    have hrel : (∀ W, W ≠ Q → (N.angle P₀ Q W).sign = (N.angle Z Q W).sign) ∨
        (∀ W, W ≠ Q → (N.angle P₀ Q W).sign = -(N.angle Z Q W).sign) := by
      have hZl : Z ∈ N.line Q P₀ := by rw [N.line_comm]; exact hZ
      rcases N.mem_metricHalfLine_or_isBetween hPQ.symm hZl with h | h
      · left
        intro W hW
        rw [N.angle_ray_left hPQ h hZQ hW]
      · right
        intro W hW
        exact N.sign_angle_of_angle_eq_pi (O := Q) (A := Z) (B := P₀) (X := W) hZQ hPQ hW
          ((N.angle_eq_pi_iff hZQ hPQ).2 h)
    rcases hrel with h | h
    · rw [h Y hYQ, h X hXQ, hmain]
    · rw [h Y hYQ, h X hXQ, hmain, neg_neg]

/-- **Lemma 3.9 and Proposition 3.10.** For `X, Y ∉ (PQ)`: `∠PQX` and `∠PQY` have the same sign iff the
segment `[XY]` does not meet `(PQ)`. -/
@[kb "petrunin2025" "Proposition 3.10, p. 26"]
theorem sign_angle_eq_iff {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q) (hY : Y ∉ N.line P₀ Q) :
    (N.angle P₀ Q X).sign = (N.angle P₀ Q Y).sign ↔
      ¬ ∃ Z ∈ N.line P₀ Q, dist X Z + dist Z Y = dist X Y := by
  constructor
  · intro hs
    rintro ⟨Z, hZ, hd⟩
    have hb := N.isBetween_of_cross hX hY hZ hd
    have hflip := N.sign_flip hPQ hX hY hZ hb
    have hne : (N.angle P₀ Q X).sign ≠ 0 :=
      N.sign_angle_ne_zero ⟨hPQ, (N.ne_right_of_notin hX).symm, N.ne_left_of_notin hX⟩
        (N.nd_of_notin hPQ hX)
    rw [hflip] at hs
    exact hne (sign_eq_zero_of_eq_neg' hs)
  · exact N.sign_eq_of_no_cross hPQ hX hY

/-- Two points off a line `(PQ)` lie on one side of it (Corollary 3.11): the segment between them misses the
line; equivalently, the angles `∠PQX` and `∠PQY` have the same sign. -/
@[kb "petrunin2025" "Corollary 3.11, p. 27"]
def SameSide (L : Set P) (X Y : P) : Prop :=
  X ∉ L ∧ Y ∉ L ∧ ¬ ∃ Z ∈ L, dist X Z + dist Z Y = dist X Y

/-- **Corollary 3.11.** The half-plane relation does not depend on the two points chosen on the line: for any
distinct `P', Q'` on `(PQ)`, the sign criterion holds with `P', Q'`. -/
@[kb "petrunin2025" "Corollary 3.11, p. 27"]
theorem sameSide_iff_sign {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q) (hY : Y ∉ N.line P₀ Q) :
    SameSide (N.line P₀ Q) X Y ↔ (N.angle P₀ Q X).sign = (N.angle P₀ Q Y).sign := by
  rw [N.sign_angle_eq_iff hPQ hX hY]
  exact ⟨fun h => h.2.2, fun h => ⟨hX, hY, h⟩⟩

theorem SameSide.symm {L : Set P} {X Y : P} (h : SameSide L X Y) : SameSide L Y X := by
  obtain ⟨hX, hY, h3⟩ := h
  refine ⟨hY, hX, ?_⟩
  rintro ⟨Z, hZ, hd⟩
  apply h3
  exact ⟨Z, hZ, by rw [dist_comm X Z, dist_comm Z Y, dist_comm X Y]; linarith⟩

/-- The same-side relation is transitive (from the sign criterion). -/
theorem sameSide_trans {P₀ Q X Y Z : P} (hPQ : P₀ ≠ Q) (h₁ : SameSide (N.line P₀ Q) X Y)
    (h₂ : SameSide (N.line P₀ Q) Y Z) : SameSide (N.line P₀ Q) X Z := by
  have a := (N.sameSide_iff_sign hPQ h₁.1 h₁.2.1).1 h₁
  have b := (N.sameSide_iff_sign hPQ h₂.1 h₂.2.1).1 h₂
  exact (N.sameSide_iff_sign hPQ h₁.1 h₂.2.1).2 (a.trans b)


/-- Two points off a line that are not on one side are separated: the segment between them crosses the
line. -/
theorem exists_mem_line_of_not_sameSide {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q)
    (hY : Y ∉ N.line P₀ Q) (h : ¬ SameSide (N.line P₀ Q) X Y) :
    ∃ Z ∈ N.line P₀ Q, IsBetween X Z Y := by
  have h' : ∃ Z ∈ N.line P₀ Q, dist X Z + dist Z Y = dist X Y := by
    by_contra h2
    exact h ⟨hX, hY, h2⟩
  obtain ⟨Z, hZ, hd⟩ := h'
  exact ⟨Z, hZ, N.isBetween_of_cross hX hY hZ hd⟩

/-- The sign of `∠PQX` with `P, Q` replaced by other points `P', Q'` of the same line in the same
order changes consistently: same side iff same sign, whatever two points are used. -/
theorem sign_angle_eq_iff_of_line {P₀ Q P' Q' X Y : P} (hPQ : P₀ ≠ Q) (hP' : P' ∈ N.line P₀ Q)
    (hQ' : Q' ∈ N.line P₀ Q) (hPQ' : P' ≠ Q') (hX : X ∉ N.line P₀ Q) (hY : Y ∉ N.line P₀ Q) :
    (N.angle P₀ Q X).sign = (N.angle P₀ Q Y).sign ↔ (N.angle P' Q' X).sign = (N.angle P' Q' Y).sign := by
  have hl : N.line P' Q' = N.line P₀ Q := N.line_eq_of_mem hPQ hP' hQ' hPQ'
  have hX' : X ∉ N.line P' Q' := by rw [hl]; exact hX
  have hY' : Y ∉ N.line P' Q' := by rw [hl]; exact hY
  rw [N.sign_angle_eq_iff hPQ hX hY, N.sign_angle_eq_iff hPQ' hX' hY', hl]

/-- For `X ∉ (PQ)`, the angle at `X` has the opposite sign to the angle `∠PQX`. -/
theorem sign_apex {P₀ Q X : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q) :
    (N.angle P₀ X Q).sign = -(N.angle P₀ Q X).sign := by
  have hXQ : X ≠ Q := N.ne_right_of_notin hX
  have hXP : X ≠ P₀ := N.ne_left_of_notin hX
  have hnd : ¬ IsTriangle.Degenerate P₀ X Q := not_degenerate_swap_right (N.nd_of_notin hPQ hX)
  have h := N.sign_angle_triangle ⟨hXP.symm, hXQ, hPQ.symm⟩ hnd
  rw [h.1, N.angle_rev hXQ hPQ, Real.Angle.sign_neg]

/-- **Exercise 3.14.** `X, Y ∉ (PQ)` lie on one side of `(PQ)` iff `∠PXQ` and `∠PYQ` have the same
sign. -/
@[kb "petrunin2025" "Exercise 3.14, p. 28"]
theorem sameSide_iff_sign_angle_at {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q)
    (hY : Y ∉ N.line P₀ Q) :
    SameSide (N.line P₀ Q) X Y ↔ (N.angle P₀ X Q).sign = (N.angle P₀ Y Q).sign := by
  rw [N.sameSide_iff_sign hPQ hX hY, N.sign_apex hPQ hX, N.sign_apex hPQ hY, neg_inj]

include N in
/-- **Pasch's theorem 3.13.** A line through no vertex of a triangle that meets one side meets one of the
other two sides. -/
@[kb "petrunin2025" "Theorem 3.13, p. 27"]
theorem pasch {L : Set P} (hL : IsLine L) {A B C : P} (hA : A ∉ L) (hB : B ∉ L) (hC : C ∉ L)
    (hAB : ∃ Z ∈ L, IsBetween A Z B) :
    (∃ Z ∈ L, IsBetween B Z C) ∨ (∃ Z ∈ L, IsBetween A Z C) := by
  obtain ⟨P₀, Q, hPQ, rfl⟩ := N.exists_points_of_isLine hL
  obtain ⟨Z, hZ, hb⟩ := hAB
  have hnAB : ¬ SameSide (N.line P₀ Q) A B := by
    intro hs
    exact hs.2.2 ⟨Z, hZ, hb.dist_add⟩
  by_cases hAC : SameSide (N.line P₀ Q) A C
  · left
    refine N.exists_mem_line_of_not_sameSide hPQ hB hC ?_
    intro hBC
    exact hnAB (N.sameSide_trans hPQ hAC hBC.symm)
  · right
    exact N.exists_mem_line_of_not_sameSide hPQ hA hC hAC

/-- **Crossbar property** (cf. Exercise 3.15). If the half-line `[OX)` lies inside the angle `∠AOB` of a
nondegenerate triangle, i.e. `∠AOX` and `∠XOB` have the sign of `∠AOB`, then `[OX)` meets the segment `[AB]`
at a point between `A` and `B`. -/
theorem crossbar {O A B X : P} (hT : IsTriangle A O B) (hnd : ¬ IsTriangle.Degenerate A O B) (hX : X ≠ O)
    (h₁ : (N.angle A O X).sign = (N.angle A O B).sign) (h₂ : (N.angle X O B).sign = (N.angle A O B).sign) :
    ∃ Z, Z ∈ metricHalfLine O X ∧ IsBetween A Z B := by
  obtain ⟨hAO, hOB, hBA⟩ := hT
  have hXO' : O ≠ X := hX.symm
  have hs0 : (N.angle A O B).sign ≠ 0 := N.sign_angle_ne_zero ⟨hAO, hOB, hBA⟩ hnd
  have hnAB : O ∉ N.line A B := by
    intro hO
    obtain ⟨L, hL, h1, h2, h3⟩ := (N.degenerate_iff_mem_line hBA.symm).2 hO
    exact hnd ⟨L, hL, h1, h3, h2⟩
  have hA0 : A ∉ N.line X O := by
    intro hAl
    have hd := (N.degenerate_iff_mem_line hX).2 hAl
    have := (N.sign_angle_eq_zero_iff hX hAO).2 hd
    rw [N.angle_rev hX hAO, Real.Angle.sign_neg, h₁] at this
    exact hs0 (sign_eq_zero_of_neg_eq_zero' this)
  have hB0 : B ∉ N.line X O := by
    intro hBl
    have hd := (N.degenerate_iff_mem_line hX).2 hBl
    have := (N.sign_angle_eq_zero_iff hX hOB.symm).2 hd
    rw [h₂] at this
    exact hs0 this
  have hnot : ¬ SameSide (N.line X O) A B := by
    intro hss
    have := (N.sameSide_iff_sign hX hA0 hB0).1 hss
    rw [N.angle_rev hX hAO, Real.Angle.sign_neg, h₁, h₂] at this
    exact hs0 (sign_eq_zero_of_eq_neg' this.symm)
  obtain ⟨Z, hZ, hbZ⟩ := N.exists_mem_line_of_not_sameSide hX hA0 hB0 hnot
  refine ⟨Z, ?_, hbZ⟩
  have hZl : Z ∈ N.line O X := by rw [N.line_comm]; exact hZ
  rcases N.mem_metricHalfLine_or_isBetween hXO' hZl with h | h
  · exact h
  · exfalso
    have hZO : Z ≠ O := h.1.symm
    obtain ⟨e1, e2, -⟩ := N.isBetween_angle_sign_and_uangle hbZ hnAB
    have hsum := N.axiomIIIb O A Z X hAO hZO hX
    rw [(N.angle_eq_pi_iff hZO hX).2 h] at hsum
    have h3 : (N.angle A O X).sign = -(N.angle A O Z).sign := by
      rw [← hsum, Real.Angle.sign_add_pi]
    rw [h₁, e2] at h3
    exact hs0 (sign_eq_zero_of_eq_neg' h3)

/-- **Exercise 3.16.** If `X` and `Y` lie on opposite sides of `(PQ)`, then `[PX)` does not meet `[QY)`. -/
@[kb "petrunin2025" "Exercise 3.16, p. 28"]
theorem metricHalfLine_disjoint_of_not_sameSide {P₀ Q X Y : P} (hPQ : P₀ ≠ Q) (hX : X ∉ N.line P₀ Q)
    (hY : Y ∉ N.line P₀ Q) (h : ¬ SameSide (N.line P₀ Q) X Y) :
    Disjoint (metricHalfLine P₀ X) (metricHalfLine Q Y) := by
  rw [Set.disjoint_left]
  intro W hWP hWQ
  have hPX : P₀ ≠ X := (N.ne_left_of_notin hX).symm
  have hQY : Q ≠ Y := (N.ne_right_of_notin hY).symm
  by_cases hWL : W ∈ N.line P₀ Q
  · have h1 : W = P₀ := by
      by_contra hne
      have hWl : W ∈ N.line P₀ X := N.metricHalfLine_subset_line hPX hWP
      have e1 : N.line P₀ W = N.line P₀ X :=
        N.line_eq_of_mem hPX (N.left_mem_line P₀ X) hWl (Ne.symm hne)
      have e2 : N.line P₀ W = N.line P₀ Q :=
        N.line_eq_of_mem hPQ (N.left_mem_line P₀ Q) hWL (Ne.symm hne)
      exact hX (by rw [← e2, e1]; exact N.right_mem_line P₀ X)
    have h2 : W = Q := by
      by_contra hne
      have hWl : W ∈ N.line Q Y := N.metricHalfLine_subset_line hQY hWQ
      have hWL' : W ∈ N.line Q P₀ := by rw [N.line_comm]; exact hWL
      have e1 : N.line Q W = N.line Q Y :=
        N.line_eq_of_mem hQY (N.left_mem_line Q Y) hWl (Ne.symm hne)
      have e2 : N.line Q W = N.line Q P₀ :=
        N.line_eq_of_mem hPQ.symm (N.left_mem_line Q P₀) hWL' (Ne.symm hne)
      apply hY
      rw [N.line_comm P₀ Q, ← e2, e1]
      exact N.right_mem_line Q Y
    exact hPQ (h1.symm.trans h2)
  · have hWP0 : W ≠ P₀ := fun e => hWL (e ▸ N.left_mem_line P₀ Q)
    have hWQ0 : W ≠ Q := fun e => hWL (e ▸ N.right_mem_line P₀ Q)
    have sX : (N.angle P₀ Q X).sign = (N.angle P₀ Q W).sign := by
      have h1 : N.angle Q P₀ W = N.angle Q P₀ X :=
        N.angle_ray_right hPQ.symm (N.ne_left_of_notin hX) hWP hWP0
      exact (N.sign_angle_eq_iff_of_line hPQ (N.right_mem_line P₀ Q) (N.left_mem_line P₀ Q) hPQ.symm
        hX hWL).2 (by rw [h1])
    have sY : (N.angle P₀ Q W).sign = (N.angle P₀ Q Y).sign := by
      rw [N.angle_ray_right hPQ (N.ne_right_of_notin hY) hWQ hWQ0]
    exact h ((N.sameSide_iff_sign hPQ hX hY).2 (sX.trans sY))

/-! ### The reflection across a point keeps angles -/

/-- **Proposition 7.6** (the book's proof does not use Axiom V). The reflection across a point is a direct
motion: it keeps the measures of angles. -/
@[kb "petrunin2025" "Proposition 7.6, p. 47"]
theorem angle_pointRefl (O : P) {A B C : P} (hA : A ≠ B) (hC : C ≠ B) :
    N.angle (N.pointRefl O A) (N.pointRefl O B) (N.pointRefl O C) = N.angle A B C := by
  set σ := N.pointRefl O with hσ
  have hσO : σ O = O := by rw [hσ, N.pointRefl_apply, N.pointReflFun_self]
  have hbt : ∀ {X : P}, X ≠ O → IsBetween X O (σ X) := fun {X} hX => by
    rw [hσ, N.pointRefl_apply]
    exact N.isBetween_pointReflFun hX
  have hne : ∀ {X : P}, X ≠ O → σ X ≠ O := fun {X} hX e => hX (σ.injective (e.trans hσO.symm))
  by_cases hBO : B = O
  · rw [hBO] at hA hC ⊢
    rw [hσO]
    exact (N.angle_vertical (hbt hA) (hbt hC)).symm
  -- the key claim: the angle `∡ABO` is kept
  have M : ∀ {A : P}, A ≠ B → N.angle (σ A) (σ B) O = N.angle A B O := by
    intro A hAB
    have hOB : O ≠ B := Ne.symm hBO
    by_cases hAO : A = O
    · rw [hAO, hσO, N.angle_self hOB, N.angle_self (Ne.symm (hne hBO))]
    have hσAB : σ A ≠ σ B := fun e => hAB (σ.injective e)
    have iso := N.angle_isometryEquiv σ hAB hOB
    rw [hσO] at iso
    by_cases hd : IsTriangle.Degenerate A B O
    · rcases (N.degenerate_iff_angle hAB hOB).1 hd with h0 | hpi
      · rw [h0] at iso ⊢
        simpa using iso
      · rw [hpi] at iso ⊢
        rcases iso with h | h
        · exact h
        · rw [h, Real.Angle.neg_coe_pi]
    · have hnd' : ¬ IsTriangle.Degenerate (σ A) (σ B) O := by
        intro hd'
        apply hd
        rw [N.degenerate_iff_angle hσAB (Ne.symm (hne hBO))] at hd'
        rw [N.degenerate_iff_angle hAB hOB]
        rcases iso with h | h
        · rwa [← h]
        · have h' : N.angle A B O = -N.angle (σ A) (σ B) O := by rw [h, neg_neg]
          rcases hd' with e | e
          · left; rw [h', e, neg_zero]
          · right; rw [h', e, Real.Angle.neg_coe_pi]
      have T := N.sign_angle_triangle ⟨hAB, hBO, fun e => hAO e.symm⟩ hd
      have T' := N.sign_angle_triangle ⟨hσAB, Ne.symm (hne hBO) |>.symm, fun e => hne hAO e.symm⟩ hnd'
      have hvert : N.angle B O A = N.angle (σ B) O (σ A) :=
        N.angle_vertical (hbt hBO) (hbt hAO)
      have hsg : (N.angle (σ A) (σ B) O).sign = (N.angle A B O).sign := by
        rw [T'.1, ← hvert, ← T.1]
      have hne0 : (N.angle A B O).sign ≠ 0 :=
        N.sign_angle_ne_zero ⟨hAB, hBO, fun e => hAO e.symm⟩ hd
      rcases iso with h | h
      · exact h
      · exfalso
        rw [h, Real.Angle.sign_neg] at hsg
        exact hne0 (sign_eq_zero_of_eq_neg' hsg.symm)
  have e1 := N.axiomIIIb B A O C hA (Ne.symm hBO) hC
  have e2 := N.axiomIIIb (σ B) (σ A) O (σ C) (fun e => hA (σ.injective e))
    (Ne.symm (hne hBO)) (fun e => hC (σ.injective e))
  rw [← e1, ← e2, M hA, N.angle_rev (Ne.symm (hne hBO)) (fun e => hC (σ.injective e)),
    N.angle_rev (Ne.symm hBO) hC, M hC]

end NeutralPlane

end Neutral

end UndergradKB.Geometry
