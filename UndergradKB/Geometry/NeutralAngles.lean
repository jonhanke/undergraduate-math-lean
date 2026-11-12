import UndergradKB.Geometry.NeutralLines
import UndergradKB.Common.Attr

/-! # Neutral plane II: angles and the reflection across a point (Petrunin, Sections 2C-2F)

Derived from Axioms I-IV of `NeutralPlane` (including `axiomIII_halfLine`: the measure is that of the
angle, i.e. it depends only on the two half-lines). -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

open Classical

/-! ### Angles (Sections 2C-2E) -/

/-- The image of a line under a motion is a line. -/
private theorem isLine_image {L : Set P} (hL : IsLine L) (f : P ≃ᵢ P) : IsLine (f '' L) := by
  obtain ⟨g, hg, rfl⟩ := hL
  exact ⟨f ∘ g, f.isometry.comp hg, by rw [Set.range_comp]⟩

private theorem linePt_ne_self {O A : P} (h : O ≠ A) {s : ℝ} (hs : s ≠ 0) : N.linePt O A s ≠ O := by
  intro e
  apply hs
  exact N.linePt_injective h (by rw [linePt_zero]; exact e)

/-- Two points of `(OA)` on the negative side of `O` lie on one half-line from `O`. -/
private theorem mem_half_neg {O A : P} (h : O ≠ A) {t u : ℝ} (ht : t < 0) (hu : u < 0) :
    N.linePt O A u ∈ metricHalfLine O (N.linePt O A t) := by
  refine ⟨fun s => N.linePt O A (-s), ?_, by simp, ⟨-t, by linarith, by simp⟩, -u, by linarith, by simp⟩
  refine Isometry.of_dist_eq fun x y => ?_
  rw [N.dist_linePt h, Real.dist_eq, show -x - -y = -(x - y) by ring, abs_neg]


/-- An angle with a motion applied: by Axiom IV the measure is kept up to sign. -/
theorem angle_isometryEquiv (f : P ≃ᵢ P) {A O B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.angle (f A) (f O) (f B) = N.angle A O B ∨ N.angle (f A) (f O) (f B) = -N.angle A O B := by
  have hfA : f A ≠ f O := fun h => hA (f.injective h)
  have hfB : f B ≠ f O := fun h => hB (f.injective h)
  by_cases hAB : A = B
  · subst hAB
    left
    rw [N.angle_self hA, N.angle_self hfA]
  · have hfAB : f A ≠ f B := fun h => hAB (f.injective h)
    have h := (N.axiomIV O A B (f O) (f A) (f B) hA.symm hAB hB hfA.symm hfAB hfB).1 ⟨f, rfl, rfl, rfl⟩
    have e1 := N.angle_rev hA hB
    have e2 := N.angle_rev hfA hfB
    rcases h.2.2 with h3 | h3
    · left
      rw [e2, h3, e1]
    · right
      rw [e2, h3, e1]

/-- A motion fixing two distinct points `A`, `B` fixes the line `(AB)` pointwise. -/
theorem isometryEquiv_fix_line (f : P ≃ᵢ P) {A B : P} (hAB : A ≠ B) (hA : f A = A) (hB : f B = B)
    {X : P} (hX : X ∈ N.line A B) : f X = X := by
  have hL := N.isLine_line hAB
  have himg : f '' N.line A B = N.line A B :=
    N.eq_line (isLine_image hL f) ⟨A, N.left_mem_line A B, hA⟩ ⟨B, N.right_mem_line A B, hB⟩ hAB
  have hfX : f X ∈ N.line A B := by
    rw [← himg]
    exact ⟨X, hX, rfl⟩
  have d1 := f.dist_eq A X
  have d2 := f.dist_eq B X
  rw [hA] at d1
  rw [hB] at d2
  exact hL.eq_of_dist_eq (N.left_mem_line A B) (N.right_mem_line A B) hfX hX hAB d1 d2

/-- If `B ∈ [OA)`, `B ≠ O`, then `∡AOB = 0` (from `axiomIII_halfLine` and Proposition 2.4). -/
theorem angle_eq_zero_of_mem_ray {O A B : P} (hA : A ≠ O) (hB : B ∈ metricHalfLine O A) (hBO : B ≠ O) :
    N.angle A O B = 0 := by
  have := N.axiomIII_halfLine O A B B hA hB hBO hBO
  rw [← this]
  exact N.angle_self hBO

theorem angle_ray_left {O A A' B : P} (hA : A ≠ O) (hA' : A' ∈ metricHalfLine O A) (hA'O : A' ≠ O)
    (hB : B ≠ O) : N.angle A' O B = N.angle A O B :=
  N.axiomIII_halfLine O A A' B hA hA' hA'O hB

theorem angle_ray_right {O A B B' : P} (hA : A ≠ O) (hB : B ≠ O) (hB' : B' ∈ metricHalfLine O B)
    (hB'O : B' ≠ O) : N.angle A O B' = N.angle A O B := by
  rw [N.angle_rev hA hB'O, N.angle_rev hA hB, N.angle_ray_left hB hB' hB'O hA]

/-- **Exercise 2.5.** If `∡AOB = 0` then `[OA) = [OB)`; here: `B ∈ [OA)`. -/
@[kb "petrunin2025" "Exercise 2.5, p. 20"]
theorem mem_ray_of_angle_eq_zero {O A B : P} (hA : A ≠ O) (hB : B ≠ O) (h : N.angle A O B = 0) :
    B ∈ metricHalfLine O A := by
  obtain ⟨B₀, hB₀, -, huniq⟩ := N.axiomIIIa O A hA 0
  have hAm := huniq A hA (N.angle_self hA)
  have hBm := huniq B hB h
  rw [N.metricHalfLine_eq_of_mem hB₀.symm hAm hA]
  exact hBm

theorem angle_eq_zero_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.angle A O B = 0 ↔ B ∈ metricHalfLine O A :=
  ⟨N.mem_ray_of_angle_eq_zero hA hB, fun h => N.angle_eq_zero_of_mem_ray hA h hB⟩

/-- The point of `(OA)` opposite to `A` at the same distance from `O` makes a straight angle with `A`. -/
private theorem angle_opp_eq_pi {O A : P} (hA : A ≠ O) :
    N.angle A O (N.linePt O A (-dist O A)) = π := by
  have h : O ≠ A := hA.symm
  obtain ⟨r, hr⟩ : ∃ r, r = dist O A := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := hr ▸ dist_pos.2 h
  have hAr : N.linePt O A r = A := by rw [hr]; exact N.linePt_dist h
  have hA₂O : N.linePt O A (-r) ≠ O := N.linePt_ne_self h (by linarith)
  have hA₂m : N.linePt O A (-r) ∈ N.line O A := N.linePt_mem_line O A (-r)
  have hOA₂ : dist O (N.linePt O A (-r)) = r := by
    rw [N.dist_left_linePt h, abs_neg, abs_of_pos hr0]
  have hAA₂ : A ≠ N.linePt O A (-r) := by
    intro e
    have := N.linePt_injective h (show N.linePt O A r = N.linePt O A (-r) by rw [hAr]; exact e)
    linarith
  obtain ⟨α, hα⟩ : ∃ α, α = N.angle A O (N.linePt O A (-r)) := ⟨_, rfl⟩
  rw [← hα]
  have hα0 : α ≠ 0 := by
    intro h0
    have hm := N.mem_ray_of_angle_eq_zero hA hA₂O (hα.symm.trans h0)
    rw [N.metricHalfLine_eq_linePt h] at hm
    obtain ⟨s, hs, hse⟩ := hm
    have := N.linePt_injective h hse
    have hs' : 0 ≤ s := hs
    linarith
  obtain ⟨A', hA'O, hA'ang, -⟩ := N.axiomIIIa O (N.linePt O A (-r)) hA₂O α
  obtain ⟨A'', ⟨hA''m, hA''d⟩, -⟩ := N.existsUnique_mem_metricHalfLine_dist hA'O.symm hr0.le
  have hA''O : A'' ≠ O := by
    intro e
    rw [e, dist_self] at hA''d
    linarith
  have hA''ang : N.angle (N.linePt O A (-r)) O A'' = α := by
    rw [N.angle_ray_right hA₂O hA'O hA''m hA''O]
    exact hA'ang
  have hA₂A'' : N.linePt O A (-r) ≠ A'' := by
    intro e
    rw [← e, N.angle_self hA₂O] at hA''ang
    exact hα0 hA''ang.symm
  have hiv := (N.axiomIV O A (N.linePt O A (-r)) O (N.linePt O A (-r)) A'' h hAA₂ hA₂O hA₂O.symm
    hA₂A'' hA''O).2 ⟨by rw [hOA₂, hr], by rw [hA''d, hOA₂], Or.inl (by
      rw [N.angle_rev hA''O hA₂O, hA''ang, N.angle_rev hA₂O hA, ← hα])⟩
  obtain ⟨f, hfO, hfA, hfA₂⟩ := hiv
  have himg : f '' N.line O A = N.line O (N.linePt O A (-r)) :=
    N.eq_line (isLine_image (N.isLine_line h) f) ⟨O, N.left_mem_line O A, hfO⟩
      ⟨A, N.right_mem_line O A, hfA⟩ hA₂O.symm
  have hl2 : N.line O (N.linePt O A (-r)) = N.line O A :=
    N.line_eq_of_mem h (N.left_mem_line O A) hA₂m hA₂O.symm
  have hA''l : A'' ∈ N.line O A := by
    have : A'' ∈ f '' N.line O A := ⟨_, hA₂m, hfA₂⟩
    rw [himg, hl2] at this
    exact this
  obtain ⟨u, hu⟩ := N.exists_linePt_eq h hA''l
  rw [← hu, N.dist_left_linePt h] at hA''d
  rcases (abs_eq hr0.le).1 hA''d with hu' | hu'
  · have hA''A : A'' = A := by rw [← hu, hu', hAr]
    rw [hA''A] at hA''ang
    have h1 := N.angle_rev hA₂O hA
    rw [hA''ang, ← hα] at h1
    have h2 : α + α = 0 := by
      calc α + α = α + -α := by rw [← h1]
        _ = 0 := add_neg_cancel α
    have h3 : (2 : ℤ) • α = 0 := by rw [two_zsmul]; exact h2
    rcases Real.Angle.two_zsmul_eq_zero_iff.1 h3 with h4 | h4
    · exact absurd h4 hα0
    · exact h4
  · exfalso
    apply hA₂A''
    rw [← hu, hu']

/-- A straight angle `∡AOB` puts `B` on `(OA)` with `O` between `A` and `B`. -/
private theorem mem_line_of_angle_eq_pi {O A B : P} (hA : A ≠ O) (hB : B ≠ O) (h : N.angle A O B = π) :
    B ∈ N.line O A ∧ IsBetween A O B := by
  have hO : O ≠ A := hA.symm
  have hA₂ := N.angle_opp_eq_pi hA
  obtain ⟨r, hr⟩ : ∃ r, r = dist O A := ⟨_, rfl⟩
  rw [← hr] at hA₂
  have hr0 : 0 < r := hr ▸ dist_pos.2 hO
  have hA₂O : N.linePt O A (-r) ≠ O := N.linePt_ne_self hO (by linarith)
  obtain ⟨B₀, hB₀, -, huniq⟩ := N.axiomIIIa O A hA (π : Real.Angle)
  have h1 := huniq B hB h
  have h2 := huniq _ hA₂O hA₂
  have heq := N.metricHalfLine_eq_of_mem hB₀.symm h2 hA₂O
  rw [← heq] at h1
  have hl2 : N.line O (N.linePt O A (-r)) = N.line O A :=
    N.line_eq_of_mem hO (N.left_mem_line O A) (N.linePt_mem_line O A (-r)) hA₂O.symm
  have hBl : B ∈ N.line O A := by
    rw [← hl2]
    exact N.metricHalfLine_subset_line hA₂O.symm h1
  rcases N.mem_metricHalfLine_or_isBetween hO hBl with hm | hb
  · exact absurd (h.symm.trans (N.angle_eq_zero_of_mem_ray hA hm hB)) Real.Angle.pi_ne_zero
  · exact ⟨hBl, hb.symm⟩

/-- On a line, a point on the other side of `O` makes a straight angle. -/
private theorem angle_eq_pi_of_isBetween {O A B : P} (hA : A ≠ O) (hB : B ≠ O) (hBl : B ∈ N.line O A)
    (hbt : IsBetween A O B) : N.angle A O B = π := by
  have h : O ≠ A := hA.symm
  obtain ⟨t, rfl⟩ := N.exists_linePt_eq h hBl
  obtain ⟨r, hr⟩ : ∃ r, r = dist O A := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ dist_pos.2 h
  have hAr : N.linePt O A r = A := by rw [hr]; exact N.linePt_dist h
  have ht : t ≠ 0 := fun e => hB (by rw [e, linePt_zero])
  have ht0 : t < 0 := by
    have h1 := hbt.dist_add
    have h2 := N.dist_linePt h r t
    rw [hAr] at h2
    rw [dist_comm A O, ← hr, N.dist_left_linePt h, h2] at h1
    by_contra hneg
    have htp : 0 < t := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm ht)
    rw [abs_of_pos htp] at h1
    rcases abs_cases (r - t) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
  have hA₂ := N.angle_opp_eq_pi hA
  rw [← hr] at hA₂
  have hA₂O : N.linePt O A (-r) ≠ O := N.linePt_ne_self h (by linarith)
  have hmem := N.mem_half_neg h ht0 (show -r < 0 by linarith)
  rw [← N.angle_ray_right hA hB hmem hA₂O]
  exact hA₂

/-- **Theorem 2.7.** `∠AOB` is straight iff `O` lies between `A` and `B`. -/
@[kb "petrunin2025" "Theorem 2.7, p. 20"]
theorem angle_eq_pi_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    N.angle A O B = π ↔ IsBetween A O B := by
  constructor
  · intro h
    exact (N.mem_line_of_angle_eq_pi hA hB h).2
  · intro hbt
    have hl := N.mem_line_of_isBetween hbt
    have hAB : A ≠ B := hbt.ne
    have hBl : B ∈ N.line O A := by
      have : N.line A O = N.line A B := N.line_eq_of_mem hAB (N.left_mem_line A B) hl hA
      rw [N.line_comm O A, this]
      exact N.right_mem_line A B
    exact N.angle_eq_pi_of_isBetween hA hB hBl hbt

/-- **Corollary 2.8.** A triangle is degenerate iff its angle at a vertex is `0` or `π`. -/
@[kb "petrunin2025" "Corollary 2.8, p. 21"]
theorem degenerate_iff_angle {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    IsTriangle.Degenerate A O B ↔ N.angle A O B = 0 ∨ N.angle A O B = π := by
  constructor
  · intro hd
    have hB' : B ∈ N.line A O := (N.degenerate_iff_mem_line hA).1 hd
    rw [N.line_comm] at hB'
    rcases N.mem_metricHalfLine_or_isBetween hA.symm hB' with hm | hb
    · exact Or.inl (N.angle_eq_zero_of_mem_ray hA hm hB)
    · exact Or.inr (N.angle_eq_pi_of_isBetween hA hB hB' hb.symm)
  · intro h
    refine (N.degenerate_iff_mem_line hA).2 ?_
    rw [N.line_comm]
    rcases h with h | h
    · exact N.metricHalfLine_subset_line hA.symm (N.mem_ray_of_angle_eq_zero hA hB h)
    · exact (N.mem_line_of_angle_eq_pi hA hB h).1

theorem sign_angle_eq_zero_iff {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    (N.angle A O B).sign = 0 ↔ IsTriangle.Degenerate A O B := by
  rw [Real.Angle.sign_eq_zero_iff, N.degenerate_iff_angle hA hB]

/-- **Exercise 2.9.** `A, O, B` lie on one line iff `2·∡AOB = 0`. -/
@[kb "petrunin2025" "Exercise 2.9, p. 21"]
theorem degenerate_iff_two_zsmul {O A B : P} (hA : A ≠ O) (hB : B ≠ O) :
    IsTriangle.Degenerate A O B ↔ (2 : ℤ) • N.angle A O B = 0 := by
  rw [Real.Angle.two_zsmul_eq_zero_iff, N.degenerate_iff_angle hA hB]

/-- At a vertex `A` with `B ≠ A` there is a point `C` with a right angle `∡BAC`. -/
private theorem exists_right_angle {A B : P} (h : A ≠ B) :
    ∃ C, C ≠ A ∧ N.angle B A C = ((π / 2 : ℝ) : Real.Angle) := by
  obtain ⟨C, hC, hang, -⟩ := N.axiomIIIa A B h.symm ((π / 2 : ℝ) : Real.Angle)
  exact ⟨C, hC, hang⟩

private theorem right_angle_not (θ : Real.Angle) (h : θ = ((π / 2 : ℝ) : Real.Angle)) :
    ¬ (θ = 0 ∨ θ = π) := by
  intro h0
  have := Real.Angle.sign_eq_zero_iff.2 h0
  rw [h, Real.Angle.sign_coe_pi_div_two] at this
  exact one_ne_zero this

include N in
/-- **Exercise 2.11.** There is a nondegenerate triangle. -/
@[kb "petrunin2025" "Exercise 2.11, p. 22"]
theorem exists_nondegenerate : ∃ A B C : P, IsTriangle A B C ∧ ¬ IsTriangle.Degenerate A B C := by
  obtain ⟨A, B, hAB⟩ := N.axiomI
  obtain ⟨C, hCA, hang⟩ := N.exists_right_angle hAB
  have hCB : C ≠ B := by
    intro e
    rw [e, N.angle_self hAB.symm] at hang
    have := Real.Angle.sign_coe_pi_div_two
    rw [← hang, Real.Angle.sign_zero] at this
    exact zero_ne_one this
  refine ⟨B, A, C, ⟨hAB.symm, hCA.symm, hCB⟩, ?_⟩
  rw [N.degenerate_iff_angle hAB.symm hCA]
  exact right_angle_not _ hang

/-- Every line misses some point. -/
theorem exists_not_mem_line {A B : P} (h : A ≠ B) : ∃ C, C ∉ N.line A B := by
  obtain ⟨C, hCA, hang⟩ := N.exists_right_angle h
  refine ⟨C, fun hC => right_angle_not _ hang ?_⟩
  rw [← N.degenerate_iff_angle h.symm hCA]
  exact (N.degenerate_iff_mem_line h.symm).2 (by rw [N.line_comm]; exact hC)

/-- **Proposition 2.12.** Vertical angles have equal measures. -/
@[kb "petrunin2025" "Proposition 2.12, p. 22"]
theorem angle_vertical {O A B A' B' : P} (hA : IsBetween A O A') (hB : IsBetween B O B') :
    N.angle A O B = N.angle A' O B' := by
  have hAO : A ≠ O := hA.1.symm
  have hA'O : A' ≠ O := hA.2.1.symm
  have hBO : B ≠ O := hB.1.symm
  have hB'O : B' ≠ O := hB.2.1.symm
  have hAA := (N.angle_eq_pi_iff hAO hA'O).2 hA
  have hBB := (N.angle_eq_pi_iff hBO hB'O).2 hB
  have h1 := N.axiomIIIb O A B A' hAO hBO hA'O
  have h2 := N.axiomIIIb O B A' B' hBO hA'O hB'O
  have e : N.angle A O B + N.angle B O A' = N.angle A' O B' + N.angle B O A' := by
    rw [add_comm (N.angle A' O B') (N.angle B O A'), h1, h2, hAA, hBB]
  exact add_right_cancel e

/-! ### Reflection across a point (Section 2F) -/

include N in
/-- **Lemma 2.13.** For `X ≠ O` there is a unique `X'` with `O` the midpoint of `[XX']`. -/
@[kb "petrunin2025" "Lemma 2.13, p. 22"]
theorem existsUnique_midpoint_reflection {O X : P} (h : X ≠ O) :
    ∃! X', IsBetween X O X' ∧ dist O X' = dist O X := by
  have hO : O ≠ X := h.symm
  obtain ⟨d, hd⟩ : ∃ d, d = dist O X := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ dist_pos.2 hO
  have hXd : N.linePt O X d = X := by rw [hd]; exact N.linePt_dist hO
  have hdX : dist O (N.linePt O X (-d)) = d := by
    rw [N.dist_left_linePt hO, abs_neg, abs_of_pos hd0]
  refine ⟨N.linePt O X (-d), ⟨⟨hO, (N.linePt_ne_self hO (by linarith)).symm, ?_,
    ⟨N.line O X, N.isLine_line hO, N.right_mem_line O X, N.left_mem_line O X, N.linePt_mem_line O X (-d)⟩⟩,
    by rw [hdX, hd]⟩, ?_⟩
  · have h2 := N.dist_linePt hO d (-d)
    rw [hXd] at h2
    rw [dist_comm X O, ← hd, hdX, h2, abs_of_pos (by linarith)]
    ring
  · rintro Y ⟨hY, hYd⟩
    have hl := N.mem_line_of_isBetween hY
    have hXY : X ≠ Y := hY.ne
    have hYl : Y ∈ N.line O X := by
      have : N.line X O = N.line X Y := N.line_eq_of_mem hXY (N.left_mem_line X Y) hl h
      rw [N.line_comm O X, this]
      exact N.right_mem_line X Y
    obtain ⟨u, rfl⟩ := N.exists_linePt_eq hO hYl
    have h2 := N.dist_linePt hO d u
    rw [hXd] at h2
    have h3 := hY.dist_add
    rw [dist_comm X O, ← hd, hYd, ← hd, h2] at h3
    rw [N.dist_left_linePt hO, ← hd] at hYd
    rcases (abs_eq hd0.le).1 hYd with hu | hu
    · rw [hu, sub_self, abs_zero] at h3
      linarith
    · rw [hu]

/-- The reflection across `O` as a plain map (`O ↦ O`). -/
noncomputable def pointReflFun (O X : P) : P :=
  if h : X ≠ O then Classical.choose (N.existsUnique_midpoint_reflection h).exists else O

theorem pointReflFun_self (O : P) : N.pointReflFun O O = O := by
  unfold pointReflFun
  rw [dif_neg (not_not.2 rfl)]

private theorem pointReflFun_spec {O X : P} (h : X ≠ O) :
    IsBetween X O (N.pointReflFun O X) ∧ dist O (N.pointReflFun O X) = dist O X := by
  unfold pointReflFun
  rw [dif_pos h]
  exact Classical.choose_spec (N.existsUnique_midpoint_reflection h).exists

theorem isBetween_pointReflFun {O X : P} (h : X ≠ O) : IsBetween X O (N.pointReflFun O X) :=
  (N.pointReflFun_spec h).1

theorem dist_pointReflFun (O X : P) : dist O (N.pointReflFun O X) = dist O X := by
  by_cases h : X = O
  · rw [h, pointReflFun_self]
  · exact (N.pointReflFun_spec h).2

theorem pointReflFun_pointReflFun (O X : P) : N.pointReflFun O (N.pointReflFun O X) = X := by
  by_cases h : X = O
  · rw [h, pointReflFun_self, pointReflFun_self]
  · have hb := N.pointReflFun_spec h
    have hY : N.pointReflFun O X ≠ O := hb.1.2.1.symm
    exact (N.existsUnique_midpoint_reflection hY).unique (N.pointReflFun_spec hY)
      ⟨hb.1.symm, hb.2.symm⟩

theorem dist_pointReflFun_pointReflFun (O X Y : P) :
    dist (N.pointReflFun O X) (N.pointReflFun O Y) = dist X Y := by
  by_cases hX : X = O
  · rw [hX, pointReflFun_self]
    exact N.dist_pointReflFun O Y
  by_cases hY : Y = O
  · rw [hY, pointReflFun_self, dist_comm, N.dist_pointReflFun, dist_comm]
  by_cases hXY : X = Y
  · rw [hXY, dist_self, dist_self]
  have hbX := N.isBetween_pointReflFun hX
  have hbY := N.isBetween_pointReflFun hY
  have hdX := N.dist_pointReflFun O X
  have hdY := N.dist_pointReflFun O Y
  have hne : N.pointReflFun O X ≠ N.pointReflFun O Y := by
    intro e
    apply hXY
    have := congrArg (N.pointReflFun O) e
    rwa [N.pointReflFun_pointReflFun, N.pointReflFun_pointReflFun] at this
  have hvert := N.angle_vertical hbY hbX
  have hiv := (N.axiomIV O X Y O (N.pointReflFun O X) (N.pointReflFun O Y) (Ne.symm hX) hXY hY
    hbX.2.1 hne hbY.2.1.symm).2 ⟨hdX, hdY, Or.inl hvert.symm⟩
  obtain ⟨f, -, hfX, hfY⟩ := hiv
  rw [← hfX, ← hfY]
  exact f.dist_eq X Y

/-- **Proposition 2.14.** The reflection across a point is a motion of the plane. -/
@[kb "petrunin2025" "Proposition 2.14, p. 23"]
noncomputable def pointRefl (O : P) : P ≃ᵢ P where
  toFun := N.pointReflFun O
  invFun := N.pointReflFun O
  left_inv X := N.pointReflFun_pointReflFun O X
  right_inv X := N.pointReflFun_pointReflFun O X
  isometry_toFun := Isometry.of_dist_eq fun X Y => N.dist_pointReflFun_pointReflFun O X Y

theorem pointRefl_apply (O X : P) : N.pointRefl O X = N.pointReflFun O X := rfl

/-- The reflection across `O` is characterized by `O` being the midpoint. -/
theorem pointRefl_eq_of_isBetween {O X Y : P} (h : IsBetween X O Y) (hd : dist O Y = dist O X) :
    N.pointRefl O X = Y := by
  rw [pointRefl_apply]
  have hX : X ≠ O := h.1.symm
  exact (N.existsUnique_midpoint_reflection hX).unique (N.pointReflFun_spec hX) ⟨h, hd⟩

end NeutralPlane

end Neutral

end UndergradKB.Geometry
