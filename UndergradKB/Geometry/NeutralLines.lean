import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Geometry.Neutral
import UndergradKB.Common.Attr

/-! # Neutral plane I: lines, half-lines and angles (Petrunin, Chapters 1-2)

Everything here is derived from Axioms I-IV of the structure `NeutralPlane` (the results the book marks
with a check mark: they hold in every neutral plane). Notation:

* `IsBetween A B C`: `B` lies between `A` and `C` (`B ≠ A`, `B ≠ C`, `AB + BC = AC`);
* `N.line A B`: the line `(AB)` of Axiom II, and `N.linePt A B t`: its point at signed distance `t` from
  `A` (positive towards `B`), an isometric parametrization `ℝ → (AB)`;
* `metricHalfLine O A`: the half-line `[OA)`.

A subtle point: the structure `NeutralPlane` gives the angle measure as a function of three points, while the
book's angle measure is a function of the angle, i.e. of the two half-lines. That the measure depends only on
the half-lines (`NeutralPlane.angle_eq_zero_of_mem_ray`) is derived from Axioms III and IV: a motion fixing
the line `(OA)` pointwise gives `2·∡AOB = 0` for `B ∈ [OA)`, and continuity (Axiom IIIc) excludes `π`. -/

namespace UndergradKB.Geometry

open Real

section Metric

variable {P : Type*} [MetricSpace P]

/-- `B` lies between `A` and `C` (Section 2D, p. 20): `B ≠ A`, `B ≠ C` and `B ∈ [AC]`, i.e. `A, B, C` lie
on one line and `AB + BC = AC`. (By Corollary 4.5, `NeutralPlane.mem_line_of_dist_add`, the metric condition
alone already puts `B` on `(AC)` in a neutral plane; the book's definition is the segment of the line.) -/
@[kb "petrunin2025" "Between, Section 2D, p. 20"]
def IsBetween (A B C : P) : Prop :=
  B ≠ A ∧ B ≠ C ∧ dist A B + dist B C = dist A C ∧ IsTriangle.Degenerate A B C

theorem IsBetween.dist_add {A B C : P} (h : IsBetween A B C) : dist A B + dist B C = dist A C := h.2.2.1

theorem IsBetween.degenerate {A B C : P} (h : IsBetween A B C) : IsTriangle.Degenerate A B C := h.2.2.2

theorem IsBetween.symm {A B C : P} (h : IsBetween A B C) : IsBetween C B A := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h.degenerate
  refine ⟨h.2.1, h.1, ?_, ⟨L, hL, hC, hB, hA⟩⟩
  rw [dist_comm C B, dist_comm B A, dist_comm C A]
  linarith [h.dist_add]

theorem IsBetween.ne {A B C : P} (h : IsBetween A B C) : A ≠ C := by
  intro e
  subst e
  have h1 := h.dist_add
  rw [dist_self, dist_comm B A] at h1
  have := dist_pos.2 h.1.symm
  linarith

theorem IsBetween.dist_lt_left {A B C : P} (h : IsBetween A B C) : dist A B < dist A C := by
  have := dist_pos.2 h.2.1
  linarith [h.dist_add]

theorem IsBetween.dist_lt_right {A B C : P} (h : IsBetween A B C) : dist B C < dist A C := by
  have := dist_pos.2 h.1.symm
  linarith [h.dist_add]

/-- A line has an isometric parametrization sending `0` to any given point `A` of it and
`dist A B` to any other given point `B` of it. -/
theorem IsLine.exists_isometry {L : Set P} (hL : IsLine L) {A B : P} (hA : A ∈ L) (hB : B ∈ L) :
    ∃ f : ℝ → P, Isometry f ∧ Set.range f = L ∧ f 0 = A ∧ f (dist A B) = B := by
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  have hd : dist (g a) (g b) = |a - b| := by rw [hg.dist_eq, Real.dist_eq]
  by_cases hab : a ≤ b
  · have hb : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    refine ⟨fun t => g (a + t), Isometry.of_dist_eq fun x y => ?_, ?_, by simp, ?_⟩
    · rw [hg.dist_eq, Real.dist_eq, Real.dist_eq, show a + x - (a + y) = x - y by ring]
    · ext X
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨a + t, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨s - a, by simp⟩
    · simp only [hd, hb]
      congr 1
      ring
  · have hb : |a - b| = a - b := abs_of_nonneg (by linarith)
    refine ⟨fun t => g (a - t), Isometry.of_dist_eq fun x y => ?_, ?_, by simp, ?_⟩
    · rw [hg.dist_eq, Real.dist_eq, Real.dist_eq, show a - x - (a - y) = -(x - y) by ring, abs_neg]
    · ext X
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨a - t, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨a - s, by simp⟩
    · simp only [hd, hb]
      congr 1
      ring

/-- A point of a line is determined by its distances to two distinct points of the line. -/
theorem IsLine.eq_of_dist_eq {L : Set P} (hL : IsLine L) {A B X Y : P} (hA : A ∈ L) (hB : B ∈ L)
    (hX : X ∈ L) (hY : Y ∈ L) (hAB : A ≠ B) (h₁ : dist A X = dist A Y) (h₂ : dist B X = dist B Y) :
    X = Y := by
  obtain ⟨f, hf, rfl⟩ := hL
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨x, rfl⟩ := hX
  obtain ⟨y, rfl⟩ := hY
  have hab : a ≠ b := fun e => hAB (by rw [e])
  rw [hf.dist_eq, hf.dist_eq, Real.dist_eq, Real.dist_eq] at h₁ h₂
  have hxy : x = y := by
    rcases abs_eq_abs.1 h₁ with h | h
    · linarith
    · rcases abs_eq_abs.1 h₂ with h' | h'
      · linarith
      · exact absurd (by linarith) hab
  rw [hxy]

/-- Of three distinct points of a line, one lies between the other two. -/
theorem IsLine.isBetween_trichotomy {L : Set P} (hL : IsLine L) {A B C : P} (hA : A ∈ L) (hB : B ∈ L)
    (hC : C ∈ L) (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    IsBetween B A C ∨ IsBetween A B C ∨ IsBetween A C B := by
  obtain ⟨f, hf, rfl⟩ := hL
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  have hab : a ≠ b := fun e => hAB (by rw [e])
  have hbc : b ≠ c := fun e => hBC (by rw [e])
  have hca : c ≠ a := fun e => hCA (by rw [e])
  have key : ∀ {a b c : ℝ}, (a < b ∧ b < c) ∨ (c < b ∧ b < a) → IsBetween (f a) (f b) (f c) := by
    intro a b c h
    have hd : ∀ x y : ℝ, dist (f x) (f y) = |x - y| := fun x y => by rw [hf.dist_eq, Real.dist_eq]
    refine ⟨fun e => ?_, fun e => ?_, ?_, ⟨Set.range f, ⟨f, hf, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩⟩
    · have := hf.injective e
      rcases h with h | h <;> linarith [h.1, h.2]
    · have := hf.injective e
      rcases h with h | h <;> linarith [h.1, h.2]
    · rw [hd, hd, hd]
      rcases h with h | h
      · rw [abs_sub_comm a b, abs_sub_comm b c, abs_sub_comm a c, abs_of_nonneg (by linarith : 0 ≤ b - a),
          abs_of_nonneg (by linarith : 0 ≤ c - b), abs_of_nonneg (by linarith : 0 ≤ c - a)]
        ring
      · rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_of_nonneg (by linarith : 0 ≤ b - c),
          abs_of_nonneg (by linarith : 0 ≤ a - c)]
        ring
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hca with h3 | h3
  all_goals first
    | (exfalso; linarith)
    | (apply Or.inl; apply key; left; constructor <;> linarith)
    | (apply Or.inl; apply key; right; constructor <;> linarith)
    | (apply Or.inr; apply Or.inl; apply key; left; constructor <;> linarith)
    | (apply Or.inr; apply Or.inl; apply key; right; constructor <;> linarith)
    | (apply Or.inr; apply Or.inr; apply key; left; constructor <;> linarith)
    | (apply Or.inr; apply Or.inr; apply key; right; constructor <;> linarith)

/-- Real-line fact: a number is determined by `|s|` and `|q - s|` when `q > 0`. -/
private theorem eq_of_abs_eq_abs {q s t : ℝ} (hq : 0 < q) (h1 : |s| = |t|) (h2 : |q - s| = |q - t|) :
    s = t := by
  rcases abs_eq_abs.1 h1 with h | h
  · exact h
  · rcases abs_eq_abs.1 h2 with h' | h'
    · linarith
    · linarith

end Metric

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

open Classical

/-! ### Lines -/

/-- The line `(AB)` through two distinct points (Axiom II). For `A = B` it is `{A}` (never used). -/
noncomputable def line (A B : P) : Set P :=
  if h : A ≠ B then Classical.choose (N.axiomII A B h).exists else {A}

private theorem line_spec {A B : P} (h : A ≠ B) :
    IsLine (N.line A B) ∧ A ∈ N.line A B ∧ B ∈ N.line A B := by
  have := Classical.choose_spec (N.axiomII A B h).exists
  simpa only [line, dif_pos h] using this

theorem isLine_line {A B : P} (h : A ≠ B) : IsLine (N.line A B) := (N.line_spec h).1

theorem left_mem_line (A B : P) : A ∈ N.line A B := by
  by_cases h : A = B
  · subst h
    simp [line]
  · exact (N.line_spec h).2.1

theorem right_mem_line (A B : P) : B ∈ N.line A B := by
  by_cases h : A = B
  · subst h
    simp [line]
  · exact (N.line_spec h).2.2

/-- Axiom II, uniqueness: a line through two distinct points `A`, `B` is `(AB)`. -/
theorem eq_line {L : Set P} (hL : IsLine L) {A B : P} (hA : A ∈ L) (hB : B ∈ L) (h : A ≠ B) :
    L = N.line A B :=
  (N.axiomII A B h).unique ⟨hL, hA, hB⟩ (N.line_spec h)

theorem line_comm (A B : P) : N.line A B = N.line B A := by
  by_cases h : A = B
  · subst h
    rfl
  · exact (N.eq_line (N.isLine_line h) (N.right_mem_line A B) (N.left_mem_line A B) (fun e => h e.symm))

/-- Two distinct points of `(AB)` span the same line. -/
theorem line_eq_of_mem {A B X Y : P} (hAB : A ≠ B) (hX : X ∈ N.line A B) (hY : Y ∈ N.line A B)
    (hXY : X ≠ Y) : N.line X Y = N.line A B :=
  (N.eq_line (N.isLine_line hAB) hX hY hXY).symm

include N in
/-- **Proposition 2.2.** Two distinct lines meet in at most one point. -/
@[kb "petrunin2025" "Proposition 2.2, p. 20"]
theorem eq_of_mem_line_of_mem_line {L M : Set P} (hL : IsLine L) (hM : IsLine M) (hLM : L ≠ M)
    {X Y : P} (hXL : X ∈ L) (hXM : X ∈ M) (hYL : Y ∈ L) (hYM : Y ∈ M) : X = Y := by
  by_contra hXY
  exact hLM ((N.eq_line hL hXL hYL hXY).trans (N.eq_line hM hXM hYM hXY).symm)

/-- A triple with `A ≠ B` is degenerate iff the third point is on `(AB)`. -/
theorem degenerate_iff_mem_line {A B C : P} (h : A ≠ B) :
    IsTriangle.Degenerate A B C ↔ C ∈ N.line A B := by
  constructor
  · rintro ⟨L, hL, hA, hB, hC⟩
    rw [← N.eq_line hL hA hB h]
    exact hC
  · intro hC
    exact ⟨N.line A B, N.isLine_line h, N.left_mem_line A B, N.right_mem_line A B, hC⟩

/-- If `B` lies between `A` and `C` then `B ∈ (AC)`. -/
theorem mem_line_of_isBetween {A B C : P} (h : IsBetween A B C) : B ∈ N.line A C := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h.degenerate
  rw [← N.eq_line hL hA hC h.ne]
  exact hB

/-- A point `B ≠ A, C` of `(AC)` closer to each end than the ends are to each other lies between them. -/
theorem isBetween_of_mem_line {A B C : P} (hAC : A ≠ C) (hB : B ∈ N.line A C) (hBA : B ≠ A) (hBC : B ≠ C)
    (h : dist A B < dist A C) (h' : dist B C < dist A C) : IsBetween A B C := by
  have hdeg : IsTriangle.Degenerate A B C :=
    ⟨N.line A C, N.isLine_line hAC, N.left_mem_line A C, hB, N.right_mem_line A C⟩
  obtain ⟨f, hf, hr, hf0, hfq⟩ :=
    IsLine.exists_isometry (N.isLine_line hAC) (N.left_mem_line A C) (N.right_mem_line A C)
  rw [← hr] at hB
  obtain ⟨t, rfl⟩ := hB
  have hd : ∀ x y : ℝ, dist (f x) (f y) = |x - y| := fun x y => by rw [hf.dist_eq, Real.dist_eq]
  set q := dist A C with hq
  have h1 : dist A (f t) = |t| := by
    rw [← hf0, hd, zero_sub, abs_neg]
  have h2 : dist (f t) C = |t - q| := by
    rw [← hfq, hd]
  have hqpos : 0 < q := dist_pos.2 hAC
  refine ⟨hBA, hBC, ?_, hdeg⟩
  rw [h1, h2]
  rw [h1] at h
  rw [h2] at h'
  have h3 := (abs_lt.1 h)
  have h4 := (abs_lt.1 h')
  rw [abs_of_nonneg (by linarith : 0 ≤ t), abs_of_nonpos (by linarith : t - q ≤ 0)]
  ring

/-! ### The isometric parametrization of a line -/

/-- `N.linePt A B t`: the point of `(AB)` at signed distance `t` from `A`, positive towards `B`. -/
noncomputable def linePt (A B : P) (t : ℝ) : P :=
  if h : A ≠ B then
    Classical.choose (IsLine.exists_isometry (N.isLine_line h) (N.left_mem_line A B)
      (N.right_mem_line A B)) t
  else A

private theorem linePt_spec {A B : P} (h : A ≠ B) :
    Isometry (N.linePt A B) ∧ Set.range (N.linePt A B) = N.line A B ∧ N.linePt A B 0 = A ∧
      N.linePt A B (dist A B) = B := by
  have e : N.linePt A B = Classical.choose (IsLine.exists_isometry (N.isLine_line h)
      (N.left_mem_line A B) (N.right_mem_line A B)) := by
    funext t
    unfold linePt
    rw [dif_pos h]
  rw [e]
  exact Classical.choose_spec (IsLine.exists_isometry (N.isLine_line h) (N.left_mem_line A B)
      (N.right_mem_line A B))

theorem isometry_linePt {A B : P} (h : A ≠ B) : Isometry (N.linePt A B) := (N.linePt_spec h).1

theorem range_linePt {A B : P} (h : A ≠ B) : Set.range (N.linePt A B) = N.line A B :=
  (N.linePt_spec h).2.1

@[simp] theorem linePt_zero (A B : P) : N.linePt A B 0 = A := by
  by_cases h : A = B
  · subst h
    simp [linePt]
  · exact (N.linePt_spec h).2.2.1

theorem linePt_dist {A B : P} (h : A ≠ B) : N.linePt A B (dist A B) = B := (N.linePt_spec h).2.2.2

theorem dist_linePt {A B : P} (h : A ≠ B) (s t : ℝ) :
    dist (N.linePt A B s) (N.linePt A B t) = |s - t| := by
  rw [(N.isometry_linePt h).dist_eq, Real.dist_eq]

theorem dist_left_linePt {A B : P} (h : A ≠ B) (t : ℝ) : dist A (N.linePt A B t) = |t| := by
  have := N.dist_linePt h 0 t
  rw [linePt_zero] at this
  rw [this, zero_sub, abs_neg]

theorem linePt_mem_line (A B : P) (t : ℝ) : N.linePt A B t ∈ N.line A B := by
  by_cases h : A = B
  · subst h
    have : N.linePt A A t = A := by simp [linePt]
    rw [this]
    exact N.left_mem_line A A
  · rw [← N.range_linePt h]
    exact ⟨t, rfl⟩

theorem exists_linePt_eq {A B X : P} (h : A ≠ B) (hX : X ∈ N.line A B) : ∃ t, N.linePt A B t = X := by
  rw [← N.range_linePt h] at hX
  exact hX

theorem linePt_injective {A B : P} (h : A ≠ B) : Function.Injective (N.linePt A B) :=
  (N.isometry_linePt h).injective

theorem continuous_linePt {A B : P} (h : A ≠ B) : Continuous (N.linePt A B) :=
  (N.isometry_linePt h).continuous

/-! ### Half-lines -/

/-- An isometry agreeing with `linePt O A` at `0` and at one positive time agrees everywhere. -/
private theorem isometry_eq_linePt {O A : P} (h : O ≠ A) {f : ℝ → P} (hf : Isometry f) (hf0 : f 0 = O)
    {q : ℝ} (hq : 0 < q) (hfq : f q = N.linePt O A q) (t : ℝ) : f t = N.linePt O A t := by
  have hne : O ≠ N.linePt O A q := by
    intro e
    have := N.linePt_injective h (show N.linePt O A 0 = N.linePt O A q by rw [linePt_zero]; exact e)
    linarith
  have hOm : O ∈ N.line O A := N.left_mem_line O A
  have hqm : N.linePt O A q ∈ N.line O A := N.linePt_mem_line O A q
  have hrange : Set.range f = N.line O A := by
    rw [N.eq_line (L := Set.range f) ⟨f, hf, rfl⟩ ⟨0, hf0⟩ ⟨q, hfq⟩ hne]
    exact N.line_eq_of_mem h hOm hqm hne
  have hft : f t ∈ N.line O A := by
    rw [← hrange]
    exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := N.exists_linePt_eq h hft
  have hd1 : dist O (f t) = |t| := by
    rw [← hf0, hf.dist_eq, Real.dist_eq, zero_sub, abs_neg]
  have hd2 : dist (N.linePt O A q) (f t) = |q - t| := by
    rw [← hfq, hf.dist_eq, Real.dist_eq]
  rw [← hs] at hd1 hd2
  rw [N.dist_left_linePt h] at hd1
  rw [N.dist_linePt h] at hd2
  rw [← hs]
  congr 1
  exact eq_of_abs_eq_abs hq hd1 hd2

theorem metricHalfLine_eq_linePt {O A : P} (h : O ≠ A) :
    metricHalfLine O A = N.linePt O A '' Set.Ici 0 := by
  ext X
  constructor
  · rintro ⟨f, hf, hf0, ⟨q, hq, hfq⟩, t, ht, rfl⟩
    have hqd : q = dist O A := by
      rw [← hf0, ← hfq, hf.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hq]
    refine ⟨t, ht, ?_⟩
    symm
    refine N.isometry_eq_linePt h hf hf0 hq ?_ t
    rw [hfq, hqd, N.linePt_dist h]
  · rintro ⟨t, ht, rfl⟩
    exact ⟨N.linePt O A, N.isometry_linePt h, N.linePt_zero O A,
      ⟨dist O A, dist_pos.2 h, N.linePt_dist h⟩, t, ht, rfl⟩

include N in
theorem self_mem_metricHalfLine {O A : P} (h : O ≠ A) : A ∈ metricHalfLine O A := by
  rw [N.metricHalfLine_eq_linePt h]
  exact ⟨dist O A, dist_nonneg, N.linePt_dist h⟩

include N in
theorem left_mem_metricHalfLine {O A : P} (h : O ≠ A) : O ∈ metricHalfLine O A := by
  rw [N.metricHalfLine_eq_linePt h]
  exact ⟨0, Set.mem_Ici.2 le_rfl, N.linePt_zero O A⟩

theorem metricHalfLine_subset_line {O A : P} (h : O ≠ A) : metricHalfLine O A ⊆ N.line O A := by
  rw [N.metricHalfLine_eq_linePt h]
  rintro _ ⟨t, _, rfl⟩
  exact N.linePt_mem_line O A t

include N in
/-- **Exercise 1.12.** A half-line has exactly one point at each distance `t ≥ 0` from its vertex. -/
@[kb "petrunin2025" "Exercise 1.12, p. 14"]
theorem existsUnique_mem_metricHalfLine_dist {O A : P} (h : O ≠ A) {t : ℝ} (ht : 0 ≤ t) :
    ∃! X, X ∈ metricHalfLine O A ∧ dist O X = t := by
  refine ⟨N.linePt O A t, ⟨?_, ?_⟩, ?_⟩
  · rw [N.metricHalfLine_eq_linePt h]
    exact ⟨t, ht, rfl⟩
  · rw [N.dist_left_linePt h, abs_of_nonneg ht]
  · rintro X ⟨hX, hd⟩
    rw [N.metricHalfLine_eq_linePt h] at hX
    obtain ⟨s, hs, rfl⟩ := hX
    rw [N.dist_left_linePt h, abs_of_nonneg hs] at hd
    rw [hd]

include N in
/-- **Exercise 2.3.** If `A' ∈ [OA)` and `A' ≠ O` then `[OA) = [OA')`. -/
@[kb "petrunin2025" "Exercise 2.3, p. 20"]
theorem metricHalfLine_eq_of_mem {O A A' : P} (h : O ≠ A) (hA' : A' ∈ metricHalfLine O A)
    (hA'O : A' ≠ O) : metricHalfLine O A' = metricHalfLine O A := by
  rw [N.metricHalfLine_eq_linePt h] at hA'
  obtain ⟨s, hs, rfl⟩ := hA'
  have hs : 0 ≤ s := hs
  have hs0 : 0 < s := by
    rcases hs.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      apply hA'O
      rw [← h1]
      exact N.linePt_zero O A
  have hne : O ≠ N.linePt O A s := hA'O.symm
  ext X
  constructor
  · rintro ⟨f, hf, hf0, ⟨q, hq, hfq⟩, t, ht, rfl⟩
    have hqd : q = s := by
      have h1 : dist O (N.linePt O A s) = s := by
        rw [N.dist_left_linePt h, abs_of_pos hs0]
      have h3 := hf.dist_eq 0 q
      rw [hf0, hfq, h1, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hq] at h3
      exact h3.symm
    have := N.isometry_eq_linePt h hf hf0 hq (by rw [hfq, hqd]) t
    rw [this, N.metricHalfLine_eq_linePt h]
    exact ⟨t, ht, rfl⟩
  · intro hX
    rw [N.metricHalfLine_eq_linePt h] at hX
    obtain ⟨t, ht, rfl⟩ := hX
    have ht : 0 ≤ t := ht
    exact ⟨N.linePt O A, N.isometry_linePt h, N.linePt_zero O A, ⟨s, hs0, rfl⟩, t, ht, rfl⟩

/-- A point of `(OA)` is on `[OA)` or `O` lies between it and `A` (and conversely, see
`mem_line_of_isBetween`). -/
theorem mem_metricHalfLine_or_isBetween {O A X : P} (h : O ≠ A) (hX : X ∈ N.line O A) :
    X ∈ metricHalfLine O A ∨ IsBetween X O A := by
  · obtain ⟨t, rfl⟩ := N.exists_linePt_eq h hX
    rcases le_or_gt 0 t with ht | ht
    · left
      rw [N.metricHalfLine_eq_linePt h]
      exact ⟨t, ht, rfl⟩
    · right
      have hA : N.linePt O A (dist O A) = A := N.linePt_dist h
      have hq := dist_pos.2 h
      refine ⟨?_, h, ?_, ⟨N.line O A, N.isLine_line h, hX, N.left_mem_line O A, N.right_mem_line O A⟩⟩
      · intro e
        have := N.linePt_injective h (show N.linePt O A t = N.linePt O A 0 by rw [linePt_zero]; exact e.symm)
        linarith
      · have h2 := N.dist_linePt h t (dist O A)
        rw [hA] at h2
        rw [dist_comm (N.linePt O A t) O, N.dist_left_linePt h, h2, abs_of_neg ht,
          abs_of_nonpos (by linarith)]
        ring

include N in
/-- A point `X ≠ O` of `[OA)`: `A` and `X` are not separated by `O`, i.e. `AX = |OA - OX|`. -/
theorem dist_of_mem_metricHalfLine {O A X : P} (h : O ≠ A) (hX : X ∈ metricHalfLine O A) :
    dist A X = |dist O A - dist O X| := by
  rw [N.metricHalfLine_eq_linePt h] at hX
  obtain ⟨t, ht, rfl⟩ := hX
  have ht : 0 ≤ t := ht
  have hA : N.linePt O A (dist O A) = A := N.linePt_dist h
  have h2 := N.dist_linePt h (dist O A) t
  rw [hA] at h2
  rw [h2, N.dist_left_linePt h, abs_of_nonneg ht]

end NeutralPlane

end Neutral

end UndergradKB.Geometry
