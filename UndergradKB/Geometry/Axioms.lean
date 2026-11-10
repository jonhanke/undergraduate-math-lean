import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import UndergradKB.Common.Attr

/-! # The book's formulation of the axioms (Petrunin, chapters 1-3, 5-7)

A *line* in the sense of Definition 1.9 is a subset of a metric space isometric to the real line
(`IsLine`); in a strictly convex normed space these are exactly the affine lines (GE-010), and
Axiom II holds in this form (GE-024). We also treat half-lines and segments (p. 13), Exercise 1.11,
Axioms III(a) and V (p. 19), Corollary 3.5, Classroom exercise 3.8, Exercises 5.17 and 7.24,
Ptolemy's inequality 6.12, and the Manhattan-plane example of Section 1J (p. 17). -/

namespace UndergradKB.Geometry

open EuclideanGeometry AffineSubspace AffineMap

section Lines

/-- A subset of a metric space is a *line* in the book's sense (Definition 1.9) if it is the image of
an isometry `ℝ → P`, i.e. it is isometric to the real line. -/
def IsLine {P : Type*} [MetricSpace P] (S : Set P) : Prop :=
  ∃ f : ℝ → P, Isometry f ∧ Set.range f = S

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

private lemma isometry_apply_of_one_lt {f : ℝ → P} (hf : Isometry f) {t : ℝ} (ht : 1 < t) :
    f t = lineMap (f 0) (f 1) t := by
  have hd : ∀ s u, dist (f s) (f u) = |s - u| := fun s u => by rw [hf.dist_eq, Real.dist_eq]
  have ht0 : 0 < t := by linarith
  have h := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (x := f 0) (y := f 1) (z := f t) (r := 1 / t)
    (by rw [hd, hd]; simp [abs_of_pos ht0]; field_simp)
    (by
      rw [hd, hd, abs_of_neg (by linarith), abs_of_neg (by linarith)]
      field_simp; ring)
  rw [h, lineMap_apply, lineMap_apply]
  simp [smul_smul, ht0.ne']

/-- An isometry `ℝ → P` into a strictly convex space is the affine map through its values at `0`
and `1`. -/
theorem isometry_apply_eq_lineMap {f : ℝ → P} (hf : Isometry f) (t : ℝ) :
    f t = lineMap (f 0) (f 1) t := by
  have hd : ∀ s u, dist (f s) (f u) = |s - u| := fun s u => by rw [hf.dist_eq, Real.dist_eq]
  rcases lt_trichotomy t 0 with h | h | h
  · have hg : Isometry (fun s => f (1 - s)) := Isometry.of_dist_eq fun a b => by
      have : (1 - a) - (1 - b) = -(a - b) := by ring
      rw [hd, Real.dist_eq, this, abs_neg]
    have := isometry_apply_of_one_lt hg (t := 1 - t) (by linarith)
    simp only [sub_sub_cancel, sub_zero, sub_self] at this
    rw [this, lineMap_apply_one_sub]
  · subst h; simp
  · rcases le_or_gt t 1 with h1 | h1
    · apply (eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (x := f 0) (y := f t) (z := f 1) (r := t) ?_ ?_)
      · rw [hd, hd, abs_of_nonpos (by linarith)]
        rw [abs_of_neg (by linarith)]; ring
      · rw [hd, hd, abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; ring
    · exact isometry_apply_of_one_lt hf h1

/-- **Definition 1.9 / Axiom II (p. 12, 19), GE-010.** In a strictly convex normed space (e.g. the
Euclidean plane), a subset is isometric to `ℝ` iff it is an affine line `line[ℝ, A, B]` with
`A ≠ B`. -/
@[kb "petrunin2025" "Definition 1.9, p. 12"]
theorem isLine_iff_exists_affineSpan {S : Set P} :
    IsLine S ↔ ∃ A B : P, A ≠ B ∧ S = (line[ℝ, A, B] : Set P) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f 0, f 1, fun h => zero_ne_one (hf.injective h), ?_⟩
    ext X
    constructor
    · rintro ⟨t, rfl⟩
      rw [isometry_apply_eq_lineMap (V := V) hf t]
      exact AffineMap.lineMap_mem_affineSpan_pair t (f 0) (f 1)
    · intro hX
      obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hX
      exact ⟨r, isometry_apply_eq_lineMap (V := V) hf r⟩
  · rintro ⟨A, B, hAB, rfl⟩
    have hd : 0 < dist A B := dist_pos.2 hAB
    refine ⟨fun t => lineMap A B (t / dist A B), ?_, ?_⟩
    · refine Isometry.of_dist_eq fun s u => ?_
      rw [dist_lineMap_lineMap, Real.dist_eq, Real.dist_eq, ← sub_div, abs_div,
        abs_of_pos hd]
      field_simp
    · ext X
      constructor
      · rintro ⟨t, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair _ A B
      · intro hX
        obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hX
        exact ⟨r * dist A B, by simp [hd.ne']⟩

omit [StrictConvexSpace ℝ V] in
private lemma affineSpan_pair_eq_of_mem {A B C D : P} (hAB : A ≠ B)
    (hA : A ∈ line[ℝ, C, D]) (hB : B ∈ line[ℝ, C, D]) (hCD : C ≠ D) :
    line[ℝ, A, B] = line[ℝ, C, D] := by
  obtain ⟨a, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hA
  obtain ⟨b, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hB
  have hcol : Collinear ℝ ({C, D, lineMap C D a, lineMap C D b} : Set P) := by
    rw [collinear_iff_of_mem (p₀ := C) (by simp)]
    refine ⟨D -ᵥ C, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨a, by rw [lineMap_apply]⟩
    · exact ⟨b, by rw [lineMap_apply]⟩
  have h1 := hcol.affineSpan_eq_of_ne (p₁ := lineMap C D a) (p₂ := lineMap C D b)
    (by simp) (by simp) hAB
  have h2 := hcol.affineSpan_eq_of_ne (p₁ := C) (p₂ := D) (by simp) (by simp) hCD
  rw [h1, h2]

include V in
/-- **Axiom II (p. 19), GE-024, in the book's terms.** Any two distinct points lie on exactly one
subset isometric to the real line. -/
@[kb "petrunin2025" "Axiom II, p. 19"]
theorem existsUnique_isLine {A B : P} (hAB : A ≠ B) :
    ∃! S : Set P, IsLine S ∧ A ∈ S ∧ B ∈ S := by
  refine ⟨(line[ℝ, A, B] : Set P),
    ⟨isLine_iff_exists_affineSpan.2 ⟨A, B, hAB, rfl⟩, left_mem_affineSpan_pair ℝ A B,
      right_mem_affineSpan_pair ℝ A B⟩, ?_⟩
  rintro S ⟨hS, hA, hB⟩
  obtain ⟨C, D, hCD, rfl⟩ := isLine_iff_exists_affineSpan.1 hS
  rw [← affineSpan_pair_eq_of_mem hAB hA hB hCD]

/-- **Definition 1.9 (p. 12), GE-010.** If `A, B, C` lie on a line (a subset isometric to `ℝ`) and
`AC ≥ AB`, `AC ≥ BC`, then `AC = AB + BC`. -/
@[kb "petrunin2025" "Definition 1.9 (collinear triples), p. 12"]
theorem dist_eq_add_of_isLine {S : Set P} (hS : IsLine S) {A B C : P} (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) (h1 : dist A B ≤ dist A C) (h2 : dist B C ≤ dist A C) :
    dist A C = dist A B + dist B C := by
  obtain ⟨f, hf, rfl⟩ := hS
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  simp only [hf.dist_eq, Real.dist_eq] at *
  simp only [abs_eq_max_neg, max_def] at *
  split_ifs at * <;> linarith

/-- **Exercise 1.11 (p. 13), GE-011.** A motion maps lines (subsets isometric to `ℝ`) to lines. -/
@[kb "petrunin2025" "Exercise 1.11, p. 13"]
theorem IsLine.image_isometryEquiv {Q : Type*} [MetricSpace Q] {S : Set Q} (hS : IsLine S)
    (g : Q ≃ᵢ P) : IsLine (g '' S) := by
  obtain ⟨f, hf, rfl⟩ := hS
  exact ⟨g ∘ f, g.isometry.comp hf, by rw [Set.range_comp]⟩

end Lines

section HalfLines

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The book's half-line `[PQ)` (p. 13): the image of `[0, ∞)` under an isometry `f : ℝ → (PQ)` with
`f 0 = P` and `Q = f q` for some `q > 0`. (The point set does not depend on the choice of `f`;
this follows from `halfLine_eq`.) -/
def HalfLine (O A : P) : Set P :=
  {X | ∃ f : ℝ → P, Isometry f ∧ f 0 = O ∧ (∃ q : ℝ, 0 < q ∧ f q = A) ∧ ∃ t : ℝ, 0 ≤ t ∧ f t = X}

private lemma lineMap_div_of_isometry {f : ℝ → P} {Q : P} (hf : Isometry f) {p : P} {q : ℝ} (hq : 0 < q)
    (h0 : f 0 = p) (hQ : f q = Q) (t : ℝ) : f t = lineMap p Q (t / q) := by
  have h1 := isometry_apply_eq_lineMap hf t
  have h2 := isometry_apply_eq_lineMap hf q
  rw [h0] at h1 h2
  rw [h1, ← hQ, h2, lineMap_apply, lineMap_apply]
  simp [smul_smul, hq.ne']

/-- **Half-line (p. 13), GE-012.** For `P ≠ Q`, `[PQ) = {lineMap P Q t | t ≥ 0}`. -/
@[kb "petrunin2025" "Half-line, p. 13"]
theorem halfLine_eq {O A : P} (hPQ : O ≠ A) :
    HalfLine O A = {X | ∃ t : ℝ, 0 ≤ t ∧ lineMap O A t = X} := by
  have hd : 0 < dist O A := dist_pos.2 hPQ
  ext X
  constructor
  · rintro ⟨f, hf, h0, ⟨q, hq, hQ⟩, t, ht, rfl⟩
    exact ⟨t / q, div_nonneg ht hq.le, (lineMap_div_of_isometry hf hq h0 hQ t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun s => lineMap O A (s / dist O A), ?_, by simp, ⟨dist O A, hd, by simp [hd.ne']⟩,
      t * dist O A, by positivity, by simp [hd.ne']⟩
    refine Isometry.of_dist_eq fun s u => ?_
    rw [dist_lineMap_lineMap, Real.dist_eq, Real.dist_eq, ← sub_div, abs_div,
      abs_of_pos hd]
    field_simp

/-- **Segment (p. 13), GE-012.** For `O ≠ A`, the intersection `[PQ) ∩ [QP)` of the half-lines is
the affine segment `[PQ]`. -/
@[kb "petrunin2025" "Segment [PQ], p. 13"]
theorem halfLine_inter_halfLine {O A : P} (hPQ : O ≠ A) :
    HalfLine O A ∩ HalfLine A O = affineSegment ℝ O A := by
  rw [halfLine_eq hPQ, halfLine_eq hPQ.symm]
  ext X
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, ⟨u, hu, hX⟩⟩
    have hX' : lineMap O A s = lineMap O A (1 - u) := by rw [lineMap_apply_one_sub]; exact hX.symm
    have hinj : Function.Injective (lineMap O A : ℝ → P) := by
      intro a b hab
      have := congrArg (· -ᵥ O) hab
      simp only [lineMap_apply, vadd_vsub] at this
      have hne : A -ᵥ O ≠ 0 := vsub_ne_zero.2 hPQ.symm
      exact smul_left_injective ℝ hne this
    have := hinj hX'
    exact ⟨s, ⟨hs, by linarith⟩, rfl⟩
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact ⟨⟨s, hs0, rfl⟩, ⟨1 - s, by linarith, by rw [lineMap_apply_one_sub]⟩⟩

end HalfLines

section Plane

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Exercise 5.17 (p. 42), GE-087.** Let `X ≠ Y` be points of a circle and `Q` a point of the line
`XY`. Then `Q` is inside the circle iff `Q` lies strictly between `X` and `Y`. (The book's
hypothesis that `Q` is off the circle is not needed.) -/
@[kb "petrunin2025" "Exercise 5.17, p. 42"]
theorem dist_center_lt_radius_iff_sbtw {s : Sphere P} {X Y Q : P} (hX : X ∈ s) (hY : Y ∈ s)
    (hXY : X ≠ Y) (hQ : Q ∈ line[ℝ, X, Y]) :
    dist Q s.center < s.radius ↔ Sbtw ℝ X Q Y := by
  constructor
  · intro h
    have hcol : Collinear ℝ ({X, Q, Y} : Set P) := by
      have := collinear_insert_of_mem_affineSpan_pair hQ
      rwa [Set.insert_comm] at this
    exact sbtw_of_collinear_of_dist_center_lt_radius hcol hX h hY hXY
  · intro h
    have := h.dist_lt_max_dist s.center
    rw [mem_sphere.1 hX, mem_sphere.1 hY, max_self] at this
    exact this

include V in
/-- **Ptolemy's inequality 6.12 (p. 48), GE-100.** For any four points `A, B, C, D` of the
Euclidean plane, `AC · BD ≤ AB · CD + BC · DA`. -/
@[kb "petrunin2025" "Ptolemy's inequality 6.12, p. 48"]
theorem ptolemy_inequality (A B C D : P) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist D A := by
  rw [dist_comm D A]
  exact mul_dist_le_mul_dist_add_mul_dist A B C D

section Oriented

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Axiom III(a) (p. 19), GE-014/GE-026.** Given a half-line `[OA)` and an angle `α`, there is a
half-line `[OB)` with `∡AOB = α`, and it is unique: any other `B'` with `∡AOB' = α` lies on the
same ray from `O` as `B`. -/
@[kb "petrunin2025" "Axiom III(a), p. 19"]
theorem exists_unique_halfLine_oangle {O A : P} (hA : A ≠ O) (α : Real.Angle) :
    ∃ B : P, B ≠ O ∧ ∡ A O B = α ∧
      ∀ B' : P, B' ≠ O → ∡ A O B' = α → SameRay ℝ (B' -ᵥ O) (B -ᵥ O) := by
  have hv : A -ᵥ O ≠ 0 := vsub_ne_zero.2 hA
  set o : Orientation ℝ V (Fin 2) := Module.Oriented.positiveOrientation
  have hr : o.rotation α (A -ᵥ O) ≠ 0 := by simpa using hv
  have hB : (o.rotation α (A -ᵥ O) +ᵥ O) ≠ O := by
    intro h
    have := vsub_eq_zero_iff_eq.2 h
    rw [vadd_vsub] at this
    exact hr this
  have hang : ∡ A O (o.rotation α (A -ᵥ O) +ᵥ O) = α := by
    unfold EuclideanGeometry.oangle
    rw [vadd_vsub]
    exact o.oangle_rotation_self_right hv α
  refine ⟨_, hB, hang, fun B' hB' h' => ?_⟩
  have h0 : ∡ (o.rotation α (A -ᵥ O) +ᵥ O) O B' = 0 := by
    rw [← oangle_sub_left hA hB hB', hang, h', sub_self]
  have := (o.oangle_eq_zero_iff_sameRay (x := (o.rotation α (A -ᵥ O) +ᵥ O) -ᵥ O) (y := B' -ᵥ O)).1 h0
  exact this.symm

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
private lemma lineMap_vsub_lineMap_same (A X Y : P) (k : ℝ) :
    lineMap A X k -ᵥ lineMap A Y k = k • (X -ᵥ Y) := by
  simp [lineMap_apply, ← smul_sub, vsub_sub_vsub_cancel_right]

omit [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] in
private lemma lineMap_eq_of_dist {A B B' : P} {k : ℝ} (hAB : A ≠ B)
    (hB' : ∃ t : ℝ, 0 ≤ t ∧ lineMap A B t = B') (hd : dist A B' = k * dist A B) :
    B' = lineMap A B k := by
  obtain ⟨t, ht, rfl⟩ := hB'
  rw [dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht] at hd
  have := mul_right_cancel₀ (dist_pos.2 hAB).ne' hd
  rw [this]

/-- **Axiom V (p. 19), GE-030.** If `B'` lies on the half-line `[AB)` and `C'` on `[AC)` with
`AB' = k · AB`, `AC' = k · AC` (`k > 0`, `A ≠ B`, `A ≠ C`), then `B'C' = k · BC` and the signed angles
`∡ABC`, `∡BCA`, `∡CAB` equal `∡AB'C'`, `∡B'C'A`, `∡C'AB'`. -/
@[kb "petrunin2025" "Axiom V, p. 19"]
theorem axiomV {A B C B' C' : P} {k : ℝ} (hk : 0 < k) (hAB : A ≠ B) (hAC : A ≠ C)
    (hB' : ∃ t : ℝ, 0 ≤ t ∧ lineMap A B t = B') (hC' : ∃ t : ℝ, 0 ≤ t ∧ lineMap A C t = C')
    (hB'd : dist A B' = k * dist A B) (hC'd : dist A C' = k * dist A C) :
    dist B' C' = k * dist B C ∧ ∡ A B C = ∡ A B' C' ∧ ∡ B C A = ∡ B' C' A ∧
      ∡ C A B = ∡ C' A B' := by
  have e1 := lineMap_eq_of_dist hAB hB' hB'd
  have e2 := lineMap_eq_of_dist hAC hC' hC'd
  subst e1 e2
  have v1 : A -ᵥ lineMap A B k = k • (A -ᵥ B) := by
    rw [lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, ← smul_neg, neg_vsub_eq_vsub_rev]
  have v2 : A -ᵥ lineMap A C k = k • (A -ᵥ C) := by
    rw [lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, ← smul_neg, neg_vsub_eq_vsub_rev]
  have v3 : lineMap A B k -ᵥ A = k • (B -ᵥ A) := by simp [lineMap_apply]
  have v4 : lineMap A C k -ᵥ A = k • (C -ᵥ A) := by simp [lineMap_apply]
  have v5 : lineMap A C k -ᵥ lineMap A B k = k • (C -ᵥ B) := lineMap_vsub_lineMap_same A C B k
  have v6 : lineMap A B k -ᵥ lineMap A C k = k • (B -ᵥ C) := lineMap_vsub_lineMap_same A B C k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm_vsub V, v6, norm_smul, Real.norm_eq_abs, abs_of_pos hk, dist_eq_norm_vsub V]
  · unfold EuclideanGeometry.oangle
    rw [v1, v5, Orientation.oangle_smul_left_of_pos _ _ _ hk, Orientation.oangle_smul_right_of_pos _ _ _ hk]
  · unfold EuclideanGeometry.oangle
    rw [v6, v2, Orientation.oangle_smul_left_of_pos _ _ _ hk, Orientation.oangle_smul_right_of_pos _ _ _ hk]
  · unfold EuclideanGeometry.oangle
    rw [v4, v3, Orientation.oangle_smul_left_of_pos _ _ _ hk, Orientation.oangle_smul_right_of_pos _ _ _ hk]

end Oriented

end Plane

section MoreAngles

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Classroom exercise 3.8 (p. 26), GE-050.** If `B` is strictly between `A` and `C` and `X` is
off the line `AC`, then the angles `∡AXB`, `∡BXC`, `∡AXC` are nondegenerate with the same sign, and
`|∡AXB| + |∡BXC| = |∡AXC|` (absolute values of the representatives in `(-π, π]`). -/
@[kb "petrunin2025" "Classroom exercise 3.8, p. 26"]
theorem sbtw_oangle_sign_and_abs {A B C X : P} (h : Sbtw ℝ A B C) (hX : X ∉ line[ℝ, A, C]) :
    (∡ A X B).sign ≠ 0 ∧ (∡ A X B).sign = (∡ B X C).sign ∧ (∡ B X C).sign = (∡ A X C).sign ∧
      |(∡ A X B).toReal| + |(∡ B X C).toReal| = |(∡ A X C).toReal| := by
  have hA : A ∈ line[ℝ, A, C] := left_mem_affineSpan_pair ℝ A C
  have hC : C ∈ line[ℝ, A, C] := right_mem_affineSpan_pair ℝ A C
  have hB : B ∈ line[ℝ, A, C] := h.wbtw.mem_affineSpan
  have hAX : A ≠ X := fun e => hX (e ▸ hA)
  have hBX : B ≠ X := fun e => hX (e ▸ hB)
  have hCX : C ≠ X := fun e => hX (e ▸ hC)
  refine ⟨?_, h.oangle_sign_eq X, h.oangle_sign_eq_right X, ?_⟩
  · rw [Ne, oangle_sign_eq_zero_iff_collinear]
    intro hcol
    have hcol' : Collinear ℝ ({A, X, B} : Set P) := hcol
    exact hX (by
      have := hcol'.mem_affineSpan_of_mem_of_ne (p₁ := A) (p₂ := B) (p₃ := X)
        (by simp) (by simp) (by simp) h.left_ne
      exact affineSpan_pair_le_of_mem_of_mem hA hB this)
  · rw [← angle_eq_abs_oangle_toReal hAX hBX, ← angle_eq_abs_oangle_toReal hBX hCX,
      ← angle_eq_abs_oangle_toReal hAX hCX]
    exact angle_add_angle_eq_of_sbtw h

/-- **Corollary 3.5 (p. 25), GE-047.** Let `O t, A t, B t` be continuous on `[0,1]` and never
collinear there. Then `∡ A₀ O₀ B₀` and `∡ A₁ O₁ B₁` have the same sign. -/
@[kb "petrunin2025" "Corollary 3.5, p. 25"]
theorem oangle_sign_eq_of_continuousOn {O A B : ℝ → P} (hO : ContinuousOn O (Set.Icc 0 1))
    (hA : ContinuousOn A (Set.Icc 0 1)) (hB : ContinuousOn B (Set.Icc 0 1))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, ¬ Collinear ℝ ({A t, O t, B t} : Set P)) :
    (∡ (A 0) (O 0) (B 0)).sign = (∡ (A 1) (O 1) (B 1)).sign := by
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, A t ≠ O t ∧ B t ≠ O t := by
    intro t ht
    refine ⟨fun e => h t ht ?_, fun e => h t ht ?_⟩
    · rw [e]; simp [collinear_pair]
    · rw [e]; simp [collinear_pair]
  have hcont : ContinuousOn (fun t => ∡ (A t) (O t) (B t)) (Set.Icc 0 1) := by
    intro t ht
    have := (continuousAt_oangle (hne t ht).1 (hne t ht).2).comp_continuousWithinAt
      ((hA t ht).prodMk ((hO t ht).prodMk (hB t ht)))
    exact this
  exact (Real.Angle.sign_eq_of_continuousOn (f := fun t => ∡ (A t) (O t) (B t)) (isConnected_Icc zero_le_one) hcont
    (fun t ht => oangle_ne_zero_and_ne_pi_iff_not_collinear.2 (h t ht))
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)).symm

end MoreAngles

section Coordinates

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

/-- **Exercise 7.24 (p. 56), GE-119.** Given two perpendicular lines through `O` with unit
direction vectors `e₁ ⊥ e₂`, the map sending `X` to its signed coordinates
`(⟪e₁, X - O⟫, ⟪e₂, X - O⟫)` is an isometry of the plane onto `EuclideanSpace ℝ (Fin 2)`. -/
@[kb "petrunin2025" "Exercise 7.24, p. 56"]
theorem exists_isometryEquiv_coordinates (O : P) {e₁ e₂ : V} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h : inner ℝ e₁ e₂ = 0) :
    ∃ φ : P ≃ᵢ EuclideanSpace ℝ (Fin 2), φ O = 0 ∧
      ∀ X : P, φ X 0 = inner ℝ e₁ (X -ᵥ O) ∧ φ X 1 = inner ℝ e₂ (X -ᵥ O) := by
  have hfin : FiniteDimensional ℝ V :=
    Module.finite_of_finrank_eq_succ (n := 1) (Fact.out (p := Module.finrank ℝ V = 2))
  have hon : Orthonormal ℝ ![e₁, e₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [h₁, h₂, h, real_inner_comm e₁ e₂]
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ V := by
    simp [Fact.out (p := Module.finrank ℝ V = 2)]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![e₁, e₂]) := by
    have := (basisOfOrthonormalOfCardEqFinrank hon hcard).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at this
    exact this.ge
  let b : OrthonormalBasis (Fin 2) ℝ V := OrthonormalBasis.mk hon hsp
  have hb : ∀ i, b i = ![e₁, e₂] i := fun i => by simp [b]
  refine ⟨(IsometryEquiv.vaddConst O).symm.trans b.repr.toIsometryEquiv, by simp, fun X => ?_⟩
  refine ⟨?_, ?_⟩
  · simp [b.repr_apply_apply, hb]
  · simp [b.repr_apply_apply, hb]

end Coordinates

section Manhattan

/-- The Manhattan plane `(ℝ², d₁)`. -/
abbrev Manhattan : Type := PiLp 1 (fun _ : Fin 2 => ℝ)

/-- The point `(a, b)` of the Manhattan plane. -/
def mpt (a b : ℝ) : Manhattan := WithLp.toLp 1 ![a, b]

@[simp] lemma mpt_zero (a b : ℝ) : mpt a b 0 = a := rfl
@[simp] lemma mpt_one (a b : ℝ) : mpt a b 1 = b := rfl

lemma manhattan_dist (X Y : Manhattan) : dist X Y = |X 0 - Y 0| + |X 1 - Y 1| := by
  rw [PiLp.dist_eq_of_L1, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]

/-- **Section 1J example (p. 17), GE-022, distances.** In the Manhattan plane the points
`A = (0,1)`, `B = (1,0)`, `C = (-1,0)` are pairwise at distance `2`. -/
@[kb "petrunin2025" "Example in Section 1J, p. 17 (distances)"]
theorem manhattan_dist_ABC :
    dist (mpt 0 1) (mpt 1 0) = 2 ∧ dist (mpt 0 1) (mpt (-1) 0) = 2 ∧
      dist (mpt 1 0) (mpt (-1) 0) = 2 := by
  simp only [manhattan_dist, mpt_zero, mpt_one]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [abs_of_nonneg, abs_of_nonpos]

/-- The motion `(x, y) ↦ (-x, y)` of the Manhattan plane. -/
def manhattanReflect : Manhattan ≃ᵢ Manhattan where
  toFun X := mpt (-(X 0)) (X 1)
  invFun X := mpt (-(X 0)) (X 1)
  left_inv X := by ext i; fin_cases i <;> simp
  right_inv X := by ext i; fin_cases i <;> simp
  isometry_toFun := Isometry.of_dist_eq fun X Y => by
    simp only [manhattan_dist, mpt_zero, mpt_one]
    rw [← abs_neg]; congr 2; ring

/-- **Section 1J example (p. 17), GE-022, `△ABC ≅ △ACB`.** The motion `(x, y) ↦ (-x, y)` sends
`A ↦ A`, `B ↦ C`, `C ↦ B`. -/
@[kb "petrunin2025" "Example in Section 1J, p. 17 (congruence ABC, ACB)"]
theorem manhattan_congruent_ACB :
    manhattanReflect (mpt 0 1) = mpt 0 1 ∧ manhattanReflect (mpt 1 0) = mpt (-1) 0 ∧
      manhattanReflect (mpt (-1) 0) = mpt 1 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [manhattanReflect]

/-- **Section 1J example (p. 17), GE-022, `△ABC ≇ △BCA`.** No motion of the Manhattan plane sends
`A ↦ B`, `B ↦ C`, `C ↦ A`, although all sides have length `2`. (The book argues with midpoints:
`A, B` have two midpoints `(0,0)`, `(1,1)` while `B, C` have only one.) -/
@[kb "petrunin2025" "Example in Section 1J, p. 17 (no congruence ABC, BCA)"]
theorem manhattan_not_congruent_BCA :
    ¬ ∃ f : Manhattan ≃ᵢ Manhattan,
      f (mpt 0 1) = mpt 1 0 ∧ f (mpt 1 0) = mpt (-1) 0 ∧ f (mpt (-1) 0) = mpt 0 1 := by
  rintro ⟨f, hA, hB, -⟩
  -- a midpoint of `B` and `C` is the origin
  have key : ∀ N : Manhattan, dist N (mpt 1 0) = 1 → dist N (mpt (-1) 0) = 1 → N = mpt 0 0 := by
    intro N h1 h2
    simp only [manhattan_dist, mpt_zero, mpt_one, sub_zero] at h1 h2
    have hx : N 0 = 0 ∧ N 1 = 0 := by
      simp only [abs_eq_max_neg, max_def] at h1 h2
      split_ifs at h1 h2 <;> constructor <;> linarith
    ext i; fin_cases i
    · exact hx.1
    · exact hx.2
  have hmid : ∀ M : Manhattan, dist M (mpt 0 1) = 1 → dist M (mpt 1 0) = 1 → f M = mpt 0 0 := by
    intro M h1 h2
    apply key
    · rw [← hA, f.dist_eq]; exact h1
    · rw [← hB, f.dist_eq]; exact h2
  have e1 := hmid (mpt 0 0) (by simp [manhattan_dist]) (by simp [manhattan_dist])
  have e2 := hmid (mpt 1 1) (by simp [manhattan_dist]) (by simp [manhattan_dist])
  have := f.injective (e1.trans e2.symm)
  have := congrArg (fun X : Manhattan => X 0) this
  simp at this

end Manhattan

end UndergradKB.Geometry
