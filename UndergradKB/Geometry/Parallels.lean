import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.PerpBisector
import UndergradKB.Common.Attr

/-! # Parallel lines, parallelograms, perpendiculars (Petrunin, chapters 5, 7, 8)

Lines are affine subspaces (`AffineSubspace.Parallel`, notation `∥`); perpendicular lines have orthogonal
directions (`Submodule.IsOrtho`, `⟂`); a "line" in the plane is a subspace whose direction has dimension `1`.
Parallelograms (Lemma 7.18, Exercises 7.19, 8.7), the intercept theorem (Exercise 7.11), the quadrangle
angle sum (Exercise 7.17), uniqueness of parallels (Theorem 7.2), reflection across a point (Theorem 7.8),
the perpendicular bisector (Exercise 5.3) and the foot of a perpendicular (Lemma 5.13). -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real Affine

section Parallelogram

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- A parallelogram `ABCD`: a nondegenerate quadrangle (no three vertices collinear) with opposite sides
parallel. -/
structure IsParallelogram (A B C D : P) : Prop where
  not_collinear_ABC : ¬Collinear ℝ ({A, B, C} : Set P)
  not_collinear_BCD : ¬Collinear ℝ ({B, C, D} : Set P)
  not_collinear_CDA : ¬Collinear ℝ ({C, D, A} : Set P)
  not_collinear_DAB : ¬Collinear ℝ ({D, A, B} : Set P)
  par_AB_CD : line[ℝ, A, B] ∥ line[ℝ, C, D]
  par_BC_DA : line[ℝ, B, C] ∥ line[ℝ, D, A]

/-- Key vector step: in a parallelogram `ABCD`, `B - A = C - D`. -/
theorem IsParallelogram.vsub_eq {A B C D : P} (h : IsParallelogram A B C D) :
    B -ᵥ A = C -ᵥ D := by
  have h1 := h.par_AB_CD.direction_eq
  have h2 := h.par_BC_DA.direction_eq
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair_rev, vectorSpan_pair_rev] at h1 h2
  have m1 : B -ᵥ A ∈ ℝ ∙ (D -ᵥ C) := by rw [← h1]; exact Submodule.mem_span_singleton_self _
  have m2 : C -ᵥ B ∈ ℝ ∙ (A -ᵥ D) := by rw [← h2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp m1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp m2
  have hDC : D -ᵥ C = -(C -ᵥ D) := (neg_vsub_eq_vsub_rev C D).symm
  have hCA : C -ᵥ A = (C -ᵥ D) - (A -ᵥ D) := (vsub_sub_vsub_cancel_right C A D).symm
  have hCA2 : C -ᵥ A = (B -ᵥ A) + (C -ᵥ B) := by rw [add_comm]; exact (vsub_add_vsub_cancel C B A).symm
  have key : (1 + a) • (C -ᵥ D) = (1 + t) • (A -ᵥ D) := by
    rw [hDC] at ha
    have : (C -ᵥ D) - (A -ᵥ D) = (B -ᵥ A) + (C -ᵥ B) := by rw [← hCA, ← hCA2]
    rw [← ha, ← ht] at this
    linear_combination (norm := module) this
  by_cases h0 : 1 + a = 0
  · have : a = -1 := by linarith
    rw [← ha, this, hDC]; simp
  · exfalso
    apply h.not_collinear_CDA
    have hmem : C ∈ line[ℝ, D, A] := by
      have : C = AffineMap.lineMap D A ((1 + t) / (1 + a)) := by
        rw [AffineMap.lineMap_apply, eq_vadd_iff_vsub_eq, div_eq_inv_mul, mul_smul, ← key,
          smul_smul, inv_mul_cancel₀ h0, one_smul]
      rw [this]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    exact collinear_insert_of_mem_affineSpan_pair hmem

/-- **Petrunin, Lemma 7.18** (central symmetry of a parallelogram, in the form listed in the book):
in a parallelogram `ABCD` the diagonals bisect each other, opposite sides are equal and opposite
angles are equal. -/
@[kb "petrunin2025" "Lemma 7.18, p. 54"]
theorem IsParallelogram.diagonals_bisect {A B C D : P} (h : IsParallelogram A B C D) :
    midpoint ℝ A C = midpoint ℝ B D := by
  rw [midpoint_eq_midpoint_iff_vsub_eq_vsub, ← neg_vsub_eq_vsub_rev B A, h.vsub_eq,
    neg_vsub_eq_vsub_rev]

theorem IsParallelogram.vsub_eq' {A B C D : P} (h : IsParallelogram A B C D) :
    C -ᵥ B = D -ᵥ A := by
  rw [← vsub_sub_vsub_cancel_right C B A, h.vsub_eq, vsub_sub_vsub_cancel_left]

/-- Opposite sides of a parallelogram are equal (Lemma 7.18). -/
@[kb "petrunin2025" "Lemma 7.18, p. 54"]
theorem IsParallelogram.dist_eq {A B C D : P} (h : IsParallelogram A B C D) :
    dist A B = dist C D ∧ dist B C = dist D A := by
  constructor
  · rw [dist_comm A B, dist_eq_norm_vsub V, dist_eq_norm_vsub V, h.vsub_eq]
  · rw [dist_comm B C, dist_eq_norm_vsub V, dist_eq_norm_vsub V, h.vsub_eq']

/-- Opposite angles of a parallelogram are equal (Lemma 7.18). -/
@[kb "petrunin2025" "Lemma 7.18, p. 54"]
theorem IsParallelogram.angle_eq {A B C D : P} (h : IsParallelogram A B C D) :
    ∠ A B C = ∠ C D A ∧ ∠ B C D = ∠ D A B := by
  have e1 : A -ᵥ B = -(C -ᵥ D) := by rw [← h.vsub_eq, neg_vsub_eq_vsub_rev]
  have e2 : C -ᵥ B = D -ᵥ A := h.vsub_eq'
  constructor
  · unfold EuclideanGeometry.angle
    rw [← InnerProductGeometry.angle_neg_neg (C -ᵥ D) (A -ᵥ D), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, e1, e2, neg_vsub_eq_vsub_rev]
  · unfold EuclideanGeometry.angle
    rw [← InnerProductGeometry.angle_neg_neg (B -ᵥ C) (D -ᵥ C), neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, e2]
    rw [h.vsub_eq]

/-- Two segments with equal displacement vectors lie on parallel lines. -/
theorem parallel_of_vsub_eq {A B C D : P} (h : B -ᵥ A = C -ᵥ D) :
    line[ℝ, A, B] ∥ line[ℝ, C, D] := by
  refine ⟨D -ᵥ A, ?_⟩
  rw [AffineSubspace.map_span, Set.image_pair, Set.pair_comm]
  show line[ℝ, D, C] = line[ℝ, (D -ᵥ A) +ᵥ A, (D -ᵥ A) +ᵥ B]
  have e2 : (D -ᵥ A) +ᵥ B = C := by
    rw [← vsub_vadd C D, ← h, vadd_eq_vadd_iff_sub_eq_vsub]
    exact vsub_sub_vsub_cancel_right B D A
  rw [vsub_vadd, e2]

/-- A nondegenerate quadrangle `ABCD` with `B - A = C - D` is a parallelogram. -/
theorem IsParallelogram.of_vsub_eq {A B C D : P} (h1 : ¬Collinear ℝ ({A, B, C} : Set P))
    (h2 : ¬Collinear ℝ ({B, C, D} : Set P)) (h3 : ¬Collinear ℝ ({C, D, A} : Set P))
    (h4 : ¬Collinear ℝ ({D, A, B} : Set P)) (h : B -ᵥ A = C -ᵥ D) : IsParallelogram A B C D := by
  refine ⟨h1, h2, h3, h4, parallel_of_vsub_eq h, parallel_of_vsub_eq ?_⟩
  rw [← vsub_sub_vsub_cancel_right C B A, h, vsub_sub_vsub_cancel_left]

/-- Varignon, vector form: in any quadrangle `ABCD`, the midpoint quadrangle `M₁M₂M₃M₄` of the sides
`[AB], [BC], [CD], [DA]` has `M₂ - M₁ = M₃ - M₄` (both equal half of `C - A`). -/
theorem varignon_vsub (A B C D : P) :
    midpoint ℝ B C -ᵥ midpoint ℝ A B = midpoint ℝ C D -ᵥ midpoint ℝ D A := by
  rw [midpoint_vsub_midpoint, midpoint_vsub_midpoint, midpoint_eq_smul_add, midpoint_eq_smul_add,
    add_comm (B -ᵥ A), vsub_add_vsub_cancel, vsub_add_vsub_cancel]

/-- **Petrunin, Exercise 8.7** (Varignon): the midpoints of the sides of a quadrangle form a
parallelogram. The book's quadrangle is implicitly such that the midpoint quadrangle is nondegenerate
(no three of the four midpoints collinear), which is the hypothesis here; without it the conclusion
holds in the degenerate form `varignon_vsub`. -/
@[kb "petrunin2025" "Exercise 8.7, p. 60"]
theorem varignon {A B C D : P}
    (h1 : ¬Collinear ℝ ({midpoint ℝ A B, midpoint ℝ B C, midpoint ℝ C D} : Set P))
    (h2 : ¬Collinear ℝ ({midpoint ℝ B C, midpoint ℝ C D, midpoint ℝ D A} : Set P))
    (h3 : ¬Collinear ℝ ({midpoint ℝ C D, midpoint ℝ D A, midpoint ℝ A B} : Set P))
    (h4 : ¬Collinear ℝ ({midpoint ℝ D A, midpoint ℝ A B, midpoint ℝ B C} : Set P)) :
    IsParallelogram (midpoint ℝ A B) (midpoint ℝ B C) (midpoint ℝ C D) (midpoint ℝ D A) :=
  IsParallelogram.of_vsub_eq h1 h2 h3 h4 (varignon_vsub A B C D)

/-- **Petrunin, Exercise 7.11** (intercept theorem): if `P ≠ B` lies on `[AB]` of a triangle `ABC`,
the line through `P` parallel to `(AC)` meets `[BC]` at a point `Q`, and `AB / PB = CB / QB`
(the triangles `ABC` and `PBQ` are similar). -/
@[kb "petrunin2025" "Exercise 7.11, p. 53"]
theorem intercept_theorem {A B C X : P} (h : ¬Collinear ℝ ({A, B, C} : Set P))
    (hP : Wbtw ℝ A X B) (hPB : X ≠ B) :
    ∃ Q, Wbtw ℝ B Q C ∧ Q ∈ AffineSubspace.mk' X (line[ℝ, A, C]).direction ∧
      dist A B / dist X B = dist C B / dist Q B := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  obtain ⟨t, ⟨ht0, ht1⟩, hPt⟩ := hP.symm
  have htne : t ≠ 0 := by
    rintro rfl; apply hPB; rw [← hPt]; simp
  refine ⟨AffineMap.lineMap B C t, ⟨t, ⟨ht0, ht1⟩, rfl⟩, ?_, ?_⟩
  · rw [AffineSubspace.mem_mk', direction_affineSpan, mem_vectorSpan_pair_rev]
    refine ⟨t, ?_⟩
    rw [← hPt, AffineMap.lineMap_apply, AffineMap.lineMap_apply, vadd_vsub_vadd_cancel_right,
      ← smul_sub, vsub_sub_vsub_cancel_right]
  · rw [← hPt, dist_lineMap_left, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht0,
      dist_comm B A, dist_comm B C]
    have : dist A B ≠ 0 := dist_ne_zero.mpr hAB
    have : dist C B ≠ 0 := dist_ne_zero.mpr hBC.symm
    field_simp

end Parallelogram

section Oriented

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- **Petrunin, Exercise 7.17**: for every quadrangle `ABCD` (consecutive vertices distinct) the four
signed angles at the vertices sum to zero (mod `2π`). -/
@[kb "petrunin2025" "Exercise 7.17, p. 54"]
theorem quadrangle_oangle_sum {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C) (hCD : C ≠ D) (hDA : D ≠ A) :
    ∡ A B C + ∡ B C D + ∡ C D A + ∡ D A B = 0 := by
  set o : Orientation ℝ V (Fin 2) := Module.Oriented.positiveOrientation
  have e1 : B -ᵥ A ≠ 0 := vsub_ne_zero.2 hAB.symm
  have e2 : C -ᵥ B ≠ 0 := vsub_ne_zero.2 hBC.symm
  have e3 : D -ᵥ C ≠ 0 := vsub_ne_zero.2 hCD.symm
  have e4 : A -ᵥ D ≠ 0 := vsub_ne_zero.2 hDA.symm
  have h1 : ∡ A B C = o.oangle (B -ᵥ A) (C -ᵥ B) + π := by
    unfold EuclideanGeometry.oangle
    rw [← neg_vsub_eq_vsub_rev B A, o.oangle_neg_left e1 e2]
  have h2 : ∡ B C D = o.oangle (C -ᵥ B) (D -ᵥ C) + π := by
    unfold EuclideanGeometry.oangle
    rw [← neg_vsub_eq_vsub_rev C B, o.oangle_neg_left e2 e3]
  have h3 : ∡ C D A = o.oangle (D -ᵥ C) (A -ᵥ D) + π := by
    unfold EuclideanGeometry.oangle
    rw [← neg_vsub_eq_vsub_rev D C, o.oangle_neg_left e3 e4]
  have h4 : ∡ D A B = o.oangle (A -ᵥ D) (B -ᵥ A) + π := by
    unfold EuclideanGeometry.oangle
    rw [← neg_vsub_eq_vsub_rev A D, o.oangle_neg_left e4 e1]
  have s1 := o.oangle_add e1 e2 e3
  have s2 := o.oangle_add e1 e3 e4
  have s3 := o.oangle_add e1 e4 e1
  rw [o.oangle_self] at s3
  have hpp : ((π : ℝ) : Real.Angle) + (π : ℝ) = 0 := Real.Angle.coe_pi_add_coe_pi
  rw [h1, h2, h3, h4]
  have : ∀ a b c d : Real.Angle, a + (π : ℝ) + (b + (π : ℝ)) + (c + (π : ℝ)) + (d + (π : ℝ)) =
      (a + b + c + d) + (((π : ℝ) : Real.Angle) + (π : ℝ)) + (((π : ℝ) : Real.Angle) + (π : ℝ)) := by
    intro a b c d; abel
  rw [this, s1, s2, s3, hpp]; simp

end Oriented

section Lines

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- A line (an affine subspace whose direction has dimension `1`) is not empty. -/
theorem ne_bot_of_finrank_direction_eq_one {l : AffineSubspace ℝ P}
    (h : Module.finrank ℝ l.direction = 1) : l ≠ ⊥ := by
  rintro rfl
  rw [AffineSubspace.direction_bot, finrank_bot] at h
  exact absurd h (by norm_num)

/-- In the plane, two lines perpendicular to a third have the same direction. -/
theorem direction_eq_of_perp [Fact (Module.finrank ℝ V = 2)] {l n m : AffineSubspace ℝ P}
    (hl : Module.finrank ℝ l.direction = 1) (hn : Module.finrank ℝ n.direction = 1)
    (hm : Module.finrank ℝ m.direction = 1) (h1 : l.direction ⟂ m.direction)
    (h2 : n.direction ⟂ m.direction) : l.direction = n.direction := by
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ (n := 1) (Fact.out)
  have hc : Module.finrank ℝ m.directionᗮ = 1 := by
    have := Submodule.finrank_add_finrank_orthogonal m.direction
    rw [hm, Fact.out (p := Module.finrank ℝ V = 2)] at this
    omega
  have e1 := Submodule.eq_of_le_of_finrank_eq h1.le (by rw [hl, hc])
  have e2 := Submodule.eq_of_le_of_finrank_eq h2.le (by rw [hn, hc])
  rw [e1, e2]

/-- **Petrunin, Proposition 7.1**: two lines perpendicular to the same line are parallel (in the
plane). Lines are affine subspaces with one-dimensional direction; perpendicularity is orthogonality of
the directions. -/
@[kb "petrunin2025" "Proposition 7.1, p. 49"]
theorem parallel_of_perp_perp [Fact (Module.finrank ℝ V = 2)] {l n m : AffineSubspace ℝ P}
    (hl : Module.finrank ℝ l.direction = 1) (hn : Module.finrank ℝ n.direction = 1)
    (hm : Module.finrank ℝ m.direction = 1) (h1 : l.direction ⟂ m.direction)
    (h2 : n.direction ⟂ m.direction) : l ∥ n := by
  rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
  exact ⟨direction_eq_of_perp hl hn hm h1 h2,
    iff_of_false (ne_bot_of_finrank_direction_eq_one hl) (ne_bot_of_finrank_direction_eq_one hn)⟩

/-- **Petrunin, Theorem 7.2**: through every point passes a unique line parallel to a given line
(proved for any nonempty affine subspace, in any dimension; the line is `AffineSubspace.mk' p l.direction`). -/
@[kb "petrunin2025" "Theorem 7.2, p. 49"]
theorem existsUnique_parallel_through (l : AffineSubspace ℝ P) (hl : l ≠ ⊥) (p : P) :
    ∃! m : AffineSubspace ℝ P, p ∈ m ∧ m ∥ l := by
  refine ⟨AffineSubspace.mk' p l.direction, ⟨AffineSubspace.self_mem_mk' _ _, ?_⟩, ?_⟩
  · rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot, AffineSubspace.direction_mk']
    refine ⟨rfl, ?_⟩
    simp only [hl, iff_false]
    exact (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨p, AffineSubspace.self_mem_mk' _ _⟩
  · rintro m ⟨hpm, hml⟩
    rw [← AffineSubspace.mk'_eq hpm, hml.direction_eq]

/-- **Petrunin, Classroom exercise 7.4**: if `k ⟂ l`, `l ⟂ m`, `m ⟂ n` (lines in the plane), then `k`
and `n` are not parallel. -/
@[kb "petrunin2025" "Classroom exercise 7.4, p. 50"]
theorem not_parallel_of_perp_chain [Fact (Module.finrank ℝ V = 2)] {k l m n : AffineSubspace ℝ P}
    (hk : Module.finrank ℝ k.direction = 1) (hl : Module.finrank ℝ l.direction = 1)
    (hm : Module.finrank ℝ m.direction = 1) (hn : Module.finrank ℝ n.direction = 1)
    (hkl : k.direction ⟂ l.direction) (hlm : l.direction ⟂ m.direction)
    (hmn : m.direction ⟂ n.direction) : ¬ k ∥ n := by
  intro hkn
  have e := direction_eq_of_perp hk hm hl hkl hlm.symm
  have h2 : n.direction ⟂ n.direction := by
    have := hmn.symm
    rwa [← e, hkn.direction_eq] at this
  have : n.direction = ⊥ := by
    rw [Submodule.isOrtho_self] at h2
    exact h2
  rw [this] at hn
  simp at hn

/-- The linear part of the point reflection is `-id`. -/
theorem pointReflection_linear_apply (O : P) (v : V) :
    (AffineEquiv.pointReflection ℝ O).toAffineMap.linear v = -v := by
  have : v = (v +ᵥ O) -ᵥ O := (vadd_vsub v O).symm
  rw [this, AffineMap.linear_apply_vsub]
  simp only [AffineEquiv.coe_toAffineMap, AffineEquiv.pointReflection_apply]
  simp [vsub_vadd_eq_vsub_sub]

/-- **Petrunin, Theorem 7.8**: for `P ∈ l`, `Q ∈ m` and `O` the midpoint of `[PQ]`, the line `m` is
parallel to `l` iff `m` is the image of `l` under the point reflection across `O` (proved for affine
subspaces of any dimension). -/
@[kb "petrunin2025" "Theorem 7.8, p. 51"]
theorem parallel_iff_eq_map_pointReflection {l m : AffineSubspace ℝ P} {X Q : P} (hX : X ∈ l)
    (hQ : Q ∈ m) :
    m ∥ l ↔ m = l.map (AffineEquiv.pointReflection ℝ (midpoint ℝ X Q)).toAffineMap := by
  set f := (AffineEquiv.pointReflection ℝ (midpoint ℝ X Q)).toAffineMap with hf
  have hl : l ≠ ⊥ := (AffineSubspace.nonempty_iff_ne_bot _).1 ⟨X, hX⟩
  have hfX : f X = Q := by
    simp only [hf, AffineEquiv.coe_toAffineMap, AffineEquiv.coe_pointReflection]
    exact Equiv.pointReflection_midpoint_left X Q
  have hdir : (l.map f).direction = l.direction := by
    rw [AffineSubspace.map_direction]
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [pointReflection_linear_apply] at *
      exact l.direction.neg_mem hu
    · intro u hu
      refine ⟨-u, l.direction.neg_mem hu, ?_⟩
      rw [pointReflection_linear_apply, neg_neg]
  have hpar : l.map f ∥ l := by
    rw [AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot]
    exact ⟨hdir, by simp [hl]⟩
  have hQl : Q ∈ l.map f := ⟨X, hX, hfX⟩
  constructor
  · intro hm
    obtain ⟨m', _, huniq⟩ := existsUnique_parallel_through l hl Q
    exact (huniq m ⟨hQ, hm⟩).trans (huniq _ ⟨hQl, hpar⟩).symm
  · intro hm
    rw [hm]; exact hpar

/-- **Petrunin, Exercise 7.19**: for a parallelogram `ABCD` and a point `P`, the lines through
`A, B, C, D` parallel to `(CP), (DP), (AP), (BP)` all pass through the point `A + C - P`
(the reflection of `P` across the center of the parallelogram). -/
@[kb "petrunin2025" "Exercise 7.19, p. 55"]
theorem IsParallelogram.parallels_concurrent {A B C D : P} (h : IsParallelogram A B C D) (X : P) :
    ∃ Y : P, Y ∈ AffineSubspace.mk' A (line[ℝ, C, X]).direction ∧
      Y ∈ AffineSubspace.mk' B (line[ℝ, D, X]).direction ∧
      Y ∈ AffineSubspace.mk' C (line[ℝ, A, X]).direction ∧
      Y ∈ AffineSubspace.mk' D (line[ℝ, B, X]).direction := by
  have hb : B -ᵥ A = (C -ᵥ A) - (D -ᵥ A) := by rw [h.vsub_eq, vsub_sub_vsub_cancel_right]
  have hY : ((C -ᵥ X) +ᵥ A) -ᵥ A = (C -ᵥ A) - (X -ᵥ A) := by
    rw [vadd_vsub, vsub_sub_vsub_cancel_right]
  refine ⟨(C -ᵥ X) +ᵥ A, ?_, ?_, ?_, ?_⟩ <;>
    rw [AffineSubspace.mem_mk', direction_affineSpan, mem_vectorSpan_pair] <;>
    refine ⟨1, ?_⟩ <;> rw [one_smul]
  · rw [vadd_vsub]
  · rw [← vsub_sub_vsub_cancel_right _ B A, hY, ← vsub_sub_vsub_cancel_right D X A, hb]
    abel
  · rw [← vsub_sub_vsub_cancel_right _ C A, hY, ← vsub_sub_vsub_cancel_right A X A, vsub_self]
    abel
  · rw [← vsub_sub_vsub_cancel_right _ D A, hY, ← vsub_sub_vsub_cancel_right B X A, hb]
    abel

end Lines

section Perpendicular

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- `XA² - XB² = 2 ⟨X - M, B - A⟩` where `M` is the midpoint of `[AB]`. -/
theorem dist_sq_sub_dist_sq_eq (A B X : P) :
    dist A X ^ 2 - dist B X ^ 2 = 2 * inner ℝ (X -ᵥ midpoint ℝ A B) (B -ᵥ A) := by
  have hA : A -ᵥ X = -((⅟2 : ℝ) • (B -ᵥ A)) - (X -ᵥ midpoint ℝ A B) := by
    rw [← smul_neg, neg_vsub_eq_vsub_rev, ← left_vsub_midpoint (R := ℝ) A B, vsub_sub_vsub_cancel_right]
  have hB : B -ᵥ X = ((⅟2 : ℝ) • (B -ᵥ A)) - (X -ᵥ midpoint ℝ A B) := by
    rw [← right_vsub_midpoint (R := ℝ) A B, vsub_sub_vsub_cancel_right]
  rw [dist_eq_norm_vsub V A X, dist_eq_norm_vsub V B X, hA, hB, norm_sub_sq_real, norm_sub_sq_real,
    norm_neg, inner_neg_left, real_inner_smul_left, real_inner_comm, invOf_eq_inv]
  ring

/-- **Petrunin, Exercise 5.3**: for `A ≠ B`, `AX < BX` iff `X` lies strictly on the same side of the
perpendicular bisector of `[AB]` as `A`. -/
@[kb "petrunin2025" "Exercise 5.3, p. 38"]
theorem dist_lt_iff_sSameSide_perpBisector {A B : P} (hAB : A ≠ B) (X : P) :
    dist A X < dist B X ↔ (AffineSubspace.perpBisector A B).SSameSide X A := by
  set M := midpoint ℝ A B with hM
  set w := B -ᵥ A with hw
  have hw0 : w ≠ 0 := vsub_ne_zero.2 hAB.symm
  have hww : 0 < inner ℝ w w := real_inner_self_pos.2 hw0
  have hgA : inner ℝ (A -ᵥ M) w = -(inner ℝ w w) / 2 := by
    rw [hM, left_vsub_midpoint, ← neg_vsub_eq_vsub_rev B A, ← hw, smul_neg, invOf_eq_inv,
      inner_neg_left, real_inner_smul_left]; ring
  have hmem : ∀ Y, Y ∈ AffineSubspace.perpBisector A B ↔ inner ℝ (Y -ᵥ M) w = 0 :=
    fun Y => AffineSubspace.mem_perpBisector_iff_inner_eq_zero
  have hlt : dist A X < dist B X ↔ inner ℝ (X -ᵥ M) w < 0 := by
    have := dist_sq_sub_dist_sq_eq A B X
    rw [← hM, ← hw] at this
    constructor
    · intro h
      have : dist A X ^ 2 < dist B X ^ 2 := by gcongr
      linarith
    · intro h
      by_contra hc
      have hc' : dist B X ≤ dist A X := not_lt.1 hc
      have : dist B X ^ 2 ≤ dist A X ^ 2 := by gcongr
      linarith
  rw [hlt, AffineSubspace.sSameSide_iff_exists_left (AffineSubspace.midpoint_mem_perpBisector A B)]
  constructor
  · intro h
    refine ⟨fun hX => by rw [hmem] at hX; linarith,
      fun hA => by rw [hmem] at hA; linarith, ?_⟩
    have hc : 0 < (inner ℝ w w / 2) / (-inner ℝ (X -ᵥ M) w) := div_pos (by linarith) (by linarith)
    set c := (inner ℝ w w / 2) / (-inner ℝ (X -ᵥ M) w) with hcdef
    refine ⟨(-c) • (X -ᵥ M) +ᵥ A, ?_, ?_⟩
    · rw [hmem, vadd_vsub_assoc, inner_add_left, real_inner_smul_left, hgA, hcdef]
      have : inner ℝ (X -ᵥ M) w ≠ 0 := h.ne
      field_simp
      ring
    · rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_smul, neg_neg]
      exact SameRay.sameRay_pos_smul_right _ hc
  · rintro ⟨hX, hA, p, hp, hray⟩
    rw [hmem] at hX hp
    have hAp : inner ℝ (A -ᵥ p) w = -(inner ℝ w w) / 2 := by
      rw [← vsub_sub_vsub_cancel_right A p M, inner_sub_left, hgA, hp, sub_zero]
    by_contra hge
    have hpos : 0 < inner ℝ (X -ᵥ M) w := lt_of_le_of_ne (not_lt.1 hge) (Ne.symm hX)
    have hx0 : X -ᵥ M ≠ 0 := fun h0 => by rw [h0, inner_zero_left] at hpos; exact lt_irrefl _ hpos
    have hy0 : A -ᵥ p ≠ 0 := fun h0 => by rw [h0, inner_zero_left] at hAp; linarith
    obtain ⟨r₁, r₂, h1, h2, hr⟩ := hray.exists_pos hx0 hy0
    have := congrArg (fun v => inner ℝ v w) hr
    simp only [real_inner_smul_left, hAp] at this
    nlinarith

/-- **Petrunin, Lemma 5.13**: if `Q` is the foot of the perpendicular from `P` to a line (more generally,
an affine subspace) `l`, then `PX > PQ` for every `X ∈ l` other than `Q`. -/
@[kb "petrunin2025" "Lemma 5.13, p. 41"]
theorem dist_foot_lt_dist {l : AffineSubspace ℝ P} [Nonempty l] [l.direction.HasOrthogonalProjection]
    (X : P) (Y : P) (hY : Y ∈ l) (hne : Y ≠ (EuclideanGeometry.orthogonalProjection l X : P)) :
    dist X (EuclideanGeometry.orthogonalProjection l X : P) < dist X Y := by
  have h := EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := l) X hY
  have hpos : 0 < dist Y (EuclideanGeometry.orthogonalProjection l X : P) := dist_pos.2 hne
  by_contra hc
  have hc' : dist X Y ≤ dist X (EuclideanGeometry.orthogonalProjection l X : P) := not_lt.1 hc
  rw [dist_comm X Y] at hc'
  nlinarith [dist_nonneg (x := Y) (y := X),
    dist_nonneg (x := X) (y := (EuclideanGeometry.orthogonalProjection l X : P))]

end Perpendicular

end UndergradKB.Geometry
