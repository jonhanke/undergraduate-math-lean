import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Complex.Angle
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Geometry.Euclidean.Volume.Triangle
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import UndergradKB.Common.Attr

/-! # Course layer: Petrunin chapters 16 to 20

Thin theorems in the book's terms, each proved by the Mathlib lemma named in the checklist.

* Chapter 16: the cosine of the spherical distance is the scalar product.
* Chapter 18 (complex coordinates): coordinates and distance, conjugation, absolute value, the
  exponential, polar coordinates, fractional linear transformations and the Schwarz lemma.
* Chapter 20 (area): the area function is Lebesgue measure `MeasureTheory.volume` on
  `EuclideanSpace ℝ (Fin 2)` (the unit square has area `1`). Polygonal sets are not a Mathlib notion,
  so statements about them are given for null-measurable sets whose pairwise intersections have
  area zero, which contains the book's case.

Definition-only items (complex numbers as pairs, the extended complex plane, holomorphic functions,
solid triangles, bounded sets) have no wrapper here. -/

namespace UndergradKB.Geometry.Course

open Complex Real MeasureTheory Metric OnePoint

/-- Petrunin, Section 16 (scalar product on `ℝ³`): for unit vectors the cosine of their spherical
distance (the angle between them) equals their scalar product. -/
@[kb "petrunin2025" "Section 16, scalar product, p. 137"]
theorem petrunin_ch16_cos_spherical_distance (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.cos (InnerProductGeometry.angle x y) = inner ℝ x y := by
  simpa [hx, hy] using InnerProductGeometry.cos_angle_mul_norm_mul_norm x y

/-! ### Chapter 18 -/

/-- Petrunin, Section 18B, formula 4: in complex coordinates the distance between the points
with coordinates `z` and `w` is `|z - w|`. -/
@[kb "petrunin2025" "Section 18B, formula 4, p. 148"]
theorem petrunin_ch18_distance (z w : ℂ) : dist z w = ‖z - w‖ := Complex.dist_eq z w

/-- Petrunin, Section 18B: with the book's orientation convention the angle `∠ E O I` at the origin
between the points `1` and `i` is `π / 2`. -/
@[kb "petrunin2025" "Section 18B, p. 147"]
theorem petrunin_ch18_right_angle :
    EuclideanGeometry.angle (1 : ℂ) 0 Complex.I = π / 2 := by
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero,
    ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [Complex.inner]

/-- Petrunin, Section 18C: complex conjugation is the reflection in the real line: it is the
orthogonal reflection in the real axis `ℝ·1`, an isometry that fixes exactly the real numbers. -/
@[kb "petrunin2025" "Section 18C, p. 147"]
theorem petrunin_ch18_complex_conjugate :
    (∀ z : ℂ, starRingEnd ℂ z = (Submodule.span ℝ {(1 : ℂ)}).reflection z) ∧
      Isometry (starRingEnd ℂ) ∧ ∀ z : ℂ, starRingEnd ℂ z = z ↔ z.im = 0 := by
  refine ⟨fun z => ?_, Complex.conjLIE.isometry, fun z => Complex.conj_eq_iff_im⟩
  rw [Submodule.reflection_apply, Submodule.starProjection_singleton]
  apply Complex.ext
  · simp [Complex.inner]; ring
  · simp [Complex.inner]

/-- Petrunin, Section 18C, formula 3 and the lines that follow: `Re z = (z + z̄)/2`,
`Im z = (z - z̄)/(2i)`, `z z̄ = x² + y²` and `w/z = w z̄ /(x² + y²)`. -/
@[kb "petrunin2025" "Section 18C, formula 3, p. 147"]
theorem petrunin_ch18_conj_formulas (z w : ℂ) :
    (z.re : ℂ) = (z + starRingEnd ℂ z) / 2 ∧ (z.im : ℂ) = (z - starRingEnd ℂ z) / (2 * Complex.I) ∧
      z * starRingEnd ℂ z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) ∧
      w / z = w * starRingEnd ℂ z / ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
  have hz : z * starRingEnd ℂ z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_apply]; push_cast; ring_nf
  refine ⟨?_, ?_, hz, ?_⟩
  · exact Complex.re_eq_add_conj z
  · rw [Complex.im_eq_sub_conj z]
  · rw [← hz]
    by_cases h : z = 0
    · simp [h]
    · have : starRingEnd ℂ z ≠ 0 := by simpa using h
      field_simp

/-- Petrunin, Section 18C: conjugation respects sum, difference, product and quotient. -/
@[kb "petrunin2025" "Section 18C, p. 147"]
theorem petrunin_ch18_conj_respects_operations (z w : ℂ) :
    starRingEnd ℂ (z + w) = starRingEnd ℂ z + starRingEnd ℂ w ∧
      starRingEnd ℂ (z - w) = starRingEnd ℂ z - starRingEnd ℂ w ∧
      starRingEnd ℂ (z * w) = starRingEnd ℂ z * starRingEnd ℂ w ∧
      starRingEnd ℂ (z / w) = starRingEnd ℂ z / starRingEnd ℂ w :=
  ⟨map_add _ z w, map_sub _ z w, map_mul _ z w, map_div₀ _ z w⟩

/-- Petrunin, Section 18C: the absolute value is `|z| = √(z z̄) = √(x² + y²)`, and `|z| = 1` means
`x² + y² = 1`. -/
@[kb "petrunin2025" "Section 18C, p. 147"]
theorem petrunin_ch18_abs (z : ℂ) :
    ‖z‖ = Real.sqrt ((z * starRingEnd ℂ z).re) ∧ ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) ∧
      (‖z‖ = 1 ↔ z.re ^ 2 + z.im ^ 2 = 1) := by
  have h2 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  refine ⟨?_, h2, ?_⟩
  · rw [h2, Complex.mul_conj, Complex.normSq_apply]; simp [sq]
  · rw [h2, Real.sqrt_eq_one]

/-- Petrunin, Exercise 18.1: `|v w| = |v| |w|`. -/
@[kb "petrunin2025" "Exercise 18.1, p. 147"]
theorem petrunin_18_1 (v w : ℂ) : ‖v * w‖ = ‖v‖ * ‖w‖ := norm_mul v w

/-- Petrunin, Section 18C (after formula 4): the triangle inequality `|v + w| ≤ |v| + |w|`. -/
@[kb "petrunin2025" "Section 18C, triangle inequality, p. 148"]
theorem petrunin_ch18_triangle_inequality (v w : ℂ) : ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le v w

/-- Petrunin, Section 18D, formula 5 and consequences: Euler's formula, `e^{iπ} = -1` and
`e^{iα} e^{iβ} = e^{i(α+β)}`. -/
@[kb "petrunin2025" "Section 18D, formula 5, p. 148"]
theorem petrunin_ch18_euler (α β : ℝ) :
    Complex.exp (α * Complex.I) = (Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I ∧
      Complex.exp (π * Complex.I) = -1 ∧
      Complex.exp (α * Complex.I) * Complex.exp (β * Complex.I) =
        Complex.exp (((α + β : ℝ) : ℂ) * Complex.I) := by
  refine ⟨by rw [Complex.exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin], Complex.exp_pi_mul_I, ?_⟩
  rw [← Complex.exp_add]; push_cast; ring_nf

/-- Petrunin, Section 18D: a point of the unit circle centred at the origin has coordinate `e^{iα}`
for a unique `α ∈ (-π, π]`. -/
@[kb "petrunin2025" "Section 18D, p. 148"]
theorem petrunin_ch18_unit_circle {z : ℂ} (hz : ‖z‖ = 1) :
    ∃! α : ℝ, α ∈ Set.Ioc (-π) π ∧ z = Complex.exp (α * Complex.I) := by
  refine ⟨Complex.arg z, ⟨Complex.arg_mem_Ioc z, ?_⟩, ?_⟩
  · simpa [hz] using (Complex.norm_mul_exp_arg_mul_I z).symm
  · rintro α ⟨hα, hzα⟩
    rw [hzα, Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hα]

/-- Petrunin, Section 18E: polar coordinates, `z = ρ e^{iθ}` with `ρ = |z|` and `θ = arg z`
in `(-π, π]`. -/
@[kb "petrunin2025" "Section 18E, p. 149"]
theorem petrunin_ch18_polar (z : ℂ) :
    z = (‖z‖ : ℂ) * Complex.exp (Complex.arg z * Complex.I) ∧ Complex.arg z ∈ Set.Ioc (-π) π :=
  ⟨(Complex.norm_mul_exp_arg_mul_I z).symm, Complex.arg_mem_Ioc z⟩

/-- Petrunin, Section 18E: `arg (z w) ≡ arg z + arg w` and `arg (z / w) ≡ arg z - arg w`
modulo `2π`, for nonzero `z`, `w`. -/
@[kb "petrunin2025" "Section 18E, p. 149"]
theorem petrunin_ch18_arg_mul_div {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ((Complex.arg (z * w) : ℝ) : Real.Angle) = Complex.arg z + Complex.arg w ∧
      ((Complex.arg (z / w) : ℝ) : Real.Angle) = Complex.arg z - Complex.arg w :=
  ⟨Complex.arg_mul_coe_angle hz hw, Complex.arg_div_coe_angle hz hw⟩

/-- Petrunin, Section 18G: a fractional linear transformation `z ↦ (a z + b)/(c z + d)` with
`ad - bc ≠ 0` (an element of `GL₂(ℂ)`) acts on the extended plane `ℂ ∪ {∞}`, with value `∞` at
`-d/c` and `a/c` at `∞`. -/
@[kb "petrunin2025" "Section 18G, p. 152"]
theorem petrunin_ch18_fractional_linear (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    (∀ z : ℂ, g • (z : OnePoint ℂ) =
      if g 1 0 * z + g 1 1 = 0 then (∞ : OnePoint ℂ)
      else (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) : OnePoint ℂ)) ∧
    g • (∞ : OnePoint ℂ) = if g 1 0 = 0 then (∞ : OnePoint ℂ) else ((g 0 0 / g 1 0 : ℂ) : OnePoint ℂ) :=
  ⟨fun _ => OnePoint.smul_some_eq_ite, OnePoint.smul_infty_eq_ite g⟩

/-- Petrunin, Schwarz lemma 18.23: a holomorphic `f : D → D` on the unit disc with `f 0 = 0`
satisfies `|f z| ≤ |z|`; if equality holds at some `z ≠ 0` then `f z = u z` on `D` for a unit
complex number `u`. -/
@[kb "petrunin2025" "Schwarz lemma 18.23, p. 156"]
theorem petrunin_18_23 {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hmaps : Set.MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0) :
    (∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖) ∧
      ((∃ z ∈ ball (0 : ℂ) 1, z ≠ 0 ∧ ‖f z‖ = ‖z‖) →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, f z = u * z) := by
  have hmaps' : Set.MapsTo f (ball 0 1) (closedBall 0 1) := fun z hz =>
    ball_subset_closedBall (hmaps hz)
  refine ⟨fun z hz => Complex.norm_le_norm_of_mapsTo_ball hd hmaps' h0 (by simpa using hz), ?_⟩
  rintro ⟨z₀, hz₀, hne, heq⟩
  have hmaps'' : Set.MapsTo f (ball 0 1) (closedBall (f 0) 1) := by simpa [h0] using hmaps'
  obtain ⟨C, hC, hf⟩ := Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hd hmaps''
    ⟨z₀, hz₀, by
      rw [dslope_of_ne _ hne]
      simp only [slope_def_module, sub_zero, h0, norm_smul, norm_inv, heq]
      simp [hne]⟩
  refine ⟨C, by simpa using hC, fun z hz => ?_⟩
  simpa [h0, mul_comm] using hf hz

/-! ### Chapter 20 -/

/-- Petrunin, Exercise 20.1: a solid triangle is convex. A solid triangle is the closed interior of
the triangle, which Mathlib proves equal to the convex hull of its vertices. -/
@[kb "petrunin2025" "Exercise 20.1, p. 165"]
theorem petrunin_20_1 (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    Convex ℝ t.closedInterior := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior]
  exact convex_convexHull ℝ _

/-- Petrunin, Proposition 20.8: points and segments have area zero (area is Lebesgue measure). -/
@[kb "petrunin2025" "Proposition 20.8, p. 168"]
theorem petrunin_20_8 (A B : EuclideanSpace ℝ (Fin 2)) :
    volume (segment ℝ A B) = 0 ∧ volume ({A} : Set (EuclideanSpace ℝ (Fin 2))) = 0 := by
  refine ⟨?_, measure_singleton A⟩
  have hne : (line[ℝ, A, B] : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≠ ⊤ := by
    intro htop
    have hc : Collinear ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) := collinear_pair ℝ A B
    have h1 := hc.finrank_le_one
    have h2 : vectorSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
    rw [h2, finrank_top] at h1
    simp at h1
  refine measure_mono_null ?_ (Measure.addHaar_affineSubspace volume _ hne)
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  exact AffineMap.lineMap_mem_affineSpan_pair t A B

/-- Petrunin, Corollary 20.9: a degenerate polygonal set, a finite union of segments and points,
has area zero. -/
@[kb "petrunin2025" "Corollary 20.9, p. 169"]
theorem petrunin_20_9 (n k : ℕ) (A B : Fin n → EuclideanSpace ℝ (Fin 2))
    (C : Fin k → EuclideanSpace ℝ (Fin 2)) :
    volume ((⋃ i, segment ℝ (A i) (B i)) ∪ Set.range C) = 0 :=
  measure_union_null (measure_iUnion_null fun i => (petrunin_20_8 (A i) (B i)).1)
    ((Set.finite_range C).measure_zero volume)

/-- Petrunin, Proposition 20.10: if a set is subdivided into pieces whose pairwise intersections
have area zero, its area is the sum of the areas of the pieces. (Stated for null-measurable pieces,
which includes the polygonal sets of the book.) -/
@[kb "petrunin2025" "Proposition 20.10, p. 169"]
theorem petrunin_20_10 {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin 2)))
    (Q : Fin n → Set (EuclideanSpace ℝ (Fin 2))) (hP : P = ⋃ i, Q i)
    (hm : ∀ i, NullMeasurableSet (Q i) volume)
    (hd : ∀ i j, i ≠ j → volume (Q i ∩ Q j) = 0) :
    volume P = ∑ i, volume (Q i) := by
  subst hP
  rw [measure_iUnion₀ (fun i j hij => hd i j hij) hm, tsum_fintype]

section Parallelogram

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The solid parallelogram with vertices `A`, `B`, `B + D - A`, `D` (the vertex `A` adjacent to `B`
and `D`): the set of points `A + s (B - A) + t (D - A)` with `s, t ∈ [0, 1]`. -/
def solidParallelogram (A B D : E2) : Set E2 :=
  {X | ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, X = A + s • (B - A) + t • (D - A)}

theorem solidParallelogram_eq (A B D : E2) :
    solidParallelogram A B D = (fun x => A + x) '' parallelepiped ![B - A, D - A] := by
  ext X
  simp only [solidParallelogram, Set.mem_ofPred_eq, Set.mem_image, mem_parallelepiped_iff]
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨s • (B - A) + t • (D - A), ⟨![s, t], ⟨fun i => ?_, fun i => ?_⟩, ?_⟩, by abel⟩
    · fin_cases i <;> simp [hs.1, ht.1]
    · fin_cases i <;> simp [hs.2, ht.2]
    · simp [Fin.sum_univ_two]
  · rintro ⟨x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨c 0, ⟨hc.1 0, hc.2 0⟩, c 1, ⟨hc.1 1, hc.2 1⟩, ?_⟩
    simp [Fin.sum_univ_two]
    abel

theorem volume_solidParallelogram (A B D : E2) :
    volume (solidParallelogram A B D) =
      ENNReal.ofReal |(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det ![B - A, D - A]| := by
  rw [solidParallelogram_eq, Set.image_add_left, measure_preimage_add,
    ← (EuclideanSpace.basisFun (Fin 2) ℝ).addHaar_eq_volume, Measure.addHaar_parallelepiped]

/-- The area of the parallelogram spanned by `u` and `v` is `|u| ` times the distance from `v` to
the line `ℝ u`. -/
theorem abs_det_eq (u v : E2) :
    |(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det ![u, v]| =
      ‖u‖ * ‖v - (Submodule.span ℝ {u}).starProjection v‖ := by
  have : Fact (Module.finrank ℝ E2 = 2) := ⟨by simp⟩
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let o : Orientation ℝ E2 (Fin 2) := b.toBasis.orientation
  rw [← o.volumeForm_robust' b, ← o.areaForm_to_volumeForm]
  set K := Submodule.span ℝ {u}
  have hp : K.starProjection v ∈ K := Submodule.starProjection_apply_mem K v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hp
  have hw : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hperp : inner ℝ u (v - K.starProjection v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hw
  have : o.areaForm u v = o.areaForm u (v - K.starProjection v) := by
    rw [map_sub, ← hc, _root_.map_smul]; simp
  rw [this, o.abs_areaForm_of_orthogonal hperp]

/-- The distance from `D` to the line `(AB)` is the length of the component of `D - A`
orthogonal to `B - A`. -/
theorem infDist_line_eq (A B D : E2) :
    Metric.infDist D (line[ℝ, A, B] : Set E2) =
      ‖(D - A) - (Submodule.span ℝ {B - A}).starProjection (D - A)‖ := by
  set K := Submodule.span ℝ {B - A}
  set v := D - A
  have hp : K.starProjection v ∈ K := Submodule.starProjection_apply_mem K v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hp
  have hw : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  apply le_antisymm
  · have hmem : A + K.starProjection v ∈ (line[ℝ, A, B] : Set E2) := by
      rw [← hc]
      have := AffineMap.lineMap_mem_affineSpan_pair c A B
      simpa [AffineMap.lineMap_apply, add_comm] using this
    have := Metric.infDist_le_dist_of_mem (x := D) hmem
    rw [dist_eq_norm] at this
    convert this using 2
    simp only [v]; abel
  · rw [Metric.le_infDist ⟨A, left_mem_affineSpan_pair ℝ A B⟩]
    intro y hy
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    rw [dist_eq_norm]
    have hy' : D - AffineMap.lineMap A B t = (v - K.starProjection v) +
        (K.starProjection v - t • (B - A)) := by
      simp [v, AffineMap.lineMap_apply]; abel
    have hperp : inner ℝ (v - K.starProjection v) (K.starProjection v - t • (B - A)) = 0 := by
      refine Submodule.inner_left_of_mem_orthogonal ?_ hw
      exact K.sub_mem hp (K.smul_mem t (Submodule.mem_span_singleton_self _))
    rw [hy']
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [norm_nonneg ((v - K.starProjection v) + (K.starProjection v - t • (B - A))),
      sq_nonneg ‖K.starProjection v - t • (B - A)‖]

/-- Petrunin, Proposition 20.12: the area of a solid parallelogram is its base times its height:
`|AB|` times the distance from `D` to the line `(AB)`. -/
@[kb "petrunin2025" "Proposition 20.12, p. 171"]
theorem petrunin_20_12 (A B D : E2) :
    volume (solidParallelogram A B D) =
      ENNReal.ofReal (dist A B * Metric.infDist D (line[ℝ, A, B] : Set E2)) := by
  rw [volume_solidParallelogram, abs_det_eq, infDist_line_eq, dist_comm, dist_eq_norm]

/-- Petrunin, Theorem 20.11: the area of a solid rectangle is the product of its adjacent sides.
The rectangle has vertex `A` with perpendicular sides `[AB]` and `[AD]`. -/
@[kb "petrunin2025" "Theorem 20.11, p. 170"]
theorem petrunin_20_11 (A B D : E2) (h : inner ℝ (B - A) (D - A) = 0) :
    volume (solidParallelogram A B D) = ENNReal.ofReal (dist A B * dist A D) := by
  rw [petrunin_20_12, infDist_line_eq, Submodule.starProjection_singleton]
  rw [dist_comm A D]
  simp [h, dist_eq_norm]

end Parallelogram

/-- Petrunin, Theorem 20.14: the area of a solid triangle is `½ · a · h`, half a side length times
the corresponding height (altitude length). The solid triangle is the closed interior of the
triangle `t`; `i`, `j`, `k` are distinct vertex indices and the height is taken from vertex `i`. -/
@[kb "petrunin2025" "Theorem 20.14, p. 172"]
theorem petrunin_20_14 (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    volume.real t.closedInterior = 2⁻¹ * dist (t.points j) (t.points k) * t.height i := by
  rw [← Affine.Simplex.volume_eq_volume_real_closedInterior (by simp) t]
  rw [Affine.Triangle.volume_eq_height_mul t hij hik hjk]
  ring
