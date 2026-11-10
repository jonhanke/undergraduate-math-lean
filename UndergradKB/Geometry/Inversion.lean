import Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Topology.MetricSpace.Similarity
import UndergradKB.Common.Attr

/-! # Inversion (Petrunin, chapter 10)

Basic facts about inversion (p. 73), Lemma 10.2, the cross-ratio (Theorem 10.6a), the Apollonian
circle, images of circles (Theorems 10.7 and 10.11), Ptolemy's identity (Theorem 10.12),
perpendicular circles (Theorem 10.15, Corollaries 10.17 and 10.18).

We use Mathlib's `EuclideanGeometry.inversion c R` (centre `c`, radius `R`) in a real inner product
space. The inversive plane (the extra point `∞`) is not formalized: the statements about circlines
are split into the cases "circle not through the centre", "circle through the centre minus the
centre" and "hyperplane (line) not through the centre". -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real Metric
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### Basic facts -/

/-- Basic facts about inversion (Petrunin, p. 73): for `x ≠ c` the inverse `x'` lies on the open ray
from `c` through `x`, `|cx|·|cx'| = R²`, the inverse of `x'` is `x`, the point is fixed exactly when it
lies on the circle, and inside and outside are swapped. -/
@[kb "petrunin2025" "Remarks on inversion, p. 73"]
theorem inversion_basic {c x : P} {R : ℝ} (hR : 0 < R) (hx : x ≠ c) :
    (∃ t : ℝ, 0 < t ∧ inversion c R x -ᵥ c = t • (x -ᵥ c)) ∧
    dist c x * dist c (inversion c R x) = R ^ 2 ∧
    inversion c R (inversion c R x) = x ∧
    (inversion c R x = x ↔ x ∈ sphere c R) ∧
    (dist x c < R ↔ R < dist (inversion c R x) c) ∧
    (R < dist x c ↔ dist (inversion c R x) c < R) := by
  have hd : 0 < dist x c := dist_pos.mpr hx
  refine ⟨⟨(R / dist x c) ^ 2, by positivity, inversion_vsub_center c R x⟩, ?_,
    inversion_inversion c hR.ne' x, ?_, ?_, ?_⟩
  · rw [dist_center_inversion, dist_comm c x]; field_simp
  · refine ⟨fun h => ?_, fun h => inversion_of_mem_sphere h⟩
    have h1 := congrArg (fun y => dist y c) h
    simp only [dist_inversion_center] at h1
    rw [Metric.mem_sphere]
    field_simp at h1
    nlinarith [sq_nonneg (dist x c - R), sq_nonneg (dist x c + R)]
  · rw [dist_inversion_center, lt_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  · rw [dist_inversion_center, div_lt_iff₀ hd]
    constructor <;> intro h <;> nlinarith

/-! ### Lemma 10.2 and the cross-ratio -/

/-- Petrunin, Lemma 10.2 (side-ratio form of `△OAB ∼ △OB'A'`): the inverses `A'`, `B'` of `A`, `B`
satisfy `|A'B'| = R²·|AB| / (|OA|·|OB|)`, and `|OA|·|OA'| = |OB|·|OB'|`. -/
@[kb "petrunin2025" "Lemma 10.2, p. 73"]
theorem dist_inversion_inversion_eq {O A B : P} {R : ℝ} (hA : A ≠ O) (hB : B ≠ O) :
    dist (inversion O R A) (inversion O R B) = R ^ 2 * dist A B / (dist A O * dist B O) ∧
    dist O A * dist O (inversion O R A) = dist O B * dist O (inversion O R B) := by
  refine ⟨?_, ?_⟩
  · rw [dist_inversion_inversion hA hB]; ring
  · rw [dist_center_inversion, dist_center_inversion]
    have h1 : dist O A ≠ 0 := dist_ne_zero.mpr hA.symm
    have h2 : dist O B ≠ 0 := dist_ne_zero.mpr hB.symm
    field_simp

/-- Petrunin, Lemma 10.2: the triangle `OAB` is similar to `OB'A'`. -/
@[kb "petrunin2025" "Lemma 10.2, p. 73"]
theorem similar_inversion {O A B : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O) :
    Similar ![O, A, B] ![O, inversion O R B, inversion O R A] := by
  have hA0 : 0 < dist A O := dist_pos.mpr hA
  have hB0 : 0 < dist B O := dist_pos.mpr hB
  have hr : 0 < dist A O * dist B O / R ^ 2 := by positivity
  rw [similar_iff_exists_dist_eq]
  refine ⟨(dist A O * dist B O / R ^ 2).toNNReal, by simpa using hr, ?_⟩
  rw [Real.coe_toNNReal _ hr.le]
  have e1 := dist_inversion_inversion hA hB R
  have e2 := dist_center_inversion O A R
  have e3 := dist_center_inversion O B R
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  rw [dist_comm O A] at e2
  rw [dist_comm O B] at e3
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dist_comm O A, dist_comm O B, dist_comm B A, dist_comm (inversion O R B) (inversion O R A),
      dist_comm (inversion O R A) O, dist_comm (inversion O R B) O, e2, e3, e1] <;>
    field_simp

/-- The (distance) cross-ratio of four points `A, B, C, D`, namely `AB·CD / (BC·DA)`
(Petrunin, p. 75). -/
noncomputable def crossRatio (A B C D : P) : ℝ :=
  dist A B * dist C D / (dist B C * dist D A)

/-- Petrunin, Theorem 10.6(a): the cross-ratio is unchanged by inversion (the points are distinct from
the centre `O`). -/
@[kb "petrunin2025" "Theorem 10.6(a), p. 74"]
theorem crossRatio_inversion {O A B C D : P} {R : ℝ} (hR : R ≠ 0) (hA : A ≠ O) (hB : B ≠ O)
    (hC : C ≠ O) (hD : D ≠ O) :
    crossRatio (inversion O R A) (inversion O R B) (inversion O R C) (inversion O R D) =
      crossRatio A B C D := by
  unfold crossRatio
  rw [dist_inversion_inversion hA hB, dist_inversion_inversion hC hD,
    dist_inversion_inversion hB hC, dist_inversion_inversion hD hA]
  have hA0 : 0 < dist A O := dist_pos.mpr hA
  have hB0 : 0 < dist B O := dist_pos.mpr hB
  have hC0 : 0 < dist C O := dist_pos.mpr hC
  have hD0 : 0 < dist D O := dist_pos.mpr hD
  have hK : R ^ 2 / (dist A O * dist B O) * (R ^ 2 / (dist C O * dist D O)) ≠ 0 := by positivity
  have : R ^ 2 / (dist B O * dist C O) * dist B C * (R ^ 2 / (dist D O * dist A O) * dist D A) =
      (R ^ 2 / (dist A O * dist B O) * (R ^ 2 / (dist C O * dist D O))) * (dist B C * dist D A) := by
    field_simp
  rw [this, show R ^ 2 / (dist A O * dist B O) * dist A B * (R ^ 2 / (dist C O * dist D O) * dist C D)
    = (R ^ 2 / (dist A O * dist B O) * (R ^ 2 / (dist C O * dist D O))) * (dist A B * dist C D) by
      ring, mul_div_mul_left _ _ hK]

/-! ### Images of circles -/

/-- Centre of the image of the circle `sphere Q s` under the inversion with centre `c`, radius `R`
(Petrunin, Theorem 10.7): `c + R²/(|cQ|² - s²) · (Q - c)`. -/
noncomputable def invSphereCenter (c : P) (R : ℝ) (Q : P) (s : ℝ) : P :=
  AffineMap.lineMap c Q (R ^ 2 / (dist Q c ^ 2 - s ^ 2))

/-- Radius of the image of the circle `sphere Q s`: `R² s / | |cQ|² - s² |`. -/
noncomputable def invSphereRadius (c : P) (R : ℝ) (Q : P) (s : ℝ) : ℝ :=
  R ^ 2 * s / |dist Q c ^ 2 - s ^ 2|

theorem power_ne_zero {c Q : P} {s : ℝ} (hs : 0 ≤ s) (hd : dist Q c ≠ s) :
    dist Q c ^ 2 - s ^ 2 ≠ 0 := by
  intro h
  exact hd ((sq_eq_sq₀ dist_nonneg hs).mp (by linarith))

theorem inversion_mem_invSphere {c Q x : P} {R s : ℝ} (hs : 0 ≤ s) (hd : dist Q c ≠ s)
    (hx : x ∈ sphere Q s) :
    inversion c R x ∈ sphere (invSphereCenter c R Q s) (invSphereRadius c R Q s) := by
  have hd0 := power_ne_zero hs hd
  have hxc : x ≠ c := by
    rintro rfl
    exact hd (by rw [← dist_comm]; exact Metric.mem_sphere.mp hx)
  have hn : 0 < dist x c := dist_pos.mpr hxc
  rw [Metric.mem_sphere] at hx ⊢
  have hu : ‖(x -ᵥ c) - (Q -ᵥ c)‖ ^ 2 = s ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, hx]
  rw [norm_sub_sq_real, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V (Q) c] at hu
  unfold invSphereRadius
  refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
  rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right _ _ c, inversion_vsub_center,
    invSphereCenter, AffineMap.lineMap_vsub_left, norm_sub_sq_real, norm_smul, norm_smul,
    inner_smul_left, inner_smul_right, ← dist_eq_norm_vsub V x c, ← dist_eq_norm_vsub V Q c, div_pow]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
  have hip : ⟪x -ᵥ c, Q -ᵥ c⟫ = (dist x c ^ 2 + dist Q c ^ 2 - s ^ 2) / 2 := by linarith
  rw [hip]
  rw [show (R ^ 2 * s / |dist Q c ^ 2 - s ^ 2|) ^ 2 = R ^ 4 * s ^ 2 / (dist Q c ^ 2 - s ^ 2) ^ 2 by
    rw [div_pow, mul_pow, sq_abs]; ring]
  field_simp
  ring

theorem dist_invSphereCenter (c : P) (R : ℝ) (Q : P) (s : ℝ) :
    dist (invSphereCenter c R Q s) c = |R ^ 2 / (dist Q c ^ 2 - s ^ 2)| * dist Q c := by
  rw [invSphereCenter, dist_lineMap_left, Real.norm_eq_abs, dist_comm c Q]

theorem invSphere_power {c Q : P} {R s : ℝ} (hs : 0 ≤ s) (hd : dist Q c ≠ s) :
    dist (invSphereCenter c R Q s) c ^ 2 - invSphereRadius c R Q s ^ 2 =
      R ^ 4 / (dist Q c ^ 2 - s ^ 2) := by
  have hd0 := power_ne_zero hs hd
  rw [dist_invSphereCenter, invSphereRadius]
  simp only [mul_pow, div_pow, sq_abs]
  field_simp

theorem invSphere_invSphere {c Q : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 ≤ s) (hd : dist Q c ≠ s) :
    invSphereCenter c R (invSphereCenter c R Q s) (invSphereRadius c R Q s) = Q ∧
      invSphereRadius c R (invSphereCenter c R Q s) (invSphereRadius c R Q s) = s := by
  have hd0 := power_ne_zero hs hd
  have hp := invSphere_power (R := R) hs hd
  have hR4 : R ^ 4 ≠ 0 := pow_ne_zero 4 hR
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hQ : invSphereCenter c R Q s = AffineMap.lineMap c Q (R ^ 2 / (dist Q c ^ 2 - s ^ 2)) := rfl
  have hS : invSphereRadius c R Q s = R ^ 2 * s / |dist Q c ^ 2 - s ^ 2| := rfl
  generalize invSphereCenter c R Q s = Q' at *
  generalize invSphereRadius c R Q s = s' at *
  constructor
  · rw [invSphereCenter, hp, hQ, AffineMap.lineMap_apply,
      AffineMap.lineMap_apply, vadd_vsub, smul_smul]
    rw [show R ^ 2 / (R ^ 4 / (dist Q c ^ 2 - s ^ 2)) * (R ^ 2 / (dist Q c ^ 2 - s ^ 2)) = 1 by
      field_simp, one_smul, vsub_vadd]
  · rw [invSphereRadius, hp, hS, abs_div,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ R ^ 4)]
    have : 0 < |dist Q c ^ 2 - s ^ 2| := abs_pos.mpr hd0
    rw [show R ^ 4 = R ^ 2 * R ^ 2 by ring]
    field_simp

/-- **Image of a circle not through the centre** (Petrunin, Theorems 10.7 and 10.11(c)): the inverse
of the circle with centre `Q` and radius `s ≥ 0` not passing through the centre `c` of the inversion
is the circle with centre `c + R²/(|cQ|²-s²)·(Q - c)` and radius `R² s/| |cQ|²-s² |`, which again does
not pass through `c`. -/
@[kb "petrunin2025" "Theorem 10.11(c), p. 77"]
theorem image_inversion_sphere {c Q : P} {R s : ℝ} (hR : R ≠ 0) (hs : 0 ≤ s) (hd : dist Q c ≠ s) :
    inversion c R '' sphere Q s = sphere (invSphereCenter c R Q s) (invSphereRadius c R Q s) ∧
      c ∉ sphere (invSphereCenter c R Q s) (invSphereRadius c R Q s) := by
  have hd0 := power_ne_zero hs hd
  have hp := invSphere_power (R := R) hs hd
  have hs' : 0 ≤ invSphereRadius c R Q s := by unfold invSphereRadius; positivity
  have hd' : dist (invSphereCenter c R Q s) c ≠ invSphereRadius c R Q s := by
    intro h
    have : R ^ 4 / (dist Q c ^ 2 - s ^ 2) = 0 := by rw [← hp, h]; ring
    exact (div_ne_zero (pow_ne_zero 4 hR) hd0) this
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact inversion_mem_invSphere hs hd hx
    · intro hy
      have h := inversion_mem_invSphere (R := R) hs' hd' hy
      obtain ⟨e1, e2⟩ := invSphere_invSphere hR hs hd
      rw [e1, e2] at h
      exact ⟨inversion c R y, h, inversion_inversion c hR y⟩
  · intro h
    exact hd' (by rw [dist_comm]; exact Metric.mem_sphere.mp h)

/-! ### Circles through the centre, lines -/

/-- Petrunin, Theorem 10.11(a): an affine subspace through the centre is inverted into itself. -/
@[kb "petrunin2025" "Theorem 10.11(a), p. 77"]
theorem image_inversion_line_through_centre {c : P} {R : ℝ} (hR : R ≠ 0) {L : AffineSubspace ℝ P}
    (hc : c ∈ L) : inversion c R '' (L : Set P) = L :=
  image_inversion_affineSubspace_of_mem hR hc

/-- A hyperplane (a line in the plane) `{x | ⟪x - c, n⟫ = t}` not through `c` (`t ≠ 0`, `n ≠ 0`) is the
perpendicular bisector of `c` and `y = c + (2t/|n|²) n`. -/
theorem hyperplane_eq_perpBisector (c : P) {n : V} (hn : n ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    {x : P | ⟪x -ᵥ c, n⟫ = t} =
      (AffineSubspace.perpBisector c (((2 * t / ‖n‖ ^ 2) • n) +ᵥ c) : Set P) := by
  have hn2 : ‖n‖ ^ 2 ≠ 0 := by positivity
  ext x
  rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_inner_eq_zero, vsub_midpoint,
    Set.mem_ofPred_eq]
  simp only [vadd_vsub, invOf_eq_inv, vsub_vadd_eq_vsub_sub]
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, conj_trivial]
  have hl : 2 * t / ‖n‖ ^ 2 ≠ 0 := by positivity
  have key : 2 * t / ‖n‖ ^ 2 * (2⁻¹ * ⟪x -ᵥ c, n⟫ +
      2⁻¹ * (⟪x -ᵥ c, n⟫ - 2 * t / ‖n‖ ^ 2 * ‖n‖ ^ 2)) =
      2 * t / ‖n‖ ^ 2 * (⟪x -ᵥ c, n⟫ - t) := by
    field_simp
    ring
  rw [key, mul_eq_zero, sub_eq_zero]
  simp [hl]

/-- **Petrunin, Theorem 10.11(b), line to circle**: a hyperplane `{x | ⟪x - c, n⟫ = t}` (`t ≠ 0`,
so not through the centre `c`) is inverted into the circle through `c` (minus `c` itself) with centre
the inverse `y'` of `y = c + (2t/|n|²) n` and radius `R²/|cy|`. -/
@[kb "petrunin2025" "Theorem 10.11(b), p. 77"]
theorem image_inversion_hyperplane {c : P} {R : ℝ} (hR : R ≠ 0) {n : V} (hn : n ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    inversion c R '' {x : P | ⟪x -ᵥ c, n⟫ = t} =
      sphere (inversion c R (((2 * t / ‖n‖ ^ 2) • n) +ᵥ c))
        (R ^ 2 / dist (((2 * t / ‖n‖ ^ 2) • n) +ᵥ c) c) \ {c} ∧
    c ∉ {x : P | ⟪x -ᵥ c, n⟫ = t} := by
  refine ⟨?_, ?_⟩
  · rw [hyperplane_eq_perpBisector c hn ht]
    refine image_inversion_perpBisector hR ?_
    intro h
    have : (2 * t / ‖n‖ ^ 2) • n = 0 := by
      simpa only [vadd_vsub, vsub_self] using congrArg (· -ᵥ c) h
    rcases smul_eq_zero.mp this with h0 | h0
    · exact (by positivity : 2 * t / ‖n‖ ^ 2 ≠ 0) h0
    · exact hn h0
  · simp [ht.symm]

/-- **Petrunin, Theorem 10.11(b), circle to line**: the circle through the centre `c` of the inversion
with centre `Q ≠ c` (minus the point `c`) is inverted into the hyperplane (line in the plane) which is
the perpendicular bisector of `c` and the inverse of `Q`; this hyperplane misses `c`. -/
@[kb "petrunin2025" "Theorem 10.11(b), p. 77"]
theorem image_inversion_sphere_through_centre {c Q : P} {R : ℝ} (hR : R ≠ 0) (hQ : Q ≠ c) :
    inversion c R '' (sphere Q (dist Q c) \ {c}) =
      (AffineSubspace.perpBisector c (inversion c R Q) : Set P) ∧
    c ∉ (AffineSubspace.perpBisector c (inversion c R Q) : Set P) := by
  have hy : inversion c R Q ≠ c := by simpa [inversion_eq_center hR] using hQ
  have hQ0 : dist Q c ≠ 0 := dist_ne_zero.mpr hQ
  have h1 := image_inversion_perpBisector hR hy
  rw [inversion_inversion c hR, dist_inversion_center] at h1
  rw [show R ^ 2 / (R ^ 2 / dist Q c) = dist Q c by field_simp] at h1
  refine ⟨?_, ?_⟩
  · rw [← h1, Set.image_image]
    simp [inversion_inversion c hR]
  · intro h
    rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq] at h
    simp [hy.symm] at h

/-! ### Perpendicular circles -/

/-- Two circles `Γ`, `Ω` are perpendicular (Petrunin, p. 79) if they meet at a point `X` where the
radii `OX` and `QX` are perpendicular; this is equivalent to the tangent lines at `X` being
perpendicular, since a tangent to a circle at `X` is perpendicular to the radius. -/
def OrthogonalCircles (Γ Ω : Sphere P) : Prop :=
  ∃ X, X ∈ Γ ∧ X ∈ Ω ∧ ⟪X -ᵥ Ω.center, X -ᵥ Γ.center⟫ = 0

private theorem exists_unit_orthogonal (q : V) (hdim : 2 ≤ Module.finrank ℝ V) :
    ∃ w : V, ‖w‖ = 1 ∧ ⟪q, w⟫ = 0 := by
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  have h1 : Module.finrank ℝ (Submodule.span ℝ {q}) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({q} : Set V)
  have h2 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {q})
  have h3 : 0 < Module.finrank ℝ (Submodule.span ℝ {q})ᗮ := by omega
  obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
  refine ⟨(‖(w : V)‖⁻¹) • (w : V), ?_, ?_⟩
  · have : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr this)]
  · rw [inner_smul_right]
    have := (Submodule.mem_orthogonal _ _).mp w.2 q (Submodule.mem_span_singleton_self q)
    rw [this, mul_zero]

/-- Perpendicularity criterion (Petrunin, Theorem 10.15 proof / Lemma 5.22 content): circles with
centres `Q`, `O` and radii `s ≥ 0`, `R > 0` are perpendicular iff `|OQ|² = R² + s²`. The direction
`⇐` needs a point of the circles' intersection, hence dimension at least 2. -/
@[kb "petrunin2025" "Theorem 10.15, p. 79"]
theorem orthogonalCircles_iff {Γ Ω : Sphere P} (hs : 0 ≤ Γ.radius) (hR : 0 < Ω.radius)
    (hdim : 2 ≤ Module.finrank ℝ V) :
    OrthogonalCircles Γ Ω ↔
      dist Ω.center Γ.center ^ 2 = Ω.radius ^ 2 + Γ.radius ^ 2 := by
  constructor
  · rintro ⟨X, hXΓ, hXΩ, hX⟩
    rw [EuclideanGeometry.mem_sphere] at hXΓ hXΩ
    rw [dist_eq_norm_vsub V Ω.center Γ.center,
      ← vsub_sub_vsub_cancel_left Ω.center Γ.center X, norm_sub_sq_real,
      real_inner_comm (X -ᵥ Ω.center) (X -ᵥ Γ.center), hX,
      ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, hXΓ, hXΩ]
    ring
  · intro h
    set O := Ω.center
    set R := Ω.radius
    set s := Γ.radius
    set q : V := Γ.center -ᵥ O with hq
    have hN : ‖q‖ ^ 2 = R ^ 2 + s ^ 2 := by
      rw [hq, ← dist_eq_norm_vsub V, dist_comm]; exact h
    have hNpos : 0 < ‖q‖ := by
      have : 0 < ‖q‖ ^ 2 := by rw [hN]; positivity
      exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at this; simp at this)
    obtain ⟨w, hw1, hw2⟩ := exists_unit_orthogonal q hdim
    set u : V := (R ^ 2 / ‖q‖ ^ 2) • q + (R * s / ‖q‖) • w with hu
    have huq : ⟪u, q⟫ = R ^ 2 := by
      rw [hu, inner_add_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq,
        real_inner_comm, hw2]
      simp only [conj_trivial]
      field_simp
      simp
    have huw : ⟪u, w⟫ = R * s / ‖q‖ := by
      rw [hu, inner_add_left, inner_smul_left, inner_smul_left, hw2, real_inner_self_eq_norm_sq, hw1]
      simp
    have huu : ⟪u, u⟫ = R ^ 2 := by
      calc ⟪u, u⟫ = ⟪u, (R ^ 2 / ‖q‖ ^ 2) • q + (R * s / ‖q‖) • w⟫ := rfl
        _ = R ^ 2 := by
          rw [inner_add_right, inner_smul_right, inner_smul_right, huq, huw, ← mul_div_assoc]
          have : ‖q‖ ^ 2 ≠ 0 := by positivity
          field_simp
          rw [hN]
    have hu2 : ‖u‖ ^ 2 = R ^ 2 := by rw [← real_inner_self_eq_norm_sq]; exact huu
    have hv : (u +ᵥ O) -ᵥ Γ.center = u - q := by
      rw [hq, ← vsub_sub_vsub_cancel_right (u +ᵥ O) Γ.center O, vadd_vsub]
    refine ⟨u +ᵥ O, ?_, ?_, ?_⟩
    · rw [EuclideanGeometry.mem_sphere, dist_eq_norm_vsub V, hv]
      refine (sq_eq_sq₀ (norm_nonneg _) hs).mp ?_
      rw [norm_sub_sq_real, hu2, huq, hN]; ring
    · rw [EuclideanGeometry.mem_sphere, dist_eq_norm_vsub V, vadd_vsub]
      exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp hu2
    · rw [vadd_vsub, hv, inner_sub_right, huu, huq]; ring

theorem inversion_sphere_identity {c Q x : P} {R s : ℝ} (hR : R ≠ 0) (hxc : x ≠ c)
    (hx : x ∈ sphere Q s) (hx' : inversion c R x ∈ sphere Q s) :
    (R ^ 2 - dist x c ^ 2) * (R ^ 2 - (dist Q c ^ 2 - s ^ 2)) = 0 := by
  have hn : 0 < dist x c := dist_pos.mpr hxc
  rw [Metric.mem_sphere] at hx hx'
  have E1 : ‖(x -ᵥ c) - (Q -ᵥ c)‖ ^ 2 = s ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, hx]
  have E2 : ‖(inversion c R x -ᵥ c) - (Q -ᵥ c)‖ ^ 2 = s ^ 2 := by
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub V, hx']
  rw [norm_sub_sq_real, ← dist_eq_norm_vsub V x c, ← dist_eq_norm_vsub V Q c] at E1
  rw [inversion_vsub_center, norm_sub_sq_real, norm_smul, inner_smul_left,
    ← dist_eq_norm_vsub V x c, ← dist_eq_norm_vsub V Q c] at E2
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial] at E2
  set a : ℝ := (R / dist x c) ^ 2 with ha_def
  have ha : a * dist x c ^ 2 = R ^ 2 := by rw [ha_def]; field_simp
  set ip := ⟪x -ᵥ c, Q -ᵥ c⟫
  have E3 : R ^ 4 - 2 * R ^ 2 * ip + dist x c ^ 2 * (dist Q c ^ 2 - s ^ 2) = 0 := by
    linear_combination dist x c ^ 2 * E2 - (R ^ 2 + a * dist x c ^ 2 - 2 * ip) * ha
  linear_combination E3 - R ^ 2 * E1

/-- **Petrunin, Theorem 10.15** (plane, or any space of dimension at least 2): for distinct circles
`Γ ≠ Ω` (positive radii), `Γ ⟂ Ω` iff the inversion across `Ω` maps `Γ` onto itself. -/
@[kb "petrunin2025" "Theorem 10.15, p. 79"]
theorem orthogonalCircles_iff_image_eq {Γ Ω : Sphere P} (hs : 0 < Γ.radius) (hR : 0 < Ω.radius)
    (hne : Γ ≠ Ω) (hdim : 2 ≤ Module.finrank ℝ V) :
    OrthogonalCircles Γ Ω ↔
      inversion Ω.center Ω.radius '' (Γ : Set P) = (Γ : Set P) := by
  have hcrit := orthogonalCircles_iff hs.le hR hdim
  show _ ↔ inversion Ω.center Ω.radius '' Metric.sphere Γ.center Γ.radius =
    Metric.sphere Γ.center Γ.radius
  constructor
  · intro h
    have hN := hcrit.mp h
    rw [dist_comm] at hN
    have hd0 : dist Γ.center Ω.center ≠ Γ.radius := by
      intro h'
      rw [h'] at hN
      nlinarith [pow_pos hR 2]
    have himg := (image_inversion_sphere hR.ne' hs.le hd0).1
    have hp : dist Γ.center Ω.center ^ 2 - Γ.radius ^ 2 = Ω.radius ^ 2 := by linarith
    have e1 : invSphereCenter Ω.center Ω.radius Γ.center Γ.radius = Γ.center := by
      rw [invSphereCenter, hp, div_self (pow_ne_zero 2 hR.ne'), AffineMap.lineMap_apply_one]
    have e2 : invSphereRadius Ω.center Ω.radius Γ.center Γ.radius = Γ.radius := by
      rw [invSphereRadius, hp, abs_of_pos (pow_pos hR 2)]
      field_simp
    rw [e1, e2] at himg
    exact himg
  · intro himg
    rw [hcrit]
    by_contra hcon
    set O := Ω.center
    set R := Ω.radius
    set Q := Γ.center
    set s := Γ.radius
    set q : V := Q -ᵥ O with hq
    have hNq : ‖q‖ = dist Q O := (dist_eq_norm_vsub V Q O).symm
    -- every point of `Γ` other than `O` lies on `Ω`
    have hall : ∀ x : P, dist x Q = s → x ≠ O → dist x O ^ 2 = R ^ 2 := by
      intro x hx hxO
      have hxmem : x ∈ sphere Q s := hx
      have himg' : inversion O R x ∈ sphere Q s := by
        rw [← himg]; exact ⟨x, hxmem, rfl⟩
      have := inversion_sphere_identity (c := O) hR.ne' hxO hxmem himg'
      have hd : R ^ 2 - (dist Q O ^ 2 - s ^ 2) ≠ 0 := by
        intro h0
        apply hcon
        rw [dist_comm]
        linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hd
    obtain ⟨w, hw1, hw2⟩ := exists_unit_orthogonal q hdim
    have hx2 : dist ((s • w) +ᵥ Q) Q = s := by
      rw [dist_vadd_left, norm_smul, hw1, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    have hx2O : dist ((s • w) +ᵥ Q) O ^ 2 = s ^ 2 + dist Q O ^ 2 := by
      rw [dist_eq_norm_vsub V, vadd_vsub_assoc, ← hq, norm_add_sq_real, inner_smul_left,
        (real_inner_comm q w).trans hw2]
      simp [norm_smul, hw1, hNq, abs_of_pos hs]
    have hx2ne : (s • w) +ᵥ Q ≠ O := by
      intro h0
      rw [h0, dist_self] at hx2O
      nlinarith [pow_pos hs 2, sq_nonneg (dist Q O)]
    have hR2 := hall _ hx2 hx2ne
    rw [hx2O] at hR2
    by_cases hN0 : dist Q O = 0
    · apply hne
      have hQO : Q = O := dist_eq_zero.mp hN0
      rw [hN0] at hR2
      have : s = R := by nlinarith
      exact Sphere.ext hQO this
    · have hNpos : 0 < dist Q O := lt_of_le_of_ne dist_nonneg (Ne.symm hN0)
      have hx1 : dist (((s / dist Q O) • q) +ᵥ Q) Q = s := by
        rw [dist_vadd_left, norm_smul, hNq, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
      have hx1O : dist (((s / dist Q O) • q) +ᵥ Q) O = s + dist Q O := by
        rw [dist_eq_norm_vsub V, vadd_vsub_assoc, ← hq, ← one_smul ℝ q, smul_smul, ← add_smul,
          norm_smul, hNq, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
      have hx1ne : ((s / dist Q O) • q) +ᵥ Q ≠ O := by
        intro h0
        rw [h0, dist_self] at hx1O
        linarith
      have := hall _ hx1 hx1ne
      rw [hx1O] at this
      nlinarith [mul_pos hs hNpos]

/-- **Petrunin, Corollary 10.17** (dimension at least 2): if a circle `Γ` passes through a point `P`
and its inverse `P' ≠ P` across `Ω` (positive radius), then `Γ ⟂ Ω`. -/
@[kb "petrunin2025" "Corollary 10.17, p. 80"]
theorem orthogonalCircles_of_mem_inverse {Γ Ω : Sphere P} {X : P} (hR : 0 < Ω.radius)
    (hdim : 2 ≤ Module.finrank ℝ V) (hX : X ∈ Γ) (hX' : inversion Ω.center Ω.radius X ∈ Γ)
    (hne : inversion Ω.center Ω.radius X ≠ X) : OrthogonalCircles Γ Ω := by
  have hXO : X ≠ Ω.center := by
    rintro rfl
    exact hne (inversion_self _ _)
  have hdist : dist X Ω.center ≠ Ω.radius := fun h =>
    hne (inversion_of_mem_sphere (Metric.mem_sphere.mpr h))
  have hXd : dist X Γ.center = Γ.radius := hX
  have hs : 0 ≤ Γ.radius := hXd ▸ dist_nonneg
  have hid := inversion_sphere_identity (c := Ω.center) hR.ne' hXO
    (Metric.mem_sphere.mpr hXd) (Metric.mem_sphere.mpr hX')
  rcases mul_eq_zero.mp hid with h0 | h0
  · exact absurd ((sq_eq_sq₀ dist_nonneg hR.le).mp (by linarith)) hdist
  · rw [orthogonalCircles_iff hs hR hdim, dist_comm]
    linarith

/-- **Petrunin, Corollary 10.18** (two points inside a circle, not collinear with its centre; the
collinear case is the degenerate circline, a line): two distinct points `P`, `Q` inside `Ω` lie on a
circle perpendicular to `Ω`. (Uniqueness is not formalized.) -/
@[kb "petrunin2025" "Corollary 10.18, p. 80"]
theorem exists_orthogonalCircle_through_two_points {Ω : Sphere P} {A B : P} (hR : 0 < Ω.radius)
    (hdim : 2 ≤ Module.finrank ℝ V) (hA : dist A Ω.center < Ω.radius)
    (_hB : dist B Ω.center < Ω.radius) (hcol : ¬Collinear ℝ ({Ω.center, A, B} : Set P)) :
    ∃ Γ : Sphere P, OrthogonalCircles Γ Ω ∧ A ∈ Γ ∧ B ∈ Γ := by
  set O := Ω.center
  set R := Ω.radius
  set A' := inversion O R A with hA'
  have hAO : A ≠ O := by
    intro h
    apply hcol
    rw [h]
    simpa using collinear_pair ℝ O B
  have hne : A' ≠ A := by
    intro h
    have := (inversion_basic hR hAO).2.2.2.1.mp h
    rw [Metric.mem_sphere] at this
    linarith
  have hcolA : Collinear ℝ ({A, A', O} : Set P) := by
    have : A' ∈ line[ℝ, O, A] := by
      rw [hA', inversion_eq_lineMap]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have h2 : Collinear ℝ ({A', O, A} : Set P) := collinear_insert_of_mem_affineSpan_pair this
    have : ({A, A', O} : Set P) = {A', O, A} := by ext; simp; tauto
    rwa [this]
  have hind : AffineIndependent ℝ ![A, B, A'] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hc
    apply hcol
    have h1 : B ∈ line[ℝ, A, A'] := hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne.symm
    have h2 : O ∈ line[ℝ, A, A'] := hcolA.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne.symm
    have h3 := collinear_insert_insert_of_mem_affineSpan_pair h2 h1
    exact h3.subset (by intro x hx; simp at hx ⊢; tauto)
  let T : Affine.Triangle ℝ P := ⟨![A, B, A'], hind⟩
  refine ⟨T.circumsphere, ?_, T.mem_circumsphere 0, T.mem_circumsphere 1⟩
  exact orthogonalCircles_of_mem_inverse hR hdim (T.mem_circumsphere 0) (T.mem_circumsphere 2) hne

/-- **Petrunin, Theorem 10.12, line case**: if `A, B, C, D` lie on a line in this order, then
`AB·CD + BC·DA = AC·BD`. -/
@[kb "petrunin2025" "Theorem 10.12, p. 77"]
theorem ptolemy_line {A B C D : P} (h₁ : Sbtw ℝ A B C) (h₂ : Sbtw ℝ B C D) :
    dist A B * dist C D + dist B C * dist D A = dist A C * dist B D := by
  have hABD : Wbtw ℝ A B D := h₁.wbtw.trans_expand_left h₂.wbtw h₁.right_ne.symm
  have e1 := h₁.wbtw.dist_add_dist
  have e2 := h₂.wbtw.dist_add_dist
  have e3 := hABD.dist_add_dist
  have hAD : dist A D = dist A B + dist B C + dist C D := by linarith
  rw [dist_comm D A, hAD, ← e1, ← e2]
  ring

/-- **Petrunin, Theorem 10.12, circle case** (Mathlib's Ptolemy theorem): for `A, B, C, D` on a
sphere whose diagonals `[AC]` and `[BD]` meet in a point `p` between the endpoints, i.e.
the points appear in the cyclic order `A, B, C, D`, one has `AB·CD + BC·DA = AC·BD`. -/
@[kb "petrunin2025" "Theorem 10.12, p. 77"]
theorem ptolemy_circle {A B C D p : P} (h : Cospherical ({A, B, C, D} : Set P))
    (hapc : ∠ A p C = π) (hbpd : ∠ B p D = π) :
    dist A B * dist C D + dist B C * dist D A = dist A C * dist B D :=
  mul_dist_add_mul_dist_eq_mul_dist_of_cospherical h hapc hbpd

/-- **Petrunin, Theorem 10.6(c)**: if four points lie on a circle not through the centre `c` of the
inversion, their inverses again lie on a circle not through `c`. -/
@[kb "petrunin2025" "Theorem 10.6(c), p. 74"]
theorem inscribed_inversion {c A B C D : P} {R : ℝ} (hR : R ≠ 0) {Γ : Sphere P} (hc : c ∉ Γ)
    (hA : A ∈ Γ) (hB : B ∈ Γ) (hC : C ∈ Γ) (hD : D ∈ Γ) :
    ∃ Γ' : Sphere P, c ∉ Γ' ∧ inversion c R A ∈ Γ' ∧ inversion c R B ∈ Γ' ∧
      inversion c R C ∈ Γ' ∧ inversion c R D ∈ Γ' := by
  have hs : 0 ≤ Γ.radius := (show dist A Γ.center = Γ.radius from hA) ▸ dist_nonneg
  have hd : dist Γ.center c ≠ Γ.radius := fun h => hc (by
    show dist c Γ.center = Γ.radius
    rwa [dist_comm])
  obtain ⟨himg, hnc⟩ := image_inversion_sphere hR hs hd
  have key : ∀ X ∈ Γ, inversion c R X ∈
      sphere (invSphereCenter c R Γ.center Γ.radius) (invSphereRadius c R Γ.center Γ.radius) :=
    fun X hX => himg ▸ Set.mem_image_of_mem _ hX
  exact ⟨⟨_, _⟩, hnc, key A hA, key B hB, key C hC, key D hD⟩

/-- **Apollonian circle** (Petrunin, p. 74): for distinct `A`, `B` and `k > 0`, `k ≠ 1`, the locus
`{X | XA = k·XB}` is the circle with centre `B + (A - B)/(1-k²)` and radius `k·AB/|1-k²|`, and
`B` is the inverse of `A` across this circle. -/
@[kb "petrunin2025" "Definition after Exercise 10.3, p. 74"]
theorem apollonian_sphere {A B : P} (hAB : A ≠ B) {k : ℝ} (hk : 0 < k) (hk1 : k ≠ 1) :
    {X : P | dist X A = k * dist X B} =
      sphere (AffineMap.lineMap B A (1 / (1 - k ^ 2))) (k * dist A B / |1 - k ^ 2|) ∧
    inversion (AffineMap.lineMap B A (1 / (1 - k ^ 2))) (k * dist A B / |1 - k ^ 2|) A = B := by
  have hm : 1 - k ^ 2 ≠ 0 := by
    intro h
    have : (k - 1) * (k + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact hk1 (by linarith)
    · linarith
  set m := 1 - k ^ 2 with hm_def
  set t : ℝ := 1 / m with ht
  set C := AffineMap.lineMap B A t with hC
  have hCB : C -ᵥ B = t • (A -ᵥ B) := AffineMap.lineMap_vsub_left _ _ _
  have hAB0 : 0 < dist A B := dist_pos.mpr hAB
  clear_value C t m
  refine ⟨?_, ?_⟩
  · ext X
    simp only [Set.mem_ofPred_eq, Metric.mem_sphere]
    have e1 : dist X A = ‖(X -ᵥ B) - (A -ᵥ B)‖ := by
      rw [vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]
    have e2 : dist X C = ‖(X -ᵥ B) - t • (A -ᵥ B)‖ := by
      rw [← hCB, vsub_sub_vsub_cancel_right, dist_eq_norm_vsub V]
    have e3 : dist X B = ‖X -ᵥ B‖ := dist_eq_norm_vsub V X B
    have e4 : dist A B = ‖A -ᵥ B‖ := dist_eq_norm_vsub V A B
    rw [← sq_eq_sq₀ dist_nonneg (by positivity : 0 ≤ k * dist A B / |m|),
      ← sq_eq_sq₀ dist_nonneg (mul_nonneg hk.le dist_nonneg)]
    rw [e1, e2, e3, mul_pow, div_pow, mul_pow, sq_abs, norm_sub_sq_real, norm_sub_sq_real,
      norm_smul, inner_smul_right, e4]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    rw [e4] at *
    set ip := ⟪X -ᵥ B, A -ᵥ B⟫
    have key : ‖X -ᵥ B‖ ^ 2 - 2 * (t * ip) + t ^ 2 * ‖A -ᵥ B‖ ^ 2 - k ^ 2 * ‖A -ᵥ B‖ ^ 2 / m ^ 2 =
        t * (‖X -ᵥ B‖ ^ 2 - 2 * ip + ‖A -ᵥ B‖ ^ 2 - k ^ 2 * ‖X -ᵥ B‖ ^ 2) := by
      have hk2 : k ^ 2 = 1 - m := by rw [hm_def]; ring
      rw [ht, hk2]; field_simp; ring
    constructor
    · intro h; linear_combination key + t * h
    · intro h
      have : t * (‖X -ᵥ B‖ ^ 2 - 2 * ip + ‖A -ᵥ B‖ ^ 2 - k ^ 2 * ‖X -ᵥ B‖ ^ 2) = 0 := by
        rw [← key]; linarith
      have htne : t ≠ 0 := by rw [ht]; positivity
      have := (mul_eq_zero.mp this).resolve_left htne
      linarith
  · have hk2 : k ^ 2 = 1 - m := by rw [hm_def]; ring
    have hAC : A -ᵥ C = (1 - t) • (A -ᵥ B) := by
      rw [← vsub_sub_vsub_cancel_right A C B, hCB, sub_smul, one_smul]
    have h1t : 1 - t = -(k ^ 2) / m := by
      rw [ht, hk2]; field_simp; ring
    have hmabs : 0 < |m| := abs_pos.mpr hm
    have hdAC : dist A C = k ^ 2 * dist A B / |m| := by
      rw [dist_eq_norm_vsub V, hAC, norm_smul, Real.norm_eq_abs, h1t, abs_div, abs_neg,
        abs_of_pos (pow_pos hk 2), ← dist_eq_norm_vsub V A B]
      ring
    have hratio : k * dist A B / |m| / (k ^ 2 * dist A B / |m|) = 1 / k := by
      field_simp
    have hBC : B -ᵥ C = -(t • (A -ᵥ B)) := by rw [← hCB, neg_vsub_eq_vsub_rev]
    rw [inversion, hdAC, hratio, hAC, eq_comm, eq_vadd_iff_vsub_eq, smul_smul, hBC, ← neg_smul]
    congr 2
    rw [h1t, ht]
    field_simp

end UndergradKB.Geometry
