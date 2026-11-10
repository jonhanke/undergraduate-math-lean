import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Angle
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.Radian
import UndergradKB.Trigonometry.Reciprocal
import UndergradKB.Trigonometry.PolarCurves
import UndergradKB.Trigonometry.ArcLength
import UndergradKB.Trigonometry.Quadrants
import UndergradKB.Trigonometry.RightTriangle

/-! # Angle vocabulary (Corral §1.1, §1.3, §1.4, §4.1, §5.1; OpenStax §7.1-§7.4, §9.2)

The words of the first trigonometry chapters, stated against Mathlib's angles:
* acute / right / obtuse / straight angles, complementary / supplementary / conjugate angles (TR-001,
  TR-002);
* minutes and seconds, grads, the degree as `1/360` of a turn (TR-004, TR-007, TR-009);
* hypotenuse, opposite and adjacent sides in a right triangle (TR-012); angles of elevation and depression
  (TR-022);
* quadrantal angles and quadrants (TR-037, TR-039); standard position (TR-005); angles as pairs of rays
  (TR-008); trigonometric functions of a point on the terminal side (TR-023); the table at the quadrantal
  angles with the undefined entries made precise (TR-026); arc length on the unit circle (TR-036).

Angles are real numbers measured in radians; the plane is `ℂ`.
-/

namespace UndergradKB.Trigonometry

open Real Filter Topology EuclideanGeometry

/-! ### Kinds of angles (TR-001) -/

/-- An acute angle: between `0` and a right angle (exclusive). -/
def IsAcuteAngle (θ : ℝ) : Prop := 0 < θ ∧ θ < π / 2

/-- A right angle: `π/2` radians. -/
def IsRightAngle (θ : ℝ) : Prop := θ = π / 2

/-- An obtuse angle: between a right angle and a straight angle (exclusive). -/
def IsObtuseAngle (θ : ℝ) : Prop := π / 2 < θ ∧ θ < π

/-- A straight angle: `π` radians. -/
def IsStraightAngle (θ : ℝ) : Prop := θ = π

/-- A real number in `(0, π]` is acute, right, obtuse or straight. (TR-001) -/
theorem angle_kind_cases {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π) :
    IsAcuteAngle θ ∨ IsRightAngle θ ∨ IsObtuseAngle θ ∨ IsStraightAngle θ := by
  unfold IsAcuteAngle IsRightAngle IsObtuseAngle IsStraightAngle
  rcases lt_trichotomy θ (π / 2) with h | h | h
  · exact Or.inl ⟨h0, h⟩
  · exact Or.inr (Or.inl h)
  · rcases h1.lt_or_eq with h' | h'
    · exact Or.inr (Or.inr (Or.inl ⟨h, h'⟩))
    · exact Or.inr (Or.inr (Or.inr h'))

/-- The four kinds of angle exclude each other. (TR-001) -/
theorem angle_kinds_exclusive (θ : ℝ) :
    ¬ (IsAcuteAngle θ ∧ IsRightAngle θ) ∧ ¬ (IsAcuteAngle θ ∧ IsObtuseAngle θ) ∧
    ¬ (IsAcuteAngle θ ∧ IsStraightAngle θ) ∧ ¬ (IsRightAngle θ ∧ IsObtuseAngle θ) ∧
    ¬ (IsRightAngle θ ∧ IsStraightAngle θ) ∧ ¬ (IsObtuseAngle θ ∧ IsStraightAngle θ) := by
  unfold IsAcuteAngle IsRightAngle IsObtuseAngle IsStraightAngle
  have := pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_, _⟩, _⟩; linarith
  · rintro ⟨⟨_, _⟩, _, _⟩; linarith
  · rintro ⟨⟨_, _⟩, _⟩; linarith
  · rintro ⟨_, _, _⟩; linarith
  · rintro ⟨_, _⟩; linarith
  · rintro ⟨⟨_, _⟩, _⟩; linarith

section Geometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Kinds of angles**: every non-zero unoriented angle `∠ A O B` is acute, right, obtuse or straight, and
exactly one of these holds. (TR-001) -/
@[kb "corraltrig" "Box §1.1, p. 9"]
theorem angle_kind_unique (A O B : P) (h : 0 < ∠ A O B) :
    (IsAcuteAngle (∠ A O B) ∨ IsRightAngle (∠ A O B) ∨ IsObtuseAngle (∠ A O B) ∨
      IsStraightAngle (∠ A O B)) ∧
    ¬ (IsAcuteAngle (∠ A O B) ∧ IsRightAngle (∠ A O B)) ∧
    ¬ (IsAcuteAngle (∠ A O B) ∧ IsObtuseAngle (∠ A O B)) ∧
    ¬ (IsAcuteAngle (∠ A O B) ∧ IsStraightAngle (∠ A O B)) ∧
    ¬ (IsRightAngle (∠ A O B) ∧ IsObtuseAngle (∠ A O B)) ∧
    ¬ (IsRightAngle (∠ A O B) ∧ IsStraightAngle (∠ A O B)) ∧
    ¬ (IsObtuseAngle (∠ A O B) ∧ IsStraightAngle (∠ A O B)) :=
  ⟨angle_kind_cases h (angle_le_pi A O B), angle_kinds_exclusive _⟩

/-- **At least two acute angles**: if the three angles of a triangle are positive, at least two of them are
acute. (TR-001) -/
@[kb "corraltrig" "Box §1.1, p. 9"]
theorem two_angles_acute {p₁ p₂ p₃ : P} (h12 : p₂ ≠ p₁) (h1 : 0 < ∠ p₁ p₂ p₃) (h2 : 0 < ∠ p₂ p₃ p₁)
    (h3 : 0 < ∠ p₃ p₁ p₂) :
    (IsAcuteAngle (∠ p₁ p₂ p₃) ∧ IsAcuteAngle (∠ p₂ p₃ p₁)) ∨
    (IsAcuteAngle (∠ p₂ p₃ p₁) ∧ IsAcuteAngle (∠ p₃ p₁ p₂)) ∨
    (IsAcuteAngle (∠ p₁ p₂ p₃) ∧ IsAcuteAngle (∠ p₃ p₁ p₂)) := by
  have hs := angle_add_angle_add_angle_eq_pi p₃ h12
  unfold IsAcuteAngle
  by_cases a : ∠ p₁ p₂ p₃ < π / 2 <;> by_cases b : ∠ p₂ p₃ p₁ < π / 2 <;>
    by_cases c : ∠ p₃ p₁ p₂ < π / 2
  · exact Or.inl ⟨⟨h1, a⟩, h2, b⟩
  · exact Or.inl ⟨⟨h1, a⟩, h2, b⟩
  · exact Or.inr (Or.inr ⟨⟨h1, a⟩, h3, c⟩)
  · exfalso; linarith
  · exact Or.inr (Or.inl ⟨⟨h2, b⟩, h3, c⟩)
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

end Geometry

/-! ### Complementary, supplementary and conjugate angles (TR-002) -/

/-- Complementary angles: the sum is a right angle. -/
def AreComplementary (α β : ℝ) : Prop := α + β = π / 2

/-- Supplementary angles: the sum is a straight angle. -/
def AreSupplementary (α β : ℝ) : Prop := α + β = π

/-- Conjugate angles (explementary): the sum is a full turn. -/
def AreConjugate (α β : ℝ) : Prop := α + β = 2 * π

/-- **Complementary angles** have `sin β = cos α` and `cos β = sin α`. (TR-002) -/
@[kb "openstaxalgtrig2e" "§9.2, p. 831"]
theorem sin_cos_of_complementary {α β : ℝ} (h : AreComplementary α β) :
    sin β = cos α ∧ cos β = sin α := by
  have : β = π / 2 - α := by unfold AreComplementary at h; linarith
  subst this
  exact ⟨sin_pi_div_two_sub α, cos_pi_div_two_sub α⟩

/-- **Supplementary angles** have the same sine and opposite cosines. (TR-002) -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem sin_cos_of_supplementary {α β : ℝ} (h : AreSupplementary α β) :
    sin β = sin α ∧ cos β = - cos α := by
  have : β = π - α := by unfold AreSupplementary at h; linarith
  subst this
  exact ⟨sin_pi_sub α, cos_pi_sub α⟩

/-- **Conjugate angles** have the same cosine and opposite sines. (TR-002) -/
theorem sin_cos_of_conjugate {α β : ℝ} (h : AreConjugate α β) :
    sin β = - sin α ∧ cos β = cos α := by
  have : β = 2 * π - α := by unfold AreConjugate at h; linarith
  subst this
  rw [sin_two_pi_sub, cos_two_pi_sub]
  exact ⟨rfl, rfl⟩

section Geometry2

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- If `O` lies strictly between `A` and `C`, the angles `∠ A O B` and `∠ B O C` are supplementary (a linear
pair). (TR-002) -/
@[kb "corraltrig" "Box §1.1, p. 10"]
theorem areSupplementary_angle_of_sbtw {A O C : P} (B : P) (h : Sbtw ℝ A O C) :
    AreSupplementary (∠ A O B) (∠ B O C) := by
  have h' := angle_add_angle_eq_pi_of_angle_eq_pi B h.angle₁₂₃_eq_pi
  rw [angle_comm B O A] at h'
  exact h'

end Geometry2

/-! ### Minutes, seconds, grads, the degree (TR-004, TR-007, TR-009) -/

/-- `d` degrees, `m` minutes, `s` seconds, as a number of degrees. -/
noncomputable def dmsToDeg (d m s : ℝ) : ℝ := d + m / 60 + s / 3600

/-- **Minutes and seconds**: a minute is `1/60` of a degree, a second is `1/60` of a minute. (TR-004) -/
@[kb "corraltrig" "Box §1.3, p. 24"]
theorem dmsToDeg_minute_second :
    dmsToDeg 0 1 0 = 1 / 60 ∧ dmsToDeg 0 0 1 = dmsToDeg 0 (1 / 60) 0 := by
  unfold dmsToDeg; constructor <;> ring

/-- A measure in degrees, minutes and seconds corresponds to `π (d + m/60 + s/3600) / 180` radians. (TR-004) -/
theorem degToRad_dmsToDeg (d m s : ℝ) : degToRad (dmsToDeg d m s) = π * (d + m / 60 + s / 3600) / 180 := rfl

/-- A grad (gon): the angle `g` grads is `π g / 200` radians (`400` grads make a full turn). -/
noncomputable def gradToRad (g : ℝ) : ℝ := π * g / 200

/-- **Grads**: `400` grads are a full turn, `100` grads a right angle (`= 90°`). (TR-007) -/
@[kb "corraltrig" "Box §4.1, p. 96 (footnote)"]
theorem gradToRad_spec :
    gradToRad 400 = 2 * π ∧ gradToRad 100 = π / 2 ∧ gradToRad 100 = degToRad 90 := by
  unfold gradToRad degToRad
  refine ⟨by ring, by ring, by ring⟩

/-- **The degree**: one degree is `1/360` of a full rotation, a full rotation of `360°` is the zero angle
modulo `2π`, and adding `360°` does not change an angle. (TR-009) -/
@[kb "openstaxalgtrig2e" "§7.1, p. 676"]
theorem degToRad_one_eq_turn_div :
    degToRad 1 = 2 * π / 360 ∧ ((degToRad 360 : ℝ) : Real.Angle) = 0 ∧
      ∀ x : ℝ, ((degToRad (x + 360) : ℝ) : Real.Angle) = ((degToRad x : ℝ) : Real.Angle) := by
  refine ⟨by unfold degToRad; ring, ?_, fun x => ?_⟩
  · rw [(degToRad_spec).1]; exact Real.Angle.coe_two_pi
  · have : degToRad (x + 360) = degToRad x + 2 * π := by unfold degToRad; ring
    rw [this, Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]

/-! ### Right triangles (TR-012) -/

section RightTriangle

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Hypotenuse**: in a right triangle with the right angle at `p₂`, the hypotenuse `p₁p₃` is strictly
longer than each leg, and its square is the sum of the squares of the legs. (TR-012) -/
@[kb "corraltrig" "Def §1.1, p. 12"]
theorem hypotenuse_longest {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) (h32 : p₃ ≠ p₂) :
    dist p₁ p₂ < dist p₁ p₃ ∧ dist p₃ p₂ < dist p₁ p₃ ∧
      dist p₁ p₃ ^ 2 = dist p₁ p₂ ^ 2 + dist p₃ p₂ ^ 2 :=
  ⟨(legs_lt_hypotenuse h h12 h32).1, (legs_lt_hypotenuse h h12 h32).2,
    by have := (dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two p₁ p₂ p₃).2 h
       nlinarith⟩

/-- **Opposite and adjacent sides**: for the acute angle at `p₃` of a right triangle with right angle at
`p₂`, the opposite side is `p₁p₂`, the adjacent side is `p₃p₂`, and the sine, cosine and tangent are the
ratios opposite/hypotenuse, adjacent/hypotenuse, opposite/adjacent. (TR-012) -/
@[kb "openstaxalgtrig2e" "§7.2, p. 698"]
theorem ratios_opposite_adjacent {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h12 : p₁ ≠ p₂) :
    sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ ∧ cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ ∧
      tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ :=
  ⟨sin_angle_of_angle_eq_pi_div_two h (Or.inl h12), cos_angle_of_angle_eq_pi_div_two h,
    tan_angle_of_angle_eq_pi_div_two h⟩

end RightTriangle

/-! ### Angles of elevation and depression (TR-022) -/

/-- The angle between the horizontal ray (direction `1`) and the line of sight to the point at horizontal
distance `d` and height `h` (the observer is at the origin). It is the angle of elevation if `h > 0` and the
angle of depression if `h < 0`. -/
noncomputable def elevationAngle (d h : ℝ) : ℝ := InnerProductGeometry.angle (1 : ℂ) (⟨d, h⟩ : ℂ)

/-- **Elevation and depression**: for `d > 0` the angle of elevation (for `h > 0`) or depression (for
`h < 0`) is `arctan (|h| / d)`, hence `|h| = d tan(angle)`. (TR-022) -/
@[kb "openstaxalgtrig2e" "§7.2, p. 705"]
theorem elevationAngle_eq_arctan {d h : ℝ} (hd : 0 < d) :
    elevationAngle d h = Real.arctan (|h| / d) ∧ |h| = d * Real.tan (elevationAngle d h) := by
  have hz : (⟨d, h⟩ : ℂ) ≠ 0 := fun e => by
    have := congrArg Complex.re e; simp at this; linarith
  have hang : elevationAngle d h = |Complex.arg (⟨d, h⟩ : ℂ)| := Complex.angle_one_left hz
  have hlt : |Complex.arg (⟨d, h⟩ : ℂ)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hd)
  have ht : Real.tan (Complex.arg (⟨d, h⟩ : ℂ)) = h / d := Complex.tan_arg (⟨d, h⟩ : ℂ)
  have htan : Real.tan (elevationAngle d h) = |h| / d := by
    rw [hang]
    rcases le_or_gt 0 h with h0 | h0
    · have : 0 ≤ Complex.arg (⟨d, h⟩ : ℂ) := Complex.arg_nonneg_iff.2 h0
      rw [abs_of_nonneg this, ht, abs_of_nonneg h0]
    · have : Complex.arg (⟨d, h⟩ : ℂ) < 0 := Complex.arg_neg_iff.2 h0
      rw [abs_of_neg this, Real.tan_neg, ht, abs_of_neg h0, neg_div]
  refine ⟨?_, ?_⟩
  · rw [← htan, Real.arctan_tan]
    · rw [hang]; linarith [abs_lt.1 hlt, abs_nonneg (Complex.arg (⟨d, h⟩ : ℂ))]
    · rw [hang]; exact hlt
  · rw [htan]; field_simp

/-! ### Quadrantal angles and quadrants (TR-037, TR-039) -/

/-- A quadrantal angle: a multiple of a right angle. -/
def IsQuadrantal (θ : ℝ) : Prop := ∃ k : ℤ, θ = k * (π / 2)

/-- **Quadrantal angles**: an angle is quadrantal iff its terminal side lies on a coordinate axis, i.e. iff
`sin θ = 0` or `cos θ = 0`, i.e. iff the point of the unit circle at angle `θ` has a zero coordinate.
(TR-037) -/
@[kb "openstaxalgtrig2e" "Box §7.1, p. 678"]
theorem isQuadrantal_iff (θ : ℝ) :
    (IsQuadrantal θ ↔ sin θ = 0 ∨ cos θ = 0) ∧
    (IsQuadrantal θ ↔ (polarPoint 1 θ).re = 0 ∨ (polarPoint 1 θ).im = 0) := by
  have key : IsQuadrantal θ ↔ sin θ = 0 ∨ cos θ = 0 := by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
      · left
        rw [sin_eq_zero_iff]; exact ⟨n, by push_cast; ring⟩
      · right
        rw [cos_eq_zero_iff]; exact ⟨n, by push_cast; ring⟩
    · rintro (h | h)
      · obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 h
        exact ⟨2 * n, by rw [← hn]; push_cast; ring⟩
      · obtain ⟨n, hn⟩ := cos_eq_zero_iff.1 h
        exact ⟨2 * n + 1, by rw [hn]; push_cast; ring⟩
  refine ⟨key, ?_⟩
  rw [key, polarPoint_re, polarPoint_im]
  simp only [one_mul]
  exact or_comm

/-- The first quadrant: `x > 0`, `y > 0`. -/
def InQuadrantI (z : ℂ) : Prop := 0 < z.re ∧ 0 < z.im
/-- The second quadrant: `x < 0`, `y > 0`. -/
def InQuadrantII (z : ℂ) : Prop := z.re < 0 ∧ 0 < z.im
/-- The third quadrant: `x < 0`, `y < 0`. -/
def InQuadrantIII (z : ℂ) : Prop := z.re < 0 ∧ z.im < 0
/-- The fourth quadrant: `x > 0`, `y < 0`. -/
def InQuadrantIV (z : ℂ) : Prop := 0 < z.re ∧ z.im < 0

/-- The `k`-th quadrant (`k = 0, 1, 2, 3` for I, II, III, IV, numbered in the direction of positive
rotation). -/
def InQuadrant : Fin 4 → ℂ → Prop
  | 0 => InQuadrantI
  | 1 => InQuadrantII
  | 2 => InQuadrantIII
  | 3 => InQuadrantIV

/-- **Quadrants**: every point off the axes lies in exactly one quadrant. (TR-039) -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem existsUnique_quadrant {z : ℂ} (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    ∃! k : Fin 4, InQuadrant k z := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · refine ⟨2, ⟨hx, hy⟩, fun k hk => ?_⟩
    fin_cases k <;> simp_all [InQuadrant, InQuadrantI, InQuadrantII, InQuadrantIII, InQuadrantIV] <;>
      linarith
  · refine ⟨1, ⟨hx, hy⟩, fun k hk => ?_⟩
    fin_cases k <;> simp_all [InQuadrant, InQuadrantI, InQuadrantII, InQuadrantIII, InQuadrantIV] <;>
      linarith
  · refine ⟨3, ⟨hx, hy⟩, fun k hk => ?_⟩
    fin_cases k <;> simp_all [InQuadrant, InQuadrantI, InQuadrantII, InQuadrantIII, InQuadrantIV] <;>
      linarith
  · refine ⟨0, ⟨hx, hy⟩, fun k hk => ?_⟩
    fin_cases k <;> simp_all [InQuadrant, InQuadrantI, InQuadrantII, InQuadrantIII, InQuadrantIV] <;>
      linarith

/-- A point on the axes lies in no quadrant. (TR-039) -/
theorem not_inQuadrant_of_axis {z : ℂ} (h : z.re = 0 ∨ z.im = 0) (k : Fin 4) : ¬ InQuadrant k z := by
  fin_cases k <;> simp [InQuadrant, InQuadrantI, InQuadrantII, InQuadrantIII, InQuadrantIV] <;>
    rcases h with h | h <;> simp [h]

/-- **Angles and quadrants**: for `r > 0` and `kπ/2 < θ < (k+1)π/2` (`k = 0, 1, 2, 3`) the point with polar
coordinates `(r, θ)` lies in quadrant number `k` (I to IV). (TR-039) -/
@[kb "openstaxalgtrig2e" "§7.3, p. 711"]
theorem polarPoint_mem_quadrant {r θ : ℝ} (hr : 0 < r) (k : Fin 4)
    (h1 : (k : ℕ) * (π / 2) < θ) (h2 : θ < ((k : ℕ) + 1) * (π / 2)) :
    InQuadrant k (polarPoint r θ) := by
  have hpi := pi_pos
  have hre := polarPoint_re r θ
  have him := polarPoint_im r θ
  fin_cases k
  · obtain ⟨a, b, c⟩ := quadrant_one_signs (θ := θ) (by simpa using h1) (by simp at h2; linarith)
    exact ⟨by rw [hre]; positivity, by rw [him]; positivity⟩
  · obtain ⟨a, b, c⟩ := quadrant_two_signs (θ := θ) (by simpa using h1) (by simp at h2; linarith)
    exact ⟨by rw [hre]; nlinarith, by rw [him]; positivity⟩
  · obtain ⟨a, b, c⟩ := quadrant_three_signs (θ := θ) (by simp at h1; linarith)
      (by simp at h2; linarith)
    exact ⟨by rw [hre]; nlinarith, by rw [him]; nlinarith⟩
  · obtain ⟨a, b, c⟩ := quadrant_four_signs (θ := θ) (by simp at h1; linarith) (by simp at h2; linarith)
    exact ⟨by rw [hre]; positivity, by rw [him]; nlinarith⟩

/-! ### Standard position (TR-005) -/

/-- **Angle in standard position**: rotating the initial side (the positive real axis) by `θ` is
multiplication by `exp(θ i)`; the terminal side passes through the point `polarPoint 1 θ = exp(θ i)`; the
oriented angle from the initial side to the terminal side is `θ` (modulo `2π`); rotating any non-zero point
by `θ` adds `θ` to its argument; for `0 < θ < π` (counterclockwise) the terminal point lies in the upper
half-plane and for `-π < θ < 0` (clockwise) in the lower half-plane. (TR-005) -/
@[kb "corraltrig" "Def §1.4, p. 32"]
theorem standardPosition (θ : ℝ) :
    Complex.exp (θ * Complex.I) * 1 = polarPoint 1 θ ∧
      ((Complex.arg (Complex.exp (θ * Complex.I)) : ℝ) : Real.Angle) = (θ : Real.Angle) ∧
      (∀ z : ℂ, z ≠ 0 → ((Complex.arg (Complex.exp (θ * Complex.I) * z) : ℝ) : Real.Angle) =
        (Complex.arg z : ℝ) + (θ : Real.Angle)) ∧
      (0 < θ → θ < π → 0 < (Complex.exp (θ * Complex.I)).im) ∧
      (-π < θ → θ < 0 → (Complex.exp (θ * Complex.I)).im < 0) := by
  refine ⟨?_, ?_, fun z hz => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [mul_one, Complex.exp_mul_I]; apply Complex.ext <;> simp [polarPoint_re, polarPoint_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · rw [Complex.arg_exp_mul_I]; exact Real.Angle.coe_toIocMod _ _
  · rw [Complex.arg_mul_coe_angle (Complex.exp_ne_zero _) hz, Complex.arg_exp_mul_I,
      Real.Angle.coe_toIocMod, add_comm]
  · rw [Complex.exp_ofReal_mul_I_im]; exact sin_pos_of_pos_of_lt_pi h1 h2
  · rw [Complex.exp_ofReal_mul_I_im]; exact sin_neg_of_neg_of_neg_pi_lt h2 h1

/-! ### Angles as pairs of rays (TR-008) -/

section Rays

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The (closed) ray from `O` through `A`. -/
def ray (O A : P) : Set P := {X | ∃ t : ℝ, 0 ≤ t ∧ X = t • (A -ᵥ O) +ᵥ O}

private lemma exists_pos_smul_of_mem_ray {O A A' : P} (h : A' ∈ ray O A) (hne : A' ≠ O) :
    ∃ t : ℝ, 0 < t ∧ t • (A -ᵥ O) = A' -ᵥ O := by
  obtain ⟨t, ht, rfl⟩ := h
  rcases ht.lt_or_eq with ht | ht
  · exact ⟨t, ht, by simp⟩
  · exfalso; apply hne; rw [← ht]; simp

/-- **An angle is determined by its sides**: `∠ A O B` depends only on the rays `O A` and `O B`. (TR-008) -/
@[kb "openstaxalgtrig2e" "§7.1, p. 675"]
theorem angle_eq_of_mem_ray {O A B A' B' : P} (hA : A' ∈ ray O A) (hA' : A' ≠ O) (hB : B' ∈ ray O B)
    (hB' : B' ≠ O) : ∠ A' O B' = ∠ A O B := by
  obtain ⟨s, hs, hs'⟩ := exists_pos_smul_of_mem_ray hA hA'
  obtain ⟨t, ht, ht'⟩ := exists_pos_smul_of_mem_ray hB hB'
  rw [angle_smul_left_of_pos B' hs hs', angle_smul_right_of_pos A ht ht']

end Rays

/-! ### Trigonometric functions of a point on the terminal side (TR-023) -/

/-- **Functions via a point on the terminal side**: if `(x, y) = (r cos θ, r sin θ)` with `r > 0` (so
`r = √(x² + y²)`), then `sin θ = y/r`, `cos θ = x/r`, `tan θ = y/x`, `csc θ = r/y`, `sec θ = r/x`,
`cot θ = x/y` (with Lean's convention `a/0 = 0` on both sides, no further hypothesis is needed). (TR-023) -/
@[kb "corraltrig" "Box §1.4, p. 33"]
theorem trig_of_point {x y r θ : ℝ} (hr : 0 < r) (hx : x = r * cos θ) (hy : y = r * sin θ) :
    r = √(x ^ 2 + y ^ 2) ∧ sin θ = y / r ∧ cos θ = x / r ∧ tan θ = y / x ∧ csc θ = r / y ∧
      sec θ = r / x ∧ cot θ = x / y := by
  subst hx hy
  have hr' := hr.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      linear_combination r ^ 2 * sin_sq_add_cos_sq θ
    rw [this, Real.sqrt_sq hr.le]
  · field_simp
  · field_simp
  · rw [tan_eq_sin_div_cos, mul_div_mul_left _ _ hr']
  · rw [csc, inv_eq_one_div, ← mul_div_mul_left 1 (sin θ) hr', mul_one]
  · rw [sec, inv_eq_one_div, ← mul_div_mul_left 1 (cos θ) hr', mul_one]
  · rw [cot_eq_cos_div_sin, mul_div_mul_left _ _ hr']

/-- **Converse**: for `z = x + yi ≠ 0`, with `θ = arg z` and `r = ‖z‖ = √(x² + y²)` the same formulas hold. (TR-023) -/
@[kb "openstaxalgtrig2e" "§7.4, p. 729"]
theorem trig_of_point_arg {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ = √(z.re ^ 2 + z.im ^ 2) ∧ sin (Complex.arg z) = z.im / ‖z‖ ∧ cos (Complex.arg z) = z.re / ‖z‖ ∧
      tan (Complex.arg z) = z.im / z.re ∧ csc (Complex.arg z) = ‖z‖ / z.im ∧
      sec (Complex.arg z) = ‖z‖ / z.re ∧ cot (Complex.arg z) = z.re / z.im := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hx : z.re = ‖z‖ * cos (Complex.arg z) := by rw [Complex.cos_arg hz]; field_simp
  have hy : z.im = ‖z‖ * sin (Complex.arg z) := by rw [Complex.sin_arg]; field_simp
  exact trig_of_point hn hx hy

/-! ### The six functions at the quadrantal angles (TR-026) -/

/-- **Table at `0, π/2, π, 3π/2`** (the defined entries; `tan`, `sec` are undefined at `π/2`, `3π/2` and
`cot`, `csc` at `0`, `π`, see `abs_tan_sec_tendsto_atTop` and `abs_cot_csc_tendsto_atTop`). (TR-026) -/
@[kb "corraltrig" "Ex 1.23, p. 36"]
theorem six_functions_quadrantal :
    (sin 0 = 0 ∧ cos 0 = 1 ∧ tan 0 = 0 ∧ sec 0 = 1) ∧
    (sin (π / 2) = 1 ∧ cos (π / 2) = 0 ∧ cot (π / 2) = 0 ∧ csc (π / 2) = 1) ∧
    (sin π = 0 ∧ cos π = -1 ∧ tan π = 0 ∧ sec π = -1) ∧
    (sin (3 * π / 2) = -1 ∧ cos (3 * π / 2) = 0 ∧ cot (3 * π / 2) = 0 ∧ csc (3 * π / 2) = -1) := by
  have h3c : cos (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi]; simp
  have h3s : sin (3 * π / 2) = -1 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, sin_add_pi]; simp
  refine ⟨⟨by simp, by simp, by simp, by simp [sec]⟩, ⟨by simp, by simp, cot_pi_div_two, csc_pi_div_two⟩,
    ⟨by simp, by simp, by simp, by simp [sec]⟩, ⟨h3s, h3c, ?_, ?_⟩⟩
  · rw [cot_eq_cos_div_sin, h3c]; simp
  · rw [csc, h3s]; simp

/-- **The undefined entries are genuinely undefined**: where `cos x = 0` (in particular at `π/2` and
`3π/2`) the denominators of `tan` and `sec` vanish, and `|tan|` and `|sec|` are unbounded near `x`. (TR-026) -/
@[kb "openstaxalgtrig2e" "§7.4, p. 731"]
theorem abs_tan_sec_tendsto_atTop {x : ℝ} (hx : cos x = 0) :
    Tendsto (fun t => |tan t|) (𝓝[≠] x) atTop ∧ Tendsto (fun t => |sec t|) (𝓝[≠] x) atTop := by
  have h := Real.tendsto_abs_tan_of_cos_eq_zero hx
  refine ⟨h, tendsto_atTop_mono (fun t => ?_) h⟩
  rw [tan_eq_sin_div_cos, sec, abs_div, div_eq_mul_inv, ← abs_inv]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_sin_le_one t)

/-- Likewise where `sin x = 0` (in particular at `0` and `π`) for `cot` and `csc`. (TR-026) -/
theorem abs_cot_csc_tendsto_atTop {x : ℝ} (hx : sin x = 0) :
    Tendsto (fun t => |cot t|) (𝓝[≠] x) atTop ∧ Tendsto (fun t => |csc t|) (𝓝[≠] x) atTop := by
  have hc : cos (x + π / 2) = 0 := by rw [cos_add_pi_div_two, hx, neg_zero]
  have h := Real.tendsto_abs_tan_of_cos_eq_zero hc
  have hshift : Tendsto (fun t : ℝ => t + π / 2) (𝓝[≠] x) (𝓝[≠] (x + π / 2)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hcot : Tendsto (fun t => |cot t|) (𝓝[≠] x) atTop := by
    refine (h.comp hshift).congr (fun t => ?_)
    simp [Function.comp, tan_add_pi_div_two]
  refine ⟨hcot, tendsto_atTop_mono (fun t => ?_) hcot⟩
  rw [cot_eq_cos_div_sin, csc, abs_div, div_eq_mul_inv, ← abs_inv]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one t)

/-! ### Arc length on the unit circle (TR-036) -/

/-- **Wrapping the number line around the unit circle**: the arc of the unit circle from `(1, 0)` to
the point `exp(t i)` has length `t` (`t ≥ 0`), and that point is `(cos t, sin t)` on the unit circle. (TR-036) -/
@[kb "corraltrig" "Box §5.1, p. 110"]
theorem unitCircle_arc_point {t : ℝ} (ht : 0 ≤ t) :
    eVariationOn (fun φ : ℝ => Complex.exp (φ * Complex.I)) (Set.Icc 0 t) = ENNReal.ofReal t ∧
      Complex.exp (t * Complex.I) = ⟨cos t, sin t⟩ ∧ ‖Complex.exp (t * Complex.I)‖ = 1 := by
  refine ⟨?_, ?_, Complex.norm_exp_ofReal_mul_I t⟩
  · have := arc_length 0 (r := 1) (θ := t) zero_le_one ht
    simpa using this
  · apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

end UndergradKB.Trigonometry
