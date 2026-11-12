import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import UndergradKB.Common.Attr

/-! # Lines and quadratic functions (Stitz-Zeager, Chapter 2)

Slope, the point-slope and slope-intercept forms of a non-vertical line, linear functions, the standard form and
the vertex of a quadratic function, and the discriminant trichotomy. Points of the plane are pairs `(x, y) : ℝ × ℝ`;
the line through two points is Mathlib's affine span `line[ℝ, P, Q]`.
-/

namespace UndergradKB.Precalculus

open Set

/-! ## Lines -/

/-- Equation 2.1 (slope): for two points with distinct x-coordinates, a point `(x, y)` lies on the line through them
exactly when `y - y₀ = m (x - x₀)`, where `m = (y₁ - y₀)/(x₁ - x₀)` is the slope (PC-034). -/
@[kb "stitzzeager2013" "Equation 2.1, p. 163"]
theorem mem_line_iff_slope {x₀ y₀ x₁ y₁ : ℝ} (h : x₀ ≠ x₁) (x y : ℝ) :
    (x, y) ∈ line[ℝ, ((x₀, y₀) : ℝ × ℝ), (x₁, y₁)] ↔ y - y₀ = (y₁ - y₀) / (x₁ - x₀) * (x - x₀) := by
  have hx : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  constructor
  · rintro ⟨r, rfl, rfl⟩
    field_simp
    ring
  · intro hy
    refine ⟨(x - x₀) / (x₁ - x₀), by field_simp; ring, ?_⟩
    linear_combination -hy

/-- Equation 2.2 (point-slope form): the line through `(x₀, y₀)` with slope `m` (the line through `(x₀, y₀)` and
`(x₀ + 1, y₀ + m)`) consists of the points with `y - y₀ = m (x - x₀)` (PC-035). -/
@[kb "stitzzeager2013" "Equation 2.2, p. 167"]
theorem mem_line_point_slope (x₀ y₀ m x y : ℝ) :
    (x, y) ∈ line[ℝ, ((x₀, y₀) : ℝ × ℝ), (x₀ + 1, y₀ + m)] ↔ y - y₀ = m * (x - x₀) := by
  rw [mem_line_iff_slope (ne_of_lt (lt_add_one x₀))]
  have : (y₀ + m - y₀) / (x₀ + 1 - x₀) = m := by ring
  rw [this]

/-- Equation 2.3 (slope-intercept form): the point-slope equation `y - y₀ = m (x - x₀)` is the equation
`y = m x + b` with `b = y₀ - m x₀`; the line with slope `m` through the y-intercept `(0, b)` is the graph of
`y = m x + b` (PC-036). -/
@[kb "stitzzeager2013" "Equation 2.3, p. 167"]
theorem point_slope_iff_slope_intercept (x₀ y₀ m x y : ℝ) :
    y - y₀ = m * (x - x₀) ↔ y = m * x + (y₀ - m * x₀) := by
  constructor <;> intro h <;> linarith

@[kb "stitzzeager2013" "Equation 2.3, p. 167", inherit_doc point_slope_iff_slope_intercept]
theorem mem_line_slope_intercept (m b x y : ℝ) :
    (x, y) ∈ line[ℝ, ((0, b) : ℝ × ℝ), (1, b + m)] ↔ y = m * x + b := by
  have := mem_line_point_slope 0 b m x y
  simp only [zero_add, sub_zero] at this
  rw [this]
  constructor <;> intro h <;> linarith

/-- Definition 2.1 (linear functions): the graph of `f(x) = m x + b` over all real numbers is the line with slope
`m` and y-intercept `(0, b)`; conversely every line through two points with distinct x-coordinates is the graph of
such a function, with `m` the slope (a linear function when `m ≠ 0`, a constant one when `m = 0`) (PC-037). -/
@[kb "stitzzeager2013" "Definition 2.1, p. 168"]
theorem graph_linear_function (m b : ℝ) :
    Set.graphOn (fun x => m * x + b) univ = (line[ℝ, ((0, b) : ℝ × ℝ), (1, b + m)] : Set (ℝ × ℝ)) := by
  ext ⟨x, y⟩
  simp only [mem_graphOn, mem_univ, true_and, SetLike.mem_coe, mem_line_slope_intercept]
  exact eq_comm

@[kb "stitzzeager2013" "Definition 2.1, p. 168", inherit_doc graph_linear_function]
theorem line_eq_graph_linear_function {x₀ y₀ x₁ y₁ : ℝ} (h : x₀ ≠ x₁) :
    (line[ℝ, ((x₀, y₀) : ℝ × ℝ), (x₁, y₁)] : Set (ℝ × ℝ)) =
      Set.graphOn (fun x => (y₁ - y₀) / (x₁ - x₀) * x + (y₀ - (y₁ - y₀) / (x₁ - x₀) * x₀)) univ := by
  ext ⟨x, y⟩
  simp only [mem_graphOn, mem_univ, true_and, SetLike.mem_coe, mem_line_iff_slope h,
    point_slope_iff_slope_intercept]
  exact eq_comm

/-! ## Quadratic functions -/

/-- Definitions 2.5 and 2.6 (general and standard form): every quadratic function `ax² + bx + c` with `a ≠ 0` can be
written in standard form `a (x - h)² + k`, with `h = -b/(2a)` and `k = (4ac - b²)/(4a)` (completing the square)
(PC-043, PC-044). -/
@[kb "stitzzeager2013" "Definition 2.6, p. 202"]
theorem quadratic_standard_form {a : ℝ} (ha : a ≠ 0) (b c x : ℝ) :
    a * x ^ 2 + b * x + c = a * (x - -b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
  field_simp
  ring

/-- Definition 2.6: the standard form of a quadratic function is unique: if `a (x - h)² + k = a (x - h')² + k'`
for all `x` (`a ≠ 0`) then `h = h'` and `k = k'` (PC-044). -/
@[kb "stitzzeager2013" "Definition 2.6, p. 202"]
theorem quadratic_standard_form_unique {a h k h' k' : ℝ} (ha : a ≠ 0)
    (H : ∀ x, a * (x - h) ^ 2 + k = a * (x - h') ^ 2 + k') : h = h' ∧ k = k' := by
  have e1 := H h
  have e2 := H h'
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add] at e1 e2
  have hsq : (h' - h) ^ 2 = (h - h') ^ 2 := by ring
  rw [hsq] at e2
  have h0 : a * (h - h') ^ 2 = 0 := by linarith
  have hh : h = h' := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 ha
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  refine ⟨hh, ?_⟩
  subst hh
  simpa using e1

/-- Theorem 2.2 (vertex formula, standard form): for `f(x) = a (x - h)² + k` with `a ≠ 0`, the point `(h, k)` is on
the graph and is its vertex: the unique lowest point when `a > 0` and the unique highest point when `a < 0`
(PC-045). -/
@[kb "stitzzeager2013" "Theorem 2.2, p. 202"]
theorem vertex_standard_form {a : ℝ} (ha : a ≠ 0) (h k : ℝ) :
    a * (h - h) ^ 2 + k = k ∧
      (0 < a → ∀ x, x ≠ h → k < a * (x - h) ^ 2 + k) ∧
      (a < 0 → ∀ x, x ≠ h → a * (x - h) ^ 2 + k < k) := by
  have _ := ha
  refine ⟨by simp, fun hpos x hx => ?_, fun hneg x hx => ?_⟩
  · have : 0 < (x - h) ^ 2 := by positivity [sub_ne_zero.mpr hx]
    nlinarith
  · have : 0 < (x - h) ^ 2 := by positivity [sub_ne_zero.mpr hx]
    nlinarith

/-- Equation 2.4 (vertex formula, general form): for `f(x) = ax² + bx + c` with `a ≠ 0` the vertex is
`(-b/(2a), f(-b/(2a)))`, and `f(-b/(2a)) = (4ac - b²)/(4a)`: the unique lowest point if `a > 0`, the unique
highest point if `a < 0` (PC-046). -/
@[kb "stitzzeager2013" "Equation 2.4, p. 206"]
theorem vertex_general_form {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = (4 * a * c - b ^ 2) / (4 * a) ∧
      (0 < a → ∀ x, x ≠ -b / (2 * a) →
        a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c < a * x ^ 2 + b * x + c) ∧
      (a < 0 → ∀ x, x ≠ -b / (2 * a) →
        a * x ^ 2 + b * x + c < a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c) := by
  have hv := vertex_standard_form ha (-b / (2 * a)) ((4 * a * c - b ^ 2) / (4 * a))
  obtain ⟨h1, h2, h3⟩ := hv
  simp only [quadratic_standard_form ha b c]
  refine ⟨h1, fun hp x hx => ?_, fun hn x hx => ?_⟩
  · rw [h1]; exact h2 hp x hx
  · rw [h1]; exact h3 hn x hx

/-- Theorem 2.3 (discriminant trichotomy): for real `a ≠ 0`, `b`, `c`, the equation `ax² + bx + c = 0` has no real
solution if `b² - 4ac < 0`, exactly one (namely `-b/(2a)`) if `b² - 4ac = 0`, and exactly two if `b² - 4ac > 0`,
namely `(-b ± √(b² - 4ac))/(2a)` (PC-049). -/
@[kb "stitzzeager2013" "Theorem 2.3, p. 207"]
theorem discriminant_trichotomy {a : ℝ} (ha : a ≠ 0) (b c : ℝ) :
    (discrim a b c < 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0} = ∅) ∧
    (discrim a b c = 0 → {x : ℝ | a * x ^ 2 + b * x + c = 0} = {-b / (2 * a)}) ∧
    (0 < discrim a b c →
      (-b + √(discrim a b c)) / (2 * a) ≠ (-b - √(discrim a b c)) / (2 * a) ∧
      {x : ℝ | a * x ^ 2 + b * x + c = 0} =
        {(-b + √(discrim a b c)) / (2 * a), (-b - √(discrim a b c)) / (2 * a)}) := by
  have sq : ∀ x : ℝ, a * x ^ 2 + b * x + c = a * (x * x) + b * x + c := fun x => by ring
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ⟨?_, ?_⟩⟩
  · ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, sq]
    intro hx
    have := discrim_eq_sq_of_quadratic_eq_zero hx
    nlinarith [sq_nonneg (2 * a * x + b)]
  · ext x
    simp only [mem_ofPred_eq, mem_singleton_iff, sq]
    exact quadratic_eq_zero_iff_of_discrim_eq_zero ha hd x
  · intro heq
    have h2a : (2 * a) ≠ 0 := mul_ne_zero two_ne_zero ha
    rw [div_left_inj' h2a] at heq
    have : 0 < √(discrim a b c) := Real.sqrt_pos.mpr hd
    linarith
  · ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, sq]
    exact quadratic_eq_zero_iff ha (Real.mul_self_sqrt hd.le).symm x

/-! ## Perpendicular lines -/

/-- Example 11.9.3 (perpendicular slopes): the lines `y = m₁ x + b₁` and `y = m₂ x + b₂`, with direction vectors
`⟨1, m₁⟩` and `⟨1, m₂⟩`, are perpendicular (their direction vectors meet at a right angle) exactly when
`m₁ m₂ = -1` (PC-286). -/
@[kb "stitzzeager2013" "Example 11.9.3, p. 1049"]
theorem perpendicular_slopes_iff (m₁ m₂ : ℝ) :
    InnerProductGeometry.angle (!₂[1, m₁] : EuclideanSpace ℝ (Fin 2)) !₂[1, m₂] = Real.pi / 2 ↔
      m₁ * m₂ = -1 := by
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
  constructor <;> intro h <;> linarith

end UndergradKB.Precalculus
