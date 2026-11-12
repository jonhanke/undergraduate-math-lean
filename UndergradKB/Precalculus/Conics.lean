import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import UndergradKB.Common.Attr

namespace UndergradKB.Precalculus

/-- Euclidean distance between two points of the coordinate plane `ℝ × ℝ` (the product metric of `ℝ × ℝ` is
the sup metric, so the Euclidean one is written explicitly). -/
noncomputable def edist2 (p q : ℝ × ℝ) : ℝ := √((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

theorem sqrt_eq_of_sq {s w : ℝ} (hw : 0 ≤ w) (h : s = w ^ 2) : √s = w := by
  rw [h]; exact Real.sqrt_sq hw

theorem sqrt_eq_iff_sq {s r : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) : √s = r ↔ s = r ^ 2 := by
  constructor
  · rintro rfl; rw [Real.sq_sqrt hs]
  · intro h; exact sqrt_eq_of_sq hr h

theorem edist2_eq_iff_sq {p q : ℝ × ℝ} {r : ℝ} (hr : 0 ≤ r) :
    edist2 p q = r ↔ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = r ^ 2 :=
  sqrt_eq_iff_sq hr (by positivity)

/-! ### Circles -/

/-- A point `(x, y)` lies on the circle of radius `r > 0` about `(h, k)` iff `(x-h)^2 + (y-k)^2 = r^2` (PC-111). -/
@[kb "stitzzeager2013" "Equation 7.1, p. 510"]
theorem circle_mem_iff_equation {h k r : ℝ} (hr : 0 < r) (x y : ℝ) :
    edist2 (x, y) (h, k) = r ↔ (x - h) ^ 2 + (y - k) ^ 2 = r ^ 2 :=
  edist2_eq_iff_sq hr.le

/-- The alternate circle equation `(x-h)^2/r^2 + (y-k)^2/r^2 = 1` describes the same circle (PC-112). -/
@[kb "stitzzeager2013" "Equation 7.5, p. 531"]
theorem circle_alt_equation {h k r : ℝ} (hr : 0 < r) (x y : ℝ) :
    (x - h) ^ 2 / r ^ 2 + (y - k) ^ 2 / r ^ 2 = 1 ↔ edist2 (x, y) (h, k) = r := by
  rw [circle_mem_iff_equation hr, ← add_div, div_eq_one_iff_eq (by positivity)]

/-- Circle with the segment `AB` as a diameter: its center is the midpoint, its radius is half of `|AB|`,
both endpoints lie on it, and a point `P` lies on it iff `(P - A) · (P - B) = 0` (PC-113). -/
@[kb "stitzzeager2013" "Example 7.2.4, p. 512"]
theorem circle_diameter_endpoints (A B P : ℝ × ℝ) :
    edist2 A ((A.1 + B.1) / 2, (A.2 + B.2) / 2) = edist2 A B / 2 ∧
    edist2 B ((A.1 + B.1) / 2, (A.2 + B.2) / 2) = edist2 A B / 2 ∧
    (edist2 P ((A.1 + B.1) / 2, (A.2 + B.2) / 2) = edist2 A B / 2 ↔
      (P.1 - A.1) * (P.1 - B.1) + (P.2 - A.2) * (P.2 - B.2) = 0) := by
  have hnn : 0 ≤ edist2 A B / 2 := by unfold edist2; positivity
  have hsq : (edist2 A B / 2) ^ 2 = ((A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2) / 4 := by
    unfold edist2; rw [div_pow, Real.sq_sqrt (by positivity)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [edist2_eq_iff_sq hnn, hsq]; ring
  · rw [edist2_eq_iff_sq hnn, hsq]; ring
  · rw [edist2_eq_iff_sq hnn, hsq]
    constructor <;> intro h <;> nlinarith

/-- The unit circle: `(x, y)` is at distance `1` from the origin iff `x^2 + y^2 = 1`; in particular all points
`(cos t, sin t)` lie on it (PC-114). -/
@[kb "stitzzeager2013" "Definition 7.2, p. 513"]
theorem unit_circle_mem_iff (x y : ℝ) :
    edist2 (x, y) (0, 0) = 1 ↔ x ^ 2 + y ^ 2 = 1 := by
  rw [edist2_eq_iff_sq zero_le_one]; simp

/-- Every point `(cos t, sin t)` lies on the unit circle (PC-114). -/
@[kb "stitzzeager2013" "Definition 7.2, p. 513"]
theorem unit_circle_cos_sin (t : ℝ) : edist2 (Real.cos t, Real.sin t) (0, 0) = 1 := by
  rw [unit_circle_mem_iff]; exact Real.cos_sq_add_sin_sq t

/-! ### Parabolas -/

/-- Distance from the point `P` to the line `a x + b y = c` (with `(a, b) ≠ 0`). -/
noncomputable def distToLine (a b c : ℝ) (P : ℝ × ℝ) : ℝ := |a * P.1 + b * P.2 - c| / √(a ^ 2 + b ^ 2)

/-- Parabola with focus `F` and directrix the line `a x + b y = c`: the points equidistant from both. -/
def IsParabolaPt (F : ℝ × ℝ) (a b c : ℝ) (P : ℝ × ℝ) : Prop := edist2 P F = distToLine a b c P

/-- Squared-distance form of the parabola condition (PC-115). -/
@[kb "stitzzeager2013" "Definition 7.3, p. 517"]
theorem parabola_pt_iff (F : ℝ × ℝ) {a b c : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (P : ℝ × ℝ) :
    IsParabolaPt F a b c P ↔
      ((P.1 - F.1) ^ 2 + (P.2 - F.2) ^ 2) * (a ^ 2 + b ^ 2) = (a * P.1 + b * P.2 - c) ^ 2 := by
  have hm : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hab)
  have hsm : 0 < √(a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hm
  unfold IsParabolaPt distToLine edist2
  rw [eq_div_iff hsm.ne', ← Real.sqrt_mul (by positivity),
    sqrt_eq_iff_sq (abs_nonneg _) (by positivity), sq_abs]

/-- Distance to a horizontal line `y = c`. -/
theorem distToLine_horizontal (c : ℝ) (P : ℝ × ℝ) : distToLine 0 1 c P = |P.2 - c| := by
  simp [distToLine]

/-- Distance to a vertical line `x = c`. -/
theorem distToLine_vertical (c : ℝ) (P : ℝ × ℝ) : distToLine 1 0 c P = |P.1 - c| := by
  simp [distToLine]

/-- Vertical parabola with focus `(h, k + p)` and directrix `y = k - p`: `(x-h)^2 = 4p(y-k)` (PC-116). -/
@[kb "stitzzeager2013" "Equation 7.2, p. 518"]
theorem parabola_vertical_equation (h k p : ℝ) (x y : ℝ) :
    edist2 (x, y) (h, k + p) = distToLine 0 1 (k - p) (x, y) ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
  rw [distToLine_horizontal, edist2_eq_iff_sq (abs_nonneg _), sq_abs]
  constructor <;> intro h <;> nlinarith

/-- Horizontal parabola with focus `(h + p, k)` and directrix `x = h - p`: `(y-k)^2 = 4p(x-h)` (PC-117). -/
@[kb "stitzzeager2013" "Equation 7.3, p. 520"]
theorem parabola_horizontal_equation (h k p : ℝ) (x y : ℝ) :
    edist2 (x, y) (h + p, k) = distToLine 1 0 (h - p) (x, y) ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  rw [distToLine_vertical, edist2_eq_iff_sq (abs_nonneg _), sq_abs]
  constructor <;> intro h <;> nlinarith

/-- Latus rectum of the parabola `(x-h)^2 = 4p(y-k)`: the points of the parabola at the height `k + p` of the
focus are exactly `(h ± 2p, k + p)`, and these two endpoints are at distance `|4p|` (PC-118). -/
@[kb "stitzzeager2013" "§7.3, p. 519"]
theorem parabola_latus_rectum (h k p : ℝ) :
    (∀ x : ℝ, edist2 (x, k + p) (h, k + p) = distToLine 0 1 (k - p) (x, k + p) ↔ x = h - 2 * p ∨ x = h + 2 * p) ∧
    edist2 (h - 2 * p, k + p) (h + 2 * p, k + p) = |4 * p| := by
  constructor
  · intro x
    rw [parabola_vertical_equation]
    constructor
    · intro hx
      have : (x - (h - 2 * p)) * (x - (h + 2 * p)) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linarith
      · right; linarith
    · rintro (hx | hx) <;> subst hx <;> ring
  · unfold edist2
    have : (h - 2 * p - (h + 2 * p)) ^ 2 + (k + p - (k + p)) ^ 2 = (4 * p) ^ 2 := by ring
    simp only [this]
    exact Real.sqrt_sq_eq_abs _


/-- Reflection of the direction `v` across the line with direction `T` (a nonzero vector). -/
noncomputable def reflectDir (T v : ℝ × ℝ) : ℝ × ℝ :=
  (2 * (T.1 * v.1 + T.2 * v.2) / (T.1 ^ 2 + T.2 ^ 2) * T.1 - v.1,
   2 * (T.1 * v.1 + T.2 * v.2) / (T.1 ^ 2 + T.2 ^ 2) * T.2 - v.2)

/-- The parabola `y = x^2/(4p)` has, at the abscissa `x0`, the tangent direction `(1, x0/(2p))`, which is a
multiple of `(2p, x0)`. -/
theorem parabola_tangent_slope {p : ℝ} (x0 : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / (4 * p)) (x0 / (2 * p)) x0 := by
  by_cases hp : p = 0
  · subst hp; simp; exact hasDerivAt_const _ _
  · have h0 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x0) x0 := by simpa using hasDerivAt_pow 2 x0
    have := h0.div_const (4 * p)
    convert this using 1
    field_simp; ring

/-- Reflective property of the parabola `x^2 = 4py` (vertex at the origin, focus `F = (0, p)`, `p ≠ 0`): at the
point `(x0, y0)` of the parabola, the vector from the point to the focus is a nonzero multiple of the
direction obtained by reflecting a ray parallel to the axis, `(0, -1)`, across the tangent line, whose direction
is `(2p, x0)`. So rays parallel to the axis are reflected through the focus (PC-119). -/
@[kb "stitzzeager2013" "§7.3, p. 523"]
theorem parabola_reflective_property {p x0 y0 : ℝ} (hp : p ≠ 0) (hy : x0 ^ 2 = 4 * p * y0) :
    0 - x0 = (4 * p ^ 2 + x0 ^ 2) / (4 * p) * (reflectDir (2 * p, x0) (0, -1)).1 ∧
    p - y0 = (4 * p ^ 2 + x0 ^ 2) / (4 * p) * (reflectDir (2 * p, x0) (0, -1)).2 ∧
    (4 * p ^ 2 + x0 ^ 2) / (4 * p) ≠ 0 := by
  have hD : 0 < 4 * p ^ 2 + x0 ^ 2 := by positivity
  have hy' : y0 = x0 ^ 2 / (4 * p) := by field_simp; linarith
  subst hy'
  unfold reflectDir
  refine ⟨?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · positivity

/-! ### Ellipses -/

/-- Ellipse with foci `F₁`, `F₂` and distance sum `d`. -/
def IsEllipsePt (F₁ F₂ : ℝ × ℝ) (d : ℝ) (P : ℝ × ℝ) : Prop := edist2 P F₁ + edist2 P F₂ = d

/-- Hyperbola with foci `F₁`, `F₂` and difference of distances `d` (in absolute value). -/
def IsHyperbolaPt (F₁ F₂ : ℝ × ℝ) (d : ℝ) (P : ℝ × ℝ) : Prop := |edist2 P F₁ - edist2 P F₂| = d

theorem ellipse_aux {a c u v : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) :
    √((u - c) ^ 2 + v ^ 2) + √((u + c) ^ 2 + v ^ 2) = 2 * a ↔
      u ^ 2 / a ^ 2 + v ^ 2 / (a ^ 2 - c ^ 2) = 1 := by
  have hb : 0 < a ^ 2 - c ^ 2 := by nlinarith
  have h1 := Real.sq_sqrt (show 0 ≤ (u - c) ^ 2 + v ^ 2 by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ (u + c) ^ 2 + v ^ 2 by positivity)
  constructor
  · intro h
    generalize √((u - c) ^ 2 + v ^ 2) = S1 at *
    generalize √((u + c) ^ 2 + v ^ 2) = S2 at *
    have h3 : (S1 - S2) * (2 * a) = -4 * c * u := by
      rw [← h]; nlinarith
    have h5 : S1 - S2 = -2 * c * u / a := by
      field_simp; linarith
    have h4 : S1 = a - c * u / a := by
      have : S1 = ((S1 + S2) + (S1 - S2)) / 2 := by ring
      rw [this, h, h5]; field_simp; ring
    have h6 : (u - c) ^ 2 + v ^ 2 = (a - c * u / a) ^ 2 := by rw [← h1, h4]
    field_simp at h6 ⊢
    nlinarith
  · intro h
    have hu : -a ≤ u ∧ u ≤ a := by
      have : u ^ 2 / a ^ 2 ≤ 1 := by
        have : 0 ≤ v ^ 2 / (a ^ 2 - c ^ 2) := by positivity
        linarith
      rw [div_le_one (by positivity)] at this
      constructor <;> nlinarith
    have hw1 : 0 ≤ a - c * u / a := by
      rw [sub_nonneg, div_le_iff₀ ha]; nlinarith [mul_nonneg hc (sub_nonneg.2 hu.2)]
    have hw2 : 0 ≤ a + c * u / a := by
      have : 0 ≤ a * a + c * u := by nlinarith [mul_nonneg hc (neg_le_iff_add_nonneg.1 hu.1)]
      have h7 : a + c * u / a = (a * a + c * u) / a := by field_simp
      rw [h7]; positivity
    field_simp at h
    rw [sqrt_eq_of_sq hw1 (by field_simp; nlinarith), sqrt_eq_of_sq hw2 (by field_simp; nlinarith)]
    ring

theorem edist2_horizontal_foci_left (h k c x y : ℝ) :
    edist2 (x, y) (h + c, k) = √((x - h - c) ^ 2 + (y - k) ^ 2) := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_horizontal_foci_right (h k c x y : ℝ) :
    edist2 (x, y) (h - c, k) = √((x - h + c) ^ 2 + (y - k) ^ 2) := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_vertical_foci_up (h k c x y : ℝ) :
    edist2 (x, y) (h, k + c) = √((y - k - c) ^ 2 + (x - h) ^ 2) := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_vertical_foci_down (h k c x y : ℝ) :
    edist2 (x, y) (h, k - c) = √((y - k + c) ^ 2 + (x - h) ^ 2) := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_reflect_left (F G P : ℝ × ℝ) :
    edist2 (F.1 + G.1 - P.1, F.2 + G.2 - P.2) F = edist2 P G := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_reflect_right (F G P : ℝ × ℝ) :
    edist2 (F.1 + G.1 - P.1, F.2 + G.2 - P.2) G = edist2 P F := by
  unfold edist2; dsimp only; congr 1; ring

/-- Ellipse with foci `F₁`, `F₂`: the focus order is irrelevant and the curve is symmetric under the point
reflection in the midpoint of the foci (its center) (PC-120). -/
@[kb "stitzzeager2013" "Definition 7.4, p. 528"]
theorem ellipse_symm_center (F₁ F₂ : ℝ × ℝ) (d : ℝ) (P : ℝ × ℝ) :
    (IsEllipsePt F₁ F₂ d P ↔ IsEllipsePt F₂ F₁ d P) ∧
    (IsEllipsePt F₁ F₂ d P ↔
      IsEllipsePt F₁ F₂ d (F₁.1 + F₂.1 - P.1, F₁.2 + F₂.2 - P.2)) := by
  unfold IsEllipsePt
  rw [edist2_reflect_left, edist2_reflect_right]
  exact ⟨by rw [add_comm], by rw [add_comm]⟩

/-- For the ellipse with foci `(±c, 0)` and a vertex `(a, 0)` (`0 ≤ c ≤ a`), the constant is `d = 2a`; and the
co-vertex `(0, b)` with `b^2 = a^2 - c^2` lies on the ellipse with constant `2a` (PC-121). -/
@[kb "stitzzeager2013" "§7.4, p. 530"]
theorem ellipse_vertex_sum {a b c d : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) :
    (IsEllipsePt (-c, 0) (c, 0) d (a, 0) ↔ d = 2 * a) ∧
    (b ^ 2 = a ^ 2 - c ^ 2 → 0 ≤ b → IsEllipsePt (-c, 0) (c, 0) (2 * a) (0, b)) := by
  constructor
  · have e1 : edist2 (a, 0) (-c, 0) = a + c :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    have e2 : edist2 (a, 0) (c, 0) = a - c :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    unfold IsEllipsePt
    rw [e1, e2]
    constructor <;> intro h <;> linarith
  · intro hb hb0
    have e : edist2 (0, b) (-c, 0) = a :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; nlinarith)
    have e' : edist2 (0, b) (c, 0) = a :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; nlinarith)
    unfold IsEllipsePt
    rw [e, e']; ring

/-- Standard equation of the horizontal ellipse with foci `(h ± c, k)`, semi-major axis `a`, `0 ≤ c < a`,
`b^2 = a^2 - c^2`: the distances to the foci sum to `2a` iff `(x-h)^2/a^2 + (y-k)^2/b^2 = 1` (PC-122). -/
@[kb "stitzzeager2013" "Equation 7.4, p. 531"]
theorem ellipse_horizontal_equation {a b c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hb : b ^ 2 = a ^ 2 - c ^ 2) (h k x y : ℝ) :
    IsEllipsePt (h - c, k) (h + c, k) (2 * a) (x, y) ↔
      (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1 := by
  unfold IsEllipsePt
  rw [edist2_horizontal_foci_left, edist2_horizontal_foci_right, hb, add_comm]
  exact ellipse_aux ha hc hca

/-- Standard equation of the vertical ellipse with foci `(h, k ± c)`, semi-major axis `a`, `0 ≤ c < a`,
`b^2 = a^2 - c^2`: `(x-h)^2/b^2 + (y-k)^2/a^2 = 1` (PC-122). -/
@[kb "stitzzeager2013" "Equation 7.4, p. 531"]
theorem ellipse_vertical_equation {a b c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a)
    (hb : b ^ 2 = a ^ 2 - c ^ 2) (h k x y : ℝ) :
    IsEllipsePt (h, k - c) (h, k + c) (2 * a) (x, y) ↔
      (x - h) ^ 2 / b ^ 2 + (y - k) ^ 2 / a ^ 2 = 1 := by
  unfold IsEllipsePt
  rw [edist2_vertical_foci_up, edist2_vertical_foci_down, hb, add_comm ((x - h) ^ 2 / _)]
  rw [add_comm]
  exact ellipse_aux (u := y - k) (v := x - h) ha hc hca

/-- The focal distance of the standard ellipse is `c = √|a^2 - b^2|` (PC-122). -/
@[kb "stitzzeager2013" "Equation 7.4, p. 531"]
theorem ellipse_focal_distance {a b c : ℝ} (hc : 0 ≤ c) (hb : b ^ 2 = a ^ 2 - c ^ 2) :
    c = √|a ^ 2 - b ^ 2| := by
  have : |a ^ 2 - b ^ 2| = c ^ 2 := by
    rw [hb]; simp [abs_of_nonneg (sq_nonneg c)]
  rw [this, Real.sqrt_sq hc]

/-- Eccentricity of an ellipse: center-to-focus over center-to-vertex, `e = c / a`. -/
noncomputable def ellipseEccentricity (a c : ℝ) : ℝ := c / a

/-- For an ellipse with `0 ≤ c < a`, the eccentricity `c/a` equals the ratio of the distance from the center
`(h, k)` to the focus `(h + c, k)` to that to the vertex `(h + a, k)`, and satisfies `0 ≤ e < 1`, with `e > 0`
exactly when the two foci are distinct (PC-123). -/
@[kb "stitzzeager2013" "Definition 7.5, p. 534"]
theorem ellipse_eccentricity_bounds {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hca : c < a) (h k : ℝ) :
    ellipseEccentricity a c = edist2 (h, k) (h + c, k) / edist2 (h, k) (h + a, k) ∧
    0 ≤ ellipseEccentricity a c ∧ ellipseEccentricity a c < 1 ∧
    (0 < ellipseEccentricity a c ↔ 0 < c) := by
  have e1 : edist2 (h, k) (h + c, k) = c :=
    (edist2_eq_iff_sq hc).2 (by dsimp only; ring)
  have e2 : edist2 (h, k) (h + a, k) = a :=
    (edist2_eq_iff_sq ha.le).2 (by dsimp only; ring)
  unfold ellipseEccentricity
  rw [e1, e2]
  refine ⟨rfl, by positivity, (div_lt_one ha).2 hca, ?_⟩
  constructor
  · intro h0; exact (div_pos_iff_of_pos_right ha).1 h0
  · intro h0; exact div_pos h0 ha

/-! ### Hyperbolas -/

theorem hyperbola_aux {a c u v : ℝ} (ha : 0 < a) (hac : a < c) :
    |√((u - c) ^ 2 + v ^ 2) - √((u + c) ^ 2 + v ^ 2)| = 2 * a ↔
      u ^ 2 / a ^ 2 - v ^ 2 / (c ^ 2 - a ^ 2) = 1 := by
  have hb : 0 < c ^ 2 - a ^ 2 := by nlinarith
  have hc : 0 < c := by linarith
  have h1 := Real.sq_sqrt (show 0 ≤ (u - c) ^ 2 + v ^ 2 by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ (u + c) ^ 2 + v ^ 2 by positivity)
  constructor
  · intro h
    generalize √((u - c) ^ 2 + v ^ 2) = S1 at *
    generalize √((u + c) ^ 2 + v ^ 2) = S2 at *
    have h3 : (S1 - S2) * (S1 + S2) = -4 * c * u := by nlinarith
    rcases abs_cases (S1 - S2) with ⟨hd, _⟩ | ⟨hd, _⟩
    · rw [hd] at h
      rw [h] at h3
      have h5 : S1 + S2 = -2 * c * u / a := by field_simp; linarith
      have h4 : S1 = a - c * u / a := by
        have : S1 = ((S1 + S2) + (S1 - S2)) / 2 := by ring
        rw [this, h5, h]; field_simp; ring
      have h6 : (u - c) ^ 2 + v ^ 2 = (a - c * u / a) ^ 2 := by rw [← h1, h4]
      field_simp at h6 ⊢
      nlinarith
    · have h' : S1 - S2 = -(2 * a) := by linarith
      rw [h'] at h3
      have h5 : S1 + S2 = 2 * c * u / a := by field_simp; linarith
      have h4 : S1 = -a + c * u / a := by
        have : S1 = ((S1 + S2) + (S1 - S2)) / 2 := by ring
        rw [this, h5, h']; field_simp; ring
      have h6 : (u - c) ^ 2 + v ^ 2 = (-a + c * u / a) ^ 2 := by rw [← h1, h4]
      field_simp at h6 ⊢
      nlinarith
  · intro h
    have h' : (c ^ 2 - a ^ 2) * u ^ 2 - a ^ 2 * v ^ 2 = a ^ 2 * (c ^ 2 - a ^ 2) := by
      field_simp at h; linarith
    have hu : a ^ 2 ≤ u ^ 2 := by nlinarith [sq_nonneg v, sq_nonneg a]
    have hsq1 : (u - c) ^ 2 + v ^ 2 = (c * u / a - a) ^ 2 := by
      field_simp; nlinarith
    have hsq2 : (u + c) ^ 2 + v ^ 2 = (c * u / a + a) ^ 2 := by
      field_simp; nlinarith
    rcases le_or_gt a u with hu1 | hu1
    · have hca : c * a ≤ c * u := by nlinarith
      have hw1 : 0 ≤ c * u / a - a := by
        rw [sub_nonneg, le_div_iff₀ ha]; nlinarith
      have hw2 : 0 ≤ c * u / a + a := by linarith
      rw [sqrt_eq_of_sq hw1 hsq1, sqrt_eq_of_sq hw2 hsq2]
      rw [show c * u / a - a - (c * u / a + a) = -(2 * a) by ring, abs_neg, abs_of_pos (by linarith)]
    · have hu2 : u ≤ -a := by nlinarith
      have hca : c * u ≤ -(c * a) := by nlinarith
      have hw1 : 0 ≤ a - c * u / a := by
        rw [sub_nonneg, div_le_iff₀ ha]; nlinarith
      have hw2 : 0 ≤ -(c * u / a) - a := by
        have : c * u / a ≤ -c := by rw [div_le_iff₀ ha]; nlinarith
        linarith
      rw [sqrt_eq_of_sq hw1 (by rw [hsq1]; ring), sqrt_eq_of_sq hw2 (by rw [hsq2]; ring)]
      rw [show a - c * u / a - (-(c * u / a) - a) = 2 * a by ring, abs_of_pos (by linarith)]

/-- Hyperbola: the foci can be swapped, and the curve is symmetric under the point reflection in the midpoint
of the foci (its center) (PC-124). -/
@[kb "stitzzeager2013" "Definition 7.6, p. 543"]
theorem hyperbola_symm_center (F₁ F₂ : ℝ × ℝ) (d : ℝ) (P : ℝ × ℝ) :
    (IsHyperbolaPt F₁ F₂ d P ↔ IsHyperbolaPt F₂ F₁ d P) ∧
    (IsHyperbolaPt F₁ F₂ d P ↔
      IsHyperbolaPt F₁ F₂ d (F₁.1 + F₂.1 - P.1, F₁.2 + F₂.2 - P.2)) := by
  unfold IsHyperbolaPt
  rw [edist2_reflect_left, edist2_reflect_right]
  exact ⟨by rw [abs_sub_comm], by rw [abs_sub_comm]⟩

/-- For the hyperbola with foci `(±c, 0)` and a vertex `(a, 0)` (`0 < a < c`), the constant is `d = 2a`;
with `b = √(c^2 - a^2)`, `c^2 = a^2 + b^2` (PC-125). -/
@[kb "stitzzeager2013" "§7.5, p. 545"]
theorem hyperbola_vertex_difference {a c d : ℝ} (ha : 0 < a) (hac : a < c) :
    (IsHyperbolaPt (-c, 0) (c, 0) d (a, 0) ↔ d = 2 * a) ∧
    c ^ 2 = a ^ 2 + (√(c ^ 2 - a ^ 2)) ^ 2 := by
  constructor
  · have e1 : edist2 (a, 0) (-c, 0) = a + c :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    have e2 : edist2 (a, 0) (c, 0) = c - a :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    unfold IsHyperbolaPt
    rw [e1, e2, show a + c - (c - a) = 2 * a by ring, abs_of_pos (by linarith)]
    exact eq_comm
  · rw [Real.sq_sqrt (by nlinarith)]; ring

/-- Standard equation of the horizontal hyperbola with foci `(h ± c, k)`, `0 < a < c`, `b^2 = c^2 - a^2`:
the absolute difference of the focal distances is `2a` iff `(x-h)^2/a^2 - (y-k)^2/b^2 = 1` (PC-126). -/
@[kb "stitzzeager2013" "Equation 7.6, p. 546"]
theorem hyperbola_horizontal_equation {a b c : ℝ} (ha : 0 < a) (hac : a < c)
    (hb : b ^ 2 = c ^ 2 - a ^ 2) (h k x y : ℝ) :
    IsHyperbolaPt (h - c, k) (h + c, k) (2 * a) (x, y) ↔
      (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1 := by
  unfold IsHyperbolaPt
  rw [edist2_horizontal_foci_left, edist2_horizontal_foci_right, hb, abs_sub_comm]
  exact hyperbola_aux ha hac

/-- Standard equation of the vertical hyperbola with foci `(h, k ± c)`, vertices `(h, k ± b)`, `0 < b < c`,
`a^2 = c^2 - b^2`: `(y-k)^2/b^2 - (x-h)^2/a^2 = 1` (PC-126). -/
@[kb "stitzzeager2013" "Equation 7.7, p. 546"]
theorem hyperbola_vertical_equation {a b c : ℝ} (hb : 0 < b) (hbc : b < c)
    (ha : a ^ 2 = c ^ 2 - b ^ 2) (h k x y : ℝ) :
    IsHyperbolaPt (h, k - c) (h, k + c) (2 * b) (x, y) ↔
      (y - k) ^ 2 / b ^ 2 - (x - h) ^ 2 / a ^ 2 = 1 := by
  unfold IsHyperbolaPt
  rw [edist2_vertical_foci_up, edist2_vertical_foci_down, ha, abs_sub_comm]
  exact hyperbola_aux (u := y - k) (v := x - h) hb hbc

theorem asymptote_core {a b h : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Filter.Tendsto (fun x : ℝ => b / a * (√((x - h) ^ 2 - a ^ 2) - (x - h))) Filter.atTop (nhds 0) := by
  have hlow : Filter.Tendsto (fun x : ℝ => -(b / a * a ^ 2 / (x - h))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x - h) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-h) Filter.tendsto_id
    simpa using (tendsto_const_nhds.div_atTop h1 : Filter.Tendsto (fun x : ℝ => b / a * a ^ 2 / (x - h))
      Filter.atTop (nhds 0)).neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (h + a)] with x hx
    have ht : 0 < x - h := by linarith
    have hs := Real.sq_sqrt (show 0 ≤ (x - h) ^ 2 - a ^ 2 by nlinarith)
    have hs0 := Real.sqrt_nonneg ((x - h) ^ 2 - a ^ 2)
    generalize √((x - h) ^ 2 - a ^ 2) = s at *
    have h1 : -(a ^ 2) / (x - h) ≤ s - (x - h) := by
      rw [div_le_iff₀ ht]
      have : s ≤ x - h := by nlinarith
      nlinarith
    have h2 : -(b / a * a ^ 2 / (x - h)) = b / a * (-(a ^ 2) / (x - h)) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop (h + a)] with x hx
    have ht : 0 < x - h := by linarith
    have hs := Real.sq_sqrt (show 0 ≤ (x - h) ^ 2 - a ^ 2 by nlinarith)
    have hs0 := Real.sqrt_nonneg ((x - h) ^ 2 - a ^ 2)
    generalize √((x - h) ^ 2 - a ^ 2) = s at *
    have : s ≤ x - h := by nlinarith
    have : b / a * (s - (x - h)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    exact this

theorem hyperbola_branch_eq {a b h k y x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : h + a < x)
    (he : (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1) :
    (y - k) ^ 2 = (b / a * √((x - h) ^ 2 - a ^ 2)) ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (x - h) ^ 2 - a ^ 2 by nlinarith)
  rw [mul_pow, hs, div_pow]
  field_simp at he ⊢
  nlinarith

/-- Asymptotes of the horizontal hyperbola `(x-h)^2/a^2 - (y-k)^2/b^2 = 1` (`a, b > 0`): any function whose
graph runs along the upper right branch (`x > h + a`, `y > k`) approaches the line `y - k = (b/a)(x - h)`
as `x → ∞`, in the sense that the vertical gap tends to `0`; along the lower right branch (`y < k`) the gap
to the line `y - k = -(b/a)(x - h)` tends to `0` (PC-127). -/
@[kb "stitzzeager2013" "§7.5, p. 546"]
theorem hyperbola_asymptotes {a b h k : ℝ} (ha : 0 < a) (hb : 0 < b) (g : ℝ → ℝ) :
    ((∀ x, h + a < x → (x - h) ^ 2 / a ^ 2 - (g x - k) ^ 2 / b ^ 2 = 1 ∧ k < g x) →
      Filter.Tendsto (fun x => g x - (k + b / a * (x - h))) Filter.atTop (nhds 0)) ∧
    ((∀ x, h + a < x → (x - h) ^ 2 / a ^ 2 - (g x - k) ^ 2 / b ^ 2 = 1 ∧ g x < k) →
      Filter.Tendsto (fun x => g x - (k - b / a * (x - h))) Filter.atTop (nhds 0)) := by
  constructor
  · intro hg
    refine (asymptote_core (h := h) ha hb.le).congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (h + a)] with x hx
    obtain ⟨he, hk⟩ := hg x hx
    have h1 := hyperbola_branch_eq ha hb hx he
    have h2 : g x - k = b / a * √((x - h) ^ 2 - a ^ 2) :=
      (pow_left_inj₀ (by linarith) (by positivity) two_ne_zero).1 h1
    linarith
  · intro hg
    have := (asymptote_core (h := h) ha hb.le).neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (h + a)] with x hx
    obtain ⟨he, hk⟩ := hg x hx
    have h1 := hyperbola_branch_eq ha hb hx he
    have h2 : -(g x - k) = b / a * √((x - h) ^ 2 - a ^ 2) :=
      (pow_left_inj₀ (by linarith) (by positivity) two_ne_zero).1 (by rw [neg_sq]; exact h1)
    linarith

end UndergradKB.Precalculus
