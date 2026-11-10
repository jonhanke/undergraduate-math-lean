import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr

/-! # Calculus: conic sections

Mathlib has no conic sections.  The plane is described by coordinates `x y : ℝ`; distances are computed with
`Real.sqrt` (the bridging definition `planeDist`, the Euclidean distance).  Contents: parabola, ellipse and
hyperbola in standard form from the focus definitions, asymptotes, eccentricity and the focus-directrix
characterisation, polar equations of conics with a focus at the pole, rotation of axes and the discriminant
classification, and the reflective property of the parabola as a vector statement. -/

namespace UndergradKB.Calculus

open Real

/-- The Euclidean distance between the points `(x, y)` and `(u, v)` of the plane, via `Real.sqrt`. -/
noncomputable def planeDist (x y u v : ℝ) : ℝ := √((x - u) ^ 2 + (y - v) ^ 2)

theorem planeDist_eq_iff {x y u v m : ℝ} (hm : 0 ≤ m) :
    planeDist x y u v = m ↔ (x - u) ^ 2 + (y - v) ^ 2 = m ^ 2 := by
  unfold planeDist
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) hm]
  constructor <;> intro h <;> nlinarith

/-! ## Parabola -/

/-- OpenStax Calculus 3:Theorem 1.8 (CA-411): a point is equidistant from the focus `(h + p, k)` and the
directrix `x = h - p` exactly when `(y - k)^2 = 4 p (x - h)` (vertex `(h, k)`, horizontal axis). -/
@[kb "openstaxcalculus2016" "3:Theorem 1.8, p. 73"]
theorem parabola_horizontal (h k p x y : ℝ) :
    planeDist x y (h + p) k = |x - (h - p)| ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  rw [planeDist_eq_iff (abs_nonneg _), sq_abs]
  constructor <;> intro hh <;> nlinarith

/-- OpenStax Calculus 3:Theorem 1.8 (CA-411): vertical axis, focus `(h, k + p)`, directrix `y = k - p`,
equation `(x - h)^2 = 4 p (y - k)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.8, p. 73"]
theorem parabola_vertical (h k p x y : ℝ) :
    planeDist x y h (k + p) = |y - (k - p)| ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
  rw [planeDist_eq_iff (abs_nonneg _), sq_abs]
  constructor <;> intro hh <;> nlinarith

/-- OpenStax Calculus 2:§7.5 Definition (parabola) (CA-410): the vertex `(h, k)` of the parabola with focus
`(h + p, k)` and directrix `x = h - p` lies on it, and is the midpoint of the focus and the foot `(h - p, k)`
of the perpendicular from the focus to the directrix. -/
@[kb "openstaxcalculus2016" "2:§7.5 Definition (parabola), p. 600"]
theorem parabola_vertex_midpoint (h k p : ℝ) :
    planeDist h k (h + p) k = |h - (h - p)| ∧ h = ((h + p) + (h - p)) / 2 ∧ k = (k + k) / 2 := by
  refine ⟨?_, by ring, by ring⟩
  rw [parabola_horizontal]
  ring

/-! ## Ellipse -/

/-- OpenStax Calculus 3:Theorem 1.9, 2:Theorem 7.9 (CA-413, CA-414): the points whose distances to the foci
`(h - c, k)`, `(h + c, k)` add up to `2a` form the ellipse `(x-h)^2/a^2 + (y-k)^2/b^2 = 1`, where
`c^2 = a^2 - b^2` (`0 < b ≤ a`, `c ≥ 0`). -/
@[kb "openstaxcalculus2016" "3:Theorem 1.9, p. 78"]
theorem ellipse_standard (a b c h k x y : ℝ) (hb : 0 < b) (hba : b ≤ a) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    planeDist x y (h - c) k + planeDist x y (h + c) k = 2 * a ↔
      (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1 := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hb2 : b ^ 2 = a ^ 2 - c ^ 2 := by linarith
  set X := x - h with hX
  set Y := y - k with hY
  have e1 : (x - (h - c)) = X + c := by rw [hX]; ring
  have e2 : (x - (h + c)) = X - c := by rw [hX]; ring
  unfold planeDist
  rw [e1, e2]
  have s1 : (√((X + c) ^ 2 + (y - k) ^ 2)) ^ 2 = (X + c) ^ 2 + Y ^ 2 := Real.sq_sqrt (by positivity)
  have s2 : (√((X - c) ^ 2 + (y - k) ^ 2)) ^ 2 = (X - c) ^ 2 + Y ^ 2 := Real.sq_sqrt (by positivity)
  have n1 := Real.sqrt_nonneg ((X + c) ^ 2 + (y - k) ^ 2)
  have n2 := Real.sqrt_nonneg ((X - c) ^ 2 + (y - k) ^ 2)
  set d1 := √((X + c) ^ 2 + (y - k) ^ 2)
  set d2 := √((X - c) ^ 2 + (y - k) ^ 2)
  constructor
  · intro hs
    have h1 : d1 = 2 * a - d2 := by linarith
    have h2 : a * d2 = a ^ 2 - c * X := by
      rw [h1] at s1
      nlinarith
    have key : (a ^ 2 - c * X) ^ 2 = a ^ 2 * ((X - c) ^ 2 + Y ^ 2) := by
      rw [← h2, mul_pow, s2]
    rw [div_add_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
    linear_combination (-1) * key + (X ^ 2 - a ^ 2) * hb2
  · intro E
    rw [div_add_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)] at E
    have hX2 : X ^ 2 ≤ a ^ 2 := by
      have : X ^ 2 * b ^ 2 ≤ a ^ 2 * b ^ 2 := by nlinarith [sq_nonneg Y]
      exact le_of_mul_le_mul_right this (by positivity)
    have hca : c ≤ a := by nlinarith
    have hXa := abs_le_of_sq_le_sq' hX2 ha.le
    have hcX : c * X ≤ a ^ 2 := by nlinarith [hXa.1, hXa.2]
    have hcX' : -(a ^ 2) ≤ c * X := by nlinarith [hXa.1, hXa.2]
    have d2e : d2 = (a ^ 2 - c * X) / a := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (div_nonneg (by linarith) ha.le)]
      field_simp
      linear_combination E - (X ^ 2 - a ^ 2) * hb2
    have d1e : d1 = (a ^ 2 + c * X) / a := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (div_nonneg (by linarith) ha.le)]
      field_simp
      linear_combination E - (X ^ 2 - a ^ 2) * hb2
    rw [d1e, d2e]
    field_simp
    ring

/-- OpenStax Calculus 3:Theorem 1.9 (CA-414), vertical major axis: foci `(h, k ± c)`, sum of distances `2a`,
equation `(x-h)^2/b^2 + (y-k)^2/a^2 = 1`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.9, p. 78"]
theorem ellipse_standard_vertical (a b c h k x y : ℝ) (hb : 0 < b) (hba : b ≤ a) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    planeDist x y h (k - c) + planeDist x y h (k + c) = 2 * a ↔
      (x - h) ^ 2 / b ^ 2 + (y - k) ^ 2 / a ^ 2 = 1 := by
  have := ellipse_standard a b c k h y x hb hba hc hc2
  have e : ∀ u v : ℝ, planeDist x y u v = planeDist y x v u := by
    intro u v
    unfold planeDist
    rw [add_comm]
  rw [e h (k - c), e h (k + c), this, add_comm]

/-! ## Hyperbola -/

/-- OpenStax Calculus 3:Theorem 1.10, 2:Theorem 7.10 (CA-415, CA-416): the points whose distances to the foci
`(h - c, k)`, `(h + c, k)` differ by `2a` in absolute value form the hyperbola
`(x-h)^2/a^2 - (y-k)^2/b^2 = 1`, where `c^2 = a^2 + b^2`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.10, p. 81"]
theorem hyperbola_standard (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) :
    |planeDist x y (h - c) k - planeDist x y (h + c) k| = 2 * a ↔
      (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1 := by
  have hb2 : b ^ 2 = c ^ 2 - a ^ 2 := by linarith
  set X := x - h with hX
  set Y := y - k with hY
  have e1 : (x - (h - c)) = X + c := by rw [hX]; ring
  have e2 : (x - (h + c)) = X - c := by rw [hX]; ring
  unfold planeDist
  rw [e1, e2]
  have s1 : (√((X + c) ^ 2 + (y - k) ^ 2)) ^ 2 = (X + c) ^ 2 + Y ^ 2 := Real.sq_sqrt (by positivity)
  have s2 : (√((X - c) ^ 2 + (y - k) ^ 2)) ^ 2 = (X - c) ^ 2 + Y ^ 2 := Real.sq_sqrt (by positivity)
  have n1 := Real.sqrt_nonneg ((X + c) ^ 2 + (y - k) ^ 2)
  have n2 := Real.sqrt_nonneg ((X - c) ^ 2 + (y - k) ^ 2)
  set d1 := √((X + c) ^ 2 + (y - k) ^ 2)
  set d2 := √((X - c) ^ 2 + (y - k) ^ 2)
  constructor
  · intro hs
    have key : (c * X - a ^ 2) ^ 2 = a ^ 2 * ((X - c) ^ 2 + Y ^ 2) := by
      rcases abs_eq (by linarith : (0 : ℝ) ≤ 2 * a) |>.mp hs with h1 | h1
      · have h1' : d1 = d2 + 2 * a := by linarith
        have h2 : a * d2 = c * X - a ^ 2 := by
          rw [h1'] at s1
          nlinarith
        rw [← h2, mul_pow, s2]
      · have h1' : d1 = d2 - 2 * a := by linarith
        have h2 : a * d2 = a ^ 2 - c * X := by
          rw [h1'] at s1
          nlinarith
        have : (c * X - a ^ 2) ^ 2 = (a ^ 2 - c * X) ^ 2 := by ring
        rw [this, ← h2, mul_pow, s2]
    rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
    linear_combination key + (X ^ 2 - a ^ 2) * hb2
  · intro E
    rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)] at E
    have hXa : a ≤ X ∨ X ≤ -a := by
      by_contra hcon
      rw [not_or, not_le, not_le] at hcon
      have h1 : X ^ 2 < a ^ 2 := by nlinarith [hcon.1, hcon.2]
      have : a ^ 2 * b ^ 2 ≤ X ^ 2 * b ^ 2 := by nlinarith [sq_nonneg Y, sq_nonneg a]
      nlinarith [mul_pos (pow_pos ha 2) (pow_pos hb 2)]
    have hca : a < c := by nlinarith
    have d1e : d1 = |(c * X + a ^ 2) / a| := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (abs_nonneg _), abs_mul_abs_self]
      field_simp
      linear_combination (-1) * E + (X ^ 2 - a ^ 2) * hb2
    have d2e : d2 = |(c * X - a ^ 2) / a| := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (abs_nonneg _), abs_mul_abs_self]
      field_simp
      linear_combination (-1) * E + (X ^ 2 - a ^ 2) * hb2
    rw [d1e, d2e]
    rcases hXa with h1 | h1
    · have p1 : 0 ≤ (c * X + a ^ 2) / a := div_nonneg (by nlinarith) ha.le
      have p2 : 0 ≤ (c * X - a ^ 2) / a := div_nonneg (by nlinarith) ha.le
      have e : (c * X + a ^ 2) / a - (c * X - a ^ 2) / a = 2 * a := by
        field_simp; ring
      rw [abs_of_nonneg p1, abs_of_nonneg p2, e, abs_of_pos (by linarith)]
    · have p1 : (c * X + a ^ 2) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
      have p2 : (c * X - a ^ 2) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) ha.le
      have e : -((c * X + a ^ 2) / a) - -((c * X - a ^ 2) / a) = -(2 * a) := by
        field_simp; ring
      rw [abs_of_nonpos p1, abs_of_nonpos p2, e, abs_neg, abs_of_pos (by linarith)]

/-- OpenStax Calculus 3:Theorem 1.10 (CA-416), asymptotes: on the right branch, far from the center, the
hyperbola `x^2/a^2 - y^2/b^2 = 1` (center at the origin) comes arbitrarily close, in the vertical direction,
to the asymptote `y = (b/a) x` (upper half) or `y = -(b/a) x` (lower half).  The general center `(h, k)` is a
translation. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.10, p. 81"]
theorem hyperbola_asymptote (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ x y : ℝ, x ^ 2 / a ^ 2 - y ^ 2 / b ^ 2 = 1 → M ≤ x →
      (0 ≤ y → |y - b / a * x| < ε) ∧ (y < 0 → |y + b / a * x| < ε) := by
  have aux : ∀ u v : ℝ, u * v = 1 → b / ε < v → 0 < u → b * u < ε := by
    intro u v huv hv hu
    have h1 : b < ε * v := by rwa [div_lt_iff₀ hε, mul_comm] at hv
    nlinarith
  refine ⟨a * (b / ε + 1), fun x y E hx => ?_⟩
  have hxa : b / ε + 1 ≤ x / a := by
    rw [le_div_iff₀ ha]; linarith
  have hbe : 0 < b / ε := by positivity
  have hxp : 0 < x / a := by linarith
  have huv : (x / a - y / b) * (x / a + y / b) = 1 := by
    rw [← E]; ring
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · have hyb : 0 ≤ y / b := div_nonneg hy hb.le
    have hu : 0 < x / a - y / b := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    have := aux (x / a - y / b) (x / a + y / b) huv (by linarith) hu
    have e : y - b / a * x = -(b * (x / a - y / b)) := by field_simp; ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    exact this
  · have hyb : y / b < 0 := div_neg_of_neg_of_pos hy hb
    have hu : 0 < x / a + y / b := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith
    have := aux (x / a + y / b) (x / a - y / b) (by linarith) (by linarith) hu
    have e : y + b / a * x = b * (x / a + y / b) := by field_simp; ring
    rw [e, abs_of_pos (by positivity)]
    exact this

/-! ## Eccentricity and the focus-directrix property -/

/-- OpenStax Calculus 3:§1.5 Definition (eccentricity) (CA-417), parabola: eccentricity `1` means that the
distance to the focus equals the distance to the directrix (the case `e = 1` of the definition). -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (eccentricity), p. 83"]
theorem parabola_eccentricity_one (h k p x y : ℝ) :
    planeDist x y (h + p) k = 1 * |x - (h - p)| ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
  rw [one_mul]; exact parabola_horizontal h k p x y

/-- OpenStax Calculus 3:§1.5 Definition (eccentricity) (CA-417), general form: a point with distance to the
focus `(f, 0)` equal to `e` times its distance to the line `x = d` satisfies a degree-two equation whose
`x^2` coefficient is `1 - e^2`, the `y^2` coefficient `1` and which has no `xy` term. -/
@[kb "openstaxcalculus2016" "3:§1.5 Definition (eccentricity), p. 83"]
theorem focus_directrix_quadratic (e f d x y : ℝ) (he : 0 ≤ e) :
    planeDist x y f 0 = e * |x - d| ↔
      (1 - e ^ 2) * x ^ 2 + y ^ 2 - 2 * (f - e ^ 2 * d) * x + (f ^ 2 - e ^ 2 * d ^ 2) = 0 := by
  rw [planeDist_eq_iff (by positivity), mul_pow, sq_abs]
  constructor <;> intro hh <;> nlinarith

/-- OpenStax Calculus 3:§1.5 Table 1.1 (CA-417): the discriminant `B^2 - 4AC` of the equation of
`focus_directrix_quadratic` (`A = 1 - e^2`, `B = 0`, `C = 1`) is negative for `e < 1`, zero for `e = 1` and
positive for `e > 1`: ellipse, parabola, hyperbola. -/
@[kb "openstaxcalculus2016" "3:§1.5 Table 1.1, p. 85"]
theorem eccentricity_discriminant (e : ℝ) :
    ((0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1 = -4 * (1 - e ^ 2)) ∧
    (e ^ 2 < 1 ↔ (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1 < 0) ∧
    (e ^ 2 = 1 ↔ (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1 = 0) ∧
    (1 < e ^ 2 ↔ 0 < (0 : ℝ) ^ 2 - 4 * (1 - e ^ 2) * 1) := by
  refine ⟨by ring, ?_, ?_, ?_⟩ <;> constructor <;> intro h <;> nlinarith

/-- OpenStax Calculus 2:§7.5 Eccentricity of ellipse and hyperbola (CA-417, CA-418): for the ellipse
`(x-h)^2/a^2 + (y-k)^2/b^2 = 1` with focus `(h + c, k)` (`c^2 = a^2 - b^2`, `c > 0`) the distance to the focus
is `e` times the distance to the line `x = h + a^2/c` (the directrix), with `e = c/a < 1`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Eccentricity of ellipse and hyperbola, p. 612"]
theorem ellipse_directrix (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 - b ^ 2) :
    (planeDist x y (h + c) k = (c / a) * |x - (h + a ^ 2 / c)| ↔
      (x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 = 1) ∧ c / a < 1 := by
  refine ⟨?_, ?_⟩
  · rw [planeDist_eq_iff (by positivity), mul_pow, sq_abs]
    have iden : (x - (h + c)) ^ 2 + (y - k) ^ 2 - (c / a) ^ 2 * (x - (h + a ^ 2 / c)) ^ 2 =
        ((x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 := by
      field_simp
      linear_combination (a ^ 2 - (x - h) ^ 2) * hc2
    have hb2 : b ^ 2 ≠ 0 := by positivity
    constructor
    · intro hh
      have : ((x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 = 0 := by rw [← iden]; linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hb2
    · intro hh
      have : ((x - h) ^ 2 / a ^ 2 + (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 = 0 := by rw [hh]; ring
      linarith
  · rw [div_lt_one ha]
    nlinarith [sq_nonneg b, pow_pos hb 2]

/-- OpenStax Calculus 2:§7.5 Eccentricity of ellipse and hyperbola (CA-417, CA-418): for the hyperbola
`(x-h)^2/a^2 - (y-k)^2/b^2 = 1` with focus `(h + c, k)` (`c^2 = a^2 + b^2`, `c > 0`) the distance to the
focus is `e` times the distance to the line `x = h + a^2/c`, with `e = c/a > 1`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Eccentricity of ellipse and hyperbola, p. 612"]
theorem hyperbola_directrix (a b c h k x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) :
    (planeDist x y (h + c) k = (c / a) * |x - (h + a ^ 2 / c)| ↔
      (x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 = 1) ∧ 1 < c / a := by
  refine ⟨?_, ?_⟩
  · rw [planeDist_eq_iff (by positivity), mul_pow, sq_abs]
    have iden : (x - (h + c)) ^ 2 + (y - k) ^ 2 - (c / a) ^ 2 * (x - (h + a ^ 2 / c)) ^ 2 =
        -((x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 := by
      field_simp
      linear_combination (a ^ 2 - (x - h) ^ 2) * hc2
    have hb2 : b ^ 2 ≠ 0 := by positivity
    constructor
    · intro hh
      have : -((x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 = 0 := by rw [← iden]; linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hb2
    · intro hh
      have : -((x - h) ^ 2 / a ^ 2 - (y - k) ^ 2 / b ^ 2 - 1) * b ^ 2 = 0 := by rw [hh]; ring
      linarith
  · rw [one_lt_div ha]
    nlinarith [pow_pos hb 2]

/-! ## Polar equation of a conic with a focus at the pole -/

theorem planeDist_polar (r θ : ℝ) (hr : 0 ≤ r) : planeDist (r * cos θ) (r * sin θ) 0 0 = r := by
  rw [planeDist_eq_iff hr]
  nlinarith [sin_sq_add_cos_sq θ]

/-- OpenStax Calculus 3:Theorem 1.11, 2:Theorem 7.11 (CA-419), directrix `x = p` (`p > 0`, to the right of the
pole): for a point `(r cos θ, r sin θ)` (`r ≥ 0`) on the focus side of the directrix, the distance to the focus
at the pole is `e` times the distance to the directrix iff `r (1 + e cos θ) = e p`, i.e.
`r = e p / (1 + e cos θ)` when the denominator is nonzero. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.11, p. 85"]
theorem polar_conic_cos_plus (e p r θ : ℝ) (hr : 0 ≤ r) (hside : r * cos θ ≤ p) :
    (planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * cos θ - p| ↔ r * (1 + e * cos θ) = e * p) ∧
    (1 + e * cos θ ≠ 0 → (r * (1 + e * cos θ) = e * p ↔ r = e * p / (1 + e * cos θ))) := by
  refine ⟨?_, fun hne => by rw [eq_div_iff hne]⟩
  rw [planeDist_polar r θ hr, abs_of_nonpos (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- OpenStax Calculus 3:Theorem 1.11 (CA-419), directrix `x = -p`: `r (1 - e cos θ) = e p`, i.e.
`r = e p / (1 - e cos θ)`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.11, p. 85"]
theorem polar_conic_cos_minus (e p r θ : ℝ) (hr : 0 ≤ r) (hside : -p ≤ r * cos θ) :
    (planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * cos θ - -p| ↔ r * (1 - e * cos θ) = e * p) ∧
    (1 - e * cos θ ≠ 0 → (r * (1 - e * cos θ) = e * p ↔ r = e * p / (1 - e * cos θ))) := by
  refine ⟨?_, fun hne => by rw [eq_div_iff hne]⟩
  rw [planeDist_polar r θ hr, abs_of_nonneg (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- OpenStax Calculus 3:Theorem 1.11 (CA-419), vertical axis, directrix `y = p`: `r (1 + e sin θ) = e p`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.11, p. 85"]
theorem polar_conic_sin_plus (e p r θ : ℝ) (hr : 0 ≤ r) (hside : r * sin θ ≤ p) :
    (planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * sin θ - p| ↔ r * (1 + e * sin θ) = e * p) ∧
    (1 + e * sin θ ≠ 0 → (r * (1 + e * sin θ) = e * p ↔ r = e * p / (1 + e * sin θ))) := by
  refine ⟨?_, fun hne => by rw [eq_div_iff hne]⟩
  rw [planeDist_polar r θ hr, abs_of_nonpos (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- OpenStax Calculus 3:Theorem 1.11 (CA-419), vertical axis, directrix `y = -p`: `r (1 - e sin θ) = e p`. -/
@[kb "openstaxcalculus2016" "3:Theorem 1.11, p. 85"]
theorem polar_conic_sin_minus (e p r θ : ℝ) (hr : 0 ≤ r) (hside : -p ≤ r * sin θ) :
    (planeDist (r * cos θ) (r * sin θ) 0 0 = e * |r * sin θ - -p| ↔ r * (1 - e * sin θ) = e * p) ∧
    (1 - e * sin θ ≠ 0 → (r * (1 - e * sin θ) = e * p ↔ r = e * p / (1 - e * sin θ))) := by
  refine ⟨?_, fun hne => by rw [eq_div_iff hne]⟩
  rw [planeDist_polar r θ hr, abs_of_nonneg (by linarith)]
  constructor <;> intro h <;> nlinarith

/-! ## Rotation of axes and the discriminant -/

/-- New coefficient `A'` of `x'^2` after rotating the axes by `θ`. -/
noncomputable def rotA (A B C θ : ℝ) : ℝ := A * cos θ ^ 2 + B * cos θ * sin θ + C * sin θ ^ 2

/-- New coefficient `B'` of `x'y'` after rotating the axes by `θ`. -/
noncomputable def rotB (A B C θ : ℝ) : ℝ := B * (cos θ ^ 2 - sin θ ^ 2) + 2 * (C - A) * sin θ * cos θ

/-- New coefficient `C'` of `y'^2` after rotating the axes by `θ`. -/
noncomputable def rotC (A B C θ : ℝ) : ℝ := A * sin θ ^ 2 - B * cos θ * sin θ + C * cos θ ^ 2

/-- New coefficient `D'` of `x'` after rotating the axes by `θ`. -/
noncomputable def rotD (D E θ : ℝ) : ℝ := D * cos θ + E * sin θ

/-- New coefficient `E'` of `y'` after rotating the axes by `θ`. -/
noncomputable def rotE (D E θ : ℝ) : ℝ := -D * sin θ + E * cos θ

/-- OpenStax Calculus 3:§1.5 rotation of axes formulas (CA-421): if the new coordinates `(x', y')` are related
to `(x, y)` by `x = x' cos θ - y' sin θ`, `y = x' sin θ + y' cos θ`, then the quadratic expression
`A x^2 + B x y + C y^2 + D x + E y + F` equals `A' x'^2 + B' x'y' + C' y'^2 + D' x' + E' y' + F`. -/
@[kb "openstaxcalculus2016" "3:§1.5 rotation of axes formulas, p. 87"]
theorem rotation_equation (A B C D E F θ x' y' : ℝ) :
    A * (x' * cos θ - y' * sin θ) ^ 2 + B * (x' * cos θ - y' * sin θ) * (x' * sin θ + y' * cos θ) +
        C * (x' * sin θ + y' * cos θ) ^ 2 + D * (x' * cos θ - y' * sin θ) +
        E * (x' * sin θ + y' * cos θ) + F =
      rotA A B C θ * x' ^ 2 + rotB A B C θ * x' * y' + rotC A B C θ * y' ^ 2 + rotD D E θ * x' +
        rotE D E θ * y' + F := by
  unfold rotA rotB rotC rotD rotE
  ring

/-- OpenStax Calculus 3:§1.5 rotation of axes formulas (CA-421): the coefficient of the cross term is
`B' = B cos 2θ + (C - A) sin 2θ`. -/
@[kb "openstaxcalculus2016" "3:§1.5 rotation of axes formulas, p. 87"]
theorem rotB_eq (A B C θ : ℝ) : rotB A B C θ = B * cos (2 * θ) + (C - A) * sin (2 * θ) := by
  unfold rotB
  rw [cos_two_mul', sin_two_mul]
  ring

/-- OpenStax Calculus 2:§7.5 Rotation of axes (CA-421): if `B ≠ 0` and `cot 2θ = (A - C)/B` (with `sin 2θ ≠ 0`),
the rotation by `θ` removes the cross term: `B' = 0`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Rotation of axes for a conic, p. 615"]
theorem rotB_eq_zero_of_cot (A B C θ : ℝ) (hB : B ≠ 0) (hs : sin (2 * θ) ≠ 0)
    (h : cos (2 * θ) / sin (2 * θ) = (A - C) / B) : rotB A B C θ = 0 := by
  rw [rotB_eq]
  rw [div_eq_div_iff hs hB] at h
  linear_combination h

/-- OpenStax Calculus 2:§7.5 Rotation of axes (CA-421): an angle removing the cross term always exists. -/
@[kb "openstaxcalculus2016" "2:§7.5 Rotation of axes for a conic, p. 615"]
theorem exists_rotB_eq_zero (A B C : ℝ) : ∃ θ : ℝ, rotB A B C θ = 0 := by
  set z : ℂ := ((C - A : ℝ) : ℂ) + (B : ℂ) * Complex.I with hz
  refine ⟨-(Complex.arg z) / 2, ?_⟩
  rw [rotB_eq]
  have e : 2 * (-(Complex.arg z) / 2) = -(Complex.arg z) := by ring
  rw [e, Real.cos_neg, Real.sin_neg]
  have h1 := Complex.norm_mul_cos_arg z
  have h2 := Complex.norm_mul_sin_arg z
  have hre : z.re = C - A := by simp [hz]
  have him : z.im = B := by simp [hz]
  rw [hre] at h1
  rw [him] at h2
  linear_combination sin z.arg * h1 - cos z.arg * h2

/-- OpenStax Calculus 3:§1.5 discriminant classification (CA-420): the discriminant is invariant under
rotation, `B'^2 - 4A'C' = B^2 - 4AC`. -/
@[kb "openstaxcalculus2016" "3:§1.5 discriminant classification, p. 86"]
theorem rotation_discriminant (A B C θ : ℝ) :
    rotB A B C θ ^ 2 - 4 * rotA A B C θ * rotC A B C θ = B ^ 2 - 4 * A * C := by
  unfold rotA rotB rotC
  have h := sin_sq_add_cos_sq θ
  linear_combination (B ^ 2 - 4 * A * C) * (sin θ ^ 2 + cos θ ^ 2 + 1) * h

/-- OpenStax Calculus 2:§7.5 General equations of degree two (CA-420): once the cross term is removed
(`B' = 0`), the discriminant is `B^2 - 4AC = -4 A'C'`, so the equation is of elliptic type (`B^2 - 4AC < 0`)
iff `A'C' > 0`, of parabolic type (`= 0`) iff `A'C' = 0`, of hyperbolic type (`> 0`) iff `A'C' < 0`. -/
@[kb "openstaxcalculus2016" "2:§7.5 General equations of degree two (discriminant), p. 614"]
theorem discriminant_classification (A B C θ : ℝ) (h : rotB A B C θ = 0) :
    B ^ 2 - 4 * A * C = -4 * (rotA A B C θ * rotC A B C θ) ∧
    (B ^ 2 - 4 * A * C < 0 ↔ 0 < rotA A B C θ * rotC A B C θ) ∧
    (B ^ 2 - 4 * A * C = 0 ↔ rotA A B C θ * rotC A B C θ = 0) ∧
    (0 < B ^ 2 - 4 * A * C ↔ rotA A B C θ * rotC A B C θ < 0) := by
  have hd := rotation_discriminant A B C θ
  rw [h] at hd
  have e : B ^ 2 - 4 * A * C = -4 * (rotA A B C θ * rotC A B C θ) := by linarith
  refine ⟨e, ?_, ?_, ?_⟩ <;> rw [e] <;> constructor <;> intro hh <;> nlinarith

/-! ## Reflective property of the parabola -/

/-- OpenStax Calculus 2:§7.5 Reflective properties (CA-412), parabola `y = x^2/(4p)` (`p > 0`) with focus
`(0, p)` and vertical axis.  At the point `P = (t, t^2/(4p))` the tangent direction is `T = (1, s)`,
`s = t/(2p)`; a ray arriving parallel to the axis has direction `d = (0, -1)`.  Reflecting `d` in the tangent
line gives `2 (d·T)/(T·T) T - d`, and this is a positive multiple (`1/(p (1 + s^2))`) of the vector
`F - P = (-t, p - t^2/(4p))` from the point to the focus. -/
@[kb "openstaxcalculus2016" "2:§7.5 Reflective properties of parabola, ellipse, hyperbola, p. 603"]
theorem parabola_reflective (p t : ℝ) (hp : 0 < p) :
    HasDerivAt (fun u : ℝ => u ^ 2 / (4 * p)) (t / (2 * p)) t ∧
    (2 * ((0 * 1 + (-1) * (t / (2 * p))) / (1 * 1 + (t / (2 * p)) * (t / (2 * p)))) * 1 - 0 =
        (1 / (p * (1 + (t / (2 * p)) ^ 2))) * (0 - t)) ∧
    (2 * ((0 * 1 + (-1) * (t / (2 * p))) / (1 * 1 + (t / (2 * p)) * (t / (2 * p)))) * (t / (2 * p)) - (-1) =
        (1 / (p * (1 + (t / (2 * p)) ^ 2))) * (p - t ^ 2 / (4 * p))) ∧
    0 < 1 / (p * (1 + (t / (2 * p)) ^ 2)) := by
  refine ⟨?_, ?_, ?_, by positivity⟩
  · have := ((hasDerivAt_pow 2 t).div_const (4 * p))
    convert this using 1
    field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

end UndergradKB.Calculus
