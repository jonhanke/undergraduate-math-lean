import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.Conics

/-!
# Rotation of axes and polar equations of conics (Stitz-Zeager, Precalculus, §11.5-11.6)

What is proved: the coordinate change of a rotation (Theorem 11.9); the coefficient of `x'y'` after rotation and
the angle that removes it (Theorem 11.10); the invariance of `B^2 - 4AC` under rotation together with the
standard forms (ellipse/hyperbola/parabola equations) of the quadratic equations without an `xy` term, which is
what the discriminant test of Theorem 11.11 amounts to (the statement "non-degenerate conic of type X" is
rendered through these standard forms); the focus-directrix-eccentricity definition and the polar equations
(Theorems 11.12, 11.13) in the direction "points of the polar graph satisfy the focus-directrix property",
plus the converse for `r = ed/(1 - e cos θ)`.
-/

namespace UndergradKB.Precalculus

open Real

/-! ### Rotation of axes -/

/-- Rotating the axes counterclockwise by `θ`: the old coordinates `(x, y)` are given by the new ones
`(x', y')` through the first system iff the new ones are given by the old through the inverse system (PC-254). -/
@[kb "stitzzeager2013" "Theorem 11.9, p. 986"]
theorem rotation_coordinates (θ x y x' y' : ℝ) :
    (x = x' * cos θ - y' * sin θ ∧ y = x' * sin θ + y' * cos θ) ↔
      (x' = x * cos θ + y * sin θ ∧ y' = -x * sin θ + y * cos θ) := by
  have h := Real.cos_sq_add_sin_sq θ
  constructor
  · rintro ⟨rfl, rfl⟩
    constructor
    · linear_combination (-x') * h
    · linear_combination (-y') * h
  · rintro ⟨rfl, rfl⟩
    constructor
    · linear_combination (-x) * h
    · linear_combination (-y) * h

/-- A rotation of the axes preserves `x^2 + y^2` (PC-254). -/
@[kb "stitzzeager2013" "Theorem 11.9, p. 986"]
theorem rotation_preserves_norm_sq (θ x' y' : ℝ) :
    (x' * cos θ - y' * sin θ) ^ 2 + (x' * sin θ + y' * cos θ) ^ 2 = x' ^ 2 + y' ^ 2 := by
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination (x' ^ 2 + y' ^ 2) * h

/-- The general quadratic expression `A x^2 + B x y + C y^2 + D x + E y + F`. -/
def quadForm (A B C D E F x y : ℝ) : ℝ := A * x ^ 2 + B * x * y + C * y ^ 2 + D * x + E * y + F

/-- New coefficient of `x'^2` after rotating the axes by `θ`. -/
noncomputable def rotA (A B C θ : ℝ) : ℝ := A * cos θ ^ 2 + B * cos θ * sin θ + C * sin θ ^ 2
/-- New coefficient of `x'y'` after rotating the axes by `θ`. -/
noncomputable def rotB (A B C θ : ℝ) : ℝ := B * (cos θ ^ 2 - sin θ ^ 2) + 2 * (C - A) * sin θ * cos θ
/-- New coefficient of `y'^2` after rotating the axes by `θ`. -/
noncomputable def rotC (A B C θ : ℝ) : ℝ := A * sin θ ^ 2 - B * cos θ * sin θ + C * cos θ ^ 2
/-- New coefficient of `x'` after rotating the axes by `θ`. -/
noncomputable def rotD (D E θ : ℝ) : ℝ := D * cos θ + E * sin θ
/-- New coefficient of `y'` after rotating the axes by `θ`. -/
noncomputable def rotE (D E θ : ℝ) : ℝ := -D * sin θ + E * cos θ

/-- Substituting the rotation formulas into `A x^2 + B x y + C y^2 + D x + E y + F` gives the quadratic
expression in `x', y'` with the coefficients `rotA ... rotE` (PC-255). -/
theorem quadForm_rotate (A B C D E F θ x' y' : ℝ) :
    quadForm A B C D E F (x' * cos θ - y' * sin θ) (x' * sin θ + y' * cos θ) =
      quadForm (rotA A B C θ) (rotB A B C θ) (rotC A B C θ) (rotD D E θ) (rotE D E θ) F x' y' := by
  unfold quadForm rotA rotB rotC rotD rotE
  ring

/-- The `x'y'` coefficient after rotation by `θ` is `(C - A) sin 2θ + B cos 2θ` (PC-255). -/
@[kb "stitzzeager2013" "Theorem 11.10, p. 989"]
theorem rotB_eq (A B C θ : ℝ) :
    rotB A B C θ = (C - A) * sin (2 * θ) + B * cos (2 * θ) := by
  have h := Real.cos_sq_add_sin_sq θ
  rw [sin_two_mul, cos_two_mul]
  unfold rotB
  linear_combination (-B) * h

/-- If `B ≠ 0` and `cot 2θ = (A - C)/B` (with `sin 2θ ≠ 0`), the rotated equation has no `x'y'` term (PC-255). -/
@[kb "stitzzeager2013" "Theorem 11.10, p. 989"]
theorem rotB_eq_zero_of_cot {A B C θ : ℝ} (hB : B ≠ 0) (hs : sin (2 * θ) ≠ 0)
    (hcot : cos (2 * θ) / sin (2 * θ) = (A - C) / B) : rotB A B C θ = 0 := by
  rw [rotB_eq]
  field_simp at hcot
  linear_combination hcot

/-- For `B ≠ 0` there is an angle `θ` with `cot 2θ = (A - C)/B`, and for it the rotated equation has no
`x'y'` term: `rotB A B C θ = 0` (PC-255). -/
@[kb "stitzzeager2013" "Theorem 11.10, p. 989"]
theorem exists_rotation_eliminating_xy (A B C : ℝ) (hB : B ≠ 0) :
    ∃ θ : ℝ, sin (2 * θ) ≠ 0 ∧ cos (2 * θ) / sin (2 * θ) = (A - C) / B ∧ rotB A B C θ = 0 := by
  set t := (A - C) / B with ht
  refine ⟨(π / 2 - arctan t) / 2, ?_⟩
  have e : 2 * ((π / 2 - arctan t) / 2) = π / 2 - arctan t := by ring
  have hpos : 0 < √(1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs : sin (2 * ((π / 2 - arctan t) / 2)) ≠ 0 := by
    rw [e, Real.sin_pi_div_two_sub, Real.cos_arctan]; positivity
  have hc : cos (2 * ((π / 2 - arctan t) / 2)) / sin (2 * ((π / 2 - arctan t) / 2)) = t := by
    rw [e, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, Real.cos_arctan, Real.sin_arctan]
    field_simp
  exact ⟨hs, hc, rotB_eq_zero_of_cot hB hs hc⟩

/-! ### The discriminant -/

/-- The quantity `B^2 - 4AC` is unchanged by a rotation of the axes (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem discriminant_rotation_invariant (A B C θ : ℝ) :
    rotB A B C θ ^ 2 - 4 * rotA A B C θ * rotC A B C θ = B ^ 2 - 4 * A * C := by
  have h := Real.cos_sq_add_sin_sq θ
  have : rotB A B C θ ^ 2 - 4 * rotA A B C θ * rotC A B C θ =
      (B ^ 2 - 4 * A * C) * (cos θ ^ 2 + sin θ ^ 2) ^ 2 := by
    unfold rotB rotA rotC; ring
  rw [this, h]; ring

/-- Centre of the quadratic `A x^2 + C y^2 + D x + E y + F` (no `xy` term), `x0 = -D/(2A)`. -/
noncomputable def centerX (A D : ℝ) : ℝ := -D / (2 * A)

/-- The constant `R = D^2/(4A) + E^2/(4C) - F` of the completed-square form `A (x-x0)^2 + C (y-y0)^2 = R`. -/
noncomputable def centralRHS (A C D E F : ℝ) : ℝ := D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F

/-- Without an `xy` term and with `A, C ≠ 0`, the equation `A x^2 + C y^2 + D x + E y + F = 0` is, when
`R ≠ 0`, the equation `(x-x0)^2/(R/A) + (y-y0)^2/(R/C) = 1`. If `AC > 0` the two denominators have the same
sign (ellipse or circle form, as in Equation 7.4); if `AC < 0` they have opposite signs (hyperbola form,
Equations 7.6/7.7). This is the classification of Theorem 11.11 for the unrotated case `B = 0`, where
`B^2 - 4AC = -4AC` (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem conic_central_form {A C D E F : ℝ} (hA : A ≠ 0) (hC : C ≠ 0)
    (hR : centralRHS A C D E F ≠ 0) (x y : ℝ) :
    quadForm A 0 C D E F x y = 0 ↔
      (x - centerX A D) ^ 2 / (centralRHS A C D E F / A) +
        (y - centerX C E) ^ 2 / (centralRHS A C D E F / C) = 1 := by
  have key : quadForm A 0 C D E F x y =
      A * (x - centerX A D) ^ 2 + C * (y - centerX C E) ^ 2 - centralRHS A C D E F := by
    unfold quadForm centerX centralRHS; field_simp; ring
  have e : (x - centerX A D) ^ 2 / (centralRHS A C D E F / A) +
        (y - centerX C E) ^ 2 / (centralRHS A C D E F / C) =
      (A * (x - centerX A D) ^ 2 + C * (y - centerX C E) ^ 2) / centralRHS A C D E F := by
    field_simp
  rw [e, div_eq_one_iff_eq hR, key, sub_eq_zero]

/-- Sign pattern of the denominators in `conic_central_form`: for `AC > 0` the denominators `R/A`, `R/C` have the
same sign (ellipse type, `B^2 - 4AC < 0`); for `AC < 0` opposite signs (hyperbola type, `B^2 - 4AC > 0`)
(PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem conic_central_signs {A C R : ℝ} (hR : R ≠ 0) :
    (0 < A * C → 0 < (R / A) * (R / C)) ∧ (A * C < 0 → (R / A) * (R / C) < 0) := by
  have e : (R / A) * (R / C) = R ^ 2 / (A * C) := by
    rw [div_mul_div_comm, sq]
  have hR2 : 0 < R ^ 2 := by positivity
  rw [e]
  exact ⟨fun h => div_pos hR2 h, fun h => div_neg_of_pos_of_neg hR2 h⟩

/-- Parabola case of the unrotated classification (`B = 0`, `B^2 - 4AC = 0`): for `A ≠ 0`, `C = 0`, `E ≠ 0`,
the equation `A x^2 + D x + E y + F = 0` is `(x-h)^2 = 4p(y-k)` with `p = -E/(4A) ≠ 0`, `h = -D/(2A)`,
`k = (D^2/(4A) - F)/E` (Equation 7.2) (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem conic_parabola_form_vertical {A D E F : ℝ} (hA : A ≠ 0) (hE : E ≠ 0) (x y : ℝ) :
    quadForm A 0 0 D E F x y = 0 ↔
      (x - centerX A D) ^ 2 = 4 * (-E / (4 * A)) * (y - (D ^ 2 / (4 * A) - F) / E) := by
  have key : quadForm A 0 0 D E F x y =
      A * ((x - centerX A D) ^ 2 - 4 * (-E / (4 * A)) * (y - (D ^ 2 / (4 * A) - F) / E)) := by
    unfold quadForm centerX; field_simp; ring
  rw [key, mul_eq_zero, sub_eq_zero]
  simp [hA]

/-- Parabola case with `A = 0`, `C ≠ 0`, `D ≠ 0`: `(y-k)^2 = 4p(x-h)` with `p = -D/(4C)`,
`k = -E/(2C)`, `h = (E^2/(4C) - F)/D` (Equation 7.3) (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem conic_parabola_form_horizontal {C D E F : ℝ} (hC : C ≠ 0) (hD : D ≠ 0) (x y : ℝ) :
    quadForm 0 0 C D E F x y = 0 ↔
      (y - centerX C E) ^ 2 = 4 * (-D / (4 * C)) * (x - (E ^ 2 / (4 * C) - F) / D) := by
  have key : quadForm 0 0 C D E F x y =
      C * ((y - centerX C E) ^ 2 - 4 * (-D / (4 * C)) * (x - (E ^ 2 / (4 * C) - F) / D)) := by
    unfold quadForm centerX; field_simp; ring
  rw [key, mul_eq_zero, sub_eq_zero]
  simp [hC]

/-! ### Focus-directrix-eccentricity -/

/-- Conic with focus `F`, directrix the line `a x + b y = c` and eccentricity `e`: the points whose distance
to the focus is `e` times their distance to the line. -/
def IsConicPt (F : ℝ × ℝ) (a b c e : ℝ) (P : ℝ × ℝ) : Prop := edist2 P F = e * distToLine a b c P

/-- Squared form of the focus-directrix condition, for `e ≥ 0` and a genuine line (PC-257). -/
@[kb "stitzzeager2013" "Definition 11.1, p. 993"]
theorem conic_pt_iff (F : ℝ × ℝ) {a b c e : ℝ} (he : 0 ≤ e) (hab : a ^ 2 + b ^ 2 ≠ 0) (P : ℝ × ℝ) :
    IsConicPt F a b c e P ↔
      ((P.1 - F.1) ^ 2 + (P.2 - F.2) ^ 2) * (a ^ 2 + b ^ 2) = e ^ 2 * (a * P.1 + b * P.2 - c) ^ 2 := by
  have hm : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hab)
  have hsm : 0 < √(a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hm
  have hsq := Real.sq_sqrt hm.le
  unfold IsConicPt distToLine edist2
  rw [sqrt_eq_iff_sq (by positivity) (by positivity), mul_pow, div_pow, sq_abs, hsq]
  constructor
  · intro h; field_simp at h; linarith
  · intro h; field_simp; linarith

/-- Eccentricity `e = 1` is the parabola of Definition 7.3 (PC-257). -/
@[kb "stitzzeager2013" "Definition 11.1, p. 993"]
theorem conic_pt_one_iff_parabola (F : ℝ × ℝ) (a b c : ℝ) (P : ℝ × ℝ) :
    IsConicPt F a b c 1 P ↔ IsParabolaPt F a b c P := by
  unfold IsConicPt IsParabolaPt; rw [one_mul]

/-! ### Polar equations -/

theorem polar_conic_general {e r θ a b c : ℝ} (he : 0 < e) (hab : a ^ 2 + b ^ 2 = 1)
    (hr : r = e * (a * (r * cos θ) + b * (r * sin θ) - c) ∨
          r = -(e * (a * (r * cos θ) + b * (r * sin θ) - c))) :
    IsConicPt (0, 0) a b c e (r * cos θ, r * sin θ) := by
  unfold IsConicPt distToLine
  rw [hab, Real.sqrt_one, div_one]
  have h1 : edist2 (r * cos θ, r * sin θ) (0, 0) = |r| :=
    (edist2_eq_iff_sq (abs_nonneg _)).2 (by
      dsimp only; rw [sq_abs]; linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ)
  rw [h1]
  dsimp only
  rcases hr with hr | hr
  · conv_lhs => rw [hr]
    rw [abs_mul, abs_of_pos he]
  · conv_lhs => rw [hr]
    rw [abs_neg, abs_mul, abs_of_pos he]

/-- Polar graph `r = ed/(1 - e cos θ)` (`e, d > 0`): every point of it has distance to the pole equal to `e`
times its distance to the line `x = -d` (PC-258, forward direction). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_cos_minus {e d θ : ℝ} (he : 0 < e) (hd : 0 < d) (hθ : 1 - e * cos θ ≠ 0) :
    IsConicPt (0, 0) 1 0 (-d) e
      (e * d / (1 - e * cos θ) * cos θ, e * d / (1 - e * cos θ) * sin θ) := by
  apply polar_conic_general he (by norm_num)
  left
  field_simp
  ring

/-- Polar graph `r = ed/(1 + e cos θ)`: focus at the pole, directrix `x = d` (PC-258, forward direction). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_cos_plus {e d θ : ℝ} (he : 0 < e) (hd : 0 < d) (hθ : 1 + e * cos θ ≠ 0) :
    IsConicPt (0, 0) 1 0 d e
      (e * d / (1 + e * cos θ) * cos θ, e * d / (1 + e * cos θ) * sin θ) := by
  apply polar_conic_general he (by norm_num)
  right
  field_simp
  ring

/-- Polar graph `r = ed/(1 - e sin θ)`: focus at the pole, directrix `y = -d` (PC-258, forward direction). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_sin_minus {e d θ : ℝ} (he : 0 < e) (hd : 0 < d) (hθ : 1 - e * sin θ ≠ 0) :
    IsConicPt (0, 0) 0 1 (-d) e
      (e * d / (1 - e * sin θ) * cos θ, e * d / (1 - e * sin θ) * sin θ) := by
  apply polar_conic_general he (by norm_num)
  left
  field_simp
  ring

/-- Polar graph `r = ed/(1 + e sin θ)`: focus at the pole, directrix `y = d` (PC-258, forward direction). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_sin_plus {e d θ : ℝ} (he : 0 < e) (hd : 0 < d) (hθ : 1 + e * sin θ ≠ 0) :
    IsConicPt (0, 0) 0 1 d e
      (e * d / (1 + e * sin θ) * cos θ, e * d / (1 + e * sin θ) * sin θ) := by
  apply polar_conic_general he (by norm_num)
  right
  field_simp
  ring

theorem polar_converse_aux {e d r θ x y : ℝ} (he : 0 < e) (hd : 0 < d) (hx : r * cos θ = x)
    (hy : r * sin θ = y) (hr : r = e * (x + d)) :
    1 - e * cos θ ≠ 0 ∧
      (x, y) = (e * d / (1 - e * cos θ) * cos θ, e * d / (1 - e * cos θ) * sin θ) := by
  have h1 : r * (1 - e * cos θ) = e * d := by linear_combination hr - e * hx
  have hne : 1 - e * cos θ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    have : 0 < e * d := mul_pos he hd
    linarith
  have hr' : r = e * d / (1 - e * cos θ) := by
    rw [eq_div_iff hne]; exact h1
  refine ⟨hne, ?_⟩
  rw [← hr', hx, hy]

/-- Converse for `r = ed/(1 - e cos θ)`: every point `P ≠ (0,0)` with distance to the pole equal to `e` times
its distance to the line `x = -d` is a point `(r cos θ, r sin θ)` of the polar graph, for some `θ` with
`1 - e cos θ ≠ 0` (PC-258). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_cos_minus_converse {e d : ℝ} (he : 0 < e) (hd : 0 < d) (x y : ℝ)
    (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) (h : IsConicPt (0, 0) 1 0 (-d) e (x, y)) :
    ∃ θ : ℝ, 1 - e * cos θ ≠ 0 ∧
      (x, y) = (e * d / (1 - e * cos θ) * cos θ, e * d / (1 - e * cos θ) * sin θ) := by
  set z : ℂ := ⟨x, y⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h0
    apply hP
    have h1 : x = 0 := by simpa [hz] using congrArg Complex.re h0
    have h2 : y = 0 := by simpa [hz] using congrArg Complex.im h0
    rw [h1, h2]
  have hρ : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hρ2 : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hdist : edist2 (x, y) (0, 0) = ‖z‖ :=
    (edist2_eq_iff_sq hρ.le).2 (by dsimp only; rw [hρ2]; ring)
  have hx : ‖z‖ * cos (Complex.arg z) = x := Complex.norm_mul_cos_arg z
  have hy : ‖z‖ * sin (Complex.arg z) = y := Complex.norm_mul_sin_arg z
  unfold IsConicPt at h
  rw [distToLine_vertical, hdist] at h
  dsimp only at h
  rcases lt_trichotomy (x - -d) 0 with hlt | heq | hgt
  · -- x + d < 0: use the angle arg z + π and a negative radius
    rw [abs_of_neg hlt] at h
    have hr : -‖z‖ = e * (x + d) := by linarith
    refine ⟨Complex.arg z + π, ?_⟩
    apply polar_converse_aux he hd (r := -‖z‖) _ _ hr
    · rw [Real.cos_add_pi]; linarith
    · rw [Real.sin_add_pi]; linarith
  · rw [heq, abs_zero, mul_zero] at h
    linarith
  · rw [abs_of_pos hgt] at h
    have hr : ‖z‖ = e * (x + d) := by linarith
    exact ⟨Complex.arg z, polar_converse_aux he hd hx hy hr⟩

/-- Polar graph `r = ℓ/(1 - e cos(θ - φ))` (`ℓ > 0`, `e ≥ 0`), at an angle `θ` where the denominator is nonzero.
For `e = 0` the point is on the circle of radius `ℓ` about the pole; for `e > 0`, with `d = ℓ/e`, it satisfies the
focus-directrix property with focus the pole, eccentricity `e` and directrix the line
`x cos φ + y sin φ = -d`, which contains the point with polar coordinates `(-d, φ)` (PC-259; the book's
statement that the type is ellipse/parabola/hyperbola according to `e` is not reproduced here). -/
@[kb "stitzzeager2013" "Theorem 11.13, p. 997"]
theorem polar_conic_rotated {ℓ e φ θ : ℝ} (hℓ : 0 < ℓ) (he : 0 ≤ e) (hθ : 1 - e * cos (θ - φ) ≠ 0) :
    (e = 0 → edist2 (ℓ / (1 - e * cos (θ - φ)) * cos θ, ℓ / (1 - e * cos (θ - φ)) * sin θ) (0, 0) = ℓ) ∧
    (0 < e → IsConicPt (0, 0) (cos φ) (sin φ) (-(ℓ / e)) e
      (ℓ / (1 - e * cos (θ - φ)) * cos θ, ℓ / (1 - e * cos (θ - φ)) * sin θ)) ∧
    (0 < e → cos φ * (-(ℓ / e) * cos φ) + sin φ * (-(ℓ / e) * sin φ) = -(ℓ / e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    subst h0
    have : edist2 (ℓ / (1 - 0 * cos (θ - φ)) * cos θ, ℓ / (1 - 0 * cos (θ - φ)) * sin θ) (0, 0) = |ℓ / (1 - 0 * cos (θ - φ))| :=
      (edist2_eq_iff_sq (abs_nonneg _)).2 (by
        dsimp only; rw [sq_abs]; linear_combination (ℓ / (1 - 0 * cos (θ - φ))) ^ 2 * Real.cos_sq_add_sin_sq θ)
    rw [this]; simp [abs_of_pos hℓ]
  · intro he0
    apply polar_conic_general he0 (Real.cos_sq_add_sin_sq φ |>.symm ▸ by ring)
    left
    have hk : cos φ * (ℓ / (1 - e * cos (θ - φ)) * cos θ) + sin φ * (ℓ / (1 - e * cos (θ - φ)) * sin θ) =
        ℓ / (1 - e * cos (θ - φ)) * cos (θ - φ) := by
      rw [Real.cos_sub]; ring
    rw [hk]
    field_simp
    ring
  · intro he0
    have := Real.cos_sq_add_sin_sq φ
    linear_combination (-(ℓ / e)) * this

/-- A point `(x, y) ≠ (0, 0)` can be written `(s cos θ, s sin θ)` for any real `s` whose absolute value is its
distance to the origin. -/
theorem polar_rep_of_abs {x y s : ℝ} (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
    (h : |s| = edist2 (x, y) (0, 0)) : ∃ θ : ℝ, s * cos θ = x ∧ s * sin θ = y := by
  set z : ℂ := ⟨x, y⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h0
    apply hP
    have h1 : x = 0 := by simpa [hz] using congrArg Complex.re h0
    have h2 : y = 0 := by simpa [hz] using congrArg Complex.im h0
    rw [h1, h2]
  have hρ : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hρ2 : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hdist : edist2 (x, y) (0, 0) = ‖z‖ :=
    (edist2_eq_iff_sq hρ.le).2 (by dsimp only; rw [hρ2]; ring)
  have hx : ‖z‖ * cos (Complex.arg z) = x := Complex.norm_mul_cos_arg z
  have hy : ‖z‖ * sin (Complex.arg z) = y := Complex.norm_mul_sin_arg z
  rw [hdist] at h
  rcases (abs_eq hρ.le).1 h with hs | hs
  · exact ⟨Complex.arg z, by rw [hs]; exact hx, by rw [hs]; exact hy⟩
  · refine ⟨Complex.arg z + π, ?_, ?_⟩
    · rw [hs, Real.cos_add_pi]; linarith
    · rw [hs, Real.sin_add_pi]; linarith

theorem polar_converse_aux_cos_plus {e d r θ x y : ℝ} (he : 0 < e) (hd : 0 < d) (hx : r * cos θ = x)
    (hy : r * sin θ = y) (hr : r = e * (d - x)) :
    1 + e * cos θ ≠ 0 ∧
      (x, y) = (e * d / (1 + e * cos θ) * cos θ, e * d / (1 + e * cos θ) * sin θ) := by
  have h1 : r * (1 + e * cos θ) = e * d := by linear_combination hr + e * hx
  have hne : 1 + e * cos θ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    have : 0 < e * d := mul_pos he hd
    linarith
  have hr' : r = e * d / (1 + e * cos θ) := by
    rw [eq_div_iff hne]; exact h1
  refine ⟨hne, ?_⟩
  rw [← hr', hx, hy]

theorem polar_converse_aux_sin_minus {e d r θ x y : ℝ} (he : 0 < e) (hd : 0 < d) (hx : r * cos θ = x)
    (hy : r * sin θ = y) (hr : r = e * (y + d)) :
    1 - e * sin θ ≠ 0 ∧
      (x, y) = (e * d / (1 - e * sin θ) * cos θ, e * d / (1 - e * sin θ) * sin θ) := by
  have h1 : r * (1 - e * sin θ) = e * d := by linear_combination hr - e * hy
  have hne : 1 - e * sin θ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    have : 0 < e * d := mul_pos he hd
    linarith
  have hr' : r = e * d / (1 - e * sin θ) := by
    rw [eq_div_iff hne]; exact h1
  refine ⟨hne, ?_⟩
  rw [← hr', hx, hy]

theorem polar_converse_aux_sin_plus {e d r θ x y : ℝ} (he : 0 < e) (hd : 0 < d) (hx : r * cos θ = x)
    (hy : r * sin θ = y) (hr : r = e * (d - y)) :
    1 + e * sin θ ≠ 0 ∧
      (x, y) = (e * d / (1 + e * sin θ) * cos θ, e * d / (1 + e * sin θ) * sin θ) := by
  have h1 : r * (1 + e * sin θ) = e * d := by linear_combination hr + e * hy
  have hne : 1 + e * sin θ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    have : 0 < e * d := mul_pos he hd
    linarith
  have hr' : r = e * d / (1 + e * sin θ) := by
    rw [eq_div_iff hne]; exact h1
  refine ⟨hne, ?_⟩
  rw [← hr', hx, hy]

/-- Converse for `r = ed/(1 + e cos θ)` (directrix `x = d`) (PC-258). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_cos_plus_converse {e d : ℝ} (he : 0 < e) (hd : 0 < d) (x y : ℝ)
    (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) (h : IsConicPt (0, 0) 1 0 d e (x, y)) :
    ∃ θ : ℝ, 1 + e * cos θ ≠ 0 ∧
      (x, y) = (e * d / (1 + e * cos θ) * cos θ, e * d / (1 + e * cos θ) * sin θ) := by
  unfold IsConicPt at h
  rw [distToLine_vertical] at h
  dsimp only at h
  obtain ⟨θ, h1, h2⟩ := polar_rep_of_abs (s := -(e * (x - d))) hP (by
    rw [h, abs_neg, abs_mul, abs_of_pos he])
  exact ⟨θ, polar_converse_aux_cos_plus he hd h1 h2 (by ring)⟩

/-- Converse for `r = ed/(1 - e sin θ)` (directrix `y = -d`) (PC-258). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_sin_minus_converse {e d : ℝ} (he : 0 < e) (hd : 0 < d) (x y : ℝ)
    (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) (h : IsConicPt (0, 0) 0 1 (-d) e (x, y)) :
    ∃ θ : ℝ, 1 - e * sin θ ≠ 0 ∧
      (x, y) = (e * d / (1 - e * sin θ) * cos θ, e * d / (1 - e * sin θ) * sin θ) := by
  unfold IsConicPt at h
  rw [distToLine_horizontal] at h
  dsimp only at h
  obtain ⟨θ, h1, h2⟩ := polar_rep_of_abs (s := e * (y - -d)) hP (by
    rw [h, abs_mul, abs_of_pos he])
  exact ⟨θ, polar_converse_aux_sin_minus he hd h1 h2 (by ring)⟩

/-- Converse for `r = ed/(1 + e sin θ)` (directrix `y = d`) (PC-258). -/
@[kb "stitzzeager2013" "Theorem 11.12, p. 995"]
theorem polar_conic_sin_plus_converse {e d : ℝ} (he : 0 < e) (hd : 0 < d) (x y : ℝ)
    (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ))) (h : IsConicPt (0, 0) 0 1 d e (x, y)) :
    ∃ θ : ℝ, 1 + e * sin θ ≠ 0 ∧
      (x, y) = (e * d / (1 + e * sin θ) * cos θ, e * d / (1 + e * sin θ) * sin θ) := by
  unfold IsConicPt at h
  rw [distToLine_horizontal] at h
  dsimp only at h
  obtain ⟨θ, h1, h2⟩ := polar_rep_of_abs (s := -(e * (y - d))) hP (by
    rw [h, abs_neg, abs_mul, abs_of_pos he])
  exact ⟨θ, polar_converse_aux_sin_plus he hd h1 h2 (by ring)⟩

/-- Converse of the rotated polar form (`e > 0`): every point `P ≠ (0,0)` whose distance to the pole is `e`
times its distance to the line `x cos φ + y sin φ = -ℓ/e` lies on the graph of `r = ℓ/(1 - e cos(θ - φ))`
for some `θ` with nonzero denominator (PC-259). -/
@[kb "stitzzeager2013" "Theorem 11.13, p. 997"]
theorem polar_conic_rotated_converse {ℓ e φ : ℝ} (hℓ : 0 < ℓ) (he : 0 < e) (x y : ℝ)
    (hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ)))
    (h : IsConicPt (0, 0) (cos φ) (sin φ) (-(ℓ / e)) e (x, y)) :
    ∃ θ : ℝ, 1 - e * cos (θ - φ) ≠ 0 ∧
      (x, y) = (ℓ / (1 - e * cos (θ - φ)) * cos θ, ℓ / (1 - e * cos (θ - φ)) * sin θ) := by
  unfold IsConicPt distToLine at h
  rw [Real.cos_sq_add_sin_sq, Real.sqrt_one, div_one] at h
  dsimp only at h
  obtain ⟨θ, hx, hy⟩ := polar_rep_of_abs (s := e * (cos φ * x + sin φ * y - -(ℓ / e))) hP (by
    rw [h, abs_mul, abs_of_pos he])
  set r := e * (cos φ * x + sin φ * y - -(ℓ / e)) with hr
  have he' : e * (ℓ / e) = ℓ := by field_simp
  have h1 : r * (1 - e * cos (θ - φ)) = ℓ := by
    rw [Real.cos_sub]
    linear_combination hr - e * cos φ * hx - e * sin φ * hy + he'
  have hne : 1 - e * cos (θ - φ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    linarith
  refine ⟨θ, hne, ?_⟩
  have hr' : r = ℓ / (1 - e * cos (θ - φ)) := by
    rw [eq_div_iff hne]; exact h1
  rw [← hr', hx, hy]

/-- Discriminant test (PC-256), as far as proved. For every `A, B, C` there is a rotation angle `θ` after which
the `x'y'` coefficient vanishes (`rotB A B C θ = 0`; for `B = 0` take `θ = 0`, for `B ≠ 0` use
`cot 2θ = (A-C)/B`) and `B^2 - 4AC = -4 A'C'` where `A' = rotA`, `C' = rotC`. Consequently
`B^2 - 4AC > 0` forces `A'C' < 0`, `= 0` forces `A'C' = 0`, and `< 0` forces `A'C' > 0`. The rotated equation
has no cross term, so `conic_central_form`/`conic_central_signs` (when `A'C' ≠ 0` and the constant `R ≠ 0`:
opposite-sign denominators for `A'C' < 0` (hyperbola), same-sign ones for `A'C' > 0` (ellipse or circle)) and
`conic_parabola_form_vertical`/`_horizontal` (when `A'C' = 0` and the linear coefficient is nonzero: parabola)
describe the rotated equation. The degenerate cases (`R = 0`, or `A' = C' = 0`, or zero linear term) are
excluded, as in the book's "non-degenerate" hypothesis; it is not proved that the rotated point set is the
original one's image beyond `quadForm_rotate`, which is the substitution identity. -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem discriminant_test (A B C : ℝ) :
    ∃ θ : ℝ, rotB A B C θ = 0 ∧ B ^ 2 - 4 * A * C = -4 * (rotA A B C θ * rotC A B C θ) ∧
      (0 < B ^ 2 - 4 * A * C → rotA A B C θ * rotC A B C θ < 0) ∧
      (B ^ 2 - 4 * A * C = 0 → rotA A B C θ * rotC A B C θ = 0) ∧
      (B ^ 2 - 4 * A * C < 0 → 0 < rotA A B C θ * rotC A B C θ) := by
  have key : ∃ θ : ℝ, rotB A B C θ = 0 := by
    by_cases hB : B = 0
    · exact ⟨0, by simp [rotB, hB]⟩
    · obtain ⟨θ, -, -, h⟩ := exists_rotation_eliminating_xy A B C hB
      exact ⟨θ, h⟩
  obtain ⟨θ, hθ⟩ := key
  have hd := discriminant_rotation_invariant A B C θ
  rw [hθ] at hd
  have e : B ^ 2 - 4 * A * C = -4 * (rotA A B C θ * rotC A B C θ) := by linarith
  refine ⟨θ, hθ, e, ?_, ?_, ?_⟩ <;> intro h <;> rw [e] at h <;> nlinarith

end UndergradKB.Precalculus
