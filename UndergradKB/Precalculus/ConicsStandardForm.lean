import UndergradKB.Precalculus.ConicsClassify

/-!
# Writing a conic in standard form by completing the square (Stitz-Zeager, Precalculus, §7.2-§7.5)

Each of Sections 7.2-7.5 has a boxed procedure "to write the equation of a circle / parabola / ellipse / hyperbola in
standard form": group the variables, complete the square, divide by the right constant. The procedures rest on one
fact, proved here: for `A x² + C y² + D x + E y + F = 0` with no `xy` term,

* `A, C ≠ 0`: the equation is `A (x - h)² + C (y - k)² = K` with `h = -D/(2A)`, `k = -E/(2C)`,
  `K = D²/(4A) + E²/(4C) - F` (`conic_complete_square`);
* circle (`A = C`): a circle of center `(h, k)` and radius `√(K/A)` when `K/A > 0`, the single point `(h, k)` when
  `K = 0`, empty when `K/A < 0` (`circle_standard_form`);
* parabola (only one variable squared, the other present): `(y - k)² = 4p (x - h')` resp. `(x - h)² = 4p (y - k')`,
  hence the parabola with the corresponding focus and directrix (`parabola_standard_form_horizontal`,
  `parabola_standard_form_vertical`);
* ellipse (`A C > 0`, `K/A > 0`): `(x - h)²/(K/A) + (y - k)²/(K/C) = 1`, hence the ellipse with foci on the line of the
  longer axis (`ellipse_standard_form`, `ellipse_standard_form_foci`); `K = 0` a point, `K/A < 0` empty;
* hyperbola (`A C < 0`, `K ≠ 0`): `(x - h)²/(K/A) - (y - k)²/(-K/C) = 1` or the vertical form, hence the hyperbola with
  the corresponding foci (`hyperbola_standard_form`, `hyperbola_standard_form_foci`); `K = 0` two crossing lines.
-/

namespace UndergradKB.Precalculus

/-- Completing the square in both variables (the common step of the four boxes of §7.2-§7.5): for `A, C ≠ 0`,
`A x² + C y² + D x + E y + F = 0` iff `A (x - h)² + C (y - k)² = K` with `h = -D/(2A)`, `k = -E/(2C)` and
`K = D²/(4A) + E²/(4C) - F`. -/
@[kb "stitzzeager2013" "§7.4, p. 533"]
theorem conic_complete_square (A C D E F : ℝ) (hA : A ≠ 0) (hC : C ≠ 0) (x y : ℝ) :
    (x, y) ∈ conicGraph A 0 C D E F ↔
      A * (x - (-D / (2 * A))) ^ 2 + C * (y - (-E / (2 * C))) ^ 2 =
        D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F := by
  simp only [conicGraph, quadForm, Set.mem_ofPred_eq]
  have e : A * (x - (-D / (2 * A))) ^ 2 + C * (y - (-E / (2 * C))) ^ 2 -
      (D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F) = A * x ^ 2 + 0 * x * y + C * y ^ 2 + D * x + E * y + F := by
    field_simp
    ring
  constructor
  · intro h; linarith
  · intro h; linarith

/-- To write the equation of a circle in standard form (box in §7.2, p. 511): for `A ≠ 0`, the graph of
`A x² + A y² + D x + E y + F = 0` is, with `h = -D/(2A)`, `k = -E/(2A)` and `R = (D² + E² - 4AF)/(4A²)`, the set
`(x - h)² + (y - k)² = R`; it is the circle of center `(h, k)` and radius `√R` when `R > 0`, the single point
`(h, k)` when `R = 0`, and empty when `R < 0`. -/
@[kb "stitzzeager2013" "§7.2, p. 511"]
theorem circle_standard_form (A D E F : ℝ) (hA : A ≠ 0) :
    let h := -D / (2 * A)
    let k := -E / (2 * A)
    let R := (D ^ 2 + E ^ 2 - 4 * A * F) / (4 * A ^ 2)
    (∀ x y : ℝ, (x, y) ∈ conicGraph A 0 A D E F ↔ (x - h) ^ 2 + (y - k) ^ 2 = R) ∧
    (0 < R → conicGraph A 0 A D E F = {P | edist2 P (h, k) = √R}) ∧
    (R = 0 → conicGraph A 0 A D E F = {(h, k)}) ∧
    (R < 0 → conicGraph A 0 A D E F = ∅) := by
  intro h k R
  have key : ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 A D E F ↔ (x - h) ^ 2 + (y - k) ^ 2 = R := by
    intro x y
    rw [conic_complete_square A A D E F hA hA x y]
    have e1 : D ^ 2 / (4 * A) + E ^ 2 / (4 * A) - F = A * R := by
      simp only [R]; field_simp
    rw [e1, ← mul_add]
    exact mul_right_inj' hA
  have keyP : ∀ P : ℝ × ℝ, P ∈ conicGraph A 0 A D E F ↔ (P.1 - h) ^ 2 + (P.2 - k) ^ 2 = R :=
    fun P => key P.1 P.2
  refine ⟨key, fun hR => ?_, fun hR => ?_, fun hR => ?_⟩
  · ext P
    rw [keyP, Set.mem_ofPred_eq, edist2]
    have h0 : 0 ≤ (P.1 - h) ^ 2 + (P.2 - k) ^ 2 := by positivity
    rw [Real.sqrt_inj h0 hR.le]
  · ext P
    rw [keyP, Set.mem_singleton_iff, hR]
    constructor
    · intro hP
      have h1 : P.1 - h = 0 := by nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]
      have h2 : P.2 - k = 0 := by nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]
      exact Prod.ext (by simp only; linarith) (by simp only; linarith)
    · rintro rfl; simp
  · ext P
    simp only [Set.mem_empty_iff_false, iff_false, keyP]
    intro hP; nlinarith [sq_nonneg (P.1 - h), sq_nonneg (P.2 - k)]

/-- To write the equation of a parabola in standard form (box in §7.3, p. 521), `y` squared: for `C ≠ 0` and
`D ≠ 0`, `C y² + D x + E y + F = 0` iff `(y - k)² = 4p (x - h)` with `k = -E/(2C)`, `4p = -D/C` and
`h = (E²/(4C) - F)/D`; so the graph is the parabola with focus `(h + p, k)` and directrix `x = h - p`. -/
@[kb "stitzzeager2013" "§7.3, p. 521"]
theorem parabola_standard_form_horizontal (C D E F : ℝ) (hC : C ≠ 0) (hD : D ≠ 0) :
    let k := -E / (2 * C)
    let p := -D / (4 * C)
    let h := (E ^ 2 / (4 * C) - F) / D
    (∀ x y : ℝ, (x, y) ∈ conicGraph 0 0 C D E F ↔ (y - k) ^ 2 = 4 * p * (x - h)) ∧
    conicGraph 0 0 C D E F = parabolaSet (h + p, k) 1 0 (h - p) := by
  intro k p h
  have key : ∀ x y : ℝ, (x, y) ∈ conicGraph 0 0 C D E F ↔ (y - k) ^ 2 = 4 * p * (x - h) := by
    intro x y
    simp only [conicGraph, quadForm, Set.mem_ofPred_eq, k, p, h]
    have e : C * ((y - -E / (2 * C)) ^ 2 - 4 * (-D / (4 * C)) * (x - (E ^ 2 / (4 * C) - F) / D)) =
        0 * x ^ 2 + 0 * x * y + C * y ^ 2 + D * x + E * y + F := by
      field_simp
      ring
    rw [← e, mul_eq_zero, sub_eq_zero]
    simp [hC]
  refine ⟨key, ?_⟩
  ext ⟨x, y⟩
  rw [key]
  simp only [parabolaSet, IsParabolaPt, Set.mem_ofPred_eq]
  rw [parabola_horizontal_equation h k p x y]

/-- To write the equation of a parabola in standard form (box in §7.3, p. 521), `x` squared: for `A ≠ 0` and
`E ≠ 0`, `A x² + D x + E y + F = 0` iff `(x - h)² = 4p (y - k)` with `h = -D/(2A)`, `4p = -E/A` and
`k = (D²/(4A) - F)/E`; so the graph is the parabola with focus `(h, k + p)` and directrix `y = k - p`. -/
@[kb "stitzzeager2013" "§7.3, p. 521"]
theorem parabola_standard_form_vertical (A D E F : ℝ) (hA : A ≠ 0) (hE : E ≠ 0) :
    let h := -D / (2 * A)
    let p := -E / (4 * A)
    let k := (D ^ 2 / (4 * A) - F) / E
    (∀ x y : ℝ, (x, y) ∈ conicGraph A 0 0 D E F ↔ (x - h) ^ 2 = 4 * p * (y - k)) ∧
    conicGraph A 0 0 D E F = parabolaSet (h, k + p) 0 1 (k - p) := by
  intro h p k
  have key : ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 0 D E F ↔ (x - h) ^ 2 = 4 * p * (y - k) := by
    intro x y
    simp only [conicGraph, quadForm, Set.mem_ofPred_eq, k, p, h]
    have e : A * ((x - -D / (2 * A)) ^ 2 - 4 * (-E / (4 * A)) * (y - (D ^ 2 / (4 * A) - F) / E)) =
        A * x ^ 2 + 0 * x * y + 0 * y ^ 2 + D * x + E * y + F := by
      field_simp
      ring
    rw [← e, mul_eq_zero, sub_eq_zero]
    simp [hA]
  refine ⟨key, ?_⟩
  ext ⟨x, y⟩
  rw [key]
  simp only [parabolaSet, IsParabolaPt, Set.mem_ofPred_eq]
  rw [parabola_vertical_equation h k p x y]

/-- To write the equation of an ellipse in standard form (box in §7.4, p. 533): for `A C > 0`, with
`h = -D/(2A)`, `k = -E/(2C)` and `K = D²/(4A) + E²/(4C) - F`, the graph of `A x² + C y² + D x + E y + F = 0` is
`(x - h)²/(K/A) + (y - k)²/(K/C) = 1` when `K/A > 0` (both denominators are then positive), the single point `(h, k)`
when `K = 0`, and empty when `K/A < 0`. -/
@[kb "stitzzeager2013" "§7.4, p. 533"]
theorem ellipse_standard_form (A C D E F : ℝ) (hAC : 0 < A * C) :
    let h := -D / (2 * A)
    let k := -E / (2 * C)
    let K := D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F
    (0 < K / A → 0 < K / C ∧
      ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ (x - h) ^ 2 / (K / A) + (y - k) ^ 2 / (K / C) = 1) ∧
    (K = 0 → conicGraph A 0 C D E F = {(h, k)}) ∧
    (K / A < 0 → conicGraph A 0 C D E F = ∅) := by
  intro h k K
  have hA : A ≠ 0 := by rintro rfl; simp at hAC
  have hC : C ≠ 0 := by rintro rfl; simp at hAC
  have key : ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ A * (x - h) ^ 2 + C * (y - k) ^ 2 = K :=
    conic_complete_square A C D E F hA hC
  -- divide by `A`: `(x - h)² + (C/A) (y - k)² = K/A`, with `C/A > 0`
  have hCA : 0 < C / A := by
    have : C / A = (A * C) / A ^ 2 := by field_simp
    rw [this]; positivity
  have keyA : ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔
      (x - h) ^ 2 + C / A * (y - k) ^ 2 = K / A := by
    intro x y
    rw [key]
    constructor
    · intro e; rw [← e]; field_simp
    · intro e; field_simp at e; linarith
  refine ⟨fun hK => ?_, fun hK => ?_, fun hK => ?_⟩
  · have hKC : 0 < K / C := by
      have : K / C = (K / A) / (C / A) := by field_simp
      rw [this]; positivity
    refine ⟨hKC, fun x y => ?_⟩
    rw [keyA]
    have e : (x - h) ^ 2 / (K / A) + (y - k) ^ 2 / (K / C) =
        ((x - h) ^ 2 + C / A * (y - k) ^ 2) / (K / A) := by
      have hK0 : K ≠ 0 := by
        intro h0; rw [h0, zero_div] at hK; exact lt_irrefl 0 hK
      field_simp
    rw [e, div_eq_one_iff_eq hK.ne']
  · ext ⟨x, y⟩
    rw [keyA, hK, zero_div, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro e
      have h1 : (x - h) ^ 2 = 0 := by nlinarith [sq_nonneg (x - h), sq_nonneg (y - k)]
      have h2 : C / A * (y - k) ^ 2 = 0 := by nlinarith [sq_nonneg (x - h), sq_nonneg (y - k)]
      have h2' : (y - k) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 hCA.ne'
        · exact h3
      exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := x - h) two_ne_zero |>.1 h1],
        by nlinarith [pow_eq_zero_iff (n := 2) (a := y - k) two_ne_zero |>.1 h2']⟩
    · rintro ⟨rfl, rfl⟩; simp
  · ext ⟨x, y⟩
    simp only [Set.mem_empty_iff_false, iff_false, keyA]
    intro e
    nlinarith [sq_nonneg (x - h), sq_nonneg (y - k), mul_nonneg hCA.le (sq_nonneg (y - k))]

/-- The ellipse of `ellipse_standard_form` by its foci (Definition 7.4): if `0 < A ≤ C` (the `x` axis is the major
one) and `K > 0`, then with `a = √(K/A)` and `c = √(K/A - K/C)` the graph is the ellipse with foci `(h ± c, k)` and
distance sum `2a`. -/
@[kb "stitzzeager2013" "§7.4, p. 533"]
theorem ellipse_standard_form_foci (A C D E F : ℝ) (hA : 0 < A) (hAC : A ≤ C)
    (hK : 0 < D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F) :
    let h := -D / (2 * A)
    let k := -E / (2 * C)
    let K := D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F
    conicGraph A 0 C D E F =
      ellipseSet (h - √(K / A - K / C), k) (h + √(K / A - K / C), k) (2 * √(K / A)) := by
  intro h k K
  have hC : 0 < C := lt_of_lt_of_le hA hAC
  obtain ⟨-, key⟩ := (ellipse_standard_form A C D E F (mul_pos hA hC)).1 (div_pos hK hA)
  have hKA : 0 < K / A := div_pos hK hA
  have hKC : 0 < K / C := div_pos hK hC
  have hle : K / C ≤ K / A := div_le_div_of_nonneg_left hK.le hA hAC
  set a := √(K / A)
  set c := √(K / A - K / C)
  have ha : 0 < a := Real.sqrt_pos.2 hKA
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = K / A := Real.sq_sqrt hKA.le
  have hc2 : c ^ 2 = K / A - K / C := Real.sq_sqrt (by linarith)
  have hca : c < a := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  set b := √(K / C)
  have hb2 : b ^ 2 = a ^ 2 - c ^ 2 := by rw [Real.sq_sqrt hKC.le, ha2, hc2]; ring
  ext ⟨x, y⟩
  rw [key]
  simp only [ellipseSet, Set.mem_ofPred_eq]
  rw [ellipse_horizontal_equation ha hc hca hb2 h k x y, ha2, Real.sq_sqrt hKC.le]

/-- To write the equation of a hyperbola in standard form (box in §7.5, p. 549): for `A C < 0`, with
`h = -D/(2A)`, `k = -E/(2C)` and `K = D²/(4A) + E²/(4C) - F`, the graph of `A x² + C y² + D x + E y + F = 0` is
`(x - h)²/(K/A) - (y - k)²/(-K/C) = 1` when `K/A > 0`, `(y - k)²/(K/C) - (x - h)²/(-K/A) = 1` when `K/C > 0` (in each
case both denominators are positive), and, when `K = 0`, the two lines through `(h, k)` given by
`A (x - h)² = -C (y - k)²`. -/
@[kb "stitzzeager2013" "§7.5, p. 549"]
theorem hyperbola_standard_form (A C D E F : ℝ) (hAC : A * C < 0) :
    let h := -D / (2 * A)
    let k := -E / (2 * C)
    let K := D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F
    (0 < K / A → 0 < -K / C ∧
      ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ (x - h) ^ 2 / (K / A) - (y - k) ^ 2 / (-K / C) = 1) ∧
    (0 < K / C → 0 < -K / A ∧
      ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ (y - k) ^ 2 / (K / C) - (x - h) ^ 2 / (-K / A) = 1) ∧
    (K = 0 → ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ A * (x - h) ^ 2 = -C * (y - k) ^ 2) := by
  intro h k K
  have hA : A ≠ 0 := by rintro rfl; simp at hAC
  have hC : C ≠ 0 := by rintro rfl; simp at hAC
  have key : ∀ x y : ℝ, (x, y) ∈ conicGraph A 0 C D E F ↔ A * (x - h) ^ 2 + C * (y - k) ^ 2 = K :=
    conic_complete_square A C D E F hA hC
  have hneg : ∀ u : ℝ, 0 < u / A → 0 < -u / C := by
    intro u hu
    have : -u / C = (u / A) * (-(A * C)) / C ^ 2 := by field_simp
    rw [this]
    have : 0 < -(A * C) := by linarith
    positivity
  have hneg' : ∀ u : ℝ, 0 < u / C → 0 < -u / A := by
    intro u hu
    have : -u / A = (u / C) * (-(A * C)) / A ^ 2 := by field_simp
    rw [this]
    have : 0 < -(A * C) := by linarith
    positivity
  refine ⟨fun hK => ⟨hneg K hK, fun x y => ?_⟩, fun hK => ⟨hneg' K hK, fun x y => ?_⟩, fun hK x y => ?_⟩
  · have hK0 : K ≠ 0 := by rintro h0; rw [h0, zero_div] at hK; exact lt_irrefl 0 hK
    rw [key]
    have e : (x - h) ^ 2 / (K / A) - (y - k) ^ 2 / (-K / C) = (A * (x - h) ^ 2 + C * (y - k) ^ 2) / K := by
      field_simp; ring
    rw [e, div_eq_one_iff_eq hK0]
  · have hK0 : K ≠ 0 := by rintro h0; rw [h0, zero_div] at hK; exact lt_irrefl 0 hK
    rw [key]
    have e : (y - k) ^ 2 / (K / C) - (x - h) ^ 2 / (-K / A) = (A * (x - h) ^ 2 + C * (y - k) ^ 2) / K := by
      field_simp; ring
    rw [e, div_eq_one_iff_eq hK0]
  · rw [key, hK]
    constructor <;> intro e <;> linarith

/-- The hyperbola of `hyperbola_standard_form` by its foci (Definition 7.6), horizontal case: if `A C < 0` and
`K/A > 0`, then with `a = √(K/A)` and `c = √(K/A - K/C)` the graph is the hyperbola with foci `(h ± c, k)` and distance
difference `2a`. -/
@[kb "stitzzeager2013" "§7.5, p. 549"]
theorem hyperbola_standard_form_foci (A C D E F : ℝ) (hAC : A * C < 0)
    (hK : 0 < (D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F) / A) :
    let h := -D / (2 * A)
    let k := -E / (2 * C)
    let K := D ^ 2 / (4 * A) + E ^ 2 / (4 * C) - F
    conicGraph A 0 C D E F =
      hyperbolaSet (h - √(K / A - K / C), k) (h + √(K / A - K / C), k) (2 * √(K / A)) := by
  intro h k K
  obtain ⟨hKC, key⟩ := (hyperbola_standard_form A C D E F hAC).1 hK
  set a := √(K / A)
  set c := √(K / A - K / C)
  have ha : 0 < a := Real.sqrt_pos.2 hK
  have ha2 : a ^ 2 = K / A := Real.sq_sqrt hK.le
  have hc2 : c ^ 2 = K / A - K / C := Real.sq_sqrt (by rw [sub_eq_add_neg, ← neg_div]; positivity)
  have hca : a < c := Real.sqrt_lt_sqrt hK.le (by rw [sub_eq_add_neg, ← neg_div]; linarith)
  set b := √(-K / C)
  have hb2 : b ^ 2 = c ^ 2 - a ^ 2 := by rw [Real.sq_sqrt hKC.le, ha2, hc2]; ring
  ext ⟨x, y⟩
  rw [key]
  simp only [hyperbolaSet, Set.mem_ofPred_eq]
  rw [hyperbola_horizontal_equation ha hca hb2 h k x y, ha2, Real.sq_sqrt hKC.le]

end UndergradKB.Precalculus
