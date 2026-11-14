import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Precalculus.RationalSides

/-! # Course layer, Chapter 4 (Stitz-Zeager): the two sides of each vertical asymptote in the worked examples

The wave-4 theorems for Examples 4.1.2 and 4.2.1-4.2.3 (`Course/Ch4Ex.lean`) state that the lines are vertical
asymptotes; the book also says on which side the graph goes up and on which it goes down. Those one-sided limits are
stated here, from `tendsto_sides_of_eq_div_pow` (`RationalSides.lean`).
-/

namespace UndergradKB.Precalculus.Course

open Filter Topology Set

/-- Near `c`, the points `x ≠ c` also avoid a given `d ≠ c`. -/
theorem eventually_ne_of_ne {c d : ℝ} (h : c ≠ d) : ∀ᶠ x in 𝓝[≠] c, x ≠ c ∧ x ≠ d := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)] with x hx hd
  exact ⟨hx, hd⟩

/-- Stitz-Zeager Example 4.1.2(a), sides: for `f(x) = 2x/(x²-3)`, as `x → -√3⁻` and as `x → √3⁻` the values tend to
`-∞`, and as `x → -√3⁺` and as `x → √3⁺` they tend to `∞`. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_a_sides :
    let f := fun x : ℝ => 2 * x / (x ^ 2 - 3)
    Tendsto f (𝓝[<] (-Real.sqrt 3)) atBot ∧ Tendsto f (𝓝[>] (-Real.sqrt 3)) atTop ∧
      Tendsto f (𝓝[<] (Real.sqrt 3)) atBot ∧ Tendsto f (𝓝[>] (Real.sqrt 3)) atTop := by
  intro f
  have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨hA1, -, -, hA4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := f)
    (g := fun x => 2 * x / (x - Real.sqrt 3)) (c := -Real.sqrt 3) (m := 1) one_ne_zero
    (by fun_prop (disch := (simp only; intro h; linarith)))
    ((eventually_ne_of_ne (d := Real.sqrt 3) (by linarith)).mono fun x ⟨h1, h2⟩ => by
      have ha : x - Real.sqrt 3 ≠ 0 := sub_ne_zero.mpr h2
      have hb : x - -Real.sqrt 3 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - 3 = (x - Real.sqrt 3) * (x - -Real.sqrt 3) := by linear_combination hsq
      simp only [f, this, pow_one]; field_simp)
  obtain ⟨hB1, -, -, hB4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := f)
    (g := fun x => 2 * x / (x + Real.sqrt 3)) (c := Real.sqrt 3) (m := 1) one_ne_zero
    (by fun_prop (disch := (simp only; intro h; linarith)))
    ((eventually_ne_of_ne (d := -Real.sqrt 3) (by linarith)).mono fun x ⟨h1, h2⟩ => by
      have ha : x + Real.sqrt 3 ≠ 0 := fun h => h2 (by linarith)
      have hb : x - Real.sqrt 3 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - 3 = (x + Real.sqrt 3) * (x - Real.sqrt 3) := by linear_combination hsq
      simp only [f, this, pow_one]; field_simp)
  refine ⟨hA4 ?_, hA1 ?_, hB4 ?_, hB1 ?_⟩
  · have : 0 < 2 * -Real.sqrt 3 / (-Real.sqrt 3 - Real.sqrt 3) := by
      rw [show -Real.sqrt 3 - Real.sqrt 3 = 2 * -Real.sqrt 3 by ring, div_self (by linarith)]; norm_num
    simpa using this
  · rw [show -Real.sqrt 3 - Real.sqrt 3 = 2 * -Real.sqrt 3 by ring, div_self (by linarith)]; norm_num
  · simp
  · rw [show Real.sqrt 3 + Real.sqrt 3 = 2 * Real.sqrt 3 by ring, div_self (by linarith)]; norm_num

/-- Stitz-Zeager Example 4.1.2(b), sides: for `g(x) = (x²-x-6)/(x²-9)`, as `x → -3⁻` the values tend to `∞` and as
`x → -3⁺` to `-∞`. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_b_sides :
    let g := fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 - 9)
    Tendsto g (𝓝[<] (-3)) atTop ∧ Tendsto g (𝓝[>] (-3)) atBot := by
  intro g
  obtain ⟨-, h2, h3, -⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := g)
    (g := fun x => (x + 2)) (c := -3) (m := 1) one_ne_zero (by fun_prop)
    ((eventually_ne_of_ne (d := 3) (by norm_num)).mono fun x ⟨h1, h2⟩ => by
      have ha : x - 3 ≠ 0 := sub_ne_zero.mpr h2
      have hb : x - -3 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - 9 = (x - 3) * (x - -3) := by ring
      have h' : x ^ 2 - x - 6 = (x - 3) * (x + 2) := by ring
      simp only [g, this, h', pow_one]; field_simp)
  exact ⟨h3 (by norm_num), h2 (by norm_num)⟩

/-- Stitz-Zeager Example 4.1.2(d), sides: for `r(x) = (x²-x-6)/(x²+4x+4)`, as `x → -2⁻` the values tend to `∞` and
as `x → -2⁺` to `-∞`. -/
@[kb "stitzzeager2013" "Example 4.1.2, p. 318"]
theorem ex_4_1_2_d_sides :
    let r := fun x : ℝ => (x ^ 2 - x - 6) / (x ^ 2 + 4 * x + 4)
    Tendsto r (𝓝[<] (-2)) atTop ∧ Tendsto r (𝓝[>] (-2)) atBot := by
  intro r
  obtain ⟨-, h2, h3, -⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := r)
    (g := fun x => (x - 3)) (c := -2) (m := 1) one_ne_zero (by fun_prop)
    (self_mem_nhdsWithin |> Filter.mem_of_superset <| fun x (h1 : x ≠ -2) => by
      have hb : x - -2 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 + 4 * x + 4 = (x - -2) * (x - -2) := by ring
      have h' : x ^ 2 - x - 6 = (x - 3) * (x - -2) := by ring
      show r x = _
      simp only [r, this, h', pow_one]; field_simp)
  exact ⟨h3 (by norm_num), h2 (by norm_num)⟩

/-- Stitz-Zeager Example 4.2.1, sides: for `f(x) = 3x/(x²-4)`, as `x → -2⁻` and as `x → 2⁻` the values tend to
`-∞`, and as `x → -2⁺` and as `x → 2⁺` they tend to `∞`. -/
@[kb "stitzzeager2013" "Example 4.2.1, p. 334"]
theorem ex_4_2_1_sides :
    let f := fun x : ℝ => 3 * x / (x ^ 2 - 4)
    Tendsto f (𝓝[<] (-2)) atBot ∧ Tendsto f (𝓝[>] (-2)) atTop ∧
      Tendsto f (𝓝[<] 2) atBot ∧ Tendsto f (𝓝[>] 2) atTop := by
  intro f
  obtain ⟨hA1, -, -, hA4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := f)
    (g := fun x => 3 * x / (x - 2)) (c := -2) (m := 1) one_ne_zero
    (by fun_prop (disch := norm_num))
    ((eventually_ne_of_ne (d := 2) (by norm_num)).mono fun x ⟨h1, h2⟩ => by
      have ha : x - 2 ≠ 0 := sub_ne_zero.mpr h2
      have hb : x - -2 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - 4 = (x - 2) * (x - -2) := by ring
      simp only [f, this, pow_one]; field_simp)
  obtain ⟨hB1, -, -, hB4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := f)
    (g := fun x => 3 * x / (x + 2)) (c := 2) (m := 1) one_ne_zero
    (by fun_prop (disch := norm_num))
    ((eventually_ne_of_ne (d := -2) (by norm_num)).mono fun x ⟨h1, h2⟩ => by
      have ha : x + 2 ≠ 0 := fun h => h2 (by linarith)
      have hb : x - 2 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - 4 = (x + 2) * (x - 2) := by ring
      simp only [f, this, pow_one]; field_simp)
  exact ⟨hA4 (by norm_num), hA1 (by norm_num), hB4 (by norm_num), hB1 (by norm_num)⟩

/-- Stitz-Zeager Example 4.2.2, sides: for `g(x) = (2x²-3x-5)/(x²-x-6)`, as `x → -2⁻` the values tend to `∞` and as
`x → -2⁺` to `-∞`; as `x → 3⁻` they tend to `-∞` and as `x → 3⁺` to `∞`. -/
@[kb "stitzzeager2013" "Example 4.2.2, p. 337"]
theorem ex_4_2_2_sides :
    let g := fun x : ℝ => (2 * x ^ 2 - 3 * x - 5) / (x ^ 2 - x - 6)
    Tendsto g (𝓝[<] (-2)) atTop ∧ Tendsto g (𝓝[>] (-2)) atBot ∧
      Tendsto g (𝓝[<] 3) atBot ∧ Tendsto g (𝓝[>] 3) atTop := by
  intro g
  obtain ⟨-, hA2, hA3, -⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := g)
    (g := fun x => (2 * x ^ 2 - 3 * x - 5) / (x - 3)) (c := -2) (m := 1) one_ne_zero
    (by fun_prop (disch := norm_num))
    ((eventually_ne_of_ne (d := 3) (by norm_num)).mono fun x ⟨h1, h2⟩ => by
      have ha : x - 3 ≠ 0 := sub_ne_zero.mpr h2
      have hb : x - -2 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - x - 6 = (x - 3) * (x - -2) := by ring
      simp only [g, this, pow_one]; field_simp)
  obtain ⟨hB1, -, -, hB4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := g)
    (g := fun x => (2 * x ^ 2 - 3 * x - 5) / (x + 2)) (c := 3) (m := 1) one_ne_zero
    (by fun_prop (disch := norm_num))
    ((eventually_ne_of_ne (d := -2) (by norm_num)).mono fun x ⟨h1, h2⟩ => by
      have ha : x + 2 ≠ 0 := fun h => h2 (by linarith)
      have hb : x - 3 ≠ 0 := sub_ne_zero.mpr h1
      have : x ^ 2 - x - 6 = (x + 2) * (x - 3) := by ring
      simp only [g, this, pow_one]; field_simp)
  exact ⟨hA3 (by norm_num), hA2 (by norm_num), hB4 (by norm_num), hB1 (by norm_num)⟩

/-- Stitz-Zeager Example 4.2.3, sides: for `h(x) = (2x³+5x²+4x+1)/(x²+3x+2)`, as `x → -2⁻` the values tend to `-∞`
and as `x → -2⁺` to `∞`. -/
@[kb "stitzzeager2013" "Example 4.2.3, p. 340"]
theorem ex_4_2_3_sides :
    let h := fun x : ℝ => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x ^ 2 + 3 * x + 2)
    Tendsto h (𝓝[<] (-2)) atBot ∧ Tendsto h (𝓝[>] (-2)) atTop := by
  intro h
  obtain ⟨h1, -, -, h4⟩ := UndergradKB.Precalculus.tendsto_sides_of_eq_div_pow (f := h)
    (g := fun x => (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) / (x + 1)) (c := -2) (m := 1) one_ne_zero
    (by fun_prop (disch := norm_num))
    ((eventually_ne_of_ne (d := -1) (by norm_num)).mono fun x ⟨hx1, hx2⟩ => by
      have ha : x + 1 ≠ 0 := fun e => hx2 (by linarith)
      have hb : x - -2 ≠ 0 := sub_ne_zero.mpr hx1
      have : x ^ 2 + 3 * x + 2 = (x + 1) * (x - -2) := by ring
      simp only [h, this, pow_one]; field_simp)
  exact ⟨h4 (by norm_num), h1 (by norm_num)⟩

end UndergradKB.Precalculus.Course
