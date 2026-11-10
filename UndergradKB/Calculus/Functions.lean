import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Function
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set

/-- The graph of a real function `f`, as a subset of the plane: `{(x, f x)}`. -/
def fnGraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | p.2 = f p.1}

theorem mem_fnGraph {f : ℝ → ℝ} {x y : ℝ} : (x, y) ∈ fnGraph f ↔ y = f x := Iff.rfl

/-! ### Line tests (CA-003, CA-026) -/

/-- OpenStax Calculus 1:§1.1 Vertical Line Test (CA-003). A set `S` of points of the plane is the graph of
a function defined on its projection to the `x`-axis exactly when every vertical line meets `S` at most
once. -/
@[kb "openstaxcalculus2016" "1:§1.1 Rule: Vertical Line Test, p. 22"]
theorem vertical_line_test (S : Set (ℝ × ℝ)) :
    (∃ f : ℝ → ℝ, S = {p | p.1 ∈ Prod.fst '' S ∧ p.2 = f p.1}) ↔
      ∀ x : ℝ, {y | (x, y) ∈ S}.Subsingleton := by
  constructor
  · rintro ⟨f, hf⟩ x y₁ h₁ y₂ h₂
    have e₁ : (x, y₁) ∈ {p : ℝ × ℝ | p.1 ∈ Prod.fst '' S ∧ p.2 = f p.1} := hf ▸ h₁
    have e₂ : (x, y₂) ∈ {p : ℝ × ℝ | p.1 ∈ Prod.fst '' S ∧ p.2 = f p.1} := hf ▸ h₂
    exact e₁.2.trans e₂.2.symm
  · intro h
    classical
    let f : ℝ → ℝ := fun x => if hx : ∃ y, (x, y) ∈ S then hx.choose else 0
    have hfS : ∀ x y, (x, y) ∈ S → y = f x := by
      intro x y hy
      have hx : ∃ y, (x, y) ∈ S := ⟨y, hy⟩
      have : f x = hx.choose := dif_pos hx
      rw [this]
      exact h x hy hx.choose_spec
    refine ⟨f, ?_⟩
    ext ⟨x, y⟩
    constructor
    · intro hy
      exact ⟨⟨(x, y), hy, rfl⟩, hfS x y hy⟩
    · rintro ⟨⟨⟨x', y'⟩, hq, hx⟩, hy⟩
      have hx' : x' = x := hx
      subst hx'
      have := hfS x' y' hq
      have hyy : y = y' := hy.trans this.symm
      rw [hyy]
      exact hq

/-- OpenStax Calculus 1:§1.4 Horizontal Line Test (CA-026). A function is one-to-one exactly when every
horizontal line meets its graph at most once. -/
@[kb "openstaxcalculus2016" "1:§1.4 Rule: Horizontal Line Test, p. 74"]
theorem horizontal_line_test (f : ℝ → ℝ) :
    Function.Injective f ↔ ∀ y : ℝ, {x | (x, y) ∈ fnGraph f}.Subsingleton := by
  constructor
  · intro h y x₁ h₁ x₂ h₂
    exact h (h₁.symm.trans h₂)
  · intro h x₁ x₂ hx
    exact h (f x₁) (show (x₁, f x₁) ∈ fnGraph f from rfl) (show (x₂, f x₁) ∈ fnGraph f from hx)

/-- OpenStax Calculus 1:§1.4 Graphing Inverse Functions (CA-027). If `f` is one-to-one on `s`, the graph of
its inverse (the function `invFunOn f s` on `f '' s`) is the image of the graph of `f` (over `s`) under
the swap `(x, y) ↦ (y, x)`, the reflection across the line `y = x`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Graphing Inverse Functions, p. 77"]
theorem graph_inverse_eq_swap {f : ℝ → ℝ} {s : Set ℝ} (hf : InjOn f s) :
    {p : ℝ × ℝ | p.1 ∈ f '' s ∧ p.2 = Function.invFunOn f s p.1} =
      Prod.swap '' {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 = f p.1} := by
  have hne : ∀ a ∈ f '' s, Function.invFunOn f s a ∈ s ∧ f (Function.invFunOn f s a) = a :=
    fun a ha => ⟨Function.invFunOn_mem ha, Function.invFunOn_eq ha⟩
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb⟩
    dsimp only at ha hb
    obtain ⟨h1, h2⟩ := hne a ha
    refine ⟨(b, a), ⟨?_, ?_⟩, rfl⟩
    · show b ∈ s
      rw [hb]; exact h1
    · show a = f b
      rw [hb]; exact h2.symm
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, h⟩
    dsimp only at hx hy
    have hx' : y = a ∧ x = b := by simpa [Prod.swap] using h
    obtain ⟨rfl, rfl⟩ := hx'
    refine ⟨⟨x, hx, hy.symm⟩, ?_⟩
    show x = Function.invFunOn f s y
    rw [hy]; exact (hf.leftInvOn_invFunOn hx).symm

/-- OpenStax Calculus 1:§1.4 (CA-027). The swap `(x, y) ↦ (y, x)` fixes exactly the points of the line `y = x`. -/
@[kb "openstaxcalculus2016" "1:§1.4 Graphing Inverse Functions, p. 77"]
theorem swap_eq_self_iff (p : ℝ × ℝ) : Prod.swap p = p ↔ p.2 = p.1 := by
  obtain ⟨x, y⟩ := p
  simp [Prod.swap, eq_comm]

/-! ### Transformations of graphs (CA-015) -/

/-- OpenStax Calculus 1:§1.2 Transformations of Functions (CA-015): the graph of `f(x) + c` is the graph of
`f` shifted up by `c`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_add_const (f : ℝ → ℝ) (c : ℝ) :
    fnGraph (fun x => f x + c) = (fun p : ℝ × ℝ => (p.1, p.2 + c)) '' fnGraph f := by
  ext ⟨x, y⟩
  constructor
  · intro h
    exact ⟨(x, f x), rfl, by simp [show y = f x + c from h]⟩
  · rintro ⟨⟨x', y'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    show y' + c = f x' + c
    rw [show y' = f x' from h]

/-- OpenStax Calculus 1:§1.2 (CA-015): the graph of `f(x + c)` is the graph of `f` shifted left by `c`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_comp_add_const (f : ℝ → ℝ) (c : ℝ) :
    fnGraph (fun x => f (x + c)) = (fun p : ℝ × ℝ => (p.1 - c, p.2)) '' fnGraph f := by
  ext ⟨x, y⟩
  constructor
  · intro h
    exact ⟨(x + c, y), by simpa [fnGraph] using (show y = f (x + c) from h), by simp⟩
  · rintro ⟨⟨x', y'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    show y' = f (x' - c + c)
    rw [sub_add_cancel]; exact h

/-- OpenStax Calculus 1:§1.2 (CA-015): the graph of `a f(x)` is the graph of `f` stretched vertically by
the factor `a`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_const_mul (f : ℝ → ℝ) (a : ℝ) :
    fnGraph (fun x => a * f x) = (fun p : ℝ × ℝ => (p.1, a * p.2)) '' fnGraph f := by
  ext ⟨x, y⟩
  constructor
  · intro h
    exact ⟨(x, f x), rfl, by simp [show y = a * f x from h]⟩
  · rintro ⟨⟨x', y'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    show a * y' = a * f x'
    rw [show y' = f x' from h]

/-- OpenStax Calculus 1:§1.2 (CA-015): for `b ≠ 0`, the graph of `f(b x)` is the graph of `f` compressed
(or stretched) horizontally by the factor `1/b`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_comp_const_mul (f : ℝ → ℝ) {b : ℝ} (hb : b ≠ 0) :
    fnGraph (fun x => f (b * x)) = (fun p : ℝ × ℝ => (p.1 / b, p.2)) '' fnGraph f := by
  ext ⟨x, y⟩
  constructor
  · intro h
    refine ⟨(b * x, y), show y = f (b * x) from h, ?_⟩
    simp [mul_div_cancel_left₀ _ hb]
  · rintro ⟨⟨x', y'⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    show y' = f (b * (x' / b))
    rw [mul_div_cancel₀ _ hb]; exact h

/-- OpenStax Calculus 1:§1.2 (CA-015): the graph of `-f(x)` is the reflection of the graph of `f` in the
`x`-axis. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_neg (f : ℝ → ℝ) :
    fnGraph (fun x => -f x) = (fun p : ℝ × ℝ => (p.1, -p.2)) '' fnGraph f := by
  simpa using fnGraph_const_mul f (-1)

/-- OpenStax Calculus 1:§1.2 (CA-015): the graph of `f(-x)` is the reflection of the graph of `f` in the
`y`-axis. -/
@[kb "openstaxcalculus2016" "1:§1.2 Transformations of Functions, p. 53"]
theorem fnGraph_comp_neg (f : ℝ → ℝ) :
    fnGraph (fun x => f (-x)) = (fun p : ℝ × ℝ => (-p.1, p.2)) '' fnGraph f := by
  have := fnGraph_comp_const_mul f (b := -1) (by norm_num)
  simpa [div_neg] using this

/-! ### Equations of lines (CA-010) -/

/-- OpenStax Calculus 1:§1.2 equations of a line (CA-010): the point-slope form through a point
`(x₀, y₀)` of the line `y = m x + b` describes the same line as the slope-intercept form. -/
@[kb "openstaxcalculus2016" "1:§1.2 Definition (equations of a line), p. 40"]
theorem pointSlope_iff_slopeIntercept {m b x₀ y₀ : ℝ} (h : y₀ = m * x₀ + b) (x y : ℝ) :
    y - y₀ = m * (x - x₀) ↔ y = m * x + b := by
  subst h
  constructor <;> intro h <;> linarith

/-- OpenStax Calculus 1:§1.2 (CA-010): the standard form `a x + b y = c` with `b ≠ 0` is the line with slope
`-a/b` and intercept `c/b`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Definition (equations of a line), p. 40"]
theorem standardForm_iff_slopeIntercept {a b c : ℝ} (hb : b ≠ 0) (x y : ℝ) :
    a * x + b * y = c ↔ y = (-a / b) * x + c / b := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- OpenStax Calculus 1:§1.2 (CA-010): the standard form `a x + b y = c` with `b = 0`, `a ≠ 0` is the
vertical line `x = c/a`. -/
@[kb "openstaxcalculus2016" "1:§1.2 Definition (equations of a line), p. 40"]
theorem standardForm_vertical {a c : ℝ} (ha : a ≠ 0) (x y : ℝ) :
    a * x + 0 * y = c ↔ x = c / a := by
  rw [zero_mul, add_zero, eq_div_iff ha, mul_comm]

/-! ### Radian measure and arc length (CA-016) -/

/-- OpenStax Calculus 1:§1.3 radian measure (CA-016): the arc length cut on a circle of radius `r` by an
angle of `θ` radians is `r θ`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
def circleArcLength (r θ : ℝ) : ℝ := r * θ

/-- OpenStax Calculus 1:§1.3 (CA-016): the conversion of degrees to radians, `d° = d π / 180`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
noncomputable def radiansOfDegrees (d : ℝ) : ℝ := d * Real.pi / 180

/-- The conversion of radians to degrees, `θ = 180 θ / π`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
noncomputable def degreesOfRadians (θ : ℝ) : ℝ := θ * 180 / Real.pi

/-- OpenStax Calculus 1:§1.3 (CA-016): `180°` is `π` radians. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem radiansOfDegrees_180 : radiansOfDegrees 180 = Real.pi := by
  unfold radiansOfDegrees; ring

/-- OpenStax Calculus 1:§1.3 (CA-016): `360°` is `2π` radians, the angle of a full circle. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem radiansOfDegrees_360 : radiansOfDegrees 360 = 2 * Real.pi := by
  unfold radiansOfDegrees; ring

/-- OpenStax Calculus 1:§1.3 (CA-016): degrees to radians and back is the identity. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem degreesOfRadians_radiansOfDegrees (d : ℝ) : degreesOfRadians (radiansOfDegrees d) = d := by
  unfold degreesOfRadians radiansOfDegrees
  have := Real.pi_pos.ne'
  field_simp

/-- OpenStax Calculus 1:§1.3 (CA-016): a full turn cuts the whole circumference `2 π r`. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem circleArcLength_full_turn (r : ℝ) : circleArcLength r (2 * Real.pi) = 2 * Real.pi * r := by
  unfold circleArcLength; ring

/-- OpenStax Calculus 1:§1.3 (CA-016): the arc length is the fraction `θ / 2π` of the circumference. -/
@[kb "openstaxcalculus2016" "1:§1.3 Radian measure, p. 61"]
theorem circleArcLength_eq_fraction (r θ : ℝ) :
    circleArcLength r θ = θ / (2 * Real.pi) * (2 * Real.pi * r) := by
  unfold circleArcLength
  have := Real.pi_pos.ne'
  field_simp

end UndergradKB.Calculus
