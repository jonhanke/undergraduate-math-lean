import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Field.Basic
import UndergradKB.Common.Attr

/-!
# Function arithmetic, monotonicity and graph transformations (Stitz–Zeager, Chapter 1)

Graphs are `Set.graphOn f D`; a transformation of the graph is the image of the graph of `f`
under a map of the plane `ℝ × ℝ`.
-/

namespace UndergradKB.Precalculus

open UndergradKB

/-! ### Function arithmetic (PC-018) -/

/-- The graphs of the sum, difference, product and quotient of two functions: they are defined on
the common domain (for the quotient, only where the denominator is nonzero) with the pointwise
values (PC-018). -/
@[kb "stitzzeager2013" "§1.5, p. 88"]
theorem function_arith_graph (f g : ℝ → ℝ) (Df Dg : Set ℝ) (x y : ℝ) :
    ((x, y) ∈ Set.graphOn (fun t => f t + g t) (Df ∩ Dg) ↔ x ∈ Df ∧ x ∈ Dg ∧ y = f x + g x) ∧
    ((x, y) ∈ Set.graphOn (fun t => f t - g t) (Df ∩ Dg) ↔ x ∈ Df ∧ x ∈ Dg ∧ y = f x - g x) ∧
    ((x, y) ∈ Set.graphOn (fun t => f t * g t) (Df ∩ Dg) ↔ x ∈ Df ∧ x ∈ Dg ∧ y = f x * g x) ∧
    ((x, y) ∈ Set.graphOn (fun t => f t / g t) (Df ∩ Dg ∩ {t | g t ≠ 0}) ↔
      x ∈ Df ∧ x ∈ Dg ∧ g x ≠ 0 ∧ y = f x / g x) := by
  simp only [Set.mem_graphOn, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3.symm⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3.symm⟩
  · rintro ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩; exact ⟨h1, h2, h4, h3.symm⟩
  · rintro ⟨h1, h2, h4, h3⟩; exact ⟨⟨⟨h1, h2⟩, h4⟩, h3.symm⟩

/-! ### Difference quotient (PC-019) -/

/-- The difference quotient of `f` at `x` with increment `h`. -/
noncomputable def diffQuot (f : ℝ → ℝ) (x h : ℝ) : ℝ := (f (x + h) - f x) / h

/-- The difference quotient is the slope of the secant line through `x` and `x + h` (PC-019). -/
@[kb "stitzzeager2013" "Definition 1.8, p. 91"]
theorem diffQuot_eq_slope (f : ℝ → ℝ) (x h : ℝ) : diffQuot f x h = slope f x (x + h) := by
  rw [slope_def_field, diffQuot, add_sub_cancel_left]

/-! ### Increasing, decreasing, constant (PC-025) -/

/-- `f` is constant on `I`: any two points of `I` have the same value. -/
def ConstantOn (f : ℝ → ℝ) (I : Set ℝ) : Prop := ∀ a ∈ I, ∀ b ∈ I, f a = f b

/-- Increasing, decreasing and constant on a set `I`, in the book's form (PC-025). -/
@[kb "stitzzeager2013" "Definition 1.10, p. 113"]
theorem increasing_decreasing_constant_on (f : ℝ → ℝ) (I : Set ℝ) :
    (StrictMonoOn f I ↔ ∀ a ∈ I, ∀ b ∈ I, a < b → f a < f b) ∧
    (StrictAntiOn f I ↔ ∀ a ∈ I, ∀ b ∈ I, a < b → f b < f a) ∧
    (ConstantOn f I ↔ ∀ a ∈ I, ∀ b ∈ I, a < b → f a = f b) := by
  refine ⟨Iff.rfl, Iff.rfl, ⟨fun h a ha b hb _ => h a ha b hb, fun h a ha b hb => ?_⟩⟩
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact h a ha b hb hab
  · rfl
  · exact (h b hb a ha hab).symm

/-! ### Transformations of graphs (PC-027 .. PC-032) -/

/-- Vertical shift: the graph of `x ↦ f x + k` (any real `k`, so `k < 0` shifts down) is the graph
of `f` moved up by `k` (PC-027). -/
@[kb "stitzzeager2013" "Theorem 1.2, p. 133"]
theorem graph_vertical_shift (f : ℝ → ℝ) (D : Set ℝ) (k : ℝ) :
    Set.graphOn (fun x => f x + k) D = (fun p : ℝ × ℝ => (p.1, p.2 + k)) '' Set.graphOn f D := by
  ext ⟨x, y⟩
  simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, rfl⟩; exact ⟨x, f x, ⟨hx, rfl⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨ha, rfl⟩, rfl, rfl⟩; exact ⟨ha, rfl⟩

/-- Horizontal shift: the graph of `x ↦ f (x + h)` (any real `h`, so `h < 0` shifts right) is the
graph of `f` moved left by `h`; its domain is `{x | x + h ∈ D}` (PC-028). -/
@[kb "stitzzeager2013" "Theorem 1.3, p. 135"]
theorem graph_horizontal_shift (f : ℝ → ℝ) (D : Set ℝ) (h : ℝ) :
    Set.graphOn (fun x => f (x + h)) {x | x + h ∈ D} =
      (fun p : ℝ × ℝ => (p.1 - h, p.2)) '' Set.graphOn f D := by
  ext ⟨x, y⟩
  simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, rfl⟩; exact ⟨x + h, f (x + h), ⟨hx, rfl⟩, by ring, rfl⟩
  · rintro ⟨a, b, ⟨ha, rfl⟩, rfl, rfl⟩; simpa using ha

/-- Reflections: the graph of `-f` is the reflection of the graph of `f` in the x-axis, and the
graph of `x ↦ f (-x)` is its reflection in the y-axis (domain `{x | -x ∈ D}`) (PC-029). -/
@[kb "stitzzeager2013" "Theorem 1.4, p. 138"]
theorem graph_reflections (f : ℝ → ℝ) (D : Set ℝ) :
    Set.graphOn (fun x => -f x) D = (fun p : ℝ × ℝ => (p.1, -p.2)) '' Set.graphOn f D ∧
    Set.graphOn (fun x => f (-x)) {x | -x ∈ D} =
      (fun p : ℝ × ℝ => (-p.1, p.2)) '' Set.graphOn f D := by
  constructor
  · ext ⟨x, y⟩
    simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨x, f x, ⟨hx, rfl⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨ha, rfl⟩, rfl, rfl⟩; exact ⟨ha, rfl⟩
  · ext ⟨x, y⟩
    simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨-x, f (-x), ⟨hx, rfl⟩, by ring, rfl⟩
    · rintro ⟨a, b, ⟨ha, rfl⟩, rfl, rfl⟩; simpa using ha

/-- Vertical scaling: for `a > 0` the graph of `a • f` is the graph of `f` with every
`y`-coordinate multiplied by `a` (PC-030). -/
@[kb "stitzzeager2013" "Theorem 1.5, p. 142"]
theorem graph_vertical_scale (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ) (_ha : 0 < a) :
    Set.graphOn (fun x => a * f x) D = (fun p : ℝ × ℝ => (p.1, a * p.2)) '' Set.graphOn f D := by
  ext ⟨x, y⟩
  simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, rfl⟩; exact ⟨x, f x, ⟨hx, rfl⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨ha, rfl⟩, rfl, rfl⟩; exact ⟨ha, rfl⟩

/-- Horizontal scaling: for `b > 0` the graph of `x ↦ f (b x)` (domain `{x | b x ∈ D}`) is the
graph of `f` with every `x`-coordinate divided by `b` (PC-031). -/
@[kb "stitzzeager2013" "Theorem 1.6, p. 144"]
theorem graph_horizontal_scale (f : ℝ → ℝ) (D : Set ℝ) (b : ℝ) (hb : 0 < b) :
    Set.graphOn (fun x => f (b * x)) {x | b * x ∈ D} =
      (fun p : ℝ × ℝ => (p.1 / b, p.2)) '' Set.graphOn f D := by
  have hb' : b ≠ 0 := hb.ne'
  ext ⟨x, y⟩
  simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, rfl⟩; exact ⟨b * x, f (b * x), ⟨hx, rfl⟩, by field_simp, rfl⟩
  · rintro ⟨a, c, ⟨ha, rfl⟩, rfl, rfl⟩
    have : b * (a / b) = a := by field_simp
    simpa [this] using ha

/-- The four steps of the general transformation, as plane maps: shift left by `H`, divide the
`x`-coordinate by `B`, multiply the `y`-coordinate by `A`, shift up by `K`. -/
theorem transformation_steps_comp (A B H K : ℝ) :
    ((fun p : ℝ × ℝ => (p.1, p.2 + K)) ∘ (fun p : ℝ × ℝ => (p.1, A * p.2)) ∘
      (fun p : ℝ × ℝ => (p.1 / B, p.2)) ∘ (fun p : ℝ × ℝ => (p.1 - H, p.2))) =
    fun p : ℝ × ℝ => ((p.1 - H) / B, A * p.2 + K) := rfl

/-- General transformation: for `B ≠ 0`, the graph of `x ↦ A f(B x + H) + K` (domain
`{x | B x + H ∈ D}`) is the image of the graph of `f` under
`(x, y) ↦ ((x - H) / B, A y + K)`, i.e. shift horizontally by `H`, scale horizontally by `B`,
scale vertically by `A`, then shift vertically by `K` (PC-032). -/
@[kb "stitzzeager2013" "Theorem 1.7, p. 147"]
theorem graph_general_transformation (f : ℝ → ℝ) (D : Set ℝ) (A B H K : ℝ) (hB : B ≠ 0) :
    Set.graphOn (fun x => A * f (B * x + H) + K) {x | B * x + H ∈ D} =
      (fun p : ℝ × ℝ => ((p.1 - H) / B, A * p.2 + K)) '' Set.graphOn f D := by
  ext ⟨x, y⟩
  simp only [Set.mem_graphOn, Set.mem_image, Prod.exists, Prod.mk.injEq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨B * x + H, f (B * x + H), ⟨hx, rfl⟩, by field_simp; ring, rfl⟩
  · rintro ⟨a, c, ⟨ha, rfl⟩, rfl, rfl⟩
    have : B * ((a - H) / B) + H = a := by field_simp; ring
    simpa [this] using ha

end UndergradKB.Precalculus
