import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Order.Field
import UndergradKB.Common.Attr

/-! # The secant method (Corral §6.2)

To solve `f x = 0`, the secant method starts from two approximations `x₀, x₁` (in the book, the ends of an
interval where `f` changes sign) and replaces the curve by the secant line through `(xₙ₋₂, f xₙ₋₂)` and
`(xₙ₋₁, f xₙ₋₁)`; the next approximation is where that line meets the `x`-axis:
`xₙ = xₙ₋₁ - (xₙ₋₁ - xₙ₋₂) f(xₙ₋₁) / (f(xₙ₋₁) - f(xₙ₋₂))`.

* `secantStep`, `secantSeq`: the step and the sequence;
* `secantLine_secantStep`: the step is the zero of the secant line;
* `secantStep_affine`: for a nonconstant linear function one step gives the exact root;
* `secantSeq_limit_root`: if the sequence converges (and never divides by zero), its limit is a root, for any
  Lipschitz `f` (for instance any continuously differentiable function on an interval containing the
  sequence). The book states the method without a convergence theorem; this is the theorem that justifies
  using the limit.
-/

namespace UndergradKB.Trigonometry

open Filter Topology

/-- One step of the secant method from the two last approximations `x` (newest) and `y`. -/
noncomputable def secantStep (f : ℝ → ℝ) (x y : ℝ) : ℝ := x - (x - y) * f x / (f x - f y)

/-- The secant sequence started at `x₀`, `x₁`. -/
noncomputable def secantSeq (f : ℝ → ℝ) (x₀ x₁ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | 1 => x₁
  | n + 2 => secantStep f (secantSeq f x₀ x₁ (n + 1)) (secantSeq f x₀ x₁ n)

theorem secantSeq_add_two (f : ℝ → ℝ) (x₀ x₁ : ℝ) (n : ℕ) :
    secantSeq f x₀ x₁ (n + 2) = secantStep f (secantSeq f x₀ x₁ (n + 1)) (secantSeq f x₀ x₁ n) := rfl

/-- **The secant step is the `x`-intercept of the secant line** through `(y, f y)` and `(x, f x)`
(`x ≠ y`, `f x ≠ f y`). (TR-170) -/
@[kb "corraltrig" "Box §6.2 (secant method), p. 142"]
theorem secantLine_secantStep (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) (hf : f x ≠ f y) :
    f x + (f x - f y) / (x - y) * (secantStep f x y - x) = 0 := by
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : f x - f y ≠ 0 := sub_ne_zero.2 hf
  rw [secantStep]
  field_simp
  ring

/-- For a nonconstant linear function `f t = m t + q` the secant method finds the root `-q/m` in one step.
(TR-170) -/
theorem secantStep_affine {m q x y : ℝ} (hm : m ≠ 0) (hxy : x ≠ y) :
    secantStep (fun t => m * t + q) x y = -q / m := by
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  rw [secantStep, show m * x + q - (m * y + q) = m * (x - y) by ring]
  field_simp
  ring

/-- **The limit of the secant method is a root**: if `f` is Lipschitz, the secant sequence never divides by
zero (`f xₙ₊₁ ≠ f xₙ`) and converges to `L`, then `f L = 0`. (TR-170) -/
@[kb "corraltrig" "D032 (secant method), p. 142"]
theorem secantSeq_limit_root {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) {x₀ x₁ L : ℝ}
    (hne : ∀ n, f (secantSeq f x₀ x₁ (n + 1)) ≠ f (secantSeq f x₀ x₁ n))
    (hL : Tendsto (secantSeq f x₀ x₁) atTop (𝓝 L)) : f L = 0 := by
  set s := secantSeq f x₀ x₁ with hs
  -- the steps tend to zero
  have hstep : Tendsto (fun n => s (n + 2) - s (n + 1)) atTop (𝓝 0) := by
    have h2 := hL.comp (tendsto_add_atTop_nat 2)
    have h1 := hL.comp (tendsto_add_atTop_nat 1)
    simpa using h2.sub h1
  -- the values `f (s (n + 1))` are bounded by `K` times the next step
  have hbound : ∀ n, |f (s (n + 1))| ≤ K * |s (n + 2) - s (n + 1)| := by
    intro n
    have hd : f (s (n + 1)) - f (s n) ≠ 0 := sub_ne_zero.2 (hne n)
    have hxy : s (n + 1) ≠ s n := fun h => hne n (by rw [h])
    have hx : s (n + 1) - s n ≠ 0 := sub_ne_zero.2 hxy
    have hrec : s (n + 2) - s (n + 1) = -((s (n + 1) - s n) * f (s (n + 1)) / (f (s (n + 1)) - f (s n))) := by
      rw [hs, secantSeq_add_two, secantStep]; ring
    have hlip : |f (s (n + 1)) - f (s n)| ≤ K * |s (n + 1) - s n| := by
      have := hf.dist_le_mul (s (n + 1)) (s n)
      simpa [Real.dist_eq] using this
    have key : |f (s (n + 1))| * |f (s (n + 1)) - f (s n)| =
        |s (n + 2) - s (n + 1)| * |f (s (n + 1)) - f (s n)| * (|f (s (n + 1)) - f (s n)| / |s (n + 1) - s n|) := by
      rw [hrec, abs_neg, abs_div, abs_mul]
      have : |s (n + 1) - s n| ≠ 0 := abs_ne_zero.2 hx
      have : |f (s (n + 1)) - f (s n)| ≠ 0 := abs_ne_zero.2 hd
      field_simp
    have hpos : 0 < |f (s (n + 1)) - f (s n)| := abs_pos.2 hd
    have hxpos : 0 < |s (n + 1) - s n| := abs_pos.2 hx
    have hq : |f (s (n + 1)) - f (s n)| / |s (n + 1) - s n| ≤ K := by
      rw [div_le_iff₀ hxpos]; exact hlip
    have := mul_right_cancel₀ hpos.ne' (key.trans (by ring : _ = |s (n + 2) - s (n + 1)| *
      (|f (s (n + 1)) - f (s n)| / |s (n + 1) - s n|) * |f (s (n + 1)) - f (s n)|))
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  -- so `f (s (n + 1)) → 0`
  have hzero : Tendsto (fun n => f (s (n + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hK : Tendsto (fun n => (K : ℝ) * |s (n + 2) - s (n + 1)|) atTop (𝓝 0) := by
      simpa using (hstep.abs).const_mul (K : ℝ)
    exact squeeze_zero (fun n => abs_nonneg _) hbound hK
  -- and `f (s (n + 1)) → f L` by continuity
  have hlim : Tendsto (fun n => f (s (n + 1))) atTop (𝓝 (f L)) :=
    (hf.continuous.tendsto L).comp (hL.comp (tendsto_add_atTop_nat 1))
  exact tendsto_nhds_unique hlim hzero

end UndergradKB.Trigonometry
