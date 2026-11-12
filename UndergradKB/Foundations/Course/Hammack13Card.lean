import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 13 (limits and proofs in calculus)

Thin statements in the book's terms for the rows FO-259 to FO-287 classified `in Mathlib`.
Limits at a point `c` use the punctured neighbourhood filter `𝓝[≠] c`.
-/

open Filter Topology

namespace UndergradKB.Foundations.Course

/-- FO-259. Triangle inequality for real numbers, in the form with an intermediate point. -/
@[kb "hammack2018" "Theorem 13.1, p. 257"]
theorem hammack_thm_13_1_triangle (x y z : ℝ) : |x - y| ≤ |x - z| + |z - y| :=
  abs_sub_le x z y

/-- FO-260. Consequences of the triangle inequality. -/
@[kb "hammack2018" "Eq (13.1)-(13.3) §13.1, p. 257"]
theorem hammack_s13_1_triangle_consequences (x y : ℝ) :
    |x + y| ≤ |x| + |y| ∧ |x| - |y| ≤ |x + y| ∧ |x - y| ≤ |x| + |y| := by
  refine ⟨abs_add_le x y, ?_, abs_sub x y⟩
  have := abs_add_le (x + y) (-y)
  simp at this
  linarith

/-- FO-262. Epsilon-delta characterization of `lim_{x → c} f x = L`. -/
@[kb "hammack2018" "Definition 13.2, p. 259"]
theorem hammack_def_13_2_limit_eps_delta (f : ℝ → ℝ) (c L : ℝ) :
    Tendsto f (𝓝[≠] c) (𝓝 L) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - c| → |x - c| < δ → |f x - L| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  refine forall₂_congr fun ε hε => exists_congr fun δ => and_congr_right fun hδ => ?_
  constructor
  · intro h x h0 h1
    have := h (x := x) (fun h => by have : x = c := h; simp [this] at h0) (by simpa [Real.dist_eq] using h1)
    simpa [Real.dist_eq] using this
  · intro h x hx hd
    have hx' : x ≠ c := by simpa using hx
    have := h x (abs_pos.mpr (sub_ne_zero.mpr hx')) (by simpa [Real.dist_eq] using hd)
    simpa [Real.dist_eq] using this

/-- FO-267. Constant function rule for limits. -/
@[kb "hammack2018" "Theorem 13.2, p. 263"]
theorem hammack_thm_13_2_limit_const (a c : ℝ) :
    Tendsto (fun _ : ℝ => a) (𝓝[≠] c) (𝓝 a) :=
  tendsto_const_nhds

/-- FO-268. Identity function rule for limits. -/
@[kb "hammack2018" "Theorem 13.3, p. 263"]
theorem hammack_thm_13_3_limit_id (c : ℝ) : Tendsto (fun x : ℝ => x) (𝓝[≠] c) (𝓝 c) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

/-- FO-269. Constant multiple rule for limits. -/
@[kb "hammack2018" "Theorem 13.4, p. 264"]
theorem hammack_thm_13_4_limit_const_mul (f : ℝ → ℝ) (a c L : ℝ)
    (h : Tendsto f (𝓝[≠] c) (𝓝 L)) : Tendsto (fun x => a * f x) (𝓝[≠] c) (𝓝 (a * L)) :=
  h.const_mul a

/-- FO-270. Sum rule for limits. -/
@[kb "hammack2018" "Theorem 13.5, p. 264"]
theorem hammack_thm_13_5_limit_add (f g : ℝ → ℝ) (c L M : ℝ)
    (hf : Tendsto f (𝓝[≠] c) (𝓝 L)) (hg : Tendsto g (𝓝[≠] c) (𝓝 M)) :
    Tendsto (fun x => f x + g x) (𝓝[≠] c) (𝓝 (L + M)) :=
  hf.add hg

/-- FO-271. Difference rule for limits. -/
@[kb "hammack2018" "Theorem 13.6, p. 264"]
theorem hammack_thm_13_6_limit_sub (f g : ℝ → ℝ) (c L M : ℝ)
    (hf : Tendsto f (𝓝[≠] c) (𝓝 L)) (hg : Tendsto g (𝓝[≠] c) (𝓝 M)) :
    Tendsto (fun x => f x - g x) (𝓝[≠] c) (𝓝 (L - M)) :=
  hf.sub hg

/-- FO-272. Multiplication rule for limits. -/
@[kb "hammack2018" "Theorem 13.7, p. 265"]
theorem hammack_thm_13_7_limit_mul (f g : ℝ → ℝ) (c L M : ℝ)
    (hf : Tendsto f (𝓝[≠] c) (𝓝 L)) (hg : Tendsto g (𝓝[≠] c) (𝓝 M)) :
    Tendsto (fun x => f x * g x) (𝓝[≠] c) (𝓝 (L * M)) :=
  hf.mul hg

/-- FO-273. Division rule for limits, when the denominator's limit is nonzero. -/
@[kb "hammack2018" "Theorem 13.8, p. 265"]
theorem hammack_thm_13_8_limit_div (f g : ℝ → ℝ) (c L M : ℝ)
    (hf : Tendsto f (𝓝[≠] c) (𝓝 L)) (hg : Tendsto g (𝓝[≠] c) (𝓝 M)) (hM : M ≠ 0) :
    Tendsto (fun x => f x / g x) (𝓝[≠] c) (𝓝 (L / M)) :=
  hf.div hg hM

/-- FO-274. Continuity at `c` in epsilon-delta form. -/
@[kb "hammack2018" "Definition 13.3, p. 268"]
theorem hammack_def_13_3_continuousAt_eps_delta (f : ℝ → ℝ) (c : ℝ) :
    ContinuousAt f c ↔ ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - c| < δ → |f x - f c| < ε := by
  simp only [Metric.continuousAt_iff, Real.dist_eq]

/-- FO-275. Composition rule: if `g → L` and `f` is continuous at `L`, then `f ∘ g → f L`. -/
@[kb "hammack2018" "Theorem 13.9, p. 269"]
theorem hammack_thm_13_9_limit_comp (f g : ℝ → ℝ) (c L : ℝ)
    (hg : Tendsto g (𝓝[≠] c) (𝓝 L)) (hf : ContinuousAt f L) :
    Tendsto (fun x => f (g x)) (𝓝[≠] c) (𝓝 (f L)) :=
  hf.tendsto.comp hg

/-- FO-276. The derivative as the limit of difference quotients. -/
@[kb "hammack2018" "§13.5, p. 269"]
theorem hammack_s13_5_deriv_as_limit (f : ℝ → ℝ) (c f' : ℝ) :
    HasDerivAt f f' c ↔ Tendsto (fun x => (f x - f c) / (x - c)) (𝓝[≠] c) (𝓝 f') := by
  rw [hasDerivAt_iff_tendsto_slope]
  have : slope f c = fun x => (f x - f c) / (x - c) := by
    funext x
    simp [slope_def_field]
  rw [this]

/-- FO-277. A function differentiable at `c` is continuous at `c`. -/
@[kb "hammack2018" "Theorem 13.10, p. 269"]
theorem hammack_thm_13_10_differentiable_continuous (f : ℝ → ℝ) (c : ℝ)
    (h : DifferentiableAt ℝ f c) : ContinuousAt f c :=
  h.continuousAt

/-- FO-278. Limit at `+∞` in epsilon-`N` form. -/
@[kb "hammack2018" "Definition 13.4, p. 271"]
theorem hammack_def_13_4_limit_atTop (f : ℝ → ℝ) (L : ℝ) :
    Tendsto f atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℝ, ∀ x > N, |f x - L| < ε := by
  simp only [Metric.tendsto_atTop', Real.dist_eq]

/-- FO-278. Limit at `-∞` in epsilon-`N` form. -/
@[kb "hammack2018" "Definition 13.4, p. 271"]
theorem hammack_def_13_4_limit_atBot (f : ℝ → ℝ) (L : ℝ) :
    Tendsto f atBot (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℝ, ∀ x < N, |f x - L| < ε := by
  rw [Metric.tendsto_nhds]
  refine forall₂_congr fun ε hε => ?_
  rw [eventually_atBot]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N - 1, fun x hx => by simpa [Real.dist_eq] using hN x (by linarith)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N - 1, fun x hx => by simpa [Real.dist_eq] using hN x (by linarith)⟩

/-- FO-279. `f → ∞` as `x → ∞` means `f` eventually exceeds every bound. -/
@[kb "hammack2018" "§13.6, p. 272"]
theorem hammack_s13_6_limit_atTop_infinite (f : ℝ → ℝ) :
    Tendsto f atTop atTop ↔ ∀ b : ℝ, ∃ i : ℝ, ∀ a ≥ i, b ≤ f a :=
  tendsto_atTop_atTop

/-- FO-283. A sequence converges to `L` in epsilon-`N` form. -/
@[kb "hammack2018" "Definition 13.5, p. 274"]
theorem hammack_def_13_5_seq_converges (a : ℕ → ℝ) (L : ℝ) :
    Tendsto a atTop (𝓝 L) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n - L| < ε := by
  simp only [Metric.tendsto_atTop', Real.dist_eq]

/-- FO-284. A sequence diverges to `+∞`: it eventually exceeds every bound. -/
@[kb "hammack2018" "Definition 13.6, p. 276"]
theorem hammack_def_13_6_seq_diverges_to_infinity (a : ℕ → ℝ) :
    Tendsto a atTop atTop ↔ ∀ b : ℝ, ∃ N : ℕ, ∀ n ≥ N, b ≤ a n :=
  tendsto_atTop_atTop

/-- FO-287. If a series converges then its terms tend to zero. -/
@[kb "hammack2018" "Theorem 13.11, p. 279"]
theorem hammack_thm_13_11_series_terms_tendsto_zero (a : ℕ → ℝ) (h : Summable a) :
    Tendsto a atTop (𝓝 0) :=
  h.tendsto_atTop_zero

end UndergradKB.Foundations.Course
