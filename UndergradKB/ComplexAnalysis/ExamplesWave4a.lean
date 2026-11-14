import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.Common.Attr
import UndergradKB.ComplexAnalysis.Basics
import UndergradKB.ComplexAnalysis.Derivative
import UndergradKB.ComplexAnalysis.CauchyRiemann
import UndergradKB.ComplexAnalysis.Mobius
import UndergradKB.ComplexAnalysis.RiemannSphere
import UndergradKB.ComplexAnalysis.PathIntegral
import UndergradKB.ComplexAnalysis.PiecewisePath
import UndergradKB.ComplexAnalysis.Rectangle

/-!
# Worked examples and two definitions (Beck et al., Chapters 1 to 4)

Examples 1.4.17, 2.3.2, 2.3.3, 3.1.3, 3.1.6, 3.2.6, 3.2.7, 3.2.9, 4.1.2, 4.1.4, 4.2.6, 4.3.5, and
Definitions 4.2.1 and 4.3.6, stated in our own words on top of the existing library
(`mobius`, `mobiusExt`, `crossRatio`, `pathIntegral`, `rectPath`, `IsGHomotopic`, ...).
-/

open Set Metric Complex Filter Topology MeasureTheory intervalIntegral
open scoped Real ComplexConjugate

namespace UndergradKB.ComplexAnalysis

/-! ### Example 1.4.17 -/

/-- Example 1.4.17: the open unit disc is connected, and the punctured disc is open and
connected. -/
@[kb "beck2025" "Example 1.4.17, p. 25"]
theorem example_1_4_17 :
    IsConnected (ball (0 : ℂ) 1) ∧ IsConnected (ball (0 : ℂ) 1 \ {0}) ∧
      IsOpen (ball (0 : ℂ) 1 \ {0}) := by
  refine ⟨(convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩, ?_,
    isOpen_ball.sdiff isClosed_singleton⟩
  have hc : IsConnected (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :=
    isConnected_Ioo (by norm_num) |>.prod isConnected_univ
  have himg : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ioo (0 : ℝ) 1 ×ˢ univ)
      = ball (0 : ℂ) 1 \ {0} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      simp only [mem_Ioo] at hr
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr.1]
        exact hr.2
      · simp only [mem_singleton_iff, mul_eq_zero, Complex.ofReal_eq_zero, Complex.exp_ne_zero,
          or_false]
        exact hr.1.ne'
    · rintro ⟨hz, hz0⟩
      have hz0' : z ≠ 0 := hz0
      refine ⟨(‖z‖, arg z), ⟨?_, mem_univ _⟩, ?_⟩
      · rw [mem_ball, dist_zero_right] at hz
        exact ⟨norm_pos_iff.2 hz0', hz⟩
      · simp
  rw [← himg]
  exact hc.image _ (by fun_prop)

/-! ### Examples 2.3.2 and 2.3.3 -/

/-- Example 2.3.2: for `f z = z ^ 3`, the partial derivatives in `x` and `y` are
`3x² - 3y² + 6ixy` and `-6xy + 3ix² - 3iy²`; they satisfy `f_x = -i f_y` everywhere, and `f` is
entire. -/
@[kb "beck2025" "Example 2.3.2, p. 40"]
theorem example_2_3_2 :
    (∀ x y : ℝ,
      deriv (fun t : ℝ => (((t : ℂ) + y * I) ^ 3)) x
          = 3 * x ^ 2 - 3 * y ^ 2 + 6 * x * y * I ∧
      deriv (fun t : ℝ => (((x : ℂ) + t * I) ^ 3)) y
          = -6 * x * y + 3 * x ^ 2 * I - 3 * y ^ 2 * I ∧
      deriv (fun t : ℝ => (((t : ℂ) + y * I) ^ 3)) x
          = -I * deriv (fun t : ℝ => (((x : ℂ) + t * I) ^ 3)) y) ∧
    Differentiable ℂ (fun z : ℂ => z ^ 3) := by
  refine ⟨fun x y => ?_, fun z => (hasDerivAt_pow 3 z).differentiableAt⟩
  have h := hasDerivAt_pow 3 ((x : ℂ) + y * I)
  have hx := (hasDerivAt_horizontal (f := fun z : ℂ => z ^ 3) (x₀ := x) (y₀ := y) h).deriv
  have hy := (hasDerivAt_vertical (f := fun z : ℂ => z ^ 3) (x₀ := x) (y₀ := y) h).deriv
  simp only [Nat.cast_ofNat] at hx hy
  have e1 : 3 * ((x : ℂ) + y * I) ^ (3 - 1) = 3 * x ^ 2 - 3 * y ^ 2 + 6 * x * y * I := by
    simp only [show 3 - 1 = 2 from rfl]
    ring_nf
    rw [I_sq]; ring
  have e2 : I * (3 * ((x : ℂ) + y * I) ^ (3 - 1)) = -6 * x * y + 3 * x ^ 2 * I - 3 * y ^ 2 * I := by
    simp only [show 3 - 1 = 2 from rfl]
    ring_nf
    rw [I_sq]; ring_nf
    rw [show (I : ℂ) ^ 3 = I ^ 2 * I by ring, I_sq]; ring
  rw [hx, hy, e1.symm, e2.symm]
  refine ⟨rfl, rfl, ?_⟩
  rw [← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], one_mul]

/-- Example 2.3.3: for `f z = (conj z)^2`, the partial derivatives are `2x - 2iy` and `-2y - 2ix`;
the relation `f_x = -i f_y` holds exactly at `z = 0`, so `f` is not differentiable at any
`z ≠ 0`. -/
@[kb "beck2025" "Example 2.3.3, p. 40"]
theorem example_2_3_3 :
    (∀ x y : ℝ,
      deriv (fun t : ℝ => (conj ((t : ℂ) + y * I)) ^ 2) x = 2 * x - 2 * y * I ∧
      deriv (fun t : ℝ => (conj ((x : ℂ) + t * I)) ^ 2) y = -2 * y - 2 * x * I) ∧
    (∀ x y : ℝ,
      deriv (fun t : ℝ => (conj ((t : ℂ) + y * I)) ^ 2) x
          = -I * deriv (fun t : ℝ => (conj ((x : ℂ) + t * I)) ^ 2) y ↔ (x : ℂ) + y * I = 0) ∧
    (∀ z : ℂ, z ≠ 0 → ¬ DifferentiableAt ℂ (fun w : ℂ => (conj w) ^ 2) z) := by
  have key : ∀ x y : ℝ,
      deriv (fun t : ℝ => (conj ((t : ℂ) + y * I)) ^ 2) x = 2 * x - 2 * y * I ∧
      deriv (fun t : ℝ => (conj ((x : ℂ) + t * I)) ^ 2) y = -2 * y - 2 * x * I := by
    intro x y
    constructor
    · have h : HasDerivAt (fun t : ℝ => (conj ((t : ℂ) + y * I)) ^ 2) (2 * x - 2 * y * I) x := by
        have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) - y * I) 1 x := by
          simpa using (hasDerivAt_id x).ofReal_comp.sub_const ((y : ℂ) * I)
        have := h0.fun_pow 2
        have e : (fun t : ℝ => (conj ((t : ℂ) + y * I)) ^ 2) = fun t : ℝ => ((t : ℂ) - y * I) ^ 2 := by
          ext t; simp [sub_eq_add_neg]
        rw [e]
        convert this using 1
        push_cast; ring
      exact h.deriv
    · have h : HasDerivAt (fun t : ℝ => (conj ((x : ℂ) + t * I)) ^ 2) (-2 * y - 2 * x * I) y := by
        have h0 : HasDerivAt (fun t : ℝ => (x : ℂ) - t * I) (-I) y := by
          simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_sub (x : ℂ)
        have := h0.fun_pow 2
        have e : (fun t : ℝ => (conj ((x : ℂ) + t * I)) ^ 2) = fun t : ℝ => ((x : ℂ) - t * I) ^ 2 := by
          ext t; simp [sub_eq_add_neg]
        rw [e]
        convert this using 1
        push_cast
        ring_nf
        rw [I_sq]; ring
      exact h.deriv
  refine ⟨key, fun x y => ?_, fun z hz => conj_sq_not_differentiableAt hz⟩
  rw [(key x y).1, (key x y).2]
  have e : -I * (-2 * (y : ℂ) - 2 * x * I) = 2 * y * I - 2 * x := by
    ring_nf; rw [I_sq]; ring
  rw [e]
  constructor
  · intro h
    have h1 : (4 : ℂ) * ((x : ℂ) - y * I) = 0 := by linear_combination h
    have h2 : (x : ℂ) - y * I = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · norm_num at h
      · exact h
    have hre := congrArg Complex.re h2
    have him := congrArg Complex.im h2
    simp at hre him
    subst hre; subst him
    simp
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    subst hre; subst him
    simp

/-! ### Möbius examples 3.1.3, 3.1.6, 3.2.6, 3.2.7, 3.2.9

The running example is `f z = (z - 1) / (i z + i) = mobius 1 (-1) I I z`. -/

/-- Example 3.1.3: `f z = (z - 1)/(i z + i)` is a Möbius map (nonzero determinant) with domain
`ℂ \ {-1}`; its inverse is `w ↦ (i w + 1)/(-i w + 1)` with domain `ℂ \ {-i}`: the two compositions
are the identity on the respective domains and each lands in the domain of the other. -/
@[kb "beck2025" "Example 3.1.3, p. 49"]
theorem example_3_1_3 :
    (1 : ℂ) * I - (-1) * I ≠ 0 ∧
    (∀ z : ℂ, z ≠ -1 →
      mobius 1 (-1) I I z ≠ -I ∧
      mobius I 1 (-I) 1 (mobius 1 (-1) I I z) = z) ∧
    (∀ w : ℂ, w ≠ -I →
      mobius I 1 (-I) 1 w ≠ -1 ∧
      mobius 1 (-1) I I (mobius I 1 (-I) 1 w) = w) := by
  have hdet : (1 : ℂ) * I - (-1) * I ≠ 0 := by
    intro h
    have : (2 : ℂ) * I = 0 := by linear_combination h
    simp at this
  refine ⟨hdet, fun z hz => ?_, fun w hw => ?_⟩
  · have hz' : I * z + I ≠ 0 := by
      intro h
      apply hz
      have : I * (z + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h I_ne_zero
      · linear_combination h
    have := mobius_inv_mobius (a := 1) (b := -1) (c := I) (d := I) (z := z) hdet hz'
    refine ⟨fun h => this.1 ?_, by simpa [neg_neg] using this.2⟩
    rw [h]
    linear_combination I_sq
  · have hw' : -I * w + 1 ≠ 0 := by
      intro h
      apply hw
      linear_combination I * h + w * I_sq
    have := mobius_mobius_inv (a := 1) (b := -1) (c := I) (d := I) (w := w) hdet hw'
    simp only [neg_neg] at this
    refine ⟨fun h => this.1 ?_, this.2⟩
    rw [h]
    ring

/-- Example 3.1.6: for `e^{iφ} ≠ -1`, `f(e^{iφ}) = 2 sin φ / |e^{iφ} + 1|²`, a real number; hence
`f` maps the unit circle (minus `-1`) into the real line. -/
@[kb "beck2025" "Example 3.1.6, p. 50"]
theorem example_3_1_6 :
    (∀ φ : ℝ, exp (φ * I) ≠ -1 →
      mobius 1 (-1) I I (exp (φ * I)) = ((2 * Real.sin φ / ‖exp (φ * I) + 1‖ ^ 2 : ℝ) : ℂ)) ∧
    (∀ z : ℂ, ‖z‖ = 1 → z ≠ -1 → (mobius 1 (-1) I I z).im = 0) := by
  have main : ∀ φ : ℝ, exp (φ * I) ≠ -1 →
      mobius 1 (-1) I I (exp (φ * I)) = ((2 * Real.sin φ / ‖exp (φ * I) + 1‖ ^ 2 : ℝ) : ℂ) := by
    intro φ hφ
    have hz : exp (φ * I) = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * I := by
      rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hN : ‖exp (φ * I) + 1‖ ^ 2 = 2 + 2 * Real.cos φ := by
      rw [Complex.sq_norm, Complex.normSq_apply, hz]
      simp only [add_re, add_im, ofReal_re, mul_re, mul_im, ofReal_im, I_re, I_im, one_re, one_im]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    have hne : ‖exp (φ * I) + 1‖ ≠ 0 := by
      intro h
      apply hφ
      exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 h)
    have hpos : 2 + 2 * Real.cos φ ≠ 0 := by
      rw [← hN]; exact pow_ne_zero 2 hne
    have hden : I * exp (φ * I) + I ≠ 0 := by
      intro h
      apply hφ
      have : I * (exp (φ * I) + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h I_ne_zero
      · linear_combination h
    unfold mobius
    rw [hN, div_eq_iff (by simpa using hden), hz]
    have hpos' : (2 + 2 * (Real.cos φ : ℂ)) ≠ 0 := by exact_mod_cast hpos
    have hsc : (Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2 = 1 := by exact_mod_cast Real.sin_sq_add_cos_sq φ
    simp only [ofReal_div, ofReal_mul, ofReal_add, ofReal_ofNat]
    generalize (Real.cos φ : ℂ) = c at *
    generalize (Real.sin φ : ℂ) = s at *
    have h1c : 1 + c ≠ 0 := fun h => hpos' (by linear_combination 2 * h)
    field_simp
    linear_combination hsc - s ^ 2 * I_sq
  refine ⟨main, fun z hz hz1 => ?_⟩
  have hzz : z = exp ((arg z : ℝ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this
    simpa using this.symm
  rw [hzz] at hz1 ⊢
  rw [main _ hz1]
  exact Complex.ofReal_im _

/-- Example 3.2.6: the extension of `f z = (z - 1)/(i z + i)` to the extended plane `ℂ ∪ {∞}` sends
`-1` to `∞` and `∞` to `-i`, and is a bijection. -/
@[kb "beck2025" "Example 3.2.6, p. 52"]
theorem example_3_2_6 :
    mobiusExt 1 (-1) I I ((-1 : ℂ) : OnePoint ℂ) = OnePoint.infty ∧
    mobiusExt 1 (-1) I I OnePoint.infty = ((-I : ℂ) : OnePoint ℂ) ∧
    Function.Bijective (mobiusExt 1 (-1) I I) := by
  have hdet : (1 : ℂ) * I - (-1) * I ≠ 0 := (example_3_1_3).1
  have h := mobiusExt_pole (a := 1) (b := -1) (c := I) (d := I) I_ne_zero
  have e1 : (-I / I : ℂ) = -1 := by field_simp
  have e2 : (1 / I : ℂ) = -I := by simp
  rw [e1] at h
  rw [e2] at h
  exact ⟨h.1, h.2, mobiusExt_bijective hdet⟩

/-- Example 3.2.7: on the extended plane `f` sends `1 ↦ 0`, `i ↦ 1` and `-1 ↦ ∞`. -/
@[kb "beck2025" "Example 3.2.7, p. 53"]
theorem example_3_2_7 :
    mobiusExt 1 (-1) I I ((1 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
    mobiusExt 1 (-1) I I ((I : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) ∧
    mobiusExt 1 (-1) I I ((-1 : ℂ) : OnePoint ℂ) = OnePoint.infty := by
  have hI1 : I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  refine ⟨?_, ?_, example_3_2_6.1⟩
  · have hd : I * 1 + I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
    rw [mobiusExt_coe hd]
    simp [mobius]
  · have hd : I * I + I ≠ 0 := by
      rw [I_mul_I]; simpa [neg_add_eq_sub] using hI1
    rw [mobiusExt_coe hd]
    have : mobius 1 (-1) I I I = 1 := by
      unfold mobius
      rw [div_eq_one_iff_eq hd, I_mul_I]
      ring
    rw [this]

/-- Example 3.2.9: `f z = (z - 1)/(i z + i)` equals the cross ratio `[z, 1, i, -1]` for every
finite `z`, and at `∞` the cross ratio with the two terms in `∞` cancelled is `(i + 1)/(i - 1)`,
which equals `-i = f(∞)`. -/
@[kb "beck2025" "Example 3.2.9, p. 53"]
theorem example_3_2_9 :
    (∀ z : ℂ, mobius 1 (-1) I I z = crossRatio z 1 I (-1)) ∧
    (I - (-1)) / (I - 1) = (-I : ℂ) := by
  have hI1 : I - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hI2 : I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hval : (I + 1) / (I - 1) = (-I : ℂ) := by
    rw [div_eq_iff hI1]
    linear_combination I_sq
  refine ⟨fun z => ?_, by simpa using hval⟩
  unfold mobius crossRatio
  by_cases hz : z + 1 = 0
  · have : I * z + I = 0 := by linear_combination I * hz
    simp [this, show z - -1 = 0 by simpa using hz]
  · have hz' : I * z + I ≠ 0 := by
      intro h
      apply hz
      have : I * (z + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h I_ne_zero
      · exact h
    have hz2 : z - -1 ≠ 0 := by simpa using hz
    field_simp
    linear_combination (1 - z ^ 2) * I_sq

/-! ### Chapter 4: the paths of Example 4.1.2 -/

/-- The segment from `0` to `1 + i`, `t ↦ t + i t`. -/
def ex412Line (t : ℝ) : ℂ := (t : ℂ) + t * I

/-- The arc of the parabola `y = x²` from `0` to `1 + i`, `t ↦ t + i t²`. -/
def ex412Parabola (t : ℝ) : ℂ := (t : ℂ) + (t : ℂ) ^ 2 * I

/-- The horizontal then vertical segment from `0` through `1` to `1 + i`. -/
noncomputable def ex412Corner : ℝ → ℂ := pathConcat (fun t : ℝ => (t : ℂ)) (fun t : ℝ => 1 + (t : ℂ) * I)

lemma hasDerivAt_ofReal_id (t : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := ofRealCLM.hasDerivAt

lemma hasDerivAt_ex412Line (t : ℝ) : HasDerivAt ex412Line (1 + I) t := by
  have := (hasDerivAt_ofReal_id t).fun_add ((hasDerivAt_ofReal_id t).mul_const I)
  rw [one_mul] at this
  exact this

lemma hasDerivAt_ex412Parabola (t : ℝ) : HasDerivAt ex412Parabola (1 + 2 * t * I) t := by
  have := (hasDerivAt_ofReal_id t).fun_add (((hasDerivAt_ofReal_id t).fun_pow 2).mul_const I)
  convert this using 1
  · rfl
  · norm_num

lemma hasDerivAt_seg2 (t : ℝ) : HasDerivAt (fun x : ℝ => 1 + (x : ℂ) * I) I t := by
  have := ((hasDerivAt_ofReal_id t).mul_const I).const_add 1
  rw [one_mul] at this
  exact this

lemma isC1On_of_hasDerivAt {γ γ' : ℝ → ℂ} (hd : ∀ t, HasDerivAt γ (γ' t) t) (hc : Continuous γ')
    (a b : ℝ) : IsC1On γ a b := by
  refine ⟨fun t _ => (hd t).differentiableAt, ?_⟩
  rw [show deriv γ = γ' from funext fun t => (hd t).deriv]
  exact hc.continuousOn

lemma isPiecewiseSmooth_ex412Line : IsPiecewiseSmooth ex412Line 0 1 :=
  (isC1On_of_hasDerivAt hasDerivAt_ex412Line continuous_const 0 1).isPiecewiseSmooth zero_le_one

lemma isPiecewiseSmooth_ex412Parabola : IsPiecewiseSmooth ex412Parabola 0 1 :=
  (isC1On_of_hasDerivAt hasDerivAt_ex412Parabola (by fun_prop) 0 1).isPiecewiseSmooth zero_le_one

lemma isPiecewiseSmooth_seg1 : IsPiecewiseSmooth (fun t : ℝ => (t : ℂ)) 0 1 :=
  (isC1On_of_hasDerivAt (γ' := fun _ => 1) hasDerivAt_ofReal_id continuous_const 0 1
    ).isPiecewiseSmooth zero_le_one

lemma isPiecewiseSmooth_seg2 : IsPiecewiseSmooth (fun t : ℝ => 1 + (t : ℂ) * I) 0 1 :=
  (isC1On_of_hasDerivAt (γ' := fun _ => I) hasDerivAt_seg2 continuous_const 0 1
    ).isPiecewiseSmooth zero_le_one

lemma isPiecewiseSmooth_ex412Corner : IsPiecewiseSmooth ex412Corner 0 1 :=
  isPiecewiseSmooth_seg1.pathConcat isPiecewiseSmooth_seg2 (by simp)

/-- If `f (γ t) γ'(t) = g t` with `g` continuous and having primitive `G`, then
`∫_γ f = G 1 - G 0`. -/
lemma pathIntegral_eq_of_antideriv {f : ℂ → ℂ} {γ γ' g G : ℝ → ℂ}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hg : ∀ t, f (γ t) * γ' t = g t) (hgc : Continuous g)
    (hG : ∀ t, HasDerivAt G (g t) t) : pathIntegral f γ 0 1 = G 1 - G 0 := by
  unfold pathIntegral
  have : ∀ t, f (γ t) * deriv γ t = g t := fun t => by rw [(hγ t).deriv, hg]
  simp_rw [this]
  exact integral_eq_sub_of_hasDerivAt (fun t _ => hG t) (hgc.intervalIntegrable _ _)

lemma I_pow_three' : (I : ℂ) ^ 3 = -I := by rw [pow_succ, I_sq]; ring
lemma I_pow_four' : (I : ℂ) ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
lemma I_pow_five' : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four', one_mul]

/-- Example 4.1.2: the integral of `f z = (conj z)^2` over three paths from `0` to `1 + i`:
over the segment `t + it`, it equals `(2/3)(1 - i)`; over the parabola arc `t + i t²`, it equals
`14/15 - i/3`; over the corner path `0 → 1 → 1 + i`, it equals `4/3 + (2/3) i`. -/
@[kb "beck2025" "Example 4.1.2, p. 71"]
theorem example_4_1_2 :
    pathIntegral (fun z : ℂ => (conj z) ^ 2) ex412Line 0 1 = (2 / 3) * (1 - I) ∧
    pathIntegral (fun z : ℂ => (conj z) ^ 2) ex412Parabola 0 1 = 14 / 15 - I / 3 ∧
    pathIntegral (fun z : ℂ => (conj z) ^ 2) ex412Corner 0 1 = 4 / 3 + (2 / 3) * I := by
  have hf : Continuous (fun z : ℂ => (conj z) ^ 2) := by fun_prop
  have hI2 := I_sq
  have hI3 := I_pow_three'
  have hI4 := I_pow_four'
  refine ⟨?_, ?_, ?_⟩
  · rw [pathIntegral_eq_of_antideriv (γ' := fun _ => 1 + I)
      (g := fun t => (2 - 2 * I) * (t : ℂ) ^ 2)
      (G := fun t => ((2 - 2 * I) / 3) * (t : ℂ) ^ 3) hasDerivAt_ex412Line
      (fun t => ?_) (by fun_prop) (fun t => ?_)]
    · simp; ring
    · simp only [ex412Line, map_add, map_mul, conj_ofReal, conj_I]
      ring_nf
      simp only [hI2, hI3]
      ring
    · have := ((hasDerivAt_ofReal_id t).fun_pow 3).const_mul ((2 - 2 * I) / 3)
      convert this using 1
      simp; ring
  · rw [pathIntegral_eq_of_antideriv (γ' := fun t => 1 + 2 * (t : ℂ) * I)
      (g := fun t => (t : ℂ) ^ 2 + 3 * (t : ℂ) ^ 4 - 2 * I * (t : ℂ) ^ 5)
      (G := fun t => (t : ℂ) ^ 3 / 3 + 3 * (t : ℂ) ^ 5 / 5 - I * (t : ℂ) ^ 6 / 3)
      hasDerivAt_ex412Parabola (fun t => ?_) (by fun_prop) (fun t => ?_)]
    · simp; ring_nf
    · simp only [ex412Parabola, map_add, map_mul, map_pow, conj_ofReal, conj_I]
      ring_nf
      simp only [hI2, hI3]
      ring
    · have h3 := (((hasDerivAt_ofReal_id t).fun_pow 3).div_const 3)
      have h5 := (((hasDerivAt_ofReal_id t).fun_pow 5).const_mul 3).div_const 5
      have h6 := (((hasDerivAt_ofReal_id t).fun_pow 6).const_mul I).div_const 3
      have := (h3.add h5).sub h6
      convert this using 1
      simp; ring
  · have e1 : pathIntegral (fun z : ℂ => (conj z) ^ 2) (fun t : ℝ => (t : ℂ)) 0 1 = 1 / 3 := by
      rw [pathIntegral_eq_of_antideriv (γ' := fun _ => 1) (g := fun t => (t : ℂ) ^ 2)
        (G := fun t => (t : ℂ) ^ 3 / 3) hasDerivAt_ofReal_id (fun t => ?_) (by fun_prop)
        (fun t => ?_)]
      · simp
      · simp
      · have := ((hasDerivAt_ofReal_id t).fun_pow 3).div_const 3
        convert this using 1
        simp
    have e2 : pathIntegral (fun z : ℂ => (conj z) ^ 2) (fun t : ℝ => 1 + (t : ℂ) * I) 0 1
        = 1 + (2 / 3) * I := by
      rw [pathIntegral_eq_of_antideriv (γ' := fun _ => I)
        (g := fun t => I * (1 - 2 * I * (t : ℂ) - (t : ℂ) ^ 2))
        (G := fun t => I * ((t : ℂ) - I * (t : ℂ) ^ 2 - (t : ℂ) ^ 3 / 3)) hasDerivAt_seg2
        (fun t => ?_) (by fun_prop) (fun t => ?_)]
      · simp; ring_nf; simp only [hI2]; ring
      · simp only [map_add, map_mul, map_one, conj_ofReal, conj_I]
        ring_nf
        simp only [hI2, hI3]
        ring
      · have h1 := (hasDerivAt_ofReal_id t).mul_const I
        have h2 := ((hasDerivAt_ofReal_id t).fun_pow 2).const_mul I
        have h3 := ((hasDerivAt_ofReal_id t).fun_pow 3).div_const 3
        have := (((hasDerivAt_ofReal_id t).sub h2).sub h3).const_mul I
        convert this using 1
        simp; ring
    unfold ex412Corner
    rw [pathIntegral_pathConcat isPiecewiseSmooth_seg1 isPiecewiseSmooth_seg2 (by simp)
      (hf.continuousOn) (hf.continuousOn), e1, e2]
    ring

/-- Example 4.1.4: two parametrisations of the unit circle, `e^{it}` on `[0, 2π]` and
`e^{2πi sin t}` on `[0, π/2]`, give the same integral of any function continuous on the circle. -/
@[kb "beck2025" "Example 4.1.4, p. 72"]
theorem example_4_1_4 {f : ℂ → ℂ} (hf : ContinuousOn f (sphere (0 : ℂ) 1)) :
    pathIntegral f (fun t : ℝ => exp ((t : ℂ) * I)) 0 (2 * π) =
      pathIntegral f (fun t : ℝ => exp (2 * π * I * (Real.sin t : ℝ))) 0 (π / 2) := by
  have hγ : (fun t : ℝ => exp ((t : ℂ) * I)) = circleMap 0 1 := by
    ext t; simp [circleMap]
  have hσ : (fun t : ℝ => exp (2 * π * I * (Real.sin t : ℝ))) =
      circleMap 0 1 ∘ (fun t : ℝ => 2 * π * Real.sin t) := by
    ext t
    simp only [Function.comp, circleMap, zero_add, ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  rw [hσ, hγ]
  symm
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  refine pathIntegral_comp (isC1On_circleMap 0 1 0 (2 * π)) ?_ (σ := fun t : ℝ => 2 * π * Real.sin t)
    (fun t _ => (by fun_prop : Differentiable ℝ fun t : ℝ => 2 * π * Real.sin t) t) ?_ ?_ ?_ ?_
  · refine hf.mono ?_
    rintro _ ⟨t, -, rfl⟩
    exact circleMap_mem_sphere 0 one_pos.le t
  · exact (by fun_prop : Continuous fun t : ℝ => deriv (fun t : ℝ => 2 * π * Real.sin t) t).continuousOn
  · intro t ht
    rw [uIcc_of_le hpi] at ht
    rw [uIcc_of_le (by positivity)]
    have h0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have h1 := Real.sin_le_one t
    constructor <;> nlinarith [Real.pi_pos]
  · simp
  · simp

/-- Example 4.2.6: since `z ↦ z²/2` is an antiderivative of `z ↦ z`, the integral of `z` over each
of the three paths of Example 4.1.2 (segment, parabola, corner) is `((1 + i)² - 0)/2 = i`. -/
@[kb "beck2025" "Example 4.2.6, p. 75"]
theorem example_4_2_6 :
    pathIntegral (fun z : ℂ => z) ex412Line 0 1 = I ∧
    pathIntegral (fun z : ℂ => z) ex412Parabola 0 1 = I ∧
    pathIntegral (fun z : ℂ => z) ex412Corner 0 1 = I := by
  have hF : ∀ z ∈ (univ : Set ℂ), HasDerivAt (fun w : ℂ => w ^ 2 / 2) ((fun z : ℂ => z) z) z := by
    intro z _
    simpa using (hasDerivAt_pow 2 z).div_const 2
  have hc : ContinuousOn (fun z : ℂ => z) univ := continuousOn_id
  have key : ∀ {γ : ℝ → ℂ}, IsPiecewiseSmooth γ 0 1 → γ 0 = 0 → γ 1 = 1 + I →
      pathIntegral (fun z : ℂ => z) γ 0 1 = I := by
    intro γ hγ h0 h1
    rw [pathIntegral_eq_sub_of_isPiecewiseSmooth hγ zero_le_one (fun _ _ => mem_univ _) hF hc, h0, h1]
    simp only [zero_pow two_ne_zero, zero_div, sub_zero]
    ring_nf
    rw [I_sq]
    ring
  refine ⟨key isPiecewiseSmooth_ex412Line (by simp [ex412Line]) (by simp [ex412Line]),
    key isPiecewiseSmooth_ex412Parabola (by simp [ex412Parabola]) (by simp [ex412Parabola]),
    key isPiecewiseSmooth_ex412Corner ?_ ?_⟩
  · unfold ex412Corner
    rw [pathConcat_of_le (by norm_num)]
    simp
  · unfold ex412Corner
    rw [pathConcat_of_lt (by norm_num)]
    norm_num

/-- Example 4.3.5: the integral of `1/z` over the counterclockwise square with corners
`±1 ± i` is `2πi`; this follows from the homotopy to a circle in the plane punctured at `0`, in the
form of the integral formula for `1/(z - w)` along a positively oriented simple closed path with
`w` inside. -/
@[kb "beck2025" "Example 4.3.5, p. 78"]
theorem example_4_3_5 :
    pathIntegral (fun z : ℂ => 1 / z) (rectPath (-1) 1 (-1) 1) 0 1 = 2 * π * I := by
  have hγ := isPositivelyOrientedSimpleClosed_rectPath (x₀ := -1) (x₁ := 1) (y₀ := -1) (y₁ := 1)
    (by norm_num) (by norm_num)
  have hw : (0 : ℂ) ∈ insideOf (rectPath (-1) 1 (-1) 1) := by
    rw [insideOf_rectPath (by norm_num) (by norm_num)]
    simp only [mem_reProdIm, mem_Ioo]
    norm_num
  simpa [one_div] using hγ.pathIntegral_inv_sub hw

/-! ### Definitions 4.2.1 and 4.3.6 -/

/-- Definition 4.2.1: `F` is an antiderivative (primitive) of `f` on the set `G`: `F` is
holomorphic on `G` and `F' = f` at every point of `G`. -/
@[kb "beck2025" "Definition 4.2.1, p. 75"]
def IsAntiderivativeOn (F f : ℂ → ℂ) (G : Set ℂ) : Prop :=
  DifferentiableOn ℂ F G ∧ ∀ z ∈ G, deriv F z = f z

/-- For an open set `G` (a region), being an antiderivative on `G` is the same as having complex
derivative `f z` at each point `z` of `G`; for such `F` the fundamental theorem of path integrals
applies (`pathIntegral_eq_sub_of_isPiecewiseSmooth`). -/
@[kb "beck2025" "Definition 4.2.1, p. 75"]
theorem isAntiderivativeOn_iff {F f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) :
    IsAntiderivativeOn F f G ↔ ∀ z ∈ G, HasDerivAt F (f z) z := by
  constructor
  · rintro ⟨hd, hf⟩ z hz
    have := (hd z hz).differentiableAt (hG.mem_nhds hz)
    rw [← hf z hz]
    exact this.hasDerivAt
  · intro h
    exact ⟨fun z hz => (h z hz).differentiableAt.differentiableWithinAt, fun z hz => (h z hz).deriv⟩

/-- Definition 4.3.6: the closed path `γ` is `G`-contractible, i.e. `G`-homotopic to a constant
path. -/
@[kb "beck2025" "Definition 4.3.6, p. 80"]
def IsGContractible (G : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ∃ c : ℂ, IsGHomotopic G γ (fun _ => c)

/-- A constant path at a point of `G` is `G`-contractible (sanity check of the definition), and
for a holomorphic `f` on an open `G` a `G`-contractible piecewise smooth closed path has integral
zero (Corollary 4.3.8). -/
@[kb "beck2025" "Definition 4.3.6, p. 80"]
theorem isGContractible_const {G : Set ℂ} {c : ℂ} (hc : c ∈ G) :
    IsGContractible G (fun _ => c) :=
  ⟨c, fun _ _ => c, continuousOn_const, fun _ _ _ _ => hc, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

end UndergradKB.ComplexAnalysis
