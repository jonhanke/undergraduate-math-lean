import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Common.Attr
import UndergradKB.Precalculus.RationalExponents

/-! # Course layer, Chapter 1 (Stitz-Zeager): Exercises 1.6.74 and 1.6.75 (wave 8)

The book asks for the extrema and the intervals of monotonicity "with a graphing calculator" and prints rounded
values. Here the critical points are located in intervals of half a unit of the last printed digit (as zeros of the
derivative, by the intermediate value theorem), and the extrema and monotonicity are proved from the sign of the
derivative. The helper lemmas (a cubic with three distinct real zeros factors; strict monotonicity on both sides gives
a local extremum) are stated for reuse. -/

namespace UndergradKB.Precalculus.Course

open Set Filter Topology UndergradKB.Precalculus

/-- A real cubic `a x³ + b x² + c x + d` with three distinct zeros `r, s, t` is `a (x - r)(x - s)(x - t)`. -/
lemma cubic_eq_mul_of_three_roots {a b c d r s t : ℝ} (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : a * r ^ 3 + b * r ^ 2 + c * r + d = 0) (hs : a * s ^ 3 + b * s ^ 2 + c * s + d = 0)
    (ht : a * t ^ 3 + b * t ^ 2 + c * t + d = 0) (x : ℝ) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = a * (x - r) * (x - s) * (x - t) := by
  have hA : a * (r ^ 2 + r * s + s ^ 2) + b * (r + s) + c = 0 := by
    have : (r - s) * (a * (r ^ 2 + r * s + s ^ 2) + b * (r + s) + c) = 0 := by
      linear_combination hr - hs
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hrs)
  have hB : a * (r ^ 2 + r * t + t ^ 2) + b * (r + t) + c = 0 := by
    have : (r - t) * (a * (r ^ 2 + r * t + t ^ 2) + b * (r + t) + c) = 0 := by
      linear_combination hr - ht
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hrt)
  have hS : a * (r + s + t) + b = 0 := by
    have : (s - t) * (a * (r + s + t) + b) = 0 := by linear_combination hA - hB
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hst)
  have hb : b = -a * (r + s + t) := by linear_combination hS
  have hc : c = a * (r * s + r * t + s * t) := by linear_combination hA - (r + s) * hS
  have hd : d = -a * (r * s * t) := by
    linear_combination hr - r ^ 2 * hS - r * (hA - (r + s) * hS)
  subst hb hc hd
  ring

/-- Strictly decreasing up to `c` and strictly increasing after it, on a neighbourhood: a local minimum. -/
lemma isLocalMin_of_strictAntiOn_strictMonoOn {f : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (h₁ : StrictAntiOn f (Icc a c)) (h₂ : StrictMonoOn f (Icc c b)) : IsLocalMin f c := by
  have hmem : Icc a b ∈ 𝓝 c := Icc_mem_nhds hac hcb
  filter_upwards [hmem] with x hx
  rcases le_total x c with hxc | hxc
  · exact h₁.antitoneOn ⟨hx.1, hxc⟩ ⟨hac.le, le_rfl⟩ hxc
  · exact h₂.monotoneOn ⟨le_rfl, hcb.le⟩ ⟨hxc, hx.2⟩ hxc

/-- Strictly increasing up to `c` and strictly decreasing after it, on a neighbourhood: a local maximum. -/
lemma isLocalMax_of_strictMonoOn_strictAntiOn {f : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (h₁ : StrictMonoOn f (Icc a c)) (h₂ : StrictAntiOn f (Icc c b)) : IsLocalMax f c := by
  have hmem : Icc a b ∈ 𝓝 c := Icc_mem_nhds hac hcb
  filter_upwards [hmem] with x hx
  rcases le_total x c with hxc | hxc
  · exact h₁.monotoneOn ⟨hx.1, hxc⟩ ⟨hac.le, le_rfl⟩ hxc
  · exact h₂.antitoneOn ⟨le_rfl, hcb.le⟩ ⟨hxc, hx.2⟩ hxc

/-! ## Exercise 1.6.74 -/

/-- The function of Exercise 1.6.74. -/
private noncomputable def f174 (x : ℝ) : ℝ := x ^ 4 - 3 * x ^ 3 - 24 * x ^ 2 + 28 * x + 48

private lemma f174_cont : Continuous f174 := by unfold f174; fun_prop

private lemma f174_deriv (x : ℝ) : deriv f174 x = 4 * x ^ 3 - 9 * x ^ 2 - 48 * x + 28 := by
  have h : HasDerivAt f174 (4 * x ^ 3 - 3 * (3 * x ^ 2) - 24 * (2 * x) + 28) x := by
    have h4 := hasDerivAt_pow 4 x
    have h3 := (hasDerivAt_pow 3 x).const_mul 3
    have h2 := (hasDerivAt_pow 2 x).const_mul 24
    have h1 := (hasDerivAt_id x).const_mul 28
    have := (((h4.sub h3).sub h2).add h1).add_const 48
    convert this using 1
    · ext y; simp [f174]
    · push_cast; ring
  rw [h.deriv]; ring

/-- Stitz-Zeager Exercise 1.6.74: for `f(x) = x⁴ - 3x³ - 24x² + 28x + 48` there is no absolute maximum; there are
critical points `c₁ ≈ -2.84`, `c₂ ≈ 0.54`, `c₃ ≈ 4.55` with `f c₁ ≈ -91.32` (local minimum), `f c₂ ≈ 55.73`
(local maximum) and `f c₃ ≈ -175.46` (local and absolute minimum); `f` decreases on `(-∞, c₁]` and `[c₂, c₃]` and
increases on `[c₁, c₂]` and `[c₃, ∞)`. Each rounded value lies within half a unit of its last printed digit. -/
@[kb "stitzzeager2013" "Exercise 1.6.74, p. 121"]
theorem exer_1_6_74 :
    let f : ℝ → ℝ := fun x => x ^ 4 - 3 * x ^ 3 - 24 * x ^ 2 + 28 * x + 48
    (∀ M : ℝ, ∃ x, M < f x) ∧
    ∃ c₁ c₂ c₃ : ℝ, c₁ ∈ Ioo (-2.845) (-2.835) ∧ c₂ ∈ Ioo 0.535 0.545 ∧ c₃ ∈ Ioo 4.545 4.555 ∧
      f c₁ ∈ Ioo (-91.325) (-91.315) ∧ f c₂ ∈ Ioo 55.725 55.735 ∧ f c₃ ∈ Ioo (-175.465) (-175.455) ∧
      IsLocalMin f c₁ ∧ IsLocalMax f c₂ ∧ IsLocalMin f c₃ ∧ IsMinOn f univ c₃ ∧
      StrictAntiOn f (Iic c₁) ∧ StrictMonoOn f (Icc c₁ c₂) ∧ StrictAntiOn f (Icc c₂ c₃) ∧
      StrictMonoOn f (Ici c₃) := by
  intro f
  have hf : f = f174 := rfl
  rw [hf]
  set d : ℝ → ℝ := fun x => 4 * x ^ 3 - 9 * x ^ 2 - 48 * x + 28 with hd
  have dcont : Continuous d := by rw [hd]; fun_prop
  -- the three zeros of the derivative, in tight intervals
  obtain ⟨c₁, hc₁, hd₁⟩ : ∃ c ∈ Ioo (-2.8411 : ℝ) (-2.841), d c = 0 :=
    intermediate_value_Ioo (by norm_num) dcont.continuousOn ⟨by norm_num [hd], by norm_num [hd]⟩
  obtain ⟨c₂, hc₂, hd₂⟩ : ∃ c ∈ Ioo (0.5415 : ℝ) 0.5416, d c = 0 :=
    intermediate_value_Ioo' (by norm_num) dcont.continuousOn ⟨by norm_num [hd], by norm_num [hd]⟩
  obtain ⟨c₃, hc₃, hd₃⟩ : ∃ c ∈ Ioo (4.5494 : ℝ) 4.5495, d c = 0 :=
    intermediate_value_Ioo (by norm_num) dcont.continuousOn ⟨by norm_num [hd], by norm_num [hd]⟩
  have hfac : ∀ x, d x = 4 * (x - c₁) * (x - c₂) * (x - c₃) := by
    intro x
    have := cubic_eq_mul_of_three_roots (a := 4) (b := -9) (c := -48) (d := 28) (r := c₁) (s := c₂) (t := c₃) (x := x)
      (by linarith [hc₁.2, hc₂.1]) (by linarith [hc₁.2, hc₃.1]) (by linarith [hc₂.2, hc₃.1])
      (by simp only [hd] at hd₁; linarith) (by simp only [hd] at hd₂; linarith)
      (by simp only [hd] at hd₃; linarith)
    simp only [hd]; linarith
  have hder : ∀ x, deriv f174 x = 4 * (x - c₁) * (x - c₂) * (x - c₃) := fun x => by
    rw [f174_deriv, ← hfac x]
  have h12 : c₁ < c₂ := by linarith [hc₁.2, hc₂.1]
  have h23 : c₂ < c₃ := by linarith [hc₂.2, hc₃.1]
  have m1 : StrictAntiOn f174 (Iic c₁) := by
    refine strictAntiOn_of_deriv_neg (convex_Iic c₁) f174_cont.continuousOn fun x hx => ?_
    rw [interior_Iic] at hx
    have hx : x < c₁ := hx
    rw [hder]
    have : 0 < (c₁ - x) * (c₂ - x) * (c₃ - x) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith
    nlinarith
  have m2 : StrictMonoOn f174 (Icc c₁ c₂) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc c₁ c₂) f174_cont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [hder]
    have : 0 < (x - c₁) * (c₂ - x) * (c₃ - x) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith [hx.1, hx.2]
    nlinarith
  have m3 : StrictAntiOn f174 (Icc c₂ c₃) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc c₂ c₃) f174_cont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [hder]
    have : 0 < (x - c₁) * (x - c₂) * (c₃ - x) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith [hx.1, hx.2]
    nlinarith
  have m4 : StrictMonoOn f174 (Ici c₃) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici c₃) f174_cont.continuousOn fun x hx => ?_
    rw [interior_Ici] at hx
    have hx : c₃ < x := hx
    rw [hder]
    have : 0 < (x - c₁) * (x - c₂) * (x - c₃) := by
      apply mul_pos (mul_pos _ _) _ <;> linarith
    nlinarith
  -- values at the critical points
  have v1 : f174 c₁ ∈ Ioo (-91.325) (-91.315) := by
    obtain ⟨h1, h2⟩ := hc₁
    unfold f174
    constructor <;> nlinarith [mul_pos (by linarith : (0:ℝ) < c₁ + 2.8411) (by linarith : (0:ℝ) < -2.841 - c₁)]
  have v2 : f174 c₂ ∈ Ioo 55.725 55.735 := by
    obtain ⟨h1, h2⟩ := hc₂
    unfold f174
    constructor <;> nlinarith [mul_pos (by linarith : (0:ℝ) < c₂ - 0.5415) (by linarith : (0:ℝ) < 0.5416 - c₂)]
  have v3 : f174 c₃ ∈ Ioo (-175.465) (-175.455) := by
    obtain ⟨h1, h2⟩ := hc₃
    unfold f174
    constructor <;> nlinarith [mul_pos (by linarith : (0:ℝ) < c₃ - 4.5494) (by linarith : (0:ℝ) < 4.5495 - c₃)]
  refine ⟨fun M => ?_, c₁, c₂, c₃, ⟨by linarith [hc₁.1], by linarith [hc₁.2]⟩,
    ⟨by linarith [hc₂.1], by linarith [hc₂.2]⟩, ⟨by linarith [hc₃.1], by linarith [hc₃.2]⟩, v1, v2, v3,
    ?_, ?_, ?_, ?_, m1, m2, m3, m4⟩
  · -- unbounded above
    refine ⟨|M| + 10, ?_⟩
    have hM := le_abs_self M
    have h0 := abs_nonneg M
    unfold f174
    set y := |M| + 10 with hy
    have hy10 : 10 ≤ y := by linarith
    nlinarith [mul_le_mul hy10 hy10 (by norm_num) (by linarith), pow_le_pow_left₀ (by norm_num) hy10 3]
  · exact isLocalMin_of_strictAntiOn_strictMonoOn (a := c₁ - 1) (by linarith) h12
      (m1.mono fun x hx => hx.2) m2
  · exact isLocalMax_of_strictMonoOn_strictAntiOn (a := c₁) h12 h23 m2 m3
  · exact isLocalMin_of_strictAntiOn_strictMonoOn (b := c₃ + 1) h23 (by linarith) m3
      (m4.mono fun x hx => hx.1)
  · intro x _
    show f174 c₃ ≤ f174 x
    rcases le_total x c₁ with h | h
    · have := m1.antitoneOn (show x ∈ Iic c₁ from h) (Set.mem_Iic.2 le_rfl) h
      linarith [v1.1, v3.2]
    rcases le_total x c₂ with h' | h'
    · have := m2.monotoneOn ⟨le_rfl, h12.le⟩ ⟨h, h'⟩ h
      linarith [v1.1, v3.2]
    rcases le_total x c₃ with h'' | h''
    · exact m3.antitoneOn ⟨h', h''⟩ ⟨h23.le, le_rfl⟩ h''
    · exact m4.monotoneOn (Set.mem_Ici.2 le_rfl) (show x ∈ Ici c₃ from h'') h''

/-! ## Exercise 1.6.75 -/

private lemma cbrt_pow3 (x : ℝ) : principalRoot 3 x ^ 3 = x :=
  principalRoot_pow (by norm_num) (Or.inl (by decide))

private lemma cbrt_strictMono : StrictMono (principalRoot 3) := by
  intro x y hxy
  by_contra h
  push Not at h
  have := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).monotone h
  simp only [cbrt_pow3] at this
  linarith

private lemma cbrt_zero : principalRoot 3 0 = 0 := by
  have := cbrt_pow3 0
  exact pow_eq_zero_iff (by norm_num) |>.mp this

/-- `t ↦ t⁵ - 4t²`: the function of Exercise 1.6.75 in the variable `t = ∛x`. -/
private noncomputable def h175 (t : ℝ) : ℝ := t ^ 5 - 4 * t ^ 2

private lemma h175_cont : Continuous h175 := by unfold h175; fun_prop

private lemma h175_deriv (t : ℝ) : deriv h175 t = 5 * t ^ 4 - 8 * t := by
  have h : HasDerivAt h175 (5 * t ^ 4 - 4 * (2 * t)) t := by
    have h5 := hasDerivAt_pow 5 t
    have h2 := (hasDerivAt_pow 2 t).const_mul 4
    convert h5.sub h2 using 1
    · ext y; simp [h175]
    · push_cast; ring
  rw [h.deriv]; ring

private lemma f175_eq (x : ℝ) : bookRatPow x 2 3 * (x - 4) = h175 (principalRoot 3 x) := by
  unfold bookRatPow h175
  simp only [zpow_ofNat]
  linear_combination (-(principalRoot 3 x ^ 2)) * cbrt_pow3 x

/-- Stitz-Zeager Exercise 1.6.75: `f(x) = x^(2/3) (x - 4)` (the book's rational power: the square of the real cube
root) has no absolute maximum and no absolute minimum, a local maximum `f 0 = 0`, a local minimum at `x = 8/5`
(printed `1.60`) with value `≈ -3.28`; it increases on `(-∞, 0]` and `[8/5, ∞)` and decreases on `[0, 8/5]`. -/
@[kb "stitzzeager2013" "Exercise 1.6.75, p. 121"]
theorem exer_1_6_75 :
    let f : ℝ → ℝ := fun x => bookRatPow x 2 3 * (x - 4)
    (∀ M : ℝ, ∃ x, M < f x) ∧ (∀ M : ℝ, ∃ x, f x < M) ∧ f 0 = 0 ∧ IsLocalMax f 0 ∧
      IsLocalMin f (8 / 5) ∧ f (8 / 5) ∈ Ioo (-3.285) (-3.275) ∧
      StrictMonoOn f (Iic 0) ∧ StrictAntiOn f (Icc 0 (8 / 5)) ∧ StrictMonoOn f (Ici (8 / 5)) := by
  intro f
  have hf : ∀ x, f x = h175 (principalRoot 3 x) := f175_eq
  set t₀ := principalRoot 3 (8 / 5) with ht₀
  have ht₀3 : t₀ ^ 3 = 8 / 5 := cbrt_pow3 _
  have ht₀pos : 0 < t₀ := by
    have := cbrt_strictMono (show (0 : ℝ) < 8 / 5 by norm_num)
    rwa [cbrt_zero] at this
  have hder : ∀ t, deriv h175 t = 5 * t * (t - t₀) * (t ^ 2 + t * t₀ + t₀ ^ 2) := fun t => by
    rw [h175_deriv]; linear_combination (5 * t) * ht₀3
  have hq : ∀ t, 0 < t ^ 2 + t * t₀ + t₀ ^ 2 := fun t => by nlinarith [sq_nonneg (2 * t + t₀)]
  have k1 : StrictMonoOn h175 (Iic 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic 0) h175_cont.continuousOn fun t ht => ?_
    rw [interior_Iic] at ht
    have ht : t < 0 := ht
    rw [hder]
    have := hq t
    have : 0 < (-t) * (t₀ - t) := mul_pos (by linarith) (by linarith)
    nlinarith
  have k2 : StrictAntiOn h175 (Icc 0 t₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 t₀) h175_cont.continuousOn fun t ht => ?_
    rw [interior_Icc] at ht
    rw [hder]
    have := hq t
    have : 0 < t * (t₀ - t) := mul_pos (by linarith [ht.1]) (by linarith [ht.2])
    nlinarith
  have k3 : StrictMonoOn h175 (Ici t₀) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici t₀) h175_cont.continuousOn fun t ht => ?_
    rw [interior_Ici] at ht
    have ht : t₀ < t := ht
    rw [hder]
    have := hq t
    have : 0 < t * (t - t₀) := mul_pos (by linarith) (by linarith)
    nlinarith
  have r0 := cbrt_zero
  have rm := cbrt_strictMono
  have m1 : StrictMonoOn f (Iic 0) := by
    intro x hx y hy hxy
    rw [hf, hf]
    refine k1 ?_ ?_ (rm hxy)
    · show principalRoot 3 x ≤ 0; rw [← r0]; exact rm.monotone hx
    · show principalRoot 3 y ≤ 0; rw [← r0]; exact rm.monotone hy
  have m2 : StrictAntiOn f (Icc 0 (8 / 5)) := by
    intro x hx y hy hxy
    rw [hf, hf]
    refine k2 ⟨?_, ?_⟩ ⟨?_, ?_⟩ (rm hxy)
    · rw [← r0]; exact rm.monotone hx.1
    · exact rm.monotone hx.2
    · rw [← r0]; exact rm.monotone hy.1
    · exact rm.monotone hy.2
  have m3 : StrictMonoOn f (Ici (8 / 5)) := by
    intro x hx y hy hxy
    rw [hf, hf]
    exact k3 (rm.monotone hx) (rm.monotone hy) (rm hxy)
  have hval : f (8 / 5) = t₀ ^ 2 * (8 / 5 - 4) := by
    show bookRatPow (8 / 5) 2 3 * (8 / 5 - 4) = _
    simp [bookRatPow, ht₀]
  -- bounds on `t₀ = ∛(8/5)`: `1.1696 < t₀ < 1.1697`
  have tlo : 1.1696 < t₀ := by
    by_contra h; push Not at h
    nlinarith [pow_le_pow_left₀ ht₀pos.le h 3]
  have thi : t₀ < 1.1697 := by
    by_contra h; push Not at h
    nlinarith [pow_le_pow_left₀ (by norm_num) h 3]
  refine ⟨fun M => ?_, fun M => ?_, ?_, ?_, ?_, ?_, m1, m2, m3⟩
  · -- for `x ≥ 1`, `∛x ≥ 1`, so `f x ≥ x - 4`
    refine ⟨|M| + 5, ?_⟩
    have hx1 : (1 : ℝ) ≤ |M| + 5 := by linarith [abs_nonneg M]
    have hr1 : 1 ≤ principalRoot 3 (|M| + 5) := by
      have := rm.monotone hx1
      rwa [show principalRoot 3 1 = 1 from
        (principalRoot_unique (by norm_num) (Or.inl (by decide)) (Or.inl (by decide)) (by norm_num)).symm] at this
    show M < bookRatPow (|M| + 5) 2 3 * (|M| + 5 - 4)
    simp only [bookRatPow, zpow_ofNat]
    have h2 : 1 ≤ principalRoot 3 (|M| + 5) ^ 2 := one_le_pow₀ hr1
    have := mul_le_mul_of_nonneg_right h2 (by linarith [abs_nonneg M] : (0 : ℝ) ≤ |M| + 5 - 4)
    linarith [le_abs_self M]
  · -- for `x ≤ -1`, `∛x ≤ -1`, so `f x ≤ x - 4`
    refine ⟨-|M| - 1, ?_⟩
    have hx1 : -|M| - 1 ≤ (-1 : ℝ) := by linarith [abs_nonneg M]
    have hr1 : principalRoot 3 (-|M| - 1) ≤ -1 := by
      have := rm.monotone hx1
      rwa [show principalRoot 3 (-1) = -1 from
        (principalRoot_unique (by norm_num) (Or.inl (by decide)) (Or.inl (by decide)) (by norm_num)).symm] at this
    show bookRatPow (-|M| - 1) 2 3 * (-|M| - 1 - 4) < M
    simp only [bookRatPow, zpow_ofNat]
    have h2 : 1 ≤ principalRoot 3 (-|M| - 1) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonpos_right h2 (by linarith [abs_nonneg M] : -|M| - 1 - 4 ≤ (0 : ℝ))
    linarith [neg_abs_le M]
  · show bookRatPow 0 2 3 * (0 - 4) = 0
    simp [bookRatPow, r0]
  · exact isLocalMax_of_strictMonoOn_strictAntiOn (a := -1) (b := 8 / 5) (by norm_num) (by norm_num)
      (m1.mono fun x hx => hx.2) m2
  · exact isLocalMin_of_strictAntiOn_strictMonoOn (a := 0) (b := 3) (by norm_num) (by norm_num) m2
      (m3.mono fun x hx => hx.1)
  · rw [hval]
    constructor <;> nlinarith

end UndergradKB.Precalculus.Course
