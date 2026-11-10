import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology Asymptotics

/-! ### Growth rates (CA-169) -/

/-- OpenStax Calculus 1:§4.8 growth rates definition (CA-169). `f` grows faster than `g` as `x → ∞` when
`f(x)/g(x) → ∞`. -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
def GrowsFasterThan (f g : ℝ → ℝ) : Prop := Tendsto (fun x => f x / g x) atTop atTop

/-- OpenStax Calculus 1:§4.8 growth rates definition (CA-169). `f` and `g` grow at the same rate when
`f(x)/g(x)` tends to a nonzero constant. -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
def SameGrowthRate (f g : ℝ → ℝ) : Prop := ∃ c : ℝ, c ≠ 0 ∧ Tendsto (fun x => f x / g x) atTop (𝓝 c)

/-- OpenStax Calculus 1:§4.8 (CA-169). `e^x` grows faster than `x^n` for every natural number `n`. -/
@[kb "openstaxcalculus2016" "1:Example 4.45, p. 413"]
theorem exp_growsFasterThan_pow (n : ℕ) : GrowsFasterThan Real.exp (fun x => x ^ n) :=
  Real.tendsto_exp_div_pow_atTop n

/-- OpenStax Calculus 1:§4.8 (CA-169). `e^x` grows faster than `x^p` for every real `p`. -/
@[kb "openstaxcalculus2016" "1:Example 4.45, p. 413"]
theorem exp_growsFasterThan_rpow (p : ℝ) : GrowsFasterThan Real.exp (fun x => x ^ p) :=
  tendsto_exp_div_rpow_atTop p

/-- OpenStax Calculus 1:§4.8 (CA-169). `x^r` (`r > 0`) grows faster than `ln x`. -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
theorem rpow_growsFasterThan_log {r : ℝ} (hr : 0 < r) :
    GrowsFasterThan (fun x => x ^ r) Real.log := by
  have h : Tendsto (fun x => Real.log x / x ^ r) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have h' : Tendsto (fun x => Real.log x / x ^ r) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) r)
  exact h'.inv_tendsto_nhdsGT_zero.congr fun x => inv_div _ _

/-- OpenStax Calculus 1:§4.8 (CA-169). `x^n` (`n ≥ 1`) grows faster than `ln x`. -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
theorem pow_growsFasterThan_log {n : ℕ} (hn : n ≠ 0) :
    GrowsFasterThan (fun x => x ^ n) Real.log := by
  have := rpow_growsFasterThan_log (r := (n : ℝ)) (by exact_mod_cast Nat.pos_of_ne_zero hn)
  exact this.congr fun x => by show x ^ (n : ℝ) / Real.log x = x ^ n / Real.log x; rw [Real.rpow_natCast]

/-- OpenStax Calculus 1:§4.8 (CA-169). `c f` grows at the same rate as `f` for `c ≠ 0` (when `f` is
nonzero eventually, here `f ≠ 0` everywhere). -/
@[kb "openstaxcalculus2016" "1:§4.8 Growth rates definition, p. 412"]
theorem sameGrowthRate_const_mul {c : ℝ} (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ∀ x, f x ≠ 0) :
    SameGrowthRate (fun x => c * f x) f :=
  ⟨c, hc, (tendsto_const_nhds).congr fun x => by simp [mul_div_assoc, div_self (hf x)]⟩

/-! ### Tangent line (CA-085) -/

/-- OpenStax Calculus 1:§3.1 Definition (tangent line) (CA-085). The line through `(a, f a)` with slope
`f'(a)`. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (tangent line), p. 199"]
noncomputable def tangentLine (f : ℝ → ℝ) (a x : ℝ) : ℝ := f a + deriv f a * (x - a)

/-- OpenStax Calculus 1:§3.1 (CA-085). A line through `(a, f a)` with slope `m` approximates `f` to first
order at `a`, `f(x) - (f a + m (x - a)) = o(x - a)`, exactly when `f` has derivative `m` at `a`.
So the tangent line is the unique line through `(a, f a)` with this property. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (tangent line), p. 199"]
theorem isLittleO_line_iff_hasDerivAt (f : ℝ → ℝ) (a m : ℝ) :
    (fun x => f x - (f a + m * (x - a))) =o[𝓝 a] (fun x => x - a) ↔ HasDerivAt f m a := by
  rw [hasDerivAt_iff_isLittleO]
  have : (fun x => f x - (f a + m * (x - a))) = fun x' => f x' - f a - (x' - a) • m := by
    funext x; simp [smul_eq_mul]; ring
  rw [this]

/-- OpenStax Calculus 1:§3.1 (CA-085). The tangent line approximates `f` to first order. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (tangent line), p. 199"]
theorem tangentLine_isLittleO {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a) :
    (fun x => f x - tangentLine f a x) =o[𝓝 a] (fun x => x - a) :=
  (isLittleO_line_iff_hasDerivAt f a (deriv f a)).2 hf.hasDerivAt

/-- OpenStax Calculus 1:§3.1 (CA-085), uniqueness: if a line with slope `m` through `(a, f a)` satisfies
`f(x) - line(x) = o(x - a)`, then `f` is differentiable at `a` and `m = f'(a)`. -/
@[kb "openstaxcalculus2016" "1:§3.1 Definition (tangent line), p. 199"]
theorem tangentLine_unique {f : ℝ → ℝ} {a m : ℝ}
    (h : (fun x => f x - (f a + m * (x - a))) =o[𝓝 a] (fun x => x - a)) :
    DifferentiableAt ℝ f a ∧ m = deriv f a :=
  have h' := (isLittleO_line_iff_hasDerivAt f a m).1 h
  ⟨h'.differentiableAt, h'.deriv.symm⟩

/-! ### Implicit differentiation (CA-122) -/

/-- OpenStax Calculus 1:§3.8 implicit differentiation (CA-122). Let `F(x, y)` be differentiable at
`(x, y(x))` with partial derivatives `F_x` and `F_y`, and let `y` be differentiable at `x` with
`F(t, y(t)) = c` for `t` near `x`. Then `F_x + F_y y' = 0`; so if `F_y ≠ 0`, `y' = -F_x / F_y`. -/
@[kb "openstaxcalculus2016" "1:§3.8 Problem-Solving Strategy: Implicit Differentiation, p. 277"]
theorem implicit_differentiation {F : ℝ → ℝ → ℝ} {y : ℝ → ℝ} {x y' Fx Fy c : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (Fx • ContinuousLinearMap.fst ℝ ℝ ℝ + Fy • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y x))
    (hy : HasDerivAt y y' x) (hloc : ∀ᶠ t in 𝓝 x, F t (y t) = c) :
    Fx + Fy * y' = 0 := by
  have h1 : HasDerivAt (fun t => (t, y t)) (1, y') x := (hasDerivAt_id' x).prodMk hy
  have h2 := hF.comp_hasDerivAt x h1
  have h3 : HasDerivAt ((fun p : ℝ × ℝ => F p.1 p.2) ∘ fun t => (t, y t)) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq (hloc.mono fun t ht => by simpa using ht)
  have := h2.unique h3
  simpa using this

/-- OpenStax Calculus 1:§3.8 (CA-122), solved form: `y' = -F_x / F_y` when `F_y ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:§3.8 Problem-Solving Strategy: Implicit Differentiation, p. 277"]
theorem implicit_differentiation_eq {F : ℝ → ℝ → ℝ} {y : ℝ → ℝ} {x y' Fx Fy c : ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (Fx • ContinuousLinearMap.fst ℝ ℝ ℝ + Fy • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y x))
    (hy : HasDerivAt y y' x) (hloc : ∀ᶠ t in 𝓝 x, F t (y t) = c) (hFy : Fy ≠ 0) :
    y' = -Fx / Fy := by
  have := implicit_differentiation hF hy hloc
  field_simp
  linarith

/-! ### Antiderivatives (CA-173, CA-175, CA-176, CA-177) -/

/-- OpenStax Calculus 1:§4.10 Definition (antiderivative) (CA-173). `F` is an antiderivative of `f` on
(the interior of) `I` when `F'(x) = f(x)` at every `x ∈ I`. Intended for open intervals `I`. -/
@[kb "openstaxcalculus2016" "1:§4.10 Definition (antiderivative), p. 428"]
def IsAntiderivOn (F f : ℝ → ℝ) (I : Set ℝ) : Prop := ∀ x ∈ I, HasDerivAt F (f x) x

/-- OpenStax Calculus 1:Theorem 4.14 (CA-173). Two antiderivatives of `f` on an interval differ by a
constant. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.14, p. 429"]
theorem IsAntiderivOn.eq_add_const {F G f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hF : IsAntiderivOn F f I) (hG : IsAntiderivOn G f I) :
    ∃ C : ℝ, ∀ x ∈ I, F x = G x + C := by
  have hconst : ∀ x ∈ I, ∀ y ∈ I, x ≤ y → F y - G y = F x - G x := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ I := hI.out hx hy
    have hd : ∀ z ∈ Icc x y, HasDerivAt (fun t => F t - G t) 0 z := fun z hz => by
      exact ((hF z (hsub hz)).fun_sub (hG z (hsub hz))).congr_deriv (sub_self _)
    have hc : ContinuousOn (fun t => F t - G t) (Icc x y) := fun z hz => (hd z hz).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hc (fun z hz => (hd z (Ico_subset_Icc_self hz)).hasDerivWithinAt)
      y ⟨hxy, le_rfl⟩
  by_cases hne : I.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨F x₀ - G x₀, fun x hx => ?_⟩
    rcases le_total x₀ x with h | h
    · have := hconst x₀ hx₀ x hx h; linarith
    · have := hconst x hx x₀ hx₀ h; linarith
  · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-- OpenStax Calculus 1:Theorem 4.15 (CA-175), real exponent: for `n ≠ -1`, `x^(n+1)/(n+1)` is an
antiderivative of `x^n` on `(0, ∞)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.15, p. 430"]
theorem isAntiderivOn_rpow {n : ℝ} (hn : n ≠ -1) :
    IsAntiderivOn (fun x => x ^ (n + 1) / (n + 1)) (fun x => x ^ n) (Ioi 0) := by
  intro x hx
  have hn1 : n + 1 ≠ 0 := fun h => hn (by linarith)
  have := (Real.hasDerivAt_rpow_const (p := n + 1) (Or.inl (ne_of_gt hx))).div_const (n + 1)
  rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hn1] at this
  exact this

/-- OpenStax Calculus 1:Theorem 4.15 (CA-175), integer exponent: for an integer `n ≠ -1`, `x^(n+1)/(n+1)`
is an antiderivative of `x^n` on any set avoiding `0`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.15, p. 430"]
theorem isAntiderivOn_zpow {n : ℤ} (hn : n ≠ -1) {I : Set ℝ} (hI : ∀ x ∈ I, x ≠ 0) :
    IsAntiderivOn (fun x => x ^ (n + 1) / ((n : ℝ) + 1)) (fun x => x ^ n) I := by
  intro x hx
  have hn1 : (n : ℝ) + 1 ≠ 0 := by
    intro h
    apply hn
    have : ((n + 1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have := Int.cast_eq_zero.mp this
    omega
  have := (hasDerivAt_zpow (n + 1) x (Or.inl (hI x hx))).div_const ((n : ℝ) + 1)
  rw [add_sub_cancel_right] at this
  push_cast at this
  rw [mul_div_cancel_left₀ _ hn1] at this
  exact this

/-- OpenStax Calculus 1:Theorem 4.15 (CA-175), natural exponent, on all of `ℝ`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.15, p. 430"]
theorem isAntiderivOn_pow (n : ℕ) :
    IsAntiderivOn (fun x => x ^ (n + 1) / ((n : ℝ) + 1)) (fun x => x ^ n) univ := by
  intro x _
  have := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel] at this
  push_cast at this
  rw [mul_div_cancel_left₀ _ hn1] at this
  exact this

/-- OpenStax Calculus 1:Theorem 4.16 (CA-177): sums of antiderivatives. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.16, p. 433"]
theorem IsAntiderivOn.add {F G f g : ℝ → ℝ} {I : Set ℝ} (hF : IsAntiderivOn F f I)
    (hG : IsAntiderivOn G g I) : IsAntiderivOn (fun x => F x + G x) (fun x => f x + g x) I :=
  fun x hx => (hF x hx).add (hG x hx)

/-- OpenStax Calculus 1:Theorem 4.16 (CA-177): differences of antiderivatives. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.16, p. 433"]
theorem IsAntiderivOn.sub {F G f g : ℝ → ℝ} {I : Set ℝ} (hF : IsAntiderivOn F f I)
    (hG : IsAntiderivOn G g I) : IsAntiderivOn (fun x => F x - G x) (fun x => f x - g x) I :=
  fun x hx => (hF x hx).sub (hG x hx)

/-- OpenStax Calculus 1:Theorem 4.16 (CA-177): constant multiples of antiderivatives. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.16, p. 433"]
theorem IsAntiderivOn.const_mul {F f : ℝ → ℝ} {I : Set ℝ} (hF : IsAntiderivOn F f I) (k : ℝ) :
    IsAntiderivOn (fun x => k * F x) (fun x => k * f x) I :=
  fun x hx => (hF x hx).const_mul k

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `e^x` is an antiderivative of `e^x`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_exp : IsAntiderivOn Real.exp Real.exp univ :=
  fun x _ => Real.hasDerivAt_exp x

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `ln |x|` (Mathlib's `Real.log`) is an antiderivative of `1/x`
away from `0`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_inv : IsAntiderivOn Real.log (fun x => 1 / x) {x | x ≠ 0} := by
  intro x hx
  simpa [one_div] using Real.hasDerivAt_log hx

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `-cos` is an antiderivative of `sin`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_sin : IsAntiderivOn (fun x => -Real.cos x) Real.sin univ :=
  fun x _ => ((Real.hasDerivAt_cos x).fun_neg).congr_deriv (by ring)

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `sin` is an antiderivative of `cos`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_cos : IsAntiderivOn Real.sin Real.cos univ :=
  fun x _ => Real.hasDerivAt_sin x

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `tan` is an antiderivative of `sec²` where `cos ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_sec_sq :
    IsAntiderivOn Real.tan (fun x => 1 / Real.cos x ^ 2) {x | Real.cos x ≠ 0} :=
  fun _ hx => Real.hasDerivAt_tan hx

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `sec` is an antiderivative of `sec · tan` where `cos ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_sec_tan :
    IsAntiderivOn (fun x => 1 / Real.cos x) (fun x => 1 / Real.cos x * (Real.sin x / Real.cos x))
      {x | Real.cos x ≠ 0} := by
  intro x hx
  have := (Real.hasDerivAt_cos x).inv hx
  simp only [one_div]
  convert this using 1
  have : Real.cos x ≠ 0 := hx
  field_simp

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `-cot` is an antiderivative of `csc²` where `sin ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_csc_sq :
    IsAntiderivOn (fun x => -(Real.cos x / Real.sin x)) (fun x => 1 / Real.sin x ^ 2)
      {x | Real.sin x ≠ 0} := by
  intro x hx
  have hx' : Real.sin x ≠ 0 := hx
  have := ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx').fun_neg
  convert this using 1
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  field_simp
  nlinarith [h2]

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `-csc` is an antiderivative of `csc · cot` where `sin ≠ 0`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_csc_cot :
    IsAntiderivOn (fun x => -(1 / Real.sin x)) (fun x => 1 / Real.sin x * (Real.cos x / Real.sin x))
      {x | Real.sin x ≠ 0} := by
  intro x hx
  have hx' : Real.sin x ≠ 0 := hx
  have := ((Real.hasDerivAt_sin x).inv hx').fun_neg
  simp only [one_div]
  convert this using 1
  field_simp

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `arcsin` is an antiderivative of `1/√(1-x²)` on `(-1, 1)`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_arcsin :
    IsAntiderivOn Real.arcsin (fun x => 1 / √(1 - x ^ 2)) (Ioo (-1) 1) :=
  fun _ hx => Real.hasDerivAt_arcsin hx.1.ne' hx.2.ne

/-- OpenStax Calculus 1:Table 4.13 (CA-176): `arctan` is an antiderivative of `1/(1+x²)`. -/
@[kb "openstaxcalculus2016" "1:Table 4.13, p. 431"]
theorem isAntiderivOn_arctan : IsAntiderivOn Real.arctan (fun x => 1 / (1 + x ^ 2)) univ :=
  fun x _ => Real.hasDerivAt_arctan x

end UndergradKB.Calculus
