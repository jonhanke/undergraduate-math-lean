import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-! # The Bessel equation of order 0 (OpenStax Calculus 3:Example 7.26, CA-690)

The series `J0 x = ∑ (-1)^n x^(2n) / (4^n (n!)^2)` converges for every real `x`, is twice differentiable, and
satisfies `x² y'' + x y' + x² y = 0`. The proof uses a general lemma: a power series `∑ c_n x^n` that
converges absolutely for every radius can be differentiated term by term (Mathlib's
`hasDerivAt_tsum_of_isPreconnected` on balls), and the coefficient recursion is then compared. -/

namespace UndergradKB.Calculus
open Nat

/-- Coefficient sequence `c` whose power series converges absolutely at every radius. -/
def PS (c : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable (fun n => |c n| * R ^ n)

lemma PS.summable {c : ℕ → ℝ} (hc : PS c) (x : ℝ) : Summable (fun n => c n * x ^ n) :=
  Summable.of_norm_bounded (hc |x| (abs_nonneg x))
    (fun n => by rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs])

/-- Derivative coefficients. -/
def Dc (c : ℕ → ℝ) (n : ℕ) : ℝ := c (n + 1) * ((n : ℝ) + 1)

lemma pow_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((n : ℝ) + 1) * R ^ n ≤ (2 * (R + 1)) ^ (n + 1) := by
  have h1 : ((n : ℝ) + 1) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this
  have h2 : R ^ n ≤ (R + 1) ^ n := pow_le_pow_left₀ hR (by linarith) n
  have h3 : (2 * (R + 1)) ^ n ≤ (2 * (R + 1)) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
  calc ((n : ℝ) + 1) * R ^ n ≤ 2 ^ n * (R + 1) ^ n :=
        mul_le_mul h1 h2 (pow_nonneg hR n) (by positivity)
    _ = (2 * (R + 1)) ^ n := by rw [mul_pow]
    _ ≤ _ := h3

lemma PS.shift {c : ℕ → ℝ} (hc : PS c) : PS (fun n => c (n + 1)) := by
  intro R hR
  have hs := (summable_nat_add_iff 1).2 (hc (2 * (R + 1)) (by linarith))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have := pow_bound R hR n
  have h0 := abs_nonneg (c (n + 1))
  have h1 : R ^ n ≤ ((n : ℝ) + 1) * R ^ n := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [pow_nonneg hR n]
  exact mul_le_mul_of_nonneg_left (h1.trans this) h0

lemma PS.dc {c : ℕ → ℝ} (hc : PS c) : PS (Dc c) := by
  intro R hR
  have hs := (summable_nat_add_iff 1).2 (hc (2 * (R + 1)) (by linarith))
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have := pow_bound R hR n
  have h0 := abs_nonneg (c (n + 1))
  simp only [Dc]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), mul_assoc]
  exact mul_le_mul_of_nonneg_left this h0

/-- Term-by-term differentiation of a power series with infinite radius of convergence. -/
lemma PS.hasDerivAt {c : ℕ → ℝ} (hc : PS c) (x : ℝ) :
    HasDerivAt (fun z => ∑' n, c n * z ^ n) (∑' n, Dc c n * x ^ n) x := by
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable (fun n : ℕ => |c n| * (n : ℝ) * R ^ (n - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine (hc.dc R hR0).congr (fun n => ?_)
    simp only [Dc]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    push_cast
    rfl
  have hbd : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ |c n| * (n : ℝ) * R ^ (n - 1) := by
    intro n y hy
    have hy' : |y| ≤ R := (abs_le.2 ⟨hy.1.le, hy.2.le⟩)
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' _)
      (Nat.cast_nonneg n)) (abs_nonneg _)
  have hx : x ∈ Set.Ioo (-R) R := ⟨by rw [hR]; linarith [neg_abs_le x], by rw [hR]; linarith [le_abs_self x]⟩
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun n z => c n * z ^ n)
    (g' := fun n z => c n * ((n : ℝ) * z ^ (n - 1))) (t := Set.Ioo (-R) R) (y₀ := 0) hu isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) hbd
    ⟨by rw [hR]; linarith [abs_nonneg x], by rw [hR]; linarith [abs_nonneg x]⟩ (hc.summable 0) hx
  convert h using 1
  have hsum : Summable (fun n : ℕ => c n * ((n : ℝ) * x ^ (n - 1))) :=
    Summable.of_norm_bounded hu (fun n => hbd n x hx)
  rw [Summable.tsum_eq_zero_add hsum]
  simp only [Dc]
  simp
  exact tsum_congr (fun n => by ring)

/-- The power series `∑ c_n x^n` with `c 1 = 0` and `(n+2)² c_{n+2} + c_n = 0` solves
`x² y'' + x y' + x² y = 0`. -/
theorem PS.bessel {c : ℕ → ℝ} (hc : PS c) (h1 : c 1 = 0)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 2) ^ 2 * c (n + 2) + c n = 0) :
    Differentiable ℝ (fun z => ∑' n, c n * z ^ n) ∧
    Differentiable ℝ (deriv (fun z => ∑' n, c n * z ^ n)) ∧
    ∀ x, x ^ 2 * deriv (deriv (fun z => ∑' n, c n * z ^ n)) x +
      x * deriv (fun z => ∑' n, c n * z ^ n) x + x ^ 2 * (∑' n, c n * x ^ n) = 0 := by
  have e1 : deriv (fun z => ∑' n, c n * z ^ n) = fun z => ∑' n, Dc c n * z ^ n :=
    funext fun x => (hc.hasDerivAt x).deriv
  have hd := hc.dc
  have e2 : deriv (fun z => ∑' n, Dc c n * z ^ n) = fun z => ∑' n, Dc (Dc c) n * z ^ n :=
    funext fun x => (hd.hasDerivAt x).deriv
  refine ⟨fun x => (hc.hasDerivAt x).differentiableAt, ?_, fun x => ?_⟩
  · rw [e1]; exact fun x => (hd.hasDerivAt x).differentiableAt
  · rw [e1, e2]
    show x ^ 2 * (∑' n, Dc (Dc c) n * x ^ n) + x * (∑' n, Dc c n * x ^ n) + x ^ 2 * (∑' n, c n * x ^ n) = 0
    have hA := hd.dc.summable x
    have hB := hd.summable x
    have hB' := hd.shift.summable x
    have hC := hc.summable x
    have hBeq : ∑' n, Dc c n * x ^ n = x * ∑' n, Dc c (n + 1) * x ^ n := by
      rw [Summable.tsum_eq_zero_add hB, ← tsum_mul_left]
      have : Dc c 0 = 0 := by simp [Dc, h1]
      rw [this]
      simp only [zero_mul, zero_add]
      exact tsum_congr (fun n => by ring)
    have hall : ∑' n, Dc (Dc c) n * x ^ n + ∑' n, Dc c (n + 1) * x ^ n + ∑' n, c n * x ^ n = 0 := by
      rw [← hA.tsum_add hB', ← (hA.add hB').tsum_add hC]
      refine (tsum_congr (fun n => ?_)).trans tsum_zero
      simp only [Dc]
      push_cast
      have := hrec n
      linear_combination x ^ n * this
    rw [hBeq]
    linear_combination x ^ 2 * hall

/-- The coefficients of the Bessel series: `c_{2m} = (-1)^m / (4^m (m!)²)`, odd coefficients zero. -/
noncomputable def besselCoeff (n : ℕ) : ℝ :=
  if Even n then (-1) ^ (n / 2) / (4 ^ (n / 2) * ((n / 2)! : ℝ) ^ 2) else 0

lemma besselCoeff_even (m : ℕ) : besselCoeff (2 * m) = (-1) ^ m / (4 ^ m * (m ! : ℝ) ^ 2) := by
  simp [besselCoeff, Nat.mul_div_cancel_left m (two_pos)]

lemma besselCoeff_odd (m : ℕ) : besselCoeff (2 * m + 1) = 0 := by
  simp [besselCoeff]

lemma besselCoeff_rec (n : ℕ) : ((n : ℝ) + 2) ^ 2 * besselCoeff (n + 2) + besselCoeff n = 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have : 2 * m + 2 = 2 * (m + 1) := by ring
    rw [this, besselCoeff_even, besselCoeff_even]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · have : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by ring
    rw [this, besselCoeff_odd, besselCoeff_odd]; simp

lemma besselCoeff_PS : PS besselCoeff := by
  intro R hR
  apply Summable.even_add_odd
  · have hs := Real.summable_pow_div_factorial ((R / 2) ^ 2)
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
    rw [besselCoeff_even]
    have hm : (1 : ℝ) ≤ (m ! : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos m)
    have key : 1 / (4 ^ m * (m ! : ℝ) ^ 2) ≤ 1 / (4 ^ m * (m ! : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (0 : ℝ) < 4 ^ m := by positivity
      have h2 : (m ! : ℝ) ≤ (m ! : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h2 this.le
    have e : |(-1 : ℝ) ^ m / (4 ^ m * (m ! : ℝ) ^ 2)| * R ^ (2 * m) = 1 / (4 ^ m * (m ! : ℝ) ^ 2) * R ^ (2 * m) := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
    rw [e]
    calc 1 / (4 ^ m * (m ! : ℝ) ^ 2) * R ^ (2 * m) ≤ 1 / (4 ^ m * (m ! : ℝ)) * R ^ (2 * m) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = ((R / 2) ^ 2) ^ m / m ! := by
          rw [← pow_mul, div_pow]
          have h4 : (2 : ℝ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
          rw [h4]
          field_simp
  · simp [besselCoeff_odd]

/-- `J0 x = ∑ (-1)^n x^(2n) / (4^n (n!)^2)`, the Bessel function of order 0 as a power series. -/
noncomputable def J0 (x : ℝ) : ℝ := ∑' n : ℕ, (-1) ^ n * x ^ (2 * n) / (4 ^ n * (n ! : ℝ) ^ 2)

lemma J0_eq (x : ℝ) : J0 x = ∑' n, besselCoeff n * x ^ n := by
  have hs := besselCoeff_PS.summable x
  have he : Summable (fun k : ℕ => besselCoeff (2 * k) * x ^ (2 * k)) :=
    hs.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simp only at h; omega)
  have h0 : ∀ k : ℕ, besselCoeff (2 * k + 1) * x ^ (2 * k + 1) = 0 := fun k => by
    rw [besselCoeff_odd, zero_mul]
  have ho : Summable (fun k : ℕ => besselCoeff (2 * k + 1) * x ^ (2 * k + 1)) :=
    (summable_zero (α := ℝ)).congr (fun k => (h0 k).symm)
  have h1 : ∑' k : ℕ, besselCoeff (2 * k + 1) * x ^ (2 * k + 1) = 0 := by
    rw [tsum_congr h0]; exact tsum_zero
  have h2 : J0 x = ∑' k : ℕ, besselCoeff (2 * k) * x ^ (2 * k) := by
    unfold J0
    refine tsum_congr (fun n => ?_)
    rw [besselCoeff_even, div_mul_eq_mul_div]
  rw [h2]
  have := tsum_even_add_odd (f := fun n => besselCoeff n * x ^ n) he ho
  rw [h1, add_zero] at this
  exact this

/-- OpenStax Calculus 3:Example 7.26 (CA-690): `J0` is twice differentiable and solves the Bessel equation of
order 0, `x² y'' + x y' + x² y = 0`, for all real `x`. -/
@[kb "openstaxcalculus2016" "3:Example 7.26, p. 797"]
theorem J0_bessel_equation :
    Differentiable ℝ J0 ∧ Differentiable ℝ (deriv J0) ∧
      ∀ x, x ^ 2 * deriv (deriv J0) x + x * deriv J0 x + x ^ 2 * J0 x = 0 := by
  have hJ : J0 = fun z => ∑' n, besselCoeff n * z ^ n := funext J0_eq
  rw [hJ]
  exact PS.bessel besselCoeff_PS (besselCoeff_odd 0) besselCoeff_rec

end UndergradKB.Calculus
