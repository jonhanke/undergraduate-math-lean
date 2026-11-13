import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.FourierSeries

/-! # Convergence of Fourier series of continuously differentiable periodic functions

Lebl, *Notes on Diffy Qs*, Theorem 4.3.1 states pointwise convergence of the Fourier series of a piecewise smooth
`2L`-periodic function.  Mathlib has convergence when the coefficients are summable
(`has_pointwise_sum_fourier_series_of_summable`) and Parseval's identity.  Here: for a `C¹` periodic function
the coefficients are summable (integration by parts gives `cₙ(f) = T cₙ(f') / (2π i n)`, and
`|cₙ(f')| / |n| ≤ (|cₙ(f')|² + 1/n²) / 2` is summable by Parseval), so the series converges to `f` everywhere.
This is the case of Theorem 4.3.1 without jumps and corners. -/

namespace UndergradKB.DifferentialEquations

open Real Complex MeasureTheory Filter Topology AddCircle

section complex

variable {T : ℝ} (hT : 0 < T)

include hT in
lemma fourier_C1_coeff_eq {f f' : ℝ → ℂ} (hper : Function.Periodic f T)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT) f n
      = (T / (2 * π * I * n)) * fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT) f' n := by
  rw [fourierCoeffOn_of_hasDerivAt (lt_add_of_pos_right (0 : ℝ) hT) hn (fun x _ => hf x)
    (hf'.intervalIntegrable _ _)]
  have h0 : f (0 + T) = f 0 := hper 0
  rw [h0, sub_self, mul_zero, zero_sub]
  simp only [zero_add, Complex.ofReal_zero, sub_zero]
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

include hT in
lemma fourier_C1_summable {f f' : ℝ → ℂ} (hper : Function.Periodic f T)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    Summable (fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT) f) := by
  set hab := lt_add_of_pos_right (0 : ℝ) hT
  -- Parseval for `f'`
  have hL2 : MemLp f' 2 (volume.restrict (Set.Ioc 0 (0 + T))) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 0 + T)).exists_bound_of_continuousOn
      hf'.continuousOn
    have htop : MemLp f' ⊤ (volume.restrict (Set.Ioc 0 (0 + T))) :=
      memLp_top_of_bound hf'.aestronglyMeasurable.restrict C
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx =>
          hC x (Set.Ioc_subset_Icc_self hx)))
    exact htop.mono_exponent le_top
  have hsq : Summable fun n : ℤ => ‖fourierCoeffOn hab f' n‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn hab hL2).summable
  have hinv : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_int_pow.mpr one_lt_two
  have hbound : Summable fun n : ℤ => T / (2 * π) * ((‖fourierCoeffOn hab f' n‖ ^ 2 + 1 / (n : ℝ) ^ 2) / 2) :=
    ((hsq.add hinv).div_const 2).mul_left _
  refine Summable.of_norm_bounded_eventually hbound ?_
  have : {n : ℤ | n ≠ 0} ∈ cofinite := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with n hn
  rw [fourier_C1_coeff_eq hT hper hf hf' hn, norm_mul]
  have hnr : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
  have hnorm : ‖(T : ℂ) / (2 * π * I * n)‖ = T / (2 * π) * (1 / |(n : ℝ)|) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
      Complex.norm_intCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT, abs_of_pos Real.pi_pos]
    norm_num
    field_simp
  rw [hnorm, mul_assoc]
  have hT2 : 0 ≤ T / (2 * π) := by positivity
  apply mul_le_mul_of_nonneg_left _ hT2
  set u := ‖fourierCoeffOn hab f' n‖
  set v := 1 / |(n : ℝ)|
  have hv : 1 / (n : ℝ) ^ 2 = v ^ 2 := by
    simp only [v, div_pow, one_pow, sq_abs]
  rw [hv]
  nlinarith [sq_nonneg (u - v)]

include hT in
/-- **Fourier convergence for `C¹` periodic functions, complex form (DE-129, case without jumps).** If `f` is
`T`-periodic and differentiable with continuous derivative, then `∑ₙ cₙ e^{2π i n x / T} = f(x)` for every `x`,
where `cₙ` are the Fourier coefficients of `f` on `[0, T]`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem fourier_series_C1_complex {f f' : ℝ → ℂ} (hper : Function.Periodic f T)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (x : ℝ) :
    HasSum (fun n : ℤ => fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT) f n
      * Complex.exp (2 * π * I * n * x / T)) (f x) := by
  have : Fact (0 < T) := ⟨hT⟩
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hend : f 0 = f (0 + T) := (hper 0).symm
  let F : C(AddCircle T, ℂ) := ⟨liftIco T 0 f, liftIco_continuous hend hfc.continuousOn⟩
  have hcoeff : ∀ n, fourierCoeff F n = fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT) f n :=
    fun n => fourierCoeff_liftIco_eq f n
  have hsum : Summable (fourierCoeff F) := by
    have := fourier_C1_summable hT hper hf hf'
    exact this.congr fun n => (hcoeff n).symm
  have h := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle T)
  have hFx : F (x : AddCircle T) = f x := by
    show liftIco T 0 f (x : AddCircle T) = f x
    have hy := toIcoMod_mem_Ico hT 0 x
    have hyx : toIcoMod hT 0 x = x - toIcoDiv hT 0 x • T := rfl
    have hx : (x : AddCircle T) = ((toIcoMod hT 0 x : ℝ) : AddCircle T) := by
      rw [hyx, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
    rw [hx, liftIco_coe_apply hy, hyx]
    exact hper.sub_zsmul_eq _
  rw [hFx] at h
  convert h using 2 with n
  rw [hcoeff, smul_eq_mul, fourier_coe_apply]

end complex

section real

/-- `∫_{-L}^{L} f(y) cos(mπy/L) dy` for an integer `m`. -/
noncomputable def fcosI (f : ℝ → ℝ) (L : ℝ) (m : ℤ) : ℝ := ∫ y in (-L)..L, f y * Real.cos ((m : ℝ) * π / L * y)

/-- `∫_{-L}^{L} f(y) sin(mπy/L) dy` for an integer `m`. -/
noncomputable def fsinI (f : ℝ → ℝ) (L : ℝ) (m : ℤ) : ℝ := ∫ y in (-L)..L, f y * Real.sin ((m : ℝ) * π / L * y)

variable {L : ℝ}

lemma exp_fourier_arg (hL : L ≠ 0) (m : ℤ) (y : ℝ) :
    Complex.exp (2 * π * I * (m : ℂ) * y / ((2 * L : ℝ) : ℂ))
      = ((Real.cos ((m : ℝ) * π / L * y) : ℝ) : ℂ) + I * ((Real.sin ((m : ℝ) * π / L * y) : ℝ) : ℂ) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have : 2 * π * I * (m : ℂ) * y / ((2 * L : ℝ) : ℂ) = (((m : ℝ) * π / L * y : ℝ) : ℂ) * I := by
    push_cast; field_simp
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

lemma periodic_mul_cos {f : ℝ → ℝ} (hper : Function.Periodic f (2 * L)) (hL0 : L ≠ 0) (m : ℤ) :
    Function.Periodic (fun y => f y * Real.cos ((m : ℝ) * π / L * y)) (2 * L) := by
  intro y
  simp only
  rw [hper y, show (m : ℝ) * π / L * (y + 2 * L) = (m : ℝ) * π / L * y + m * (2 * π) by field_simp,
    Real.cos_add_int_mul_two_pi]

lemma periodic_mul_sin {f : ℝ → ℝ} (hper : Function.Periodic f (2 * L)) (hL0 : L ≠ 0) (m : ℤ) :
    Function.Periodic (fun y => f y * Real.sin ((m : ℝ) * π / L * y)) (2 * L) := by
  intro y
  simp only
  rw [hper y, show (m : ℝ) * π / L * (y + 2 * L) = (m : ℝ) * π / L * y + m * (2 * π) by field_simp,
    Real.sin_add_int_mul_two_pi]

/-- The complex Fourier coefficient on `[0, 2L]` of a real `2L`-periodic continuous function, in terms of the
cosine and sine integrals over `[-L, L]`. -/
lemma fourierCoeffOn_real (hL : 0 < L) {f : ℝ → ℝ} (hper : Function.Periodic f (2 * L)) (hf : Continuous f)
    (m : ℤ) :
    fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) (by positivity : 0 < 2 * L)) (fun x => (f x : ℂ)) m
      = (1 / (2 * L) : ℂ) * ((fcosI f L m : ℂ) - I * (fsinI f L m : ℂ)) := by
  rw [fourierCoeffOn_eq_integral]
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hpt : ∀ y : ℝ, fourier (-m) (y : AddCircle (0 + 2 * L - 0)) • (f y : ℂ)
      = ((f y * Real.cos ((m : ℝ) * π / L * y) : ℝ) : ℂ)
        - I * ((f y * Real.sin ((m : ℝ) * π / L * y) : ℝ) : ℂ) := by
    intro y
    rw [fourier_coe_apply, smul_eq_mul]
    have harg : 2 * π * I * ((-m : ℤ) : ℂ) * (y : ℂ) / ((0 + 2 * L - 0 : ℝ) : ℂ)
        = ((-((m : ℝ) * π / L * y) : ℝ) : ℂ) * I := by
      rw [show (0 + 2 * L - 0 : ℝ) = 2 * L by ring]
      push_cast; field_simp
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [hpt]
  have hc : Continuous fun y => f y * Real.cos ((m : ℝ) * π / L * y) := by fun_prop
  have hs : Continuous fun y => f y * Real.sin ((m : ℝ) * π / L * y) := by fun_prop
  have hci : IntervalIntegrable (fun y => ((f y * Real.cos ((m : ℝ) * π / L * y) : ℝ) : ℂ)) volume 0 (0 + 2 * L) :=
    (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  have hsi : IntervalIntegrable (fun y => I * ((f y * Real.sin ((m : ℝ) * π / L * y) : ℝ) : ℂ)) volume 0
      (0 + 2 * L) :=
    ((Complex.continuous_ofReal.comp hs).intervalIntegrable _ _).const_mul I
  rw [intervalIntegral.integral_sub hci hsi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hshift : ∀ h : ℝ → ℝ, Function.Periodic h (2 * L) →
      ∫ y in (0 : ℝ)..0 + 2 * L, h y = ∫ y in (-L)..L, h y := by
    intro h hh
    rw [hh.intervalIntegral_add_eq 0 (-L), show -L + 2 * L = L by ring]
  rw [hshift _ (periodic_mul_cos hper hL.ne' m), hshift _ (periodic_mul_sin hper hL.ne' m),
    show (0 + 2 * L - 0 : ℝ) = 2 * L by ring, Complex.real_smul]
  simp only [fcosI, fsinI]
  push_cast
  ring

lemma fcosI_neg (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fcosI f L (-(n : ℤ)) = fcosI f L n := by
  unfold fcosI
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [Int.cast_neg, Int.cast_natCast, show -(n : ℝ) * π / L * y = -((n : ℝ) * π / L * y) by ring, Real.cos_neg]

lemma fsinI_neg (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fsinI f L (-(n : ℤ)) = -fsinI f L n := by
  unfold fsinI
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [Int.cast_neg, Int.cast_natCast, show -(n : ℝ) * π / L * y = -((n : ℝ) * π / L * y) by ring, Real.sin_neg]
  ring

lemma fourierA_eq_fcosI (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fourierA f L n = (1 / L) * fcosI f L n := by
  simp [fourierA, fcosI]

lemma fourierB_eq_fsinI (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fourierB f L n = (1 / L) * fsinI f L n := by
  simp [fourierB, fsinI]

/-- **Fourier convergence for `C¹` periodic functions (DE-129, the case without jumps).** If `f` is
`2L`-periodic and differentiable with continuous derivative, then for every `t`
`f(t) = a₀/2 + ∑_{n ≥ 1} (aₙ cos(nπt/L) + bₙ sin(nπt/L))`, with the book's coefficients
`aₙ = (1/L) ∫_{-L}^{L} f(s) cos(nπs/L) ds`, `bₙ = (1/L) ∫_{-L}^{L} f(s) sin(nπs/L) ds`. (The book's theorem also
allows finitely many jumps and corners, where the series converges to the average of the one-sided limits; that
case is not proved here.) -/
@[kb "lebldiffyqs2026" "Theorem 4.3.1, p. 211"]
theorem fourier_series_C1 (hL : 0 < L) {f f' : ℝ → ℝ} (hper : Function.Periodic f (2 * L))
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (t : ℝ) :
    HasSum (fun n : ℕ => fourierA f L (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * π / L * t)
        + fourierB f L (n + 1) * Real.sin (((n + 1 : ℕ) : ℝ) * π / L * t))
      (f t - fourierA f L 0 / 2) := by
  have h2L : 0 < 2 * L := by positivity
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hperC : Function.Periodic (fun x => (f x : ℂ)) (2 * L) := fun x => by simp only [hper x]
  have h := fourier_series_C1_complex h2L hperC (f' := fun x => (f' x : ℂ))
    (fun x => (hf x).ofReal_comp) (Complex.continuous_ofReal.comp hf') t
  have h2 := h.nat_add_neg
  set c := fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) h2L) (fun x => (f x : ℂ))
  have hcoef : ∀ m : ℤ, c m = (1 / (2 * L) : ℂ) * ((fcosI f L m : ℂ) - I * (fsinI f L m : ℂ)) :=
    fun m => fourierCoeffOn_real hL hper hfc m
  have hL0 := hL.ne'
  set φ : ℕ → ℝ := fun n => fourierA f L n * Real.cos ((n : ℝ) * π / L * t)
    + fourierB f L n * Real.sin ((n : ℝ) * π / L * t) with hφ
  have hterm : ∀ n : ℕ,
      c (n : ℤ) * Complex.exp (2 * π * I * ((n : ℤ) : ℂ) * t / ((2 * L : ℝ) : ℂ))
        + c (-(n : ℤ)) * Complex.exp (2 * π * I * ((-(n : ℤ) : ℤ) : ℂ) * t / ((2 * L : ℝ) : ℂ))
      = ((φ n : ℝ) : ℂ) := by
    intro n
    rw [hcoef, hcoef, exp_fourier_arg hL0, exp_fourier_arg hL0, fcosI_neg, fsinI_neg]
    simp only [hφ, fourierA_eq_fcosI, fourierB_eq_fsinI, Int.cast_neg, Int.cast_natCast]
    rw [show -(n : ℝ) * π / L * t = -((n : ℝ) * π / L * t) by ring, Real.cos_neg, Real.sin_neg]
    have hI : I * I = -1 := Complex.I_mul_I
    generalize Real.sin ((n : ℝ) * π / L * t) = S
    generalize Real.cos ((n : ℝ) * π / L * t) = C
    generalize fsinI f L n = B
    generalize fcosI f L n = A
    push_cast
    linear_combination (-(1 / (L : ℂ)) * (B : ℂ) * (S : ℂ)) * hI
  have h0 : c 0 * Complex.exp (2 * π * I * ((0 : ℤ) : ℂ) * t / ((2 * L : ℝ) : ℂ))
      = ((fourierA f L 0 / 2 : ℝ) : ℂ) := by
    rw [hcoef, fourierA_eq_fcosI]
    have hs0 : fsinI f L 0 = 0 := by simp [fsinI]
    rw [hs0]
    simp only [Int.cast_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one,
      Complex.ofReal_zero, sub_zero]
    push_cast
    ring
  have e : (fun n : ℕ => ((φ n : ℝ) : ℂ)) = fun n : ℕ =>
      c (n : ℤ) * Complex.exp (2 * π * I * ((n : ℤ) : ℂ) * t / ((2 * L : ℝ) : ℂ))
        + c (-(n : ℤ)) * Complex.exp (2 * π * I * ((-(n : ℤ) : ℤ) : ℂ) * t / ((2 * L : ℝ) : ℂ)) :=
    funext fun n => (hterm n).symm
  have h3 : HasSum (fun n : ℕ => ((φ n : ℝ) : ℂ)) ((f t + fourierA f L 0 / 2 : ℝ) : ℂ) := by
    rw [e]
    convert h2 using 1
    rw [h0]
    push_cast
    ring
  have h4 := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_ofReal.mp h3)
  simp only [Finset.range_one, Finset.sum_singleton, hφ, Nat.cast_zero, zero_mul, zero_div, Real.cos_zero,
    mul_one, Real.sin_zero, mul_zero, add_zero] at h4
  convert h4 using 1
  ring

end real

