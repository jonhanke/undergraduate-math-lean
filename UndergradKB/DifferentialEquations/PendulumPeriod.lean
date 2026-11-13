import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Pendulum

/-! # The period of the pendulum

Lebl, *Notes on Diffy Qs*, §8.3.1 (period of the pendulum).  For a pendulum released from rest at the angle
`θ₀ ∈ (0, π)` the period is `T(θ₀) = 4 ∫_0^{θ₀} dθ / √((2g/L)(cos θ - cos θ₀))`, an improper integral (the
integrand blows up at `θ₀`), which we treat as a Lebesgue integral over `(0, θ₀)`.  We prove that it converges,
that it equals `4 √(L/g) ∫_0^{π/2} dφ / √(1 - κ² sin² φ)` with `κ = sin (θ₀/2)` (substitution
`sin (θ/2) = κ sin φ`), that `T(θ₀) > 2π √(L/g)` (longer than the linearized period), and that `T(θ₀) → ∞` as
`θ₀ → π⁻`.  Finally, the time a monotone swing takes to go from `θ₀` to `0` is `T(θ₀)/4`. -/

namespace UndergradKB.DifferentialEquations

open Real MeasureTheory Set

/-- The integrand `1 / √((2g/L)(cos θ - cos θ₀))` of the period integral. -/
noncomputable def pendulumPeriodIntegrand (g L θ₀ θ : ℝ) : ℝ :=
  1 / √(2 * g / L * (Real.cos θ - Real.cos θ₀))

/-- The period `T(θ₀) = 4 ∫_0^{θ₀} dθ / √((2g/L)(cos θ - cos θ₀))` (Lebesgue integral over `(0, θ₀)`). -/
noncomputable def pendulumPeriod (g L θ₀ : ℝ) : ℝ :=
  4 * ∫ θ in Ioo 0 θ₀, pendulumPeriodIntegrand g L θ₀ θ

/-- The substitution `θ = 2 arcsin (κ sin φ)`, i.e. `sin (θ/2) = κ sin φ`. -/
noncomputable def pendSub (κ φ : ℝ) : ℝ := 2 * Real.arcsin (κ * Real.sin φ)

section

variable {θ₀ κ : ℝ}

private lemma kappa_facts (h0 : 0 < θ₀) (hπ : θ₀ < π) (hκ : κ = Real.sin (θ₀ / 2)) :
    0 < κ ∧ κ < 1 ∧ 0 < Real.cos (θ₀ / 2) ∧ Real.cos θ₀ = 1 - 2 * κ ^ 2 := by
  have hc : 0 < Real.cos (θ₀ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < Real.sin (θ₀ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2 := Real.sin_sq_add_cos_sq (θ₀ / 2)
  refine ⟨hκ ▸ hs, ?_, hc, ?_⟩
  · rw [hκ]; nlinarith
  · have : Real.cos θ₀ = 2 * Real.cos (θ₀ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; congr 1; ring
    rw [this, hκ]
    nlinarith

private lemma arg_facts (hk0 : 0 < κ) (hk1 : κ < 1) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) :
    0 < κ * Real.sin φ ∧ κ * Real.sin φ < κ ∧ 0 < 1 - (κ * Real.sin φ) ^ 2 := by
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have := Real.sin_sq_add_cos_sq φ
    nlinarith
  have h2 : κ * Real.sin φ < κ := by nlinarith
  have h1 := mul_pos hk0 hs
  exact ⟨h1, h2, by nlinarith⟩

private lemma pendSub_deriv (hk0 : 0 < κ) (hk1 : κ < 1) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) :
    HasDerivAt (pendSub κ) (2 * (1 / √(1 - (κ * Real.sin φ) ^ 2) * (κ * Real.cos φ))) φ := by
  obtain ⟨h1, h2, h3⟩ := arg_facts hk0 hk1 hφ
  have h : HasDerivAt (fun x => κ * Real.sin x) (κ * Real.cos φ) φ := (Real.hasDerivAt_sin φ).const_mul κ
  have h4 : κ * Real.sin φ ≠ -1 := by intro e; linarith
  have h5 : κ * Real.sin φ ≠ 1 := by intro e; linarith
  have h6 := HasDerivAt.comp (h₂ := Real.arcsin) (h := fun x => κ * Real.sin x) φ
    (Real.hasDerivAt_arcsin h4 h5) h
  have h8 := HasDerivAt.const_mul (2:ℝ) h6
  exact h8

private lemma pendSub_pos_deriv (hk0 : 0 < κ) (hk1 : κ < 1) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) :
    0 < 2 * (1 / √(1 - (κ * Real.sin φ) ^ 2) * (κ * Real.cos φ)) := by
  obtain ⟨h1, h2, h3⟩ := arg_facts hk0 hk1 hφ
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  have := Real.sqrt_pos.mpr h3
  positivity

private lemma pendSub_injOn (hk0 : 0 < κ) (hk1 : κ < 1) : InjOn (pendSub κ) (Ioo 0 (π / 2)) := by
  intro a ha b hb hab
  obtain ⟨a1, a2, _⟩ := arg_facts hk0 hk1 ha
  obtain ⟨b1, b2, _⟩ := arg_facts hk0 hk1 hb
  have h : Real.arcsin (κ * Real.sin a) = Real.arcsin (κ * Real.sin b) := by
    unfold pendSub at hab; linarith
  have h' := Real.injOn_arcsin (show κ * Real.sin a ∈ Icc (-1:ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show κ * Real.sin b ∈ Icc (-1:ℝ) 1 from ⟨by linarith, by linarith⟩) h
  have h'' : Real.sin a = Real.sin b := mul_left_cancel₀ hk0.ne' h'
  exact Real.injOn_sin ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩ ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩ h''

private lemma pendSub_image (h0 : 0 < θ₀) (hπ : θ₀ < π) (hκ : κ = Real.sin (θ₀ / 2)) :
    pendSub κ '' Ioo 0 (π / 2) = Ioo 0 θ₀ := by
  obtain ⟨hk0, hk1, hc, _⟩ := kappa_facts h0 hπ hκ
  have harc : Real.arcsin κ = θ₀ / 2 := by
    rw [hκ]; exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
  ext θ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2, _⟩ := arg_facts hk0 hk1 hφ
    have a1 : 0 < Real.arcsin (κ * Real.sin φ) := Real.arcsin_pos.mpr h1
    have a2 : Real.arcsin (κ * Real.sin φ) < Real.arcsin κ :=
      Real.arcsin_lt_arcsin (by linarith) h2 hk1.le
    unfold pendSub
    constructor <;> linarith
  · rintro ⟨t1, t2⟩
    have hs0 : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hslt : Real.sin (θ / 2) < κ := by
      rw [hκ]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
    have hx0 : 0 < Real.sin (θ / 2) / κ := div_pos hs0 hk0
    have hx1 : Real.sin (θ / 2) / κ < 1 := (div_lt_one hk0).mpr hslt
    refine ⟨Real.arcsin (Real.sin (θ / 2) / κ), ⟨Real.arcsin_pos.mpr hx0, ?_⟩, ?_⟩
    · have := Real.arcsin_lt_arcsin (show -1 ≤ Real.sin (θ / 2) / κ by linarith) hx1 le_rfl
      rwa [Real.arcsin_one] at this
    · unfold pendSub
      rw [Real.sin_arcsin (by linarith) hx1.le, mul_div_cancel₀ _ hk0.ne',
        Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
      ring

private lemma pendSub_integrand {g L θ₀ κ : ℝ} (hg : 0 < g) (hL : 0 < L) (h0 : 0 < θ₀) (hπ : θ₀ < π)
    (hκ : κ = Real.sin (θ₀ / 2)) {φ : ℝ} (hφ : φ ∈ Ioo 0 (π / 2)) :
    |2 * (1 / √(1 - (κ * Real.sin φ) ^ 2) * (κ * Real.cos φ))| •
        pendulumPeriodIntegrand g L θ₀ (pendSub κ φ)
      = √(L / g) * (1 / √(1 - κ ^ 2 * Real.sin φ ^ 2)) := by
  obtain ⟨hk0, hk1, _, hcθ⟩ := kappa_facts h0 hπ hκ
  obtain ⟨h1, h2, h3⟩ := arg_facts hk0 hk1 hφ
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  rw [abs_of_pos (pendSub_pos_deriv hk0 hk1 hφ)]
  have hcos : Real.cos (pendSub κ φ) = 1 - 2 * (κ * Real.sin φ) ^ 2 := by
    unfold pendSub
    rw [Real.cos_two_mul, Real.cos_sq', Real.sin_arcsin (by linarith) (by linarith)]
    ring
  have hsc := Real.sin_sq_add_cos_sq φ
  have hgL : 0 < g / L := div_pos hg hL
  have hsq : 2 * g / L * (Real.cos (pendSub κ φ) - Real.cos θ₀)
      = (2 * κ * Real.cos φ * √(g / L)) ^ 2 := by
    rw [hcos, hcθ]
    simp only [mul_pow, Real.sq_sqrt hgL.le]
    have : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by linarith
    rw [this]
    field_simp
    ring
  unfold pendulumPeriodIntegrand
  rw [hsq, Real.sqrt_sq (by positivity)]
  have hD : 1 - κ ^ 2 * Real.sin φ ^ 2 = 1 - (κ * Real.sin φ) ^ 2 := by ring
  rw [hD, show L / g = (g / L)⁻¹ by rw [inv_div], Real.sqrt_inv]
  have hD0 : 0 < √(1 - (κ * Real.sin φ) ^ 2) := Real.sqrt_pos.mpr h3
  have hG0 : 0 < √(g / L) := Real.sqrt_pos.mpr hgL
  rw [smul_eq_mul]
  field_simp

/-- Change of variables for the period integral: the integrand is integrable on `(0, θ₀)` and the integral equals
`√(L/g) ∫_0^{π/2} dφ / √(1 - κ² sin² φ)`. -/
theorem pendulum_period_integral_eq {g L θ₀ : ℝ} (hg : 0 < g) (hL : 0 < L) (h0 : 0 < θ₀) (hπ : θ₀ < π) :
    IntegrableOn (pendulumPeriodIntegrand g L θ₀) (Ioo 0 θ₀) ∧
      ∫ θ in Ioo 0 θ₀, pendulumPeriodIntegrand g L θ₀ θ
        = √(L / g) * ∫ φ in Ioo 0 (π / 2), 1 / √(1 - Real.sin (θ₀ / 2) ^ 2 * Real.sin φ ^ 2) := by
  set κ := Real.sin (θ₀ / 2) with hκ
  obtain ⟨hk0, hk1, _, _⟩ := kappa_facts h0 hπ hκ
  have hder : ∀ x ∈ Ioo 0 (π / 2), HasDerivWithinAt (pendSub κ)
      (2 * (1 / √(1 - (κ * Real.sin x) ^ 2) * (κ * Real.cos x))) (Ioo 0 (π / 2)) x :=
    fun x hx => (pendSub_deriv hk0 hk1 hx).hasDerivWithinAt
  have hinj := pendSub_injOn hk0 hk1
  have himg := pendSub_image h0 hπ hκ
  have hEq : EqOn (fun x => |2 * (1 / √(1 - (κ * Real.sin x) ^ 2) * (κ * Real.cos x))| •
        pendulumPeriodIntegrand g L θ₀ (pendSub κ x))
      (fun φ => √(L / g) * (1 / √(1 - κ ^ 2 * Real.sin φ ^ 2))) (Ioo 0 (π / 2)) :=
    fun φ hφ => pendSub_integrand hg hL h0 hπ hκ hφ
  have hcont : Continuous (fun φ => √(L / g) * (1 / √(1 - κ ^ 2 * Real.sin φ ^ 2))) := by
    refine continuous_const.mul (continuous_const.div (by fun_prop) fun φ => ?_)
    have : 0 < 1 - κ ^ 2 * Real.sin φ ^ 2 := by
      nlinarith [Real.sin_sq_le_one φ, sq_nonneg κ, mul_nonneg (sq_nonneg κ) (sq_nonneg (Real.sin φ))]
    exact (Real.sqrt_pos.mpr this).ne'
  have hint : IntegrableOn (fun φ => √(L / g) * (1 / √(1 - κ ^ 2 * Real.sin φ ^ 2))) (Ioo 0 (π / 2)) :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hder hinj
    (pendulumPeriodIntegrand g L θ₀)
  rw [himg] at hiff
  have hI : IntegrableOn (pendulumPeriodIntegrand g L θ₀) (Ioo 0 θ₀) :=
    hiff.mpr ((integrableOn_congr_fun hEq measurableSet_Ioo).mpr hint)
  refine ⟨hI, ?_⟩
  have := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (pendulumPeriodIntegrand g L θ₀)
  rw [himg] at this
  rw [this, setIntegral_congr_fun measurableSet_Ioo hEq, integral_const_mul]

/-- The elliptic-type integral `∫_0^{π/2} dφ / √(1 - κ² sin² φ)` (Lebesgue integral over `(0, π/2)`). -/
noncomputable def pendulumEllipticIntegral (κ : ℝ) : ℝ :=
  ∫ φ in Ioo 0 (π / 2), 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2)

private lemma ell_arg_pos (hk1 : κ < 1) (hk0 : 0 ≤ κ) (φ : ℝ) : 0 < 1 - κ ^ 2 * Real.sin φ ^ 2 := by
  nlinarith [Real.sin_sq_le_one φ, sq_nonneg κ, mul_nonneg (sq_nonneg κ) (sq_nonneg (Real.sin φ))]

private lemma ell_cont (hk1 : κ < 1) (hk0 : 0 ≤ κ) :
    Continuous (fun φ => 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2)) := by
  refine continuous_const.div (by fun_prop) fun φ => ?_
  exact (Real.sqrt_pos.mpr (ell_arg_pos hk1 hk0 φ)).ne'

/-- **Period of the pendulum, reduction (DE-228).** For `g, L > 0` and `0 < θ₀ < π`, the improper integral
`∫_0^{θ₀} dθ / √((2g/L)(cos θ - cos θ₀))` converges (the integrand is Lebesgue integrable on `(0, θ₀)`), and
`T(θ₀) = 4 √(L/g) ∫_0^{π/2} dφ / √(1 - κ² sin² φ)` with `κ = sin (θ₀/2)`. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_period_eq {g L θ₀ : ℝ} (hg : 0 < g) (hL : 0 < L) (h0 : 0 < θ₀) (hπ : θ₀ < π) :
    IntegrableOn (pendulumPeriodIntegrand g L θ₀) (Ioo 0 θ₀) ∧
      pendulumPeriod g L θ₀
        = 4 * √(L / g) * ∫ φ in (0:ℝ)..(π / 2), 1 / √(1 - Real.sin (θ₀ / 2) ^ 2 * Real.sin φ ^ 2) := by
  obtain ⟨hI, he⟩ := pendulum_period_integral_eq hg hL h0 hπ
  refine ⟨hI, ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  unfold pendulumPeriod
  rw [he]; ring

private lemma ell_gt (hk0 : 0 < κ) (hk1 : κ < 1) : π / 2 < pendulumEllipticIntegral κ := by
  have hc := ell_cont hk1 hk0.le
  have hint : IntegrableOn (fun φ => 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2)) (Ioo 0 (π / 2)) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint1 : IntegrableOn (fun φ : ℝ => (1:ℝ)) (Ioo 0 (π / 2)) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hgt : ∀ φ ∈ Ioo 0 (π / 2), 1 < 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2) := by
    intro φ hφ
    have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (by linarith [hφ.2, Real.pi_pos])
    have h1 := ell_arg_pos hk1 hk0.le φ
    have h2 : 1 - κ ^ 2 * Real.sin φ ^ 2 < 1 := by nlinarith [mul_pos (pow_pos hk0 2) (pow_pos hs 2)]
    refine one_lt_one_div (Real.sqrt_pos.mpr h1) ?_
    rw [Real.sqrt_lt' one_pos]; linarith
  have hsub : IntegrableOn (fun φ => 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2) - 1) (Ioo 0 (π / 2)) :=
    hint.sub hint1
  have hpos : 0 < ∫ φ in Ioo 0 (π / 2), (1 / √(1 - κ ^ 2 * Real.sin φ ^ 2) - 1) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioo fun φ hφ => by
        simp only [Pi.zero_apply]; linarith [hgt φ hφ])
      hsub]
    have : Function.support (fun φ => 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2) - 1) ∩ Ioo 0 (π / 2)
        = Ioo 0 (π / 2) := by
      ext φ
      simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro hφ; linarith [hgt φ hφ]
    rw [this, Real.volume_Ioo]
    simp [Real.pi_pos]
  rw [integral_sub hint hint1] at hpos
  unfold pendulumEllipticIntegral
  have hc1 : ∫ φ in Ioo 0 (π / 2), (1:ℝ) = π / 2 := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  linarith

/-- **The pendulum is slower than its linearization (DE-228).** For `0 < θ₀ < π`, `T(θ₀) > 2π √(L/g)`, the
period of the linearized pendulum. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_period_gt_linear {g L θ₀ : ℝ} (hg : 0 < g) (hL : 0 < L) (h0 : 0 < θ₀) (hπ : θ₀ < π) :
    2 * π * √(L / g) < pendulumPeriod g L θ₀ := by
  obtain ⟨hk0, hk1, _, _⟩ := kappa_facts h0 hπ rfl
  obtain ⟨_, he⟩ := pendulum_period_integral_eq hg hL h0 hπ
  have := ell_gt hk0 hk1
  unfold pendulumEllipticIntegral at this
  unfold pendulumPeriod
  rw [he]
  have hs : 0 < √(L / g) := Real.sqrt_pos.mpr (div_pos hL hg)
  nlinarith

private lemma ell_ge_log {θ₀ : ℝ} (h0 : 0 < θ₀) (hπ : θ₀ < π) :
    Real.log ((π / 2 + Real.cos (θ₀ / 2)) / Real.cos (θ₀ / 2))
      ≤ pendulumEllipticIntegral (Real.sin (θ₀ / 2)) := by
  obtain ⟨hk0, hk1, hε, _⟩ := kappa_facts h0 hπ (κ := Real.sin (θ₀ / 2)) rfl
  set ε := Real.cos (θ₀ / 2) with hεdef
  set κ := Real.sin (θ₀ / 2) with hκ
  have hsc : κ ^ 2 + ε ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc := ell_cont hk1 hk0.le
  have hint : IntegrableOn (fun φ => 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2)) (Ioo 0 (π / 2)) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun φ : ℝ => 1 / (ε + (π / 2 - φ))) (Ioo 0 (π / 2)) := by
    have hco : ContinuousOn (fun φ : ℝ => 1 / (ε + (π / 2 - φ))) (Icc 0 (π / 2)) := by
      refine continuousOn_const.div (continuousOn_const.add (continuousOn_const.sub continuousOn_id))
        fun φ hφ => ?_
      exact (by linarith [hφ.2] : 0 < ε + (π / 2 - φ)).ne'
    exact hco.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hle : ∀ φ ∈ Ioo 0 (π / 2), 1 / (ε + (π / 2 - φ)) ≤ 1 / √(1 - κ ^ 2 * Real.sin φ ^ 2) := by
    intro φ hφ
    have hu : 0 < π / 2 - φ := by linarith [hφ.2]
    have hcφ : Real.cos φ ≤ π / 2 - φ := by
      rw [← Real.sin_pi_div_two_sub]; exact Real.sin_le hu.le
    have hcφ0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1, Real.pi_pos], hφ.2.le⟩
    have hs2 := Real.sin_sq_add_cos_sq φ
    have hpos := Real.sqrt_pos.mpr (ell_arg_pos hk1 hk0.le φ)
    have hsq : √(1 - κ ^ 2 * Real.sin φ ^ 2) ≤ ε + (π / 2 - φ) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg hcφ0 hu.le, mul_nonneg hε.le hu.le, sq_nonneg κ,
        mul_nonneg (sq_nonneg κ) (sq_nonneg (Real.cos φ)), mul_le_mul hcφ hcφ hcφ0 hu.le]
    exact one_div_le_one_div_of_le hpos hsq
  have hmono := setIntegral_mono_on hint2 hint measurableSet_Ioo hle
  have hval : ∫ φ in Ioo 0 (π / 2), 1 / (ε + (π / 2 - φ)) = Real.log ((π / 2 + ε) / ε) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have e1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2)
      (fun y : ℝ => (ε + y)⁻¹) (π / 2)
    have e2 := intervalIntegral.integral_comp_add_left (a := π / 2 - π / 2) (b := π / 2 - 0)
      (fun y : ℝ => y⁻¹) ε
    have e3 := integral_inv_of_pos (a := ε + (π / 2 - π / 2)) (b := ε + (π / 2 - 0))
      (by simpa using hε) (by linarith [Real.pi_pos])
    simp only [one_div]
    rw [e1, e2, e3]
    congr 1
    ring_nf
  unfold pendulumEllipticIntegral
  linarith

/-- **The period blows up as the amplitude approaches `π` (DE-228).** `T(θ₀) → ∞` as `θ₀ → π` from the left. -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_period_tendsto_atTop {g L : ℝ} (hg : 0 < g) (hL : 0 < L) :
    Filter.Tendsto (pendulumPeriod g L) (nhdsWithin π (Iio π)) Filter.atTop := by
  have hs : 0 < 4 * √(L / g) := by have := Real.sqrt_pos.mpr (div_pos hL hg); positivity
  have hε : Filter.Tendsto (fun θ₀ : ℝ => Real.cos (θ₀ / 2)) (nhdsWithin π (Iio π)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun θ₀ : ℝ => Real.cos (θ₀ / 2)) (nhds π) (nhds (Real.cos (π / 2))) :=
        (Real.continuous_cos.comp (continuous_id.div_const 2)).tendsto π
      rw [Real.cos_pi_div_two] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ₀ hθ
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hlog : Filter.Tendsto (fun ε : ℝ => Real.log ((π / 2 + ε) / ε)) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
    have h1 : Filter.Tendsto (fun ε : ℝ => π / 2 * ε⁻¹ + 1) (nhdsWithin 0 (Ioi 0)) Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _
        (tendsto_inv_nhdsGT_zero.const_mul_atTop (by linarith [Real.pi_pos]))
    have h2 : Filter.Tendsto (fun ε : ℝ => (π / 2 + ε) / ε) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have : ε ≠ 0 := (show (0:ℝ) < ε from hε).ne'
      field_simp
    exact Real.tendsto_log_atTop.comp h2
  have hmain : Filter.Tendsto (fun θ₀ : ℝ => 4 * √(L / g) * Real.log ((π / 2 + Real.cos (θ₀ / 2)) / Real.cos (θ₀ / 2)))
      (nhdsWithin π (Iio π)) Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hs (hlog.comp hε)
  refine Filter.tendsto_atTop_mono' _ ?_ hmain
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with θ₀ hθ
  obtain ⟨_, he⟩ := pendulum_period_integral_eq hg hL hθ.1 hθ.2
  have hge := ell_ge_log hθ.1 hθ.2
  unfold pendulumEllipticIntegral at hge
  unfold pendulumPeriod
  rw [he]
  nlinarith

/-- **A quarter of the period is the time to swing from `θ₀` to `0` (DE-228).** Let `θ'' = -(g/L) sin θ`
(written as `θ' = ω`, `ω' = -(g/L) sin θ`) with `θ(0) = θ₀`, `θ'(0) = 0`.  If `θ` reaches `0` at time `t₁ > 0`
with `θ' < 0` on `(0, t₁]`, then `t₁ = T(θ₀)/4`.  (Special case: only the monotone first quarter swing, with
`T(θ₀)` the Lebesgue integral defined above; no condition `θ₀ < π` is needed in this statement.) -/
@[kb "lebldiffyqs2026" "§8.3.1 Period of the pendulum, p. 366"]
theorem pendulum_quarter_period {g L θ₀ t₁ : ℝ} {θ ω : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (ω t) t)
    (hω : ∀ t, HasDerivAt ω (-(g / L * Real.sin (θ t))) t) (h0 : θ 0 = θ₀) (hω0 : ω 0 = 0)
    (ht₁ : 0 < t₁) (hend : θ t₁ = 0) (hneg : ∀ t ∈ Ioc 0 t₁, ω t < 0) :
    t₁ = pendulumPeriod g L θ₀ / 4 := by
  have hcont : ContinuousOn θ (Icc 0 t₁) := fun t _ => (hθ t).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn θ (Icc 0 t₁) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 t₁) hcont (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hθ x).deriv]
      exact hneg x ⟨hx.1, hx.2.le⟩)
  have himg : θ '' Ioo 0 t₁ = Ioo 0 θ₀ := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      have h1 := hanti (show (0:ℝ) ∈ Icc 0 t₁ from ⟨le_rfl, ht₁.le⟩) (Ioo_subset_Icc_self ht) ht.1
      have h2 := hanti (Ioo_subset_Icc_self ht) (show t₁ ∈ Icc 0 t₁ from ⟨ht₁.le, le_rfl⟩) ht.2
      rw [h0] at h1; rw [hend] at h2
      exact ⟨h2, h1⟩
    · have := intermediate_value_Ioo' ht₁.le hcont
      rwa [hend, h0] at this
  have hder : ∀ x ∈ Ioo 0 t₁, HasDerivWithinAt θ (ω x) (Ioo 0 t₁) x :=
    fun x _ => (hθ x).hasDerivWithinAt
  have hinj : InjOn θ (Ioo 0 t₁) := hanti.injOn.mono Ioo_subset_Icc_self
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (pendulumPeriodIntegrand g L θ₀)
  rw [himg] at key
  have hone : ∀ t ∈ Ioo 0 t₁, |ω t| • pendulumPeriodIntegrand g L θ₀ (θ t) = 1 := by
    intro t ht
    have hneg' := hneg t ⟨ht.1, ht.2.le⟩
    have hE := pendulum_released_energy hθ hω h0 hω0 t
    unfold pendulumPeriodIntegrand
    rw [← hE, Real.sqrt_sq_eq_abs, smul_eq_mul]
    have : 0 < |ω t| := abs_pos.mpr hneg'.ne
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hone] at key
  have hc1 : ∫ t in Ioo 0 t₁, (1:ℝ) = t₁ := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  unfold pendulumPeriod
  rw [key, hc1]
  ring

end

end UndergradKB.DifferentialEquations
