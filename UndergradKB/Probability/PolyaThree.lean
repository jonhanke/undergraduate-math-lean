import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.PolyaRecurrence

/-!
# Probability: the simple random walk on `ℤ³` is transient (Grinstead–Snell, Example 12.3)

By Fourier inversion on the torus, the probability that the walk is at the origin at time `N` is
`(2π)⁻³ ∫ Ψ^N` over `[-π, π]³`, where `Ψ(θ) = (cos θ₁ + cos θ₂ + cos θ₃) / 3`.  Summing over `N` and using
`1 - Ψ ≥ c |θ|²` together with the integrability of `|θ|⁻²` in dimension three (via the
arithmetic–geometric mean inequality) shows `∑ u_N < ∞`.  The renewal theory of `PolyaRecurrence` then
gives that the first-return probabilities sum to a number `< 1`.
-/

open MeasureTheory Complex Set
open scoped Real

namespace UndergradKB.Probability.Polya

namespace Three

/-- Lebesgue measure on `[-π, π]`. -/
noncomputable def μπ : Measure ℝ := volume.restrict (Icc (-π) π)

instance : IsFiniteMeasure μπ := by unfold μπ; infer_instance

/-- The measure on `[-π, π]³`. -/
noncomputable def ν : Measure (ℝ × ℝ × ℝ) := μπ.prod (μπ.prod μπ)

instance : IsFiniteMeasure ν := by unfold ν; infer_instance

theorem integral_cexp_int (m : ℤ) :
    ∫ t, cexp (I * t * m) ∂μπ = if m = 0 then (2 * π : ℂ) else 0 := by
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  have h : ∫ t, cexp (I * t * m) ∂μπ = ∫ t in (-π)..π, cexp (I * t * m) := by
    rw [intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc]; rfl
  rw [h]
  by_cases hm : m = 0
  · subst hm
    simp
    ring
  · simp only [hm, ↓reduceIte]
    have hc : I * (m : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hm)
    have : (fun t : ℝ => cexp (I * t * m)) = fun t : ℝ => cexp ((I * m) * t) := by
      funext t; ring_nf
    rw [this, integral_exp_mul_complex hc, div_eq_zero_iff]
    left
    rw [sub_eq_zero]
    have h1 : cexp (I * m * π) = cexp (I * m * (-π : ℝ)) * cexp (m * (2 * π * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `∫_{[-π,π]³} e^{i θ·v} = (2π)³ · 1[v = 0]` for `v ∈ ℤ³`. -/
theorem integral_cexp_dot (v : Fin 3 → ℤ) :
    ∫ θ, cexp (I * (θ.1 * v 0 + θ.2.1 * v 1 + θ.2.2 * v 2)) ∂ν =
      (2 * π : ℂ) ^ 3 * (if v = 0 then 1 else 0) := by
  have e : ∀ θ : ℝ × ℝ × ℝ, cexp (I * (θ.1 * v 0 + θ.2.1 * v 1 + θ.2.2 * v 2)) =
      cexp (I * θ.1 * (v 0 : ℤ)) * (cexp (I * θ.2.1 * (v 1 : ℤ)) * cexp (I * θ.2.2 * (v 2 : ℤ))) := by
    intro θ
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [e]
  unfold ν
  rw [integral_prod_mul (μ := μπ) (ν := μπ.prod μπ) (fun t : ℝ => cexp (I * t * (v 0 : ℤ)))
    (fun p : ℝ × ℝ => cexp (I * p.1 * (v 1 : ℤ)) * cexp (I * p.2 * (v 2 : ℤ)))]
  rw [integral_prod_mul (μ := μπ) (ν := μπ) (fun t : ℝ => cexp (I * t * (v 1 : ℤ)))
    (fun t : ℝ => cexp (I * t * (v 2 : ℤ)))]
  rw [integral_cexp_int, integral_cexp_int, integral_cexp_int]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0 <;>
    simp [h0, h1, h2, funext_iff, Fin.forall_fin_succ, pow_succ] <;> ring

/-- The averaged cosine `Ψ(θ) = (cos θ₁ + cos θ₂ + cos θ₃)/3`. -/
noncomputable def Ψ (θ : ℝ × ℝ × ℝ) : ℝ := (Real.cos θ.1 + Real.cos θ.2.1 + Real.cos θ.2.2) / 3

/-- The Fourier weight of one step. -/
noncomputable def gstep (θ : ℝ × ℝ × ℝ) (s : Fin 3 × Bool) : ℂ :=
  cexp (I * (θ.1 * (simpleStep 3 s 0 : ℤ) + θ.2.1 * (simpleStep 3 s 1 : ℤ) +
    θ.2.2 * (simpleStep 3 s 2 : ℤ)))

theorem sum_gstep (θ : ℝ × ℝ × ℝ) : ∑ s : Fin 3 × Bool, gstep θ s = ((6 * Ψ θ : ℝ) : ℂ) := by
  simp only [gstep, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, simpleStep,
    Pi.single_apply, Ψ]
  simp
  push_cast
  simp only [Complex.cos, mul_comm I]
  ring_nf

theorem prod_gstep {N : ℕ} (ω : Fin N → Fin 3 × Bool) (θ : ℝ × ℝ × ℝ) :
    ∏ i, gstep θ (ω i) = cexp (I * (θ.1 * (pos (simpleStep 3) ω N 0 : ℤ) +
      θ.2.1 * (pos (simpleStep 3) ω N 1 : ℤ) + θ.2.2 * (pos (simpleStep 3) ω N 2 : ℤ))) := by
  unfold gstep
  rw [← Complex.exp_sum, pos_of_le (simpleStep 3) ω le_rfl]
  congr 1
  simp only [Finset.sum_apply, Int.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

theorem norm_gstep (θ : ℝ × ℝ × ℝ) (s : Fin 3 × Bool) : ‖gstep θ s‖ = 1 := by
  unfold gstep
  have : I * ((θ.1 : ℂ) * ((simpleStep 3 s 0 : ℤ) : ℂ) + (θ.2.1 : ℂ) * ((simpleStep 3 s 1 : ℤ) : ℂ) +
      (θ.2.2 : ℂ) * ((simpleStep 3 s 2 : ℤ) : ℂ)) =
      ((θ.1 * (simpleStep 3 s 0 : ℤ) + θ.2.1 * (simpleStep 3 s 1 : ℤ) +
        θ.2.2 * (simpleStep 3 s 2 : ℤ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_gstep (s : Fin 3 × Bool) : Continuous fun θ => gstep θ s := by
  unfold gstep; fun_prop

theorem integrable_prod_gstep {N : ℕ} (ω : Fin N → Fin 3 × Bool) :
    Integrable (fun θ => ∏ i, gstep θ (ω i)) ν := by
  refine Integrable.of_bound (C := 1)
    (continuous_finsetProd _ fun i _ => continuous_gstep (ω i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => ?_)
  rw [norm_prod]
  simp [norm_gstep]

/-- Fourier formula for the return probability of the simple walk on `ℤ³`. -/
theorem zeroCount_integral (N : ℕ) :
    ((zeroCount (simpleStep 3) N : ℕ) : ℂ) * (2 * π) ^ 3 = ∫ θ, ((6 * Ψ θ : ℝ) : ℂ) ^ N ∂ν := by
  have h1 : ∀ ω : Fin N → Fin 3 × Bool,
      (if pos (simpleStep 3) ω N = 0 then (2 * π : ℂ) ^ 3 else 0) =
        ∫ θ, ∏ i, gstep θ (ω i) ∂ν := by
    intro ω
    simp_rw [prod_gstep]
    rw [integral_cexp_dot (pos (simpleStep 3) ω N)]
    split_ifs <;> simp
  have hc : ((zeroCount (simpleStep 3) N : ℕ) : ℂ) * (2 * π) ^ 3 =
      ∑ ω : Fin N → Fin 3 × Bool, (if pos (simpleStep 3) ω N = 0 then (2 * π : ℂ) ^ 3 else 0) := by
    unfold zeroCount
    rw [Finset.card_filter]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp
  rw [hc]
  simp_rw [h1]
  rw [← integral_finsetSum _ fun ω _ => integrable_prod_gstep ω]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only
  rw [← sum_gstep θ, Fintype.sum_pow]

theorem u_three_integral (N : ℕ) :
    u (simpleStep 3) N = ((2 * π) ^ 3)⁻¹ * ∫ θ, Ψ θ ^ N ∂ν := by
  have h := zeroCount_integral N
  have h2 : ∫ θ, ((6 * Ψ θ : ℝ) : ℂ) ^ N ∂ν = ((6 : ℝ) ^ N * ∫ θ, Ψ θ ^ N ∂ν : ℝ) := by
    have : ∀ θ, ((6 * Ψ θ : ℝ) : ℂ) ^ N = (((6 : ℝ) ^ N * Ψ θ ^ N : ℝ) : ℂ) := by
      intro θ; push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal, integral_const_mul]
  rw [h2] at h
  have h3 : (zeroCount (simpleStep 3) N : ℝ) * (2 * π) ^ 3 = (6 : ℝ) ^ N * ∫ θ, Ψ θ ^ N ∂ν := by
    exact_mod_cast h
  unfold u
  have hc : (Fintype.card (Fin 3 × Bool) : ℝ) = 6 := by simp
  rw [hc]
  have h6 : (6 : ℝ) ^ N ≠ 0 := by positivity
  have hpi : (2 * π) ^ 3 ≠ 0 := by positivity
  field_simp
  linarith

/-- Jordan-type lower bound `1 - cos x ≥ 2x²/π²` on `[-π, π]`. -/
theorem one_sub_cos_ge {x : ℝ} (h : |x| ≤ π) : 2 * x ^ 2 / π ^ 2 ≤ 1 - Real.cos x := by
  have hpi := Real.pi_pos
  have h1 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have := Real.cos_two_mul (x / 2)
    have h2 := Real.sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    nlinarith
  have h3 : 2 / π * (|x| / 2) ≤ Real.sin (|x| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith [abs_nonneg x])
  have h4 : Real.sin (|x| / 2) ^ 2 = Real.sin (x / 2) ^ 2 := by
    rcases abs_cases x with ⟨h5, _⟩ | ⟨h5, _⟩
    · rw [h5]
    · rw [h5, neg_div, Real.sin_neg, neg_sq]
  have h5 : (2 / π * (|x| / 2)) ^ 2 ≤ Real.sin (|x| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h6 : (2 / π * (|x| / 2)) ^ 2 = x ^ 2 / π ^ 2 := by
    rw [mul_pow, div_pow, div_pow, sq_abs]; field_simp
  rw [h1]
  have : x ^ 2 / π ^ 2 ≤ Real.sin (x / 2) ^ 2 := by rw [← h6, ← h4]; exact h5
  have e : 2 * x ^ 2 / π ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  rw [e]
  linarith

/-- AM–GM for three squares. -/
theorem amgm3 {a b c : ℝ} :
    3 * ((a ^ 2) ^ (1 / 3 : ℝ) * (b ^ 2) ^ (1 / 3 : ℝ) * (c ^ 2) ^ (1 / 3 : ℝ)) ≤
      a ^ 2 + b ^ 2 + c ^ 2 := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (p₁ := a ^ 2) (p₂ := b ^ 2) (p₃ := c ^ 2) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by positivity) (by norm_num)
  linarith

theorem sq_rpow_third (a : ℝ) : (a ^ 2) ^ (1 / 3 : ℝ) = |a| ^ (2 / 3 : ℝ) := by
  rw [← sq_abs a, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg a)]
  norm_num

/-- The pointwise majorant of the partial sums of `Ψ^N`. -/
theorem geom_sum_le {θ : ℝ × ℝ × ℝ} (ha : |θ.1| ≤ π) (hb : |θ.2.1| ≤ π) (hc : |θ.2.2| ≤ π)
    (ha0 : θ.1 ≠ 0) (hb0 : θ.2.1 ≠ 0) (hc0 : θ.2.2 ≠ 0) (M : ℕ) :
    ∑ N ∈ Finset.range (M + 1), Ψ θ ^ N ≤
      π ^ 2 * (|θ.1| ^ (-(2 / 3) : ℝ) * (|θ.2.1| ^ (-(2 / 3) : ℝ) * |θ.2.2| ^ (-(2 / 3) : ℝ))) := by
  have hpi := Real.pi_pos
  obtain ⟨a, b, c⟩ := θ
  simp only at ha hb hc ha0 hb0 hc0 ⊢
  set S := a ^ 2 + b ^ 2 + c ^ 2 with hS
  have hSpos : 0 < S := by positivity
  have h1 := one_sub_cos_ge ha
  have h2 := one_sub_cos_ge hb
  have h3 := one_sub_cos_ge hc
  have hΨ : 1 - Ψ (a, b, c) = ((1 - Real.cos a) + (1 - Real.cos b) + (1 - Real.cos c)) / 3 := by
    unfold Ψ; simp only; ring
  have hlow : 2 * S / (3 * π ^ 2) ≤ 1 - Ψ (a, b, c) := by
    rw [hΨ]
    have : 2 * S / (3 * π ^ 2) = (2 * a ^ 2 / π ^ 2 + 2 * b ^ 2 / π ^ 2 + 2 * c ^ 2 / π ^ 2) / 3 := by
      rw [hS]; field_simp
    rw [this]
    linarith
  have hpos : 0 < 1 - Ψ (a, b, c) := lt_of_lt_of_le (by positivity) hlow
  have hΨabs : |Ψ (a, b, c)| ≤ 1 := by
    unfold Ψ; simp only
    rw [abs_le]
    have := Real.neg_one_le_cos a; have := Real.neg_one_le_cos b; have := Real.neg_one_le_cos c
    have := Real.cos_le_one a; have := Real.cos_le_one b; have := Real.cos_le_one c
    constructor <;> linarith
  have hne : Ψ (a, b, c) ≠ 1 := by intro h; linarith
  have hgeo : ∑ N ∈ Finset.range (M + 1), Ψ (a, b, c) ^ N ≤ 2 / (1 - Ψ (a, b, c)) := by
    rw [geom_sum_eq hne, ← neg_div_neg_eq]
    rw [show -(Ψ (a, b, c) - 1) = 1 - Ψ (a, b, c) by ring]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have := abs_le.1 ((abs_pow _ _).le.trans (pow_le_one₀ (abs_nonneg _) hΨabs : |Ψ (a, b, c)| ^ (M + 1) ≤ 1))
    linarith [this.1]
  refine hgeo.trans ?_
  have h4 : 2 / (1 - Ψ (a, b, c)) ≤ 3 * π ^ 2 / S := by
    calc 2 / (1 - Ψ (a, b, c)) ≤ 2 / (2 * S / (3 * π ^ 2)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow
      _ = 3 * π ^ 2 / S := by field_simp
  refine h4.trans ?_
  have hA := amgm3 (a := a) (b := b) (c := c)
  rw [sq_rpow_third, sq_rpow_third, sq_rpow_third] at hA
  have hP : 0 < |a| ^ (2 / 3 : ℝ) * |b| ^ (2 / 3 : ℝ) * |c| ^ (2 / 3 : ℝ) := by
    have := abs_pos.2 ha0; have := abs_pos.2 hb0; have := abs_pos.2 hc0
    positivity
  have e : π ^ 2 * (|a| ^ (-(2 / 3) : ℝ) * (|b| ^ (-(2 / 3) : ℝ) * |c| ^ (-(2 / 3) : ℝ))) =
      π ^ 2 / (|a| ^ (2 / 3 : ℝ) * |b| ^ (2 / 3 : ℝ) * |c| ^ (2 / 3 : ℝ)) := by
    rw [Real.rpow_neg (abs_nonneg a), Real.rpow_neg (abs_nonneg b), Real.rpow_neg (abs_nonneg c)]
    field_simp
  rw [e]
  calc 3 * π ^ 2 / S ≤ 3 * π ^ 2 / (3 * (|a| ^ (2 / 3 : ℝ) * |b| ^ (2 / 3 : ℝ) * |c| ^ (2 / 3 : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hA
    _ = π ^ 2 / (|a| ^ (2 / 3 : ℝ) * |b| ^ (2 / 3 : ℝ) * |c| ^ (2 / 3 : ℝ)) := by
        field_simp

/-- The singular weight `|x|^(-2/3)`, integrable on `[-π, π]`. -/
noncomputable def g1 (x : ℝ) : ℝ := |x| ^ (-(2 / 3) : ℝ)

theorem integrable_g1 : Integrable g1 μπ := by
  have hr : (-1 : ℝ) < -(2 / 3) := by norm_num
  have h0 : IntegrableOn (fun x : ℝ => x ^ (-(2 / 3) : ℝ)) (Ioc 0 π) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := π) hr).1
  have h1 : IntegrableOn g1 (Icc 0 π) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    refine h0.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [g1]
    rw [abs_of_pos hx.1]
  have h2 : IntegrableOn g1 (Icc (-π) 0) volume := by
    have hi : IntervalIntegrable (fun x : ℝ => (-x) ^ (-(2 / 3) : ℝ)) volume (-0) (-π) :=
      (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => x ^ (-(2 / 3) : ℝ))
        (by simp)).1 (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := π) hr)
    rw [neg_zero] at hi
    have hi2 : IntegrableOn (fun x : ℝ => (-x) ^ (-(2 / 3) : ℝ)) (Ioc (-π) 0) volume :=
      hi.symm.1
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    refine hi2.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp only [g1]
    rw [abs_of_nonpos hx.2]
  have h3 : IntegrableOn g1 (Icc (-π) 0 ∪ Icc 0 π) volume := h2.union h1
  refine h3.mono_set ?_
  intro x hx
  rcases le_total x 0 with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

theorem null_nullset : μπ ({0} ∪ (Icc (-π) π)ᶜ) = 0 := by
  refine measure_union_null ?_ ?_
  · unfold μπ; simp
  · unfold μπ
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp

theorem bad_null (N : Set ℝ) (hN : μπ N = 0) :
    ν {θ : ℝ × ℝ × ℝ | θ.1 ∈ N ∨ θ.2.1 ∈ N ∨ θ.2.2 ∈ N} = 0 := by
  refine measure_mono_null (t := (N ×ˢ univ) ∪ (univ ×ˢ (N ×ˢ univ)) ∪ (univ ×ˢ (univ ×ˢ N))) ?_ ?_
  · intro θ hθ
    rcases hθ with h | h | h
    · exact Or.inl (Or.inl ⟨h, trivial⟩)
    · exact Or.inl (Or.inr ⟨trivial, h, trivial⟩)
    · exact Or.inr ⟨trivial, trivial, h⟩
  · refine measure_union_null (measure_union_null ?_ ?_) ?_
    · unfold ν; rw [Measure.prod_prod]; simp [hN]
    · unfold ν; rw [Measure.prod_prod, Measure.prod_prod]; simp [hN]
    · unfold ν; rw [Measure.prod_prod, Measure.prod_prod]; simp [hN]

/-- Uniform bound on the partial sums of the return probabilities. -/
theorem partial_sum_bound (M : ℕ) :
    ∑ N ∈ Finset.range (M + 1), u (simpleStep 3) N ≤
      ((2 * π) ^ 3)⁻¹ * (π ^ 2 * (∫ x, g1 x ∂μπ) ^ 3) := by
  have hpi := Real.pi_pos
  have hΨc : Continuous Ψ := by unfold Ψ; fun_prop
  have hΨint : ∀ N : ℕ, Integrable (fun θ => Ψ θ ^ N) ν := by
    intro N
    refine Integrable.of_bound (C := 1) (hΨc.pow N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    unfold Ψ
    rw [abs_le]
    have := Real.neg_one_le_cos θ.1; have := Real.neg_one_le_cos θ.2.1
    have := Real.neg_one_le_cos θ.2.2
    have := Real.cos_le_one θ.1; have := Real.cos_le_one θ.2.1; have := Real.cos_le_one θ.2.2
    constructor <;> linarith
  have h1 : ∑ N ∈ Finset.range (M + 1), u (simpleStep 3) N =
      ((2 * π) ^ 3)⁻¹ * ∫ θ, ∑ N ∈ Finset.range (M + 1), Ψ θ ^ N ∂ν := by
    simp_rw [u_three_integral]
    rw [← Finset.mul_sum, integral_finsetSum _ fun N _ => hΨint N]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hGint : Integrable (fun θ : ℝ × ℝ × ℝ =>
      π ^ 2 * (g1 θ.1 * (g1 θ.2.1 * g1 θ.2.2))) ν :=
    ((integrable_g1.mul_prod (integrable_g1.mul_prod integrable_g1))).const_mul _
  have hGval : ∫ θ : ℝ × ℝ × ℝ, π ^ 2 * (g1 θ.1 * (g1 θ.2.1 * g1 θ.2.2)) ∂ν =
      π ^ 2 * (∫ x, g1 x ∂μπ) ^ 3 := by
    rw [integral_const_mul]
    unfold ν
    rw [integral_prod_mul (μ := μπ) (ν := μπ.prod μπ) g1 (fun p : ℝ × ℝ => g1 p.1 * g1 p.2),
      integral_prod_mul (μ := μπ) (ν := μπ) g1 g1]
    ring
  rw [← hGval]
  refine integral_mono_ae ((integrable_finsetSum _ fun N _ => hΨint N)) hGint ?_
  have hbad := bad_null _ null_nullset
  have hae := measure_eq_zero_iff_ae_notMem.1 hbad
  filter_upwards [hae] with θ hθ
  simp only [mem_setOf_eq, mem_union, mem_singleton_iff, mem_compl_iff, not_or, not_not] at hθ
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hθ
  have := geom_sum_le (abs_le.2 h1b) (abs_le.2 h2b) (abs_le.2 h3b) h1a h2a h3a M
  simpa [g1] using this

/-- The return probabilities of the simple walk on `ℤ³` are summable. -/
theorem summable_u_simple_three : Summable (u (simpleStep 3)) := by
  refine summable_of_sum_range_le (c := ((2 * π) ^ 3)⁻¹ * (π ^ 2 * (∫ x, g1 x ∂μπ) ^ 3))
    (fun N => u_nonneg _ N) (fun M => ?_)
  calc ∑ N ∈ Finset.range M, u (simpleStep 3) N ≤ ∑ N ∈ Finset.range (M + 1), u (simpleStep 3) N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ M))
          (fun N _ _ => u_nonneg _ N)
    _ ≤ _ := partial_sum_bound M

end Three

/-- Grinstead–Snell Example 12.3 (PR-127), `m = 3`. In space the simple symmetric walk is transient: the
first-return probabilities sum to `1 - 1/U` where `U = ∑ u_N` is finite, so the probability of ever
returning to the origin is strictly less than one. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem firstReturn_three_lt_one :
    HasSum (f (simpleStep 3)) (1 - (∑' N, u (simpleStep 3) N)⁻¹) ∧ ∑' N, f (simpleStep 3) N < 1 := by
  have hU := Three.summable_u_simple_three.hasSum
  have h := hasSum_f_of_hasSum_u _ hU
  refine ⟨h, ?_⟩
  rw [h.tsum_eq]
  have hpos : 0 < ∑' N, u (simpleStep 3) N := by
    have := (Three.summable_u_simple_three).sum_le_tsum (Finset.range 1)
      (fun N _ => u_nonneg _ N)
    simp [u_zero] at this
    linarith
  have := inv_pos.2 hpos
  linarith

end UndergradKB.Probability.Polya
