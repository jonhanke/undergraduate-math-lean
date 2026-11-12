import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact
import UndergradKB.Common.Attr

/-! # Beck et al., A First Course in Complex Analysis, Appendix A (Theorems from Calculus): course layer
Thin restatements in the book's terms of results Mathlib already has (checklist rows `in Mathlib`).
Beck's Green's Theorem (A.0.10) is not restated here. -/

namespace UndergradKB.ComplexAnalysis.Course.BeckA
open Set Filter Topology MeasureTheory intervalIntegral

/-- Beck Theorem A.0.1 (CX-149). Extreme-value theorem: a continuous real function on a nonempty
closed bounded subset of `ℝⁿ` attains a minimum and a maximum. -/
@[kb "beck2025" "Theorem A.0.1, p. 166"]
theorem extreme_value_theorem (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsClosed K)
    (hb : Bornology.IsBounded K) (hne : K.Nonempty) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContinuousOn f K) :
    (∃ x ∈ K, ∀ y ∈ K, f x ≤ f y) ∧ (∃ x ∈ K, ∀ y ∈ K, f y ≤ f x) := by
  have hc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK hb
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne hf
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn hne hf
  exact ⟨⟨x, hx, fun z hz => hmin hz⟩, ⟨y, hy, fun z hz => hmax hz⟩⟩

/-- Beck Theorem A.0.2 (CX-150). Mean-value theorem: if `f` is differentiable on an interval `I`
and `x, x + Δx ∈ I` with `Δx ≠ 0`, then for some `0 < a < 1`,
`(f (x + Δx) - f x) / Δx = f' (x + a Δx)`. -/
@[kb "beck2025" "Theorem A.0.2, p. 166"]
theorem mean_value_theorem (I : Set ℝ) (hI : I.OrdConnected) (f f' : ℝ → ℝ)
    (hf : ∀ t ∈ I, HasDerivAt f (f' t) t) (x Δ : ℝ) (hx : x ∈ I) (hxΔ : x + Δ ∈ I) (hΔ : Δ ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ (f (x + Δ) - f x) / Δ = f' (x + a * Δ) := by
  have hsub : ∀ {p q : ℝ}, p ∈ I → q ∈ I → p < q → ∃ c ∈ Ioo p q,
      f' c = (f q - f p) / (q - p) := by
    intro p q hp hq hpq
    refine exists_hasDerivAt_eq_slope f f' hpq ?_ fun t ht =>
      hf t (hI.out hp hq (Ioo_subset_Icc_self ht))
    exact fun t ht => (hf t (hI.out hp hq ht)).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hΔ with h | h
  · obtain ⟨c, hc, hc'⟩ := hsub hxΔ hx (by linarith)
    refine ⟨(c - x) / Δ, ?_, ?_, ?_⟩
    · exact div_pos_of_neg_of_neg (by linarith [hc.2]) h
    · rw [div_lt_one_of_neg h]; linarith [hc.1]
    · have : x + (c - x) / Δ * Δ = c := by field_simp; ring
      rw [this, hc']
      have : x - (x + Δ) = -Δ := by ring
      rw [this]
      field_simp
      ring
  · obtain ⟨c, hc, hc'⟩ := hsub hx hxΔ (by linarith)
    refine ⟨(c - x) / Δ, ?_, ?_, ?_⟩
    · exact div_pos (by linarith [hc.1]) h
    · rw [div_lt_one h]; linarith [hc.2]
    · have : x + (c - x) / Δ * Δ = c := by field_simp; ring
      rw [this, hc']
      have : x + Δ - x = Δ := by ring
      rw [this]

/-- Beck Theorem A.0.3 (CX-151), part (a). Fundamental theorem of calculus (Mathlib-shaped: `f`
continuous on all of `ℝ`): `F x = ∫_a^x f` has derivative `f x`. -/
@[kb "beck2025" "Theorem A.0.3, p. 166"]
theorem ftc_derivative (f : ℝ → ℝ) (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun t => ∫ s in a..t, f s) (f x) x :=
  hf.integral_hasStrictDerivAt a x |>.hasDerivAt

/-- Beck Theorem A.0.3 (CX-151), part (b). If `f` is continuous on `[a, b]` and `F' = f` on
`[a, b]`, then `∫_a^b f = F b - F a`. -/
@[kb "beck2025" "Theorem A.0.3, p. 166"]
theorem ftc_antiderivative (f F : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) : ∫ x in a..b, f x = F b - F a := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  refine integral_eq_sub_of_hasDerivAt (fun x hx => hF x (hu ▸ hx)) ?_
  exact (hu ▸ hf).intervalIntegrable

/-- Beck Theorem A.0.4 (CX-152). Linearity of the integral for continuous functions on `[a, b]`. -/
@[kb "beck2025" "Theorem A.0.4, p. 166"]
theorem integral_linear (f g : ℝ → ℝ) (c a b : ℝ) (hf : ContinuousOn f (uIcc a b))
    (hg : ContinuousOn g (uIcc a b)) :
    ∫ x in a..b, (f x + c * g x) = (∫ x in a..b, f x) + c * ∫ x in a..b, g x := by
  rw [integral_add hf.intervalIntegrable (hg.intervalIntegrable.const_mul c),
    intervalIntegral.integral_const_mul]

/-- Beck Theorem A.0.5 (CX-152). `|∫ f g| ≤ ∫ |f g| ≤ (max |f|) ∫ |g|` for continuous `f`, `g`
on `[a, b]`. -/
@[kb "beck2025" "Theorem A.0.5, p. 167"]
theorem integral_abs_le (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) :
    |∫ x in a..b, f x * g x| ≤ ∫ x in a..b, |f x * g x| ∧
    ∃ M : ℝ, (∃ x ∈ Icc a b, |f x| = M) ∧ (∀ x ∈ Icc a b, |f x| ≤ M) ∧
      ∫ x in a..b, |f x * g x| ≤ M * ∫ x in a..b, |g x| := by
  refine ⟨abs_integral_le_integral_abs hab, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hf.abs
  refine ⟨|f x₀|, ⟨x₀, hx₀, rfl⟩, fun x hx => hmax hx, ?_⟩
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  rw [← intervalIntegral.integral_const_mul]
  refine integral_mono_on hab ?_ ?_ fun x hx => ?_
  · exact ((hf.mul hg).abs).intervalIntegrable_of_Icc hab
  · exact (hg.abs.intervalIntegrable_of_Icc hab).const_mul _
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hmax hx) (abs_nonneg _)

/-- Beck Theorem A.0.6 (CX-153). Substitution rule: `∫_a^b f (g t) g' (t) dt = ∫_{g a}^{g b} f`,
for `g` differentiable with continuous derivative on `[a, b]` and `f` continuous on the image
`g [a, b]` (the book writes `[g a, g b]`, which is the image for monotone `g`). -/
@[kb "beck2025" "Theorem A.0.6, p. 167"]
theorem substitution_rule (f g g' : ℝ → ℝ) (a b : ℝ) (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t)
    (hg' : ContinuousOn g' (uIcc a b)) (hf : ContinuousOn f (g '' uIcc a b)) :
    ∫ t in a..b, f (g t) * g' t = ∫ x in g a..g b, f x :=
  integral_comp_mul_deriv' hg hg' hf

/-- Beck Theorem A.0.7 (CX-154). Mixed partials commute (Mathlib-shaped: the function is `C²` at
the point, which is stronger than the continuity of the mixed partials assumed in the book). -/
@[kb "beck2025" "Theorem A.0.7, p. 167"]
theorem mixed_partials_commute (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hu : ContDiffAt ℝ 2 u p) :
    fderiv ℝ (fderiv ℝ u) p (1, 0) (0, 1) = fderiv ℝ (fderiv ℝ u) p (0, 1) (1, 0) :=
  hu.isSymmSndFDerivAt (by simp) (1, 0) (0, 1)

/-- Beck Theorem A.0.8 (CX-155). Fubini for a function continuous on a rectangle. -/
@[kb "beck2025" "Theorem A.0.8, p. 167"]
theorem fubini_rectangle (f : ℝ → ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  have hint : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hint2 : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hint.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [integral_of_le hab, integral_of_le hcd]
  exact integral_integral_swap hint2

/-- Beck Theorem A.0.9 (CX-156). Leibniz's rule (Mathlib-shaped: `f` is `C¹` on `(a, b) × [c, d]`,
and the derivative is stated as a Fréchet derivative): at an interior point `x₀`, the derivative
of `x ↦ ∫_c^d f(x, y) dy` is `∫_c^d ∂f/∂x (x₀, y) dy`. -/
@[kb "beck2025" "Theorem A.0.9, p. 167"]
theorem leibniz_rule (f : ℝ → ℝ → ℝ) (a b c d x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Ioo a b ×ˢ uIcc c d)) :
    HasFDerivAt (fun x => ∫ y in c..d, f x y) (∫ y in c..d, fderiv ℝ (fun x => f x y) x₀) x₀ :=
  hasFDerivAt_integral_of_contDiffOn (μ := volume) (Ioo_mem_nhds hx₀.1 hx₀.2) hf

/-- Beck Theorem A.0.11 (CX-158). L'Hôpital's rule, for a point `c` inside the open interval
`(a, b)`, and for the endpoint `c = a`. -/
@[kb "beck2025" "Theorem A.0.11, p. 167"]
theorem lhopital (f g : ℝ → ℝ) (L : ℝ) :
    (∀ a b c : ℝ, c ∈ Ioo a b → DifferentiableOn ℝ f (Ioo a b \ {c}) →
      DifferentiableOn ℝ g (Ioo a b \ {c}) → (∀ x ∈ Ioo a b \ {c}, deriv g x ≠ 0) →
      Tendsto f (𝓝[≠] c) (𝓝 0) → Tendsto g (𝓝[≠] c) (𝓝 0) →
      Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] c) (𝓝 L) →
      Tendsto (fun x => f x / g x) (𝓝[≠] c) (𝓝 L)) ∧
    (∀ a b : ℝ, a < b → DifferentiableOn ℝ f (Ioo a b) → DifferentiableOn ℝ g (Ioo a b) →
      (∀ x ∈ Ioo a b, deriv g x ≠ 0) → Tendsto f (𝓝[>] a) (𝓝 0) → Tendsto g (𝓝[>] a) (𝓝 0) →
      Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) (𝓝 L) →
      Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L)) := by
  refine ⟨fun a b c hc hf hg hg' hfc hgc hdiv => ?_, fun a b hab hf hg hg' hfa hga hdiv => ?_⟩
  · have hev : ∀ᶠ x in 𝓝[≠] c, x ∈ Ioo a b \ {c} := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hc.1 hc.2),
        self_mem_nhdsWithin] with x hx hxc
      exact ⟨hx, hxc⟩
    have hopen : IsOpen (Ioo a b \ {c}) := isOpen_Ioo.sdiff isClosed_singleton
    exact deriv.lhopital_zero_nhdsNE
      (hev.mono fun x hx => (hf x hx).differentiableAt (hopen.mem_nhds hx))
      (hev.mono fun x hx => hg' x hx) hfc hgc hdiv
  · exact deriv.lhopital_zero_right_on_Ioo hab hf hg' hfa hga hdiv

end UndergradKB.ComplexAnalysis.Course.BeckA
