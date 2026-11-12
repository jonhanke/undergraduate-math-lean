import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.IsolatedZeros
import UndergradKB.Common.Attr

/-!
# A law on the real line is determined by its moment generating function near zero

Mathlib proves that the complex moment generating function determines a law
(`MeasureTheory.Measure.ext_of_complexMGF_eq`) and that equal real moment generating functions give equal complex
ones on a strip (`ProbabilityTheory.eqOn_complexMGF_of_mgf`), but leaves the real statement as a TODO. We prove the
form used to identify the chi-square law: two probability laws on `ℝ` whose moment generating functions are finite
and equal on an open interval around `0` are equal.

The proof: both complex moment generating functions are analytic on the strip `|Re z| < δ` and agree on its real
points, hence (identity theorem) on the whole strip, in particular on the imaginary axis, where they are the
characteristic functions (`complexMGF_id_mul_I`); characteristic functions determine the law
(`Measure.ext_of_charFun`).
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Complex Filter Topology

/-- The strip `{z | Re z ∈ (-δ, δ)}` lies in the strip where the complex moment generating function is analytic,
as soon as `exp (t x)` is integrable for every `t ∈ (-δ, δ)`. -/
lemma strip_subset_interior {μ : Measure ℝ} {δ : ℝ}
    (hμ : ∀ t ∈ Set.Ioo (-δ) δ, Integrable (fun x ↦ Real.exp (t * x)) μ) :
    {z : ℂ | z.re ∈ Set.Ioo (-δ) δ} ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet id μ)} := by
  intro z hz
  have : Set.Ioo (-δ) δ ⊆ integrableExpSet id μ := fun t ht ↦ hμ t ht
  exact interior_mono this (by rw [interior_Ioo]; exact hz)

/-- Uniqueness of the law with a given moment generating function: two probability laws on `ℝ` whose moment
generating functions are finite and agree on `(-δ, δ)`, `δ > 0`, are equal. -/
theorem ext_of_mgf_eqOn {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : 0 < δ)
    (hμ : ∀ t ∈ Set.Ioo (-δ) δ, Integrable (fun x ↦ Real.exp (t * x)) μ)
    (hν : ∀ t ∈ Set.Ioo (-δ) δ, Integrable (fun x ↦ Real.exp (t * x)) ν)
    (h : ∀ t ∈ Set.Ioo (-δ) δ, mgf id μ t = mgf id ν t) : μ = ν := by
  set U : Set ℂ := {z : ℂ | z.re ∈ Set.Ioo (-δ) δ} with hU
  have hfa : AnalyticOnNhd ℂ (complexMGF id μ) U :=
    fun z hz ↦ analyticOnNhd_complexMGF z (strip_subset_interior hμ hz)
  have hga : AnalyticOnNhd ℂ (complexMGF id ν) U :=
    fun z hz ↦ analyticOnNhd_complexMGF z (strip_subset_interior hν hz)
  have hUc : IsPreconnected U :=
    ((convex_Ioo (-δ) δ).linear_preimage reLm).isPreconnected
  have h0 : (0 : ℂ) ∈ U := by simp [hU, hδ]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF id μ z = complexMGF id ν z := by
    have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ), complexMGF id μ x = complexMGF id ν x := by
      have hev : ∀ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ), x ∈ Set.Ioo (-δ) δ :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) hδ)
      refine (hev.mono fun x hx ↦ ?_).frequently
      rw [complexMGF_ofReal, complexMGF_ofReal, h x hx]
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ hx_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · have := (continuous_ofReal.tendsto 0).comp hx_tendsto.1
      simpa [Function.comp_def] using this
    · simpa using hx_tendsto.2
  have heq := hfa.eqOn_of_preconnected_of_frequently_eq hga hUc h0 hfreq
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq (by simp [hU, hδ])

/-- The same for random variables: if `X` and `Y` have finite and equal moment generating functions on
`(-δ, δ)`, they have the same law. -/
theorem map_eq_of_mgf_eqOn {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P') {δ : ℝ} (hδ : 0 < δ)
    (hXi : ∀ t ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (t * X ω)) P)
    (hYi : ∀ t ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P')
    (h : ∀ t ∈ Set.Ioo (-δ) δ, mgf X P t = mgf Y P' t) : P.map X = P'.map Y := by
  haveI := (Measure.isProbabilityMeasure_map_iff hX).2 inferInstance
  haveI := (Measure.isProbabilityMeasure_map_iff hY).2 inferInstance
  refine ext_of_mgf_eqOn hδ (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact (integrable_map_measure (by fun_prop) hX).2 (hXi t ht)
  · exact (integrable_map_measure (by fun_prop) hY).2 (hYi t ht)
  · rw [mgf_id_map hX, mgf_id_map hY, h t ht]

end UndergradKB.Statistics
