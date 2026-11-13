import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import UndergradKB.Common.Attr

/-! # Probability: independence and joint densities, `n` variables (Grinstead–Snell, Theorem 4.2)

Theorem 4.2: continuous random variables `X_1, ..., X_n` with densities `f_1, ..., f_n` and joint density `f` are
mutually independent iff `f(x_1, ..., x_n) = f_1(x_1) ⋯ f_n(x_n)`. The two-variable form is
`UndergradKB.Probability.indepFun_iff_joint_density` (from Mathlib). Here we prove the `n`-variable form, with the
equality of densities almost everywhere (densities are only defined up to null sets).

The bridge missing from Mathlib is the density of a product measure: `Measure.pi (μ_i.withDensity f_i)` is
`(Measure.pi μ).withDensity (x ↦ ∏ f_i (x_i))` (`pi_withDensity`), from the product formula for the lower
integral of `x ↦ ∏ f_i (x_i)` (`lintegral_pi_prod`), proved by induction on `n`. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace UndergradKB.Probability

/-- Tonelli for a product of functions of separate coordinates: `∫⁻ ∏ f_i(x_i) d(⊗ μ_i) = ∏ ∫⁻ f_i dμ_i`. -/
theorem lintegral_pi_prod : ∀ {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, α, _, μ, _, f, _ => by
    simp
  | n + 1, α, _, μ, _, f, hf => by
    have e := measurePreserving_piFinSuccAbove μ 0
    calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ
        = ∫⁻ x, (fun y : α 0 × (∀ j : Fin n, α (Fin.succAbove 0 j)) =>
            f 0 y.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (y.2 j)) (MeasurableEquiv.piFinSuccAbove α 0 x)
            ∂Measure.pi μ := by
          refine lintegral_congr fun x => ?_
          rw [Fin.prod_univ_succ]
          rfl
      _ = ∫⁻ y, f 0 y.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (y.2 j)
            ∂(μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
          e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
            (fun y : α 0 × (∀ j : Fin n, α (Fin.succAbove 0 j)) =>
              f 0 y.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (y.2 j))
      _ = _ := by
        have hg : Measurable fun z : (∀ j : Fin n, α (Fin.succAbove 0 j)) =>
            ∏ j : Fin n, f (Fin.succAbove 0 j) (z j) :=
          Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
        refine (lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable).trans ?_
        rw [lintegral_pi_prod (fun j => μ (Fin.succAbove 0 j)) (fun j => f (Fin.succAbove 0 j))
            (fun j => hf _), Fin.prod_univ_succ]
        rfl

/-- The product of measures with densities has the product density. -/
theorem pi_withDensity {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (univ.pi s).indicator (fun x => ∏ i, f i (x i)) = fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [this, lintegral_pi_prod μ _ fun i => (hf i).indicator (hs i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Grinstead–Snell Theorem 4.2 (PR-047), `n` variables. Real random variables `X_1, ..., X_n` with densities
whose joint law (of the vector `(X_1, ..., X_n)`) has a density are mutually independent iff the joint density is,
almost everywhere, the product `f_1(x_1) ⋯ f_n(x_n)` of the marginal densities. -/
@[kb "grinsteadsnell2006" "Theorem 4.2, p. 173"]
theorem iIndepFun_iff_joint_density {n : ℕ} (X : Fin n → Ω → ℝ) [∀ i, HasPDF (X i) P]
    [HasPDF (fun ω i => X i ω) P] :
    iIndepFun X P ↔ pdf (fun ω i => X i ω) P =ᵐ[volume] fun x => ∏ i, pdf (X i) P volume (x i) := by
  have hX : ∀ i, AEMeasurable (X i) P := fun i => HasPDF.aemeasurable (X i) P volume
  have hpi : Measure.pi (fun i => P.map (X i)) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => ∏ i, pdf (X i) P volume (x i)) := by
    have : ∀ i, IsProbabilityMeasure ((volume : Measure ℝ).withDensity (pdf (X i) P volume)) := fun i => by
      rw [← map_eq_withDensity_pdf (X i) P volume]; exact (Measure.isProbabilityMeasure_map_iff (hX i)).2 inferInstance
    simp_rw [map_eq_withDensity_pdf (X _) P volume]
    rw [volume_pi]
    exact pi_withDensity _ _ fun i => measurable_pdf _ _ _
  rw [iIndepFun_iff_map_fun_eq_pi_map hX, map_eq_withDensity_pdf (fun ω i => X i ω) P volume, hpi]
  exact withDensity_eq_iff_of_sigmaFinite (measurable_pdf _ _ _).aemeasurable
    (Finset.measurable_prod _ fun i _ => (measurable_pdf _ _ _).comp (measurable_pi_apply i)).aemeasurable

end UndergradKB.Probability
