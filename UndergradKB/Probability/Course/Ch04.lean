import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Beta
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 4 (Grinstead–Snell, Conditional Probability)

Thin wrappers stating the book's results of Chapter 4 as direct instances of Mathlib.
-/

namespace UndergradKB.Probability.Course

open MeasureTheory ProbabilityTheory

/-- Grinstead–Snell §4.1 conditional probability (PR-036). For an event `E` of positive
probability, `P(F | E) = P(E ∩ F) / P(E)`, and `P(· | E)` is again a probability measure. -/
@[kb "grinsteadsnell2006" "§4.1 conditional probability, p. 143"]
theorem gs_section_4_1_conditional_probability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E) (hpos : P E ≠ 0) (F : Set Ω) :
    P[F | E] = (P E)⁻¹ * P (E ∩ F) ∧ IsProbabilityMeasure P[|E] :=
  ⟨cond_apply hE P F, cond_isProbabilityMeasure hpos⟩

/-- Grinstead–Snell §4.1 product rule (PR-037). `P(E ∩ F) = P(F | E) P(E)`, and conditioning
successively on `E` and then `F` is conditioning on `E ∩ F`. -/
@[kb "grinsteadsnell2006" "§4.1 product rule, p. 143"]
theorem gs_section_4_1_product_rule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    P (E ∩ F) = P[F | E] * P E ∧ P[|E][|F] = P[|E ∩ F] :=
  ⟨(cond_mul_eq_inter hE F P).symm, cond_cond_eq_cond_inter hE hF P⟩

/-- Grinstead–Snell Theorem 4.1 (PR-040). Two events are independent exactly when the probability
of their intersection is the product of their probabilities. -/
@[kb "grinsteadsnell2006" "Theorem 4.1, p. 148"]
theorem gs_theorem_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E F : Set Ω} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IndepSet E F P ↔ P (E ∩ F) = P E * P F :=
  indepSet_iff_measure_inter_eq_mul hE hF P

/-- Grinstead–Snell Definition 4.2 (PR-041). Events `A i` are mutually independent when every
finite subfamily has intersection probability equal to the product. -/
@[kb "grinsteadsnell2006" "Definition 4.2, p. 149"]
theorem gs_definition_4_2 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    iIndepSet A P ↔ ∀ s : Finset ι, P (⋂ i ∈ s, A i) = ∏ i ∈ s, P (A i) :=
  iIndepSet_iff_meas_biInter hA

/-- Grinstead–Snell Definition 4.4 (PR-043). Random variables are mutually independent when the
probability that each lies in a measurable set is multiplicative over every finite subfamily. -/
@[kb "grinsteadsnell2006" "Definition 4.4, p. 151"]
theorem gs_definition_4_4 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) :
    iIndepFun X P ↔ ∀ (S : Finset ι) (B : ι → Set ℝ), (∀ i ∈ S, MeasurableSet (B i)) →
      P (⋂ i ∈ S, X i ⁻¹' B i) = ∏ i ∈ S, P (X i ⁻¹' B i) :=
  iIndepFun_iff_measure_inter_preimage_eq_mul

/-- Grinstead–Snell Definition 4.5 (PR-044). In an independent trials process (independent,
identically distributed variables) joint probabilities multiply with the common distribution. -/
@[kb "grinsteadsnell2006" "Definition 4.5, p. 152"]
theorem gs_definition_4_5 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (i₀ : ι) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X i₀) P P) (S : Finset ι) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    P (⋂ i ∈ S, X i ⁻¹' B i) = ∏ i ∈ S, P (X i₀ ⁻¹' B i) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind S hB]
  exact Finset.prod_congr rfl fun i hi => (hid i).measure_mem_eq (hB i hi)

/-- Grinstead–Snell Theorem 4.3 (PR-048). Continuous functions applied separately to independent
random variables give independent random variables (two-variable and family forms). -/
@[kb "grinsteadsnell2006" "Theorem 4.3, p. 175"]
theorem gs_theorem_4_3 {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (g : ι → ℝ → ℝ) (hg : ∀ i, Continuous (g i))
    (h : iIndepFun X P) :
    iIndepFun (fun i => g i ∘ X i) P ∧
      ∀ (Y Z : Ω → ℝ) (φ ψ : ℝ → ℝ), IndepFun Y Z P → Continuous φ → Continuous ψ →
        IndepFun (φ ∘ Y) (ψ ∘ Z) P :=
  ⟨h.comp g fun i => (hg i).measurable, fun _ _ _ _ hYZ hφ hψ =>
    hYZ.comp hφ.measurable hψ.measurable⟩

/-- Grinstead–Snell §4.3 beta density (PR-049). For `a, b > 0` the beta law has density
`x^(a-1) (1-x)^(b-1) / B(a,b)` on `(0,1)` and is a probability measure. -/
@[kb "grinsteadsnell2006" "§4.3 beta density, p. 176"]
theorem gs_section_4_3_beta_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) ∧
      betaMeasure a b = volume.withDensity (betaPDF a b) ∧
      ∀ x : ℝ, betaPDFReal a b x =
        if 0 < x ∧ x < 1 then (1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0 :=
  ⟨isProbabilityMeasureBeta ha hb, rfl, fun _ => rfl⟩

end UndergradKB.Probability.Course
