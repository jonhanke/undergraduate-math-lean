/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.AnovaTest
import UndergradKB.Statistics.CorrelationTest
import UndergradKB.Statistics.Pearson
import UndergradKB.Statistics.IndependenceTest
import UndergradKB.Statistics.Homogeneity

/-!
# Proofs of the statistics headline statements

Proves the statements of `Challenge_Statistics.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Statistics.lean`.
-/

namespace UndergradKB.Headlines.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset UndergradKB.Statistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n k : ℕ}

theorem indepFun_sampleMean_sampleVariance [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    IndepFun (fun ω ↦ mean fun i ↦ X i ω) (fun ω ↦ sampleVariance fun i ↦ X i ω) P :=
  UndergradKB.Statistics.indepFun_sampleMean_sampleVariance hn hσ hX

theorem hasLaw_sampleVariance_chiSquared [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ}
    (hn : 2 ≤ n) (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ ((n : ℝ) - 1) * (sampleVariance fun i ↦ X i ω) / σ ^ 2) (chiSquared ((n : ℝ) - 1)) P :=
  UndergradKB.Statistics.hasLaw_sampleVariance_chiSquared hn hσ hX

theorem hasLaw_tStatistic [IsProbabilityMeasure P] {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n) (hσ : 0 < σ)
    (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ (mean (fun i ↦ X i ω) - μ) / (sampleStdDev (fun i ↦ X i ω) / √n))
      (studentT ((n : ℝ) - 1)) P :=
  UndergradKB.Statistics.hasLaw_tStatistic hn hσ hX

theorem hasLaw_fStatistic [IsProbabilityMeasure P] (g : Fin n → Fin k) (hg : ∀ j, 0 < groupSize g j)
    (hk : 2 ≤ k) (hkn : k < n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ)
    (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ fStatistic (fun i ↦ Y i ω) g) (fDistribution ((k : ℝ) - 1) ((n : ℝ) - k)) P :=
  UndergradKB.Statistics.hasLaw_fStatistic g hg hk hkn hσ hY

theorem hasLaw_correlation_tStatistic [IsProbabilityMeasure P] (x : Fin n → ℝ) (hx : 0 < sumSqDev x)
    (hn : 3 ≤ n) {Y : Fin n → Ω → ℝ} {μ σ : ℝ} (hσ : 0 < σ) (hY : IsNormalSample Y μ σ P) :
    HasLaw (fun ω ↦ correlation x (fun i ↦ Y i ω) * √((n : ℝ) - 2) /
      √(1 - correlation x (fun i ↦ Y i ω) ^ 2)) (studentT ((n : ℝ) - 2)) P :=
  UndergradKB.Statistics.hasLaw_correlation_tStatistic x hx hn hσ hY

theorem tendstoInDistribution_pearsonStatistic [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {p : Fin k → ℝ} (hk : 2 ≤ k) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {C : ℕ → Ω → Fin k} (hmeas : ∀ m, Measurable (C m)) (hind : iIndepFun C P)
    (hident : ∀ m, IdentDistrib (C m) (C 0) P P) (hprob : ∀ i, P.real {ω | C 0 ω = i} = p i)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared ((k : ℝ) - 1)) P') :
    TendstoInDistribution (pearsonStatistic p C) Filter.atTop W (fun _ ↦ P) P' :=
  UndergradKB.Statistics.tendstoInDistribution_pearsonStatistic hk hp hsum hmeas hind hident hprob hW

theorem tendstoInDistribution_independenceStatistic {r c : ℕ} [IsProbabilityMeasure P] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c)
    {a : Fin r → ℝ} {b : Fin c → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hasum : ∑ i, a i = 1)
    (hbsum : ∑ j, b j = 1) {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m))
    (hind : iIndepFun C P) (hident : ∀ m, IdentDistrib (C m) (C 0) P P)
    (hprob : ∀ i j, P.real {ω | C 0 ω = (i, j)} = a i * b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (independenceStatistic C) Filter.atTop W (fun _ ↦ P) P' :=
  UndergradKB.Statistics.tendstoInDistribution_independenceStatistic hr hc ha hb hasum hbsum hmeas hind hident hprob hW

theorem tendstoInDistribution_homogeneityStatistic {r c : ℕ} [IsProbabilityMeasure P] {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c)
    {sz : Fin r → ℕ} (hsz : ∀ i, 0 < sz i) {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P) (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P)
    (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (homogeneityStatistic Y sz) Filter.atTop W (fun _ ↦ P) P' :=
  UndergradKB.Statistics.tendstoInDistribution_homogeneityStatistic hr hc hsz hb hbsum hmeas hind hident hprob hW

end UndergradKB.Headlines.Statistics
