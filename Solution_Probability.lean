/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.PolyaRecurrence
import UndergradKB.Probability.PolyaThree
import UndergradKB.Probability.ArcSine
import UndergradKB.Probability.Shuffles
import UndergradKB.Probability.LocalLimitLattice
import UndergradKB.Probability.MarkovClt
import UndergradKB.Probability.FirstMaximum

/-!
# Proofs of the probability headline statements

Proves the statements of `Challenge_Probability.lean` from the library. `lake comparator` checks that each
statement here is exactly the one in `Challenge_Probability.lean`.
-/

namespace UndergradKB.Headlines.Probability

open Matrix Finset Filter Topology MeasureTheory ProbabilityTheory UndergradKB.Probability
open scoped Real

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem regular_pow_tendsto [Nonempty S] {P : Matrix S S ℝ} (h : IsRegularChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧
      ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j)) :=
  UndergradKB.Probability.regular_pow_tendsto h

theorem ergodic_cesaro_tendsto [Nonempty S] {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ i j, Tendsto (fun n => cesaroAvg P n i j) atTop (𝓝 (w j)) :=
  UndergradKB.Probability.ergodic_cesaro_tendsto h

theorem absorption_certain {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : S) :
    Tendsto (fun n => ∑ a : Absorbing P, (P ^ n) i a) atTop (𝓝 1) :=
  UndergradKB.Probability.absorption_certain hP hA i

theorem hasSum_absorption_time {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P)
    (i : Transient P) :
    HasSum (fun k => ∑ j : Transient P, (P ^ k) i j) ((fundamentalMatrix P *ᵥ fun _ => 1) i) :=
  UndergradKB.Probability.hasSum_absorption_time hP hA i

theorem absorption_prob_tendsto {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P)
    (i : Transient P) (a : Absorbing P) :
    Tendsto (fun n => (P ^ n) i a) atTop (𝓝 ((fundamentalMatrix P * absorbR P) i a)) :=
  UndergradKB.Probability.absorption_prob_tendsto hP hA i a

theorem polya_two : HasSum (Polya.f (Polya.simpleStep 2)) 1 :=
  UndergradKB.Probability.Polya.hasSum_firstReturn_two

theorem polya_three :
    HasSum (Polya.f (Polya.simpleStep 3)) (1 - (∑' N, Polya.u (Polya.simpleStep 3) N)⁻¹) ∧
      ∑' N, Polya.f (Polya.simpleStep 3) N < 1 :=
  UndergradKB.Probability.Polya.firstReturn_three_lt_one

theorem arcsine_law_lead (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1),
        ((univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) :=
  UndergradKB.Probability.leadCount_cdf_tendsto α h0 h1

theorem riffle_shuffle_composition (n a b : ℕ) :
    ∃ e : ((Fin n → Fin a) × (Fin n → Fin b)) ≃ (Fin n → Fin (a * b)),
      ∀ p, shuffleOrdering (e p) = shuffleOrdering p.1 * shuffleOrdering p.2 :=
  UndergradKB.Probability.exists_shuffle_pair_equiv n a b

theorem card_riffle_shuffles (n a : ℕ) (σ : Equiv.Perm (Fin n)) :
    #{g : Fin n → Fin a | shuffleOrdering g = σ} = (n + a - risingSequences σ).choose n :=
  UndergradKB.Probability.card_shuffles_eq_choose n a σ

theorem local_limit_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℤ} (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hL2 : MemLp (fun ω => (X 0 ω : ℝ)) 2 P) {μ σ : ℝ} (hσ : 0 < σ)
    (hμ : ∫ ω, (X 0 ω : ℝ) ∂P = μ) (hv : Var[fun ω => (X 0 ω : ℝ); P] = σ ^ 2)
    (hgcd : ∀ m : ℤ, (∀ i j : ℤ, 0 < P.real {ω | X 0 ω = i} → 0 < P.real {ω | X 0 ω = j} →
      m ∣ i - j) → m ∣ 1) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n → ∀ j : ℤ,
      |σ * √(n : ℝ) * P.real {ω | ∑ i ∈ Finset.range n, X i ω = j} -
        Real.exp (-(((j - n * μ) / (σ * √(n : ℝ))) ^ 2) / 2) / √(2 * π)| ≤ ε n :=
  UndergradKB.Probability.local_limit_lattice hXm hindep hident hL2 hσ hμ hv hgcd

theorem markov_clt [Nonempty S] {P : Matrix S S ℝ} (hP : IsErgodicChain P) {u : S → ℝ} (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∑ i, u i = 1) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧ IsUnit (1 - P + rowsMatrix w) ∧
      ∀ j : S, 0 < 2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 →
        ∀ r s : ℝ, r < s →
          Tendsto (fun n : ℕ => ∑ x : Fin (n + 1) → S with
              r < (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j) /
                  √(n * (2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2)) ∧
                (((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j) /
                  √(n * (2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2)) < s,
              pathProb u P n x)
            atTop (𝓝 (∫ x in r..s, gaussianPDFReal 0 1 x)) :=
  UndergradKB.Probability.markov_clt hP hu0 hu

open UndergradKB.Probability.FirstMax in
theorem firstMaxIndex_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {μ : Measure ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = μ) (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Tendsto (fun n : ℕ => (P {ω | (firstMaxIndex X n ω : ℝ) < n * α}).toReal) atTop
      (𝓝 ((2 / π) * Real.arcsin (√α))) :=
  UndergradKB.Probability.firstMaxIndex_tendsto hX hind hlaw hcont hsymm α h0 h1

end UndergradKB.Headlines.Probability
