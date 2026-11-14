import Mathlib.MeasureTheory.Function.Floor
import UndergradKB.Common.Attr
import UndergradKB.Probability.QueueModels
import UndergradKB.Probability.QueueUniformization

/-! # Probability: the clock and the jump chain of the queue on one probability space (Example 6.29)

Wave 8, a recorded loose end (2).  `queue_uniformization_law` assumes exponential clock gaps `X` and a jump chain
`Y` of the queue (laws `queueLawFrom j`) on one probability space, with the clock independent of the chain.  Here
such a space is built: real variables indexed by `ℕ ⊕ ℕ` with given laws are independent
(`exists_hasLaw_indepFun`); the left ones are the clock gaps, the right ones (read as natural numbers) are the
initial length `j` and the coins of the coin-driven chain `coinChain`. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace UndergradKB.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The laws of the coin-driven chain started with `j` customers are the laws `queueLawFrom j` of the jump
chain. -/
theorem coinChain_law_eq_from {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) {Z : ℕ → Ω → ℕ}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hC : ∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu)) {j : ℕ}
    (h0 : P.real {ω | Z 0 ω = j} = 1) (n k : ℕ) :
    P.real {ω | coinChain Z n ω = k} = queueLawFrom lam mu j n k := by
  have hinit : ∀ k, P.real {ω | Z 0 ω = k} = if k = j then 1 else 0 := by
    intro k
    split_ifs with hk
    · rw [hk, h0]
    · have hsub : {ω | Z 0 ω = k} ⊆ {ω | Z 0 ω = j}ᶜ := fun ω hω h => hk (hω.symm.trans h)
      have := measureReal_mono (μ := P) hsub
      rw [probReal_compl_eq_one_sub (measurableSet_eq_fun (hZ 0) measurable_const), h0, sub_self] at this
      exact le_antisymm this measureReal_nonneg
  induction n generalizing k with
  | zero => rw [(queueLawFrom_step hl hm j 0).1 k]; exact hinit k
  | succ n ih =>
    have h := coinChain_law_step hl hm hZ hind hC n k
    simp_rw [ih] at h
    exact h.unique ((queueLawFrom_step hl hm j n).2 k)

theorem measurable_coinChainSeq (n : ℕ) : Measurable fun v : ℕ → ℝ => coinChainSeq (fun i => ⌊v i⌋₊) n := by
  induction n with
  | zero => exact Nat.measurable_floor.comp (measurable_pi_apply 0)
  | succ n ih =>
    exact (measurable_of_countable (Function.uncurry queueStep)).comp
      (ih.prodMk (Nat.measurable_floor.comp (measurable_pi_apply (n + 1))))

/-- Grinstead–Snell Example 6.29 (PR-209), the hypotheses of `queue_uniformization_law` can be met.  For
`λ, μ > 0` and `j`, there is a probability space with independent exponential(`λ + μ`) clock gaps `X`, a chain
`Y` whose laws are those of the jump chain of the queue started with `j` customers, and the clock independent of
the chain. -/
theorem exists_queue_uniformization_model {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) (j : ℕ) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ℕ → Ω → ℝ, ∃ Y : ℕ → Ω → ℕ,
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, P.map (X i) = expMeasure (lam + mu)) ∧ (∀ n, Measurable (Y n)) ∧
      (∀ n k, P.real {ω | Y n ω = k} = queueLawFrom lam mu j n k) ∧
      IndepFun (fun ω i => X i ω) (fun ω n => Y n ω) P := by
  have hν : 0 < lam + mu := by linarith
  set a := lam / (lam + mu) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hν]; linarith
  set μs : ℕ ⊕ ℕ → Measure ℝ := Sum.elim (fun _ => expMeasure (lam + mu))
    (fun n => if n = 0 then Measure.dirac (j : ℝ) else (coinLaw a).map (Nat.cast : ℕ → ℝ)) with hμs
  have hμ : ∀ i, IsProbabilityMeasure (μs i) := by
    intro i
    rcases i with i | n
    · exact isProbabilityMeasure_expMeasure hν
    · by_cases hn : n = 0
      · simp only [hμs, Sum.elim_inr, hn, ite_true]; infer_instance
      · simp only [hμs, Sum.elim_inr, hn, ite_false]
        have := coinLaw_prob ha0 ha1
        infer_instance
  obtain ⟨Ω, mΩ, P, W, hmW, hlaw, hind, hP⟩ := exists_hasLaw_indepFun (fun _ : ℕ ⊕ ℕ => ℝ) μs
  set X : ℕ → Ω → ℝ := fun i => W (Sum.inl i) with hX
  set Z : ℕ → Ω → ℕ := fun n ω => ⌊W (Sum.inr n) ω⌋₊ with hZdef
  have hZm : ∀ n, Measurable (Z n) := fun n => Nat.measurable_floor.comp (hmW _)
  have hZind : iIndepFun Z P :=
    (hind.precomp Sum.inr_injective).comp (fun _ x => ⌊x⌋₊) fun _ => Nat.measurable_floor
  have hfloor : ∀ (m : ℕ), {x : ℕ | ⌊(x : ℝ)⌋₊ = m} = {m} := fun m => by ext x; simp
  have hC : ∀ n, P.real {ω | Z (n + 1) ω = 1} = lam / (lam + mu) := by
    intro n
    have e : {ω | Z (n + 1) ω = 1} = W (Sum.inr (n + 1)) ⁻¹' ((fun x : ℝ => ⌊x⌋₊) ⁻¹' {1}) := rfl
    rw [e, ← map_measureReal_apply (hmW _) (Nat.measurable_floor (MeasurableSet.of_discrete)),
      (hlaw _).map_eq]
    simp only [hμs, Sum.elim_inr, Nat.add_one_ne_zero, ite_false]
    rw [map_measureReal_apply (measurable_of_countable _) (Nat.measurable_floor (MeasurableSet.of_discrete))]
    rw [show (Nat.cast : ℕ → ℝ) ⁻¹' ((fun x : ℝ => ⌊x⌋₊) ⁻¹' {1}) = {1} from hfloor 1]
    exact coinLaw_one ha0
  have h0 : P.real {ω | Z 0 ω = j} = 1 := by
    have e : {ω | Z 0 ω = j} = W (Sum.inr 0) ⁻¹' ((fun x : ℝ => ⌊x⌋₊) ⁻¹' {j}) := rfl
    rw [e, ← map_measureReal_apply (hmW _) (Nat.measurable_floor (MeasurableSet.of_discrete)),
      (hlaw _).map_eq]
    simp [hμs]
  refine ⟨Ω, mΩ, P, X, coinChain Z, hP, fun i => hmW _, hind.precomp Sum.inl_injective, fun i => ?_,
    measurable_coinChain hZm, coinChain_law_eq_from hl hm hZm hZind hC h0, ?_⟩
  · exact (hlaw (Sum.inl i)).map_eq
  · -- the left and right families are independent
    have hset := hind.indepFun_set (range Sum.inl) (range Sum.inr)
      (Set.disjoint_left.2 fun x ⟨i, hi⟩ ⟨n, hn⟩ => by rw [← hi] at hn; exact Sum.inl_ne_inr hn.symm) hmW
    set φ : (range (Sum.inl : ℕ → ℕ ⊕ ℕ) → ℝ) → (ℕ → ℝ) := fun v i => v ⟨Sum.inl i, mem_range_self i⟩
    set ψ : (range (Sum.inr : ℕ → ℕ ⊕ ℕ) → ℝ) → (ℕ → ℕ) := fun v n =>
      coinChainSeq (fun i => ⌊v ⟨Sum.inr i, mem_range_self i⟩⌋₊) n
    have hφ : Measurable φ := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hψ : Measurable ψ := by
      refine measurable_pi_iff.2 fun n => ?_
      have hr : Measurable fun v : range (Sum.inr : ℕ → ℕ ⊕ ℕ) → ℝ =>
          fun i : ℕ => v ⟨Sum.inr i, mem_range_self i⟩ := measurable_pi_iff.2 fun i => measurable_pi_apply _
      exact (measurable_coinChainSeq n).comp hr
    exact hset.comp hφ hψ

end UndergradKB.Probability
