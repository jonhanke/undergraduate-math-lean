import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli
import UndergradKB.Common.Attr

/-!
# Joint laws, joint cumulative distribution functions, and infinite fair coin tossing

Book notions of Grinstead–Snell Chapters 2 and 4: the joint distribution and marginals of a
vector of random variables, the joint cumulative distribution function (which determines the
joint law), and the infinite sequence of fair coin tosses.
-/

namespace UndergradKB.Probability

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

/-! ### Joint cumulative distribution function -/

/-- Joint cumulative distribution function of random variables `X i`, `i ∈ ι`, as in
Grinstead–Snell Definition 4.6: `F(x) = P(X_i ≤ x_i for all i)`. -/
noncomputable def jointCdf {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ)
    (x : ι → ℝ) : ℝ :=
  P.real {ω | ∀ i, X i ω ≤ x i}

/-- Two finite measures on `ι → ℝ` (`ι` finite) agreeing on all boxes `∏ (-∞, x_i]` are equal. -/
theorem measure_ext_of_pi_Iic {ι : Type*} [Finite ι] (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (h : ∀ x : ι → ℝ, μ {y | ∀ i, y i ≤ x i} = ν {y | ∀ i, y i ≤ x i}) : μ = ν := by
  have hgen : ∀ i : ι, MeasurableSpace.generateFrom (range (Iic : ℝ → Set ℝ)) =
      (inferInstance : MeasurableSpace ℝ) := fun _ => by
    exact (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm
  have hcs : ∀ i : ι, IsCountablySpanning (range (Iic : ℝ → Set ℝ)) := fun _ =>
    ⟨fun n => Iic (n : ℝ), fun n => ⟨n, rfl⟩, iUnion_eq_univ_iff.2 fun y => by
      obtain ⟨n, hn⟩ := exists_nat_ge y
      exact ⟨n, hn⟩⟩
  have hC := generateFrom_eq_pi (fun i : ι => hgen i) hcs
  have hbox : ∀ x : ι → ℝ, (Set.pi univ fun i => Iic (x i)) = {y | ∀ i, y i ≤ x i} := by
    intro x; ext y; simp only [mem_pi, mem_univ, mem_Iic, true_implies, mem_ofPred_eq]
  refine Measure.ext_of_generateFrom_of_iUnion (Set.pi univ '' Set.pi univ fun _ : ι => range Iic)
    (fun n : ℕ => {y : ι → ℝ | ∀ i, y i ≤ n}) hC.symm (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ ?_
    (fun n => measure_ne_top μ _) ?_
  · refine iUnion_eq_univ_iff.2 fun y => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (⨆ i, y i)
    exact ⟨n, fun i => (le_ciSup (Set.finite_range y).bddAbove i).trans hn⟩
  · intro n
    refine ⟨fun i => Iic (n : ℝ), fun i _ => ⟨n, rfl⟩, ?_⟩
    simp only [← hbox]
  · rintro _ ⟨s, hs, rfl⟩
    choose x hx using fun i => hs i (mem_univ i)
    have : (Set.pi univ s) = {y | ∀ i, y i ≤ x i} := by
      rw [← hbox]; congr 1; ext1 i; exact (hx i).symm
    rw [this]; exact h x

/-- Grinstead–Snell Definition 4.6 (PR-045). The joint cumulative distribution function
`F(x_1, …, x_n) = P(X_1 ≤ x_1, …, X_n ≤ x_n)` determines the joint law: random vectors with the same
joint cdf have the same joint distribution. -/
@[kb "grinsteadsnell2006" "Definition 4.6, p. 173"]
theorem jointLaw_eq_of_jointCdf_eq {Ω Ω' ι : Type*} [Finite ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω')
    [IsProbabilityMeasure Q] (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (hY : ∀ i, Measurable (Y i)) (h : jointCdf P X = jointCdf Q Y) :
    P.map (fun ω i => X i ω) = Q.map (fun ω i => Y i ω) := by
  have mX : Measurable fun ω i => X i ω := measurable_pi_iff.2 hX
  have mY : Measurable fun ω i => Y i ω := measurable_pi_iff.2 hY
  have : IsProbabilityMeasure (P.map fun ω i => X i ω) := ⟨by
    rw [Measure.map_apply mX MeasurableSet.univ]; simp⟩
  refine measure_ext_of_pi_Iic _ _ fun x => ?_
  have hb : MeasurableSet {y : ι → ℝ | ∀ i, y i ≤ x i} := by
    have : {y : ι → ℝ | ∀ i, y i ≤ x i} = Set.pi univ fun i => Iic (x i) := by
      ext; simp only [mem_pi, mem_univ, mem_Iic, true_implies, mem_ofPred_eq]
    rw [this]; exact MeasurableSet.univ_pi fun i => measurableSet_Iic
  rw [Measure.map_apply mX hb, Measure.map_apply mY hb]
  have := congrFun h x
  simp only [jointCdf] at this
  have h2 := (measureReal_eq_measureReal_iff (μ := P) (ν := Q)
    (s := {ω | ∀ i, X i ω ≤ x i}) (t := {ω | ∀ i, Y i ω ≤ x i})).1 this
  exact h2

/-! ### Joint and marginal distributions -/

/-- Grinstead–Snell Definition 4.3 (PR-042). The joint distribution of `(X_1, …, X_n)` is the law
of the random vector `ω ↦ (X_i ω)_i`; it is a probability measure on `ι → ℝ`, and its marginals
(the images under the coordinate maps) are the distributions of the individual `X_i`. -/
@[kb "grinsteadsnell2006" "Definition 4.3, p. 150"]
theorem joint_and_marginal_laws {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    IsProbabilityMeasure (P.map (fun ω i => X i ω)) ∧
      ∀ i, (P.map (fun ω i => X i ω)).map (fun x => x i) = P.map (X i) := by
  have mX : Measurable fun ω i => X i ω := measurable_pi_iff.2 hX
  refine ⟨⟨by rw [Measure.map_apply mX MeasurableSet.univ]; simp⟩, fun i => ?_⟩
  rw [Measure.map_map (measurable_pi_apply i) mX]
  rfl

/-- Grinstead–Snell §4.1 joint and marginal distributions (PR-042). Two-variable form: the
marginals of the joint law of `(X, Y)` are the laws of `X` and of `Y`. -/
@[kb "grinsteadsnell2006" "§4.1 joint and marginal distributions, p. 151"]
theorem joint_and_marginal_laws_pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    (P.map (fun ω => (X ω, Y ω))).fst = P.map X ∧ (P.map (fun ω => (X ω, Y ω))).snd = P.map Y := by
  refine ⟨?_, ?_⟩
  · rw [Measure.fst, Measure.map_map measurable_fst (hX.prodMk hY)]; rfl
  · rw [Measure.snd, Measure.map_map measurable_snd (hX.prodMk hY)]; rfl

/-! ### Infinitely many tosses of a fair coin -/

/-- The fair coin on `Bool`: `true` and `false` each with probability `1/2`. -/
noncomputable def fairCoin : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

/-- The law of infinitely many tosses of a fair coin: the infinite product of fair coins on the
sequence space `ℕ → Bool`. -/
noncomputable def fairCoinTosses : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => fairCoin

instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin; infer_instance

instance : IsProbabilityMeasure fairCoinTosses := by
  unfold fairCoinTosses; infer_instance

/-- Grinstead–Snell Example 2.18 (PR-010). Infinitely many tosses of a fair coin: there is a
probability measure on the sequence space `ℕ → Bool` under which the tosses are independent and
each is heads with probability `1/2`; the sample space is uncountable. -/
@[kb "grinsteadsnell2006" "Example 2.18, p. 77"]
theorem infinite_fair_coin_tosses :
    IsProbabilityMeasure fairCoinTosses ∧
      iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) => ω i) fairCoinTosses ∧
      (∀ i : ℕ, fairCoinTosses.real {ω | ω i = true} = 1 / 2) ∧ ¬ Countable (ℕ → Bool) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => fairCoin) (X := fun _ => id)
      (fun _ => measurable_id)
  · intro i
    have h := Measure.infinitePi_map_eval (fun _ : ℕ => fairCoin) i
    have e : {ω : ℕ → Bool | ω i = true} = (fun x : ℕ → Bool => x i) ⁻¹' {true} := rfl
    rw [e, ← map_measureReal_apply (measurable_pi_apply i) (measurableSet_singleton true)]
    rw [fairCoinTosses, h]
    unfold fairCoin
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton true) rfl
      (by simp)]
  · intro hc
    obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
    obtain ⟨n, hn⟩ := hf fun k => !f k k
    have := congrFun hn n
    cases h : f n n <;> simp_all

end UndergradKB.Probability
