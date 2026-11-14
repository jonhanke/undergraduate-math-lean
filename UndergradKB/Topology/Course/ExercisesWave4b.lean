import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.GDelta.MetrizableSpace
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapter 2 (wave 4, part b)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 2
(the euclidean topology): closed and open subsets of `ℝ`, `F_σ` and `G_δ` sets, bases and subbases.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter2

/-- Morris, Topology Without Tears, Exercises 2.1 #1(a). For `a < b`, the half-open interval `[a, b)`
is neither open nor closed in `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #1(a), p. 55"]
theorem morris_exercise_2_1_1_a {a b : ℝ} (hab : a < b) : ¬ IsOpen (Ico a b) ∧ ¬ IsClosed (Ico a b) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := h.interior_eq
    rw [interior_Ico] at h1
    have : a ∈ Ico a b := ⟨le_rfl, hab⟩
    rw [← h1] at this
    exact lt_irrefl a this.1
  · exact absurd (isClosed_Ico_iff.1 h) (not_le.2 hab)

/-- Morris, Topology Without Tears, Exercises 2.1 #1(b). For `a < b`, the half-open interval `(a, b]`
is neither open nor closed in `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #1(b), p. 55"]
theorem morris_exercise_2_1_1_b {a b : ℝ} (hab : a < b) : ¬ IsOpen (Ioc a b) ∧ ¬ IsClosed (Ioc a b) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := h.interior_eq
    rw [interior_Ioc] at h1
    have : b ∈ Ioc a b := ⟨hab, le_rfl⟩
    rw [← h1] at this
    exact lt_irrefl b this.2
  · exact absurd (isClosed_Ioc_iff.1 h) (not_le.2 hab)

/-- Morris, Topology Without Tears, Exercises 2.1 #2. The rays `[a, ∞)` and `(-∞, a]` are closed
subsets of `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #2, p. 55"]
theorem morris_exercise_2_1_2 (a : ℝ) : IsClosed (Ici a) ∧ IsClosed (Iic a) :=
  ⟨isClosed_Ici, isClosed_Iic⟩

/-- Morris, Topology Without Tears, Exercises 2.1 #3. An infinite union of closed subsets of `ℝ` need
not be closed: the union of the singletons `{1/(n+1)}` is not closed. -/
@[kb "morris2024" "Exercises 2.1 #3, p. 55"]
theorem morris_exercise_2_1_3 :
    ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ ¬ IsClosed (⋃ n, F n) := by
  refine ⟨fun n => {1 / ((n : ℝ) + 1)}, fun n => isClosed_singleton, fun h => ?_⟩
  have h0 : (0 : ℝ) ∈ closure (⋃ n : ℕ, ({1 / ((n : ℝ) + 1)} : Set ℝ)) :=
    mem_closure_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall fun n => mem_iUnion.2 ⟨n, rfl⟩)
  rw [h.closure_eq, mem_iUnion] at h0
  obtain ⟨n, hn⟩ := h0
  have : (1 : ℝ) / ((n : ℝ) + 1) = 0 := hn.symm
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- Morris, Topology Without Tears, Exercises 2.1 #6. A non-empty countable subset of `ℝ` is not
open. -/
@[kb "morris2024" "Exercises 2.1 #6, p. 55"]
theorem morris_exercise_2_1_6 {F : Set ℝ} (hne : F.Nonempty) (hc : F.Countable) : ¬ IsOpen F := by
  intro h
  obtain ⟨a, b, hab, hsub⟩ := h.exists_Ioo_subset hne
  have hcount : (Ioo a b).Countable := hc.mono hsub
  have h1 := Cardinal.mk_Ioo_real hab
  have h2 : Cardinal.mk (Ioo a b) ≤ Cardinal.aleph0 := hcount.le_aleph0
  rw [h1] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

/-- Morris, Topology Without Tears, Exercises 2.1 #4(i). The set of integers is not an open subset
of `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #4(i), p. 55"]
theorem morris_exercise_2_1_4_i : ¬ IsOpen (range ((↑) : ℤ → ℝ)) :=
  morris_exercise_2_1_6 ⟨0, 0, by simp⟩ (countable_range _)

/-- Morris, Topology Without Tears, Exercises 2.1 #4(ii). The set of primes is a closed, but not an
open, subset of `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #4(ii), p. 55"]
theorem morris_exercise_2_1_4_ii :
    IsClosed (((↑) : ℕ → ℝ) '' {p : ℕ | p.Prime}) ∧ ¬ IsOpen (((↑) : ℕ → ℝ) '' {p : ℕ | p.Prime}) :=
  ⟨Nat.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _),
    morris_exercise_2_1_6 ⟨((2 : ℕ) : ℝ), 2, Nat.prime_two, rfl⟩ ((Set.to_countable {p : ℕ | p.Prime}).image _)⟩

/-- Morris, Topology Without Tears, Exercises 2.1 #4(iii). The set of irrational numbers is neither
open nor closed in `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #4(iii), p. 55"]
theorem morris_exercise_2_1_4_iii : ¬ IsOpen {x : ℝ | Irrational x} ∧ ¬ IsClosed {x : ℝ | Irrational x} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hc : IsClosed (range ((↑) : ℚ → ℝ)) := by
      have : range ((↑) : ℚ → ℝ) = {x : ℝ | Irrational x}ᶜ := by
        ext x; simp [Irrational]
      rw [this]; exact h.isClosed_compl
    have hd : Dense (range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have h3 := hd.closure_eq
    rw [hc.closure_eq] at h3
    have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
    have h4 : Real.sqrt 2 ∈ range ((↑) : ℚ → ℝ) := by rw [h3]; trivial
    exact h2 (by simpa using h4)
  · have h3 := dense_irrational.closure_eq
    rw [h.closure_eq] at h3
    have h0 : (0 : ℝ) ∈ {x : ℝ | Irrational x} := by rw [h3]; trivial
    exact h0 (by simp)

/-- Morris, Topology Without Tears, Exercises 2.1 #5. A non-empty finite subset of `ℝ` is closed but
not open. -/
@[kb "morris2024" "Exercises 2.1 #5, p. 55"]
theorem morris_exercise_2_1_5 {F : Set ℝ} (hne : F.Nonempty) (hF : F.Finite) : IsClosed F ∧ ¬ IsOpen F :=
  ⟨hF.isClosed, morris_exercise_2_1_6 hne hF.countable⟩

/-- Morris, Topology Without Tears, Exercises 2.1 #7(i). The set `{0} ∪ {1/n : n ≥ 1}` is closed in
`ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #7(i), p. 55"]
theorem morris_exercise_2_1_7_i : IsClosed (insert (0 : ℝ) (range fun n : ℕ => 1 / ((n : ℝ) + 1))) :=
  (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).isCompact_insert_range.isClosed

/-- Morris, Topology Without Tears, Exercises 2.1 #7(ii). The set `{1/n : n ≥ 1}` is not closed in
`ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #7(ii), p. 55"]
theorem morris_exercise_2_1_7_ii : ¬ IsClosed (range fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro h
  have h0 : (0 : ℝ) ∈ closure (range fun n : ℕ => 1 / ((n : ℝ) + 1)) :=
    mem_closure_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (Eventually.of_forall fun n => mem_range_self n)
  rw [h.closure_eq] at h0
  obtain ⟨n, hn⟩ := h0
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- Morris, Topology Without Tears, Exercises 2.1 #8(ii). Open intervals and closed intervals are
`G_δ`-sets in `ℝ`. -/
@[kb "morris2024" "Exercises 2.1 #8(ii), p. 55"]
theorem morris_exercise_2_1_8_ii (a b : ℝ) : IsGδ (Ioo a b) ∧ IsGδ (Icc a b) :=
  ⟨isOpen_Ioo.isGδ, isClosed_Icc.isGδ⟩

/-- Morris, Topology Without Tears, Exercises 2.1 #8(iii). The set of rationals is an `F_σ`-set in
`ℝ`: a countable union of closed sets. -/
@[kb "morris2024" "Exercises 2.1 #8(iii), p. 55"]
theorem morris_exercise_2_1_8_iii :
    ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧ ⋃ n, F n = range ((↑) : ℚ → ℝ) := by
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  refine ⟨fun n => {((e n : ℚ) : ℝ)}, fun n => isClosed_singleton, ?_⟩
  ext x
  simp only [mem_iUnion, mem_singleton_iff, mem_range]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨e n, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨n, rfl⟩ := he q
    exact ⟨n, rfl⟩

/-- Morris, Topology Without Tears, Exercises 2.1 #8(iv). A set is a `G_δ`-set exactly when its
complement is a countable union of closed sets (an `F_σ`-set). -/
@[kb "morris2024" "Exercises 2.1 #8(iv), p. 55"]
theorem morris_exercise_2_1_8_iv {X : Type*} [TopologicalSpace X] (S : Set X) :
    IsGδ S ↔ ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ Sᶜ = ⋃₀ T := by
  constructor
  · rintro ⟨T, hT, hc, rfl⟩
    refine ⟨compl '' T, ?_, hc.image _, compl_sInter T⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (hT t ht).isClosed_compl
  · rintro ⟨T, hT, hc, h⟩
    refine ⟨compl '' T, ?_, hc.image _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hT t ht).isOpen_compl
    · rw [← compl_sUnion, ← h, compl_compl]

/-- Morris, Topology Without Tears, Exercises 2.2 #3. The open intervals with rational endpoints form
a basis for the euclidean topology on `ℝ`. -/
@[kb "morris2024" "Exercises 2.2 #3, p. 61"]
theorem morris_exercise_2_2_3 :
    IsTopologicalBasis {s : Set ℝ | ∃ a b : ℚ, a < b ∧ s = Ioo (a : ℝ) b} := by
  convert Real.isTopologicalBasis_Ioo_rat using 1
  ext s
  simp

/-- Morris, Topology Without Tears, Exercises 2.2 #4(i). The real line satisfies the second axiom of
countability. -/
@[kb "morris2024" "Exercises 2.2 #4(i), p. 62"]
theorem morris_exercise_2_2_4_i : SecondCountableTopology ℝ :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 2.2 #4(ii). The discrete topology on an uncountable set
does not satisfy the second axiom of countability. -/
@[kb "morris2024" "Exercises 2.2 #4(ii), p. 62"]
theorem morris_exercise_2_2_4_ii {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [Uncountable X] :
    ¬ SecondCountableTopology X := by
  intro h
  have : Countable X := separableSpace_iff_countable.1 inferInstance
  exact not_countable (α := X) inferInstance

/-- Morris, Topology Without Tears, Exercises 2.2 #4(iii). Euclidean `n`-space satisfies the second
axiom of countability. -/
@[kb "morris2024" "Exercises 2.2 #4(iii), p. 62"]
theorem morris_exercise_2_2_4_iii (n : ℕ) : SecondCountableTopology (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 2.2 #5(i). A line `y = m x + c` is a closed subset of
`ℝ²`. -/
@[kb "morris2024" "Exercises 2.2 #5(i), p. 62"]
theorem morris_exercise_2_2_5_i (m c : ℝ) : IsClosed {p : ℝ × ℝ | p.2 = m * p.1 + c} :=
  isClosed_eq continuous_snd (by fun_prop)

/-- Morris, Topology Without Tears, Exercises 2.2 #5(iii). The unit sphere is a closed subset of
Euclidean space of the next dimension. -/
@[kb "morris2024" "Exercises 2.2 #5(iii), p. 62"]
theorem morris_exercise_2_2_5_iii (n : ℕ) :
    IsClosed (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  Metric.isClosed_sphere

/-- Morris, Topology Without Tears, Exercises 2.2 #5(iv). The closed unit ball is a closed subset of
Euclidean `n`-space. -/
@[kb "morris2024" "Exercises 2.2 #5(iv), p. 62"]
theorem morris_exercise_2_2_5_iv (n : ℕ) :
    IsClosed (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  Metric.isClosed_closedBall

/-- Morris, Topology Without Tears, Exercises 2.2 #5(v). The hyperbola `x y = 1` is a closed subset of
`ℝ²`. -/
@[kb "morris2024" "Exercises 2.2 #5(v), p. 62"]
theorem morris_exercise_2_2_5_v : IsClosed {p : ℝ × ℝ | p.1 * p.2 = 1} :=
  isClosed_eq (by fun_prop) continuous_const

/-- Morris, Topology Without Tears, Exercises 2.2 #6. If `B₁` and `B₂` are bases of topologies on `X`
and `Y`, the products `B₁ × B₂` of basic sets form a basis of the product topology. -/
@[kb "morris2024" "Exercises 2.2 #6, p. 63"]
theorem morris_exercise_2_2_6 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {B₁ : Set (Set X)} {B₂ : Set (Set Y)} (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis {s : Set (X × Y) | ∃ u ∈ B₁, ∃ v ∈ B₂, s = u ×ˢ v} := by
  convert h₁.prod h₂ using 1
  ext s
  simp [image2, eq_comm]

/-- Morris, Topology Without Tears, Exercises 2.3 #2(i). If `B` is a basis of a topology and
`B ⊆ B₁ ⊆ τ`, then `B₁` is also a basis of that topology. -/
@[kb "morris2024" "Exercises 2.3 #2(i), p. 68"]
theorem morris_exercise_2_3_2_i {X : Type*} [TopologicalSpace X] {B B₁ : Set (Set X)}
    (hB : IsTopologicalBasis B) (hsub : B ⊆ B₁) (hopen : ∀ u ∈ B₁, IsOpen u) :
    IsTopologicalBasis B₁ :=
  IsTopologicalBasis.of_isOpen_of_subset hopen hB hsub

/-- Morris, Topology Without Tears, Exercises 2.3 #5(i). The rays `(a, ∞)` and `(-∞, b)` form a
subbasis for the euclidean topology on `ℝ`. -/
@[kb "morris2024" "Exercises 2.3 #5(i), p. 69"]
theorem morris_exercise_2_3_5_i :
    (inferInstance : TopologicalSpace ℝ) = generateFrom {s : Set ℝ | ∃ a, s = Ioi a ∨ s = Iio a} :=
  OrderTopology.topology_eq_generate_intervals

end Chapter2

end UndergradKB.Topology.Course
