import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import UndergradKB.Common.Attr

/-! # Course layer, Morris: further examples and remarks (wave 3, part 1)

Thin theorems for examples and remarks of Morris, *Topology Without Tears*, that state a real
mathematical fact and were not rows of the checklist: concrete non-examples of topologies, closed and
open sets, metric topologies, a non-metrizable continuous image of the Cantor space, and so on.
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace Metric

section Examples

/-- Morris, Topology Without Tears, Example 1.1.5. The collection consisting of `ℕ`, `∅` and the finite
subsets of `ℕ` is not the family of open sets of any topology on `ℕ`: it is not closed under infinite
unions. -/
@[kb "morris2024" "Example 1.1.5, p. 26"]
theorem morris_ex_1_1_5 :
    ¬ ∃ t : TopologicalSpace ℕ, ∀ s : Set ℕ, IsOpen[t] s ↔ (s = univ ∨ s.Finite) := by
  rintro ⟨t, ht⟩
  have h1 : ∀ n : ℕ, IsOpen[t] ({n} : Set ℕ) := fun n => (ht _).2 (Or.inr (finite_singleton n))
  have h2 : IsOpen[t] (Ici 2 : Set ℕ) := by
    have : (⋃ n ∈ (Ici 2 : Set ℕ), ({n} : Set ℕ)) = Ici 2 := biUnion_of_singleton _
    rw [← this]
    exact isOpen_biUnion fun n _ => h1 n
  rcases (ht _).1 h2 with h | h
  · have : (0 : ℕ) ∈ (Ici 2 : Set ℕ) := by rw [h]; trivial
    simp at this
  · exact (Set.Ici_infinite (2 : ℕ)) h

/-- Morris, Topology Without Tears, Example 1.3.2. In the finite-closed topology on `ℕ`, every finite
set is closed, while the set of even numbers is not closed (so its complement, the odd numbers, is
not open). -/
@[kb "morris2024" "Example 1.3.2, p. 39"]
theorem morris_ex_1_3_2 :
    (∀ s : Set (CofiniteTopology ℕ), s.Finite → IsClosed s) ∧
    ¬ IsClosed (CofiniteTopology.of '' {n : ℕ | Even n}) := by
  refine ⟨fun s hs => CofiniteTopology.isClosed_iff.2 (Or.inr hs), ?_⟩
  intro h
  rcases CofiniteTopology.isClosed_iff.1 h with h | h
  · have h1 : CofiniteTopology.of (1 : ℕ) ∈ (CofiniteTopology.of '' {n : ℕ | Even n}) := by
      rw [h]; trivial
    obtain ⟨m, hm, hm1⟩ := h1
    have : m = 1 := CofiniteTopology.of.injective hm1
    subst this
    exact absurd hm (by decide)
  · have hinf : ({n : ℕ | Even n}).Infinite :=
      Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
        (fun a b hab => by simpa using hab) (fun n => even_two_mul n)
    exact hinf (h.of_finite_image CofiniteTopology.of.injective.injOn)

/-- Morris, Topology Without Tears, Example 1.3.3. If the finite-closed topology on a set `X` has at
least three distinct clopen sets, then `X` is finite. -/
@[kb "morris2024" "Example 1.3.3, p. 40"]
theorem morris_ex_1_3_3 {X : Type*}
    (h : ∃ a b c : Set (CofiniteTopology X), IsClopen a ∧ IsClopen b ∧ IsClopen c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c) : Finite X := by
  by_contra hX
  have hX' : Infinite X := not_finite_iff_infinite.1 hX
  have hI : Infinite (CofiniteTopology X) := CofiniteTopology.of.infinite_iff.1 hX'
  have key : ∀ s : Set (CofiniteTopology X), IsClopen s → s = ∅ ∨ s = univ := by
    intro s hs
    rcases CofiniteTopology.isOpen_iff'.1 hs.isOpen with h1 | h1
    · exact Or.inl h1
    rcases CofiniteTopology.isClosed_iff.1 hs.isClosed with h2 | h2
    · exact Or.inr h2
    · exact absurd (by simpa using h2.union h1) (infinite_univ (α := CofiniteTopology X))
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := h
  rcases key a ha with rfl | rfl <;> rcases key b hb with rfl | rfl <;>
    rcases key c hc with rfl | rfl <;> simp_all

/-- Morris, Topology Without Tears, Example 3.1.7 (i). The set `[a, b)` is not closed in `ℝ`. -/
@[kb "morris2024" "Example 3.1.7, p. 76"]
theorem morris_ex_3_1_7_a {a b : ℝ} (hab : a < b) : ¬ IsClosed (Ico a b) := by
  intro h
  have hb : b ∈ closure (Ico a b) := by rw [closure_Ico hab.ne]; exact ⟨hab.le, le_rfl⟩
  rw [h.closure_eq] at hb
  exact lt_irrefl _ hb.2

/-- Morris, Topology Without Tears, Example 3.1.7 (ii). The set `[a, b]` is closed in `ℝ`. -/
@[kb "morris2024" "Example 3.1.7, p. 76"]
theorem morris_ex_3_1_7_b (a b : ℝ) : IsClosed (Icc a b) := isClosed_Icc

/-- Morris, Topology Without Tears, Example 3.1.7 (iii). The set `(a, b)` is not closed in `ℝ`. -/
@[kb "morris2024" "Example 3.1.7, p. 76"]
theorem morris_ex_3_1_7_c {a b : ℝ} (hab : a < b) : ¬ IsClosed (Ioo a b) := by
  intro h
  have ha : a ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩
  rw [h.closure_eq] at ha
  exact lt_irrefl _ ha.1

/-- Morris, Topology Without Tears, Example 3.1.7 (iv). The set `[a, ∞)` is closed in `ℝ`. -/
@[kb "morris2024" "Example 3.1.7, p. 76"]
theorem morris_ex_3_1_7_d (a : ℝ) : IsClosed (Ici a) := isClosed_Ici

/-- Morris, Topology Without Tears, Example 4.1.5. In the subspace `[1, 2]` of `ℝ` the set `[1, 3/2)`
is open although it is not open in `ℝ`; likewise `(1, 2]` and `[1, 2]` itself are open in the
subspace but not in `ℝ`. -/
@[kb "morris2024" "Example 4.1.5, p. 92"]
theorem morris_ex_4_1_5 :
    (IsOpen {x : Icc (1 : ℝ) 2 | (x : ℝ) < 3 / 2} ∧ ¬ IsOpen (Ico (1 : ℝ) (3 / 2))) ∧
    (IsOpen {x : Icc (1 : ℝ) 2 | 1 < (x : ℝ)} ∧ ¬ IsOpen (Ioc (1 : ℝ) 2)) ∧
    (IsOpen (univ : Set (Icc (1 : ℝ) 2)) ∧ ¬ IsOpen (Icc (1 : ℝ) 2)) := by
  refine ⟨⟨isOpen_lt continuous_subtype_val continuous_const, ?_⟩,
    ⟨isOpen_lt continuous_const continuous_subtype_val, ?_⟩, ⟨isOpen_univ, ?_⟩⟩
  · intro h
    have := h.mem_nhds (show (1 : ℝ) ∈ Ico (1 : ℝ) (3 / 2) from ⟨le_rfl, by norm_num⟩)
    rw [Ico_mem_nhds_iff] at this
    exact lt_irrefl _ this.1
  · intro h
    have := h.mem_nhds (show (2 : ℝ) ∈ Ioc (1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩)
    rw [Ioc_mem_nhds_iff] at this
    exact lt_irrefl _ this.2
  · intro h
    have := h.mem_nhds (show (1 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨le_rfl, by norm_num⟩)
    rw [Icc_mem_nhds_iff] at this
    exact lt_irrefl _ this.1

/-- Morris, Topology Without Tears, Example 6.1.18. The euclidean metric on `ℝ` induces the euclidean
topology: a set is open iff around each of its points it contains an interval `(x - δ, x + δ)`. -/
@[kb "morris2024" "Example 6.1.18, p. 132"]
theorem morris_ex_6_1_18 (s : Set ℝ) :
    IsOpen s ↔ ∀ x ∈ s, ∃ δ > 0, Ioo (x - δ) (x + δ) ⊆ s := by
  rw [Metric.isOpen_iff]
  simp only [Real.ball_eq_Ioo]

/-- Morris, Topology Without Tears, Example 6.1.19. The euclidean metric on `ℝ²` induces the euclidean
(product) topology: the identity is a homeomorphism from the euclidean plane to `ℝ × ℝ`. -/
@[kb "morris2024" "Example 6.1.19, p. 133"]
theorem morris_ex_6_1_19 :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ (ℝ × ℝ), ∀ p, (h p).1 = p 0 ∧ (h p).2 = p 1 :=
  ⟨(EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow), fun _ => ⟨rfl, rfl⟩⟩

/-- Morris, Topology Without Tears, Example 6.1.20. The metric `d*` on `ℝ²` (the maximum of the two
coordinate distances) induces the euclidean topology: a set is open iff around each of its points it
contains a square `(x - ε, x + ε) × (y - ε, y + ε)`. -/
@[kb "morris2024" "Example 6.1.20, p. 133"]
theorem morris_ex_6_1_20 (s : Set (ℝ × ℝ)) :
    IsOpen s ↔ ∀ p ∈ s, ∃ ε > 0, Ioo (p.1 - ε) (p.1 + ε) ×ˢ Ioo (p.2 - ε) (p.2 + ε) ⊆ s := by
  rw [Metric.isOpen_iff]
  simp only [← Real.ball_eq_Ioo]
  refine forall₂_congr fun p _ => ?_
  rw [← Prod.mk.eta (p := p)]
  simp [ball_prod_same]

end Examples

end UndergradKB.Topology.Course
