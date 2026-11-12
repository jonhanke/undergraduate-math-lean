import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Constructions
import UndergradKB.Common.Attr

/-!
# Topology Without Tears: metric spaces, basic facts (batch B1)

Morris, *Topology Without Tears* (2024), reference key `morris2024`.
-/

namespace UndergradKB.Topology

open Set TopologicalSpace Metric

/-! ### The discrete metric -/

/-- Type synonym carrying the discrete metric (the metric structure is the definition
`discreteMetricSpace`, not a global instance). -/
def DiscreteMetric (X : Type*) : Type _ := X

open scoped Classical in
/-- Morris, Topology Without Tears, Example 6.1.4 (TP-098). The discrete metric on a set: distance
`1` between distinct points and `0` otherwise; this is a metric. -/
@[kb "morris2024" "Example 6.1.4, p. 126", instance_reducible]
noncomputable def discreteMetricSpace (X : Type*) : MetricSpace (DiscreteMetric X) where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  dist_triangle x y z := by
    by_cases hxy : x = y
    · subst hxy; simp
    · by_cases hyz : y = z
      · subst hyz; simp [hxy]
      · by_cases hxz : x = z
        · subst hxz
          simp [hxy, hyz]
        · simp [hxy, hyz, hxz]
  eq_of_dist_eq_zero {x y} h := by
    by_contra hne
    simp [hne] at h

section
attribute [local instance] discreteMetricSpace

open scoped Classical in
/-- Morris, Topology Without Tears, Example 6.1.4 (TP-098). Distinct points of the discrete metric
space are at distance one, and equal points at distance zero. -/
@[kb "morris2024" "Example 6.1.4, p. 126"]
theorem dist_discreteMetric {X : Type*} (x y : DiscreteMetric X) :
    dist x y = if x = y then 0 else 1 := rfl

/-- Morris, Topology Without Tears, Example 6.1.21 (TP-106). The discrete metric induces the
discrete topology. -/
@[kb "morris2024" "Example 6.1.21, p. 133"]
theorem discreteTopology_discreteMetric (X : Type*) : DiscreteTopology (DiscreteMetric X) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun a => ?_
  refine Metric.isOpen_singleton_iff.2 ⟨1, one_pos, fun y hy => ?_⟩
  by_contra hne
  rw [dist_discreteMetric] at hy
  simp [hne] at hy

end

/-! ### Open balls -/

section
variable {X : Type*} [PseudoMetricSpace X]

/-- Morris, Topology Without Tears, Lemma 6.1.15 (TP-102). If `c` lies in the intersection of two
open balls, some open ball around `c` lies inside that intersection. -/
@[kb "morris2024" "Lemma 6.1.15, p. 132"]
theorem exists_ball_subset_ball_inter {x y c : X} {r s : ℝ} (hc : c ∈ ball x r ∩ ball y s) :
    ∃ ε > 0, ball c ε ⊆ ball x r ∩ ball y s :=
  Metric.isOpen_iff.1 (isOpen_ball.inter isOpen_ball) c hc

/-- Morris, Topology Without Tears, Proposition 6.1.17 (TP-104). The open balls of a metric space
form a basis for its (induced) topology. -/
@[kb "morris2024" "Proposition 6.1.17, p. 132"]
theorem isTopologicalBasis_balls :
    IsTopologicalBasis {b : Set X | ∃ (x : X) (r : ℝ), 0 < r ∧ b = ball x r} := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨x, r, -, rfl⟩
    exact isOpen_ball
  · intro a u ha hu
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hu a ha
    exact ⟨ball a ε, ⟨a, ε, hε, rfl⟩, mem_ball_self hε, hsub⟩

/-- Morris, Topology Without Tears, Corollary 6.1.16 (TP-103). The intersection of two open balls is
a union of open balls. -/
@[kb "morris2024" "Corollary 6.1.16, p. 132"]
theorem ball_inter_ball_eq_sUnion (x y : X) (r s : ℝ) :
    ∃ C : Set (Set X), (∀ b ∈ C, ∃ (c : X) (ε : ℝ), 0 < ε ∧ b = ball c ε) ∧
      ball x r ∩ ball y s = ⋃₀ C := by
  obtain ⟨C, hC, hEq⟩ := isTopologicalBasis_balls.open_eq_sUnion
    (isOpen_ball.inter isOpen_ball : IsOpen (ball x r ∩ ball y s))
  exact ⟨C, fun b hb => hC hb, hEq⟩

end

/-! ### Equivalent metrics -/

section
variable {X : Type*}

/-- The topology induced by a metric space structure given as an explicit term. -/
@[instance_reducible]
def inducedTopology (d : MetricSpace X) : TopologicalSpace X :=
  @UniformSpace.toTopologicalSpace X (@PseudoMetricSpace.toUniformSpace X d.toPseudoMetricSpace)

/-- Morris, Topology Without Tears, Definition 6.1.22 (TP-107). Two metrics on a set are equivalent
if they induce the same topology. -/
@[kb "morris2024" "Definition 6.1.22, p. 133"]
def MetricsEquivalent (d₁ d₂ : MetricSpace X) : Prop :=
  inducedTopology d₁ = inducedTopology d₂

/-- Morris, Topology Without Tears, Definition 6.1.22 (TP-107). Equivalence of metrics is an
equivalence relation. -/
@[kb "morris2024" "Definition 6.1.22, p. 133"]
theorem metricsEquivalent_equivalence : Equivalence (MetricsEquivalent (X := X)) where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- The open ball of radius `r` about `x` for a metric given as an explicit term. -/
def ballOf (d : MetricSpace X) (x : X) (r : ℝ) : Set X :=
  @Metric.ball X d.toPseudoMetricSpace x r

/-- One half of the characterisation of equivalent metrics: `d₁` induces a finer topology than
`d₂` when every `d₂`-ball around a point contains a `d₁`-ball around the same point. (Mathlib's
`≤` on topologies reads "finer", so the order below is `d₁ ≤ d₂` as in the statement.) -/
theorem inducedTopology_le_iff (d₁ d₂ : MetricSpace X) :
    inducedTopology d₁ ≤ inducedTopology d₂ ↔
      ∀ x : X, ∀ r : ℝ, 0 < r → ∃ s : ℝ, 0 < s ∧ ballOf d₁ x s ⊆ ballOf d₂ x r := by
  rw [le_iff_nhds]
  refine forall_congr' fun x => ?_
  exact (@Metric.nhds_basis_ball X d₁.toPseudoMetricSpace x).le_basis_iff
    (@Metric.nhds_basis_ball X d₂.toPseudoMetricSpace x)

/-- Morris, Topology Without Tears, Definition 6.1.22 (TP-107). Characterisation: two metrics are
equivalent iff every ball of either contains, around each point, a ball of the other. -/
@[kb "morris2024" "Definition 6.1.22, p. 133"]
theorem metricsEquivalent_iff (d₁ d₂ : MetricSpace X) :
    MetricsEquivalent d₁ d₂ ↔
      (∀ x : X, ∀ r : ℝ, 0 < r → ∃ s : ℝ, 0 < s ∧ ballOf d₁ x s ⊆ ballOf d₂ x r) ∧
      (∀ x : X, ∀ r : ℝ, 0 < r → ∃ s : ℝ, 0 < s ∧ ballOf d₂ x s ⊆ ballOf d₁ x r) := by
  unfold MetricsEquivalent
  rw [le_antisymm_iff, inducedTopology_le_iff, inducedTopology_le_iff]

end

/-! ### Non-metrizable spaces -/

/-- Morris, Topology Without Tears, Remark 6.1.26 (TP-110). An indiscrete space with at least two
points is not metrizable. -/
@[kb "morris2024" "Remark 6.1.26, p. 134"]
theorem not_metrizableSpace_of_indiscrete (X : Type*) [TopologicalSpace X] [IndiscreteTopology X]
    [Nontrivial X] : ¬ MetrizableSpace X := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact hxy (Inseparable.all x y).eq

/-- Morris, Topology Without Tears, Remark 6.1.26 (TP-110). An infinite set with the cofinite
topology is not metrizable. -/
@[kb "morris2024" "Remark 6.1.26, p. 134"]
theorem not_metrizableSpace_cofinite (X : Type*) [Infinite X] :
    ¬ MetrizableSpace (CofiniteTopology X) := by
  intro h
  have : Infinite (CofiniteTopology X) := CofiniteTopology.of.infinite_iff.1 ‹Infinite X›
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (CofiniteTopology X)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
  rw [CofiniteTopology.isOpen_iff] at hU hV
  have h1 := hU ⟨x, hxU⟩
  have h2 := hV ⟨y, hyV⟩
  have : (univ : Set (CofiniteTopology X)).Finite := by
    refine (h1.union h2).subset ?_
    intro z _
    by_contra hz
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hz
    exact Set.disjoint_left.1 hUV hz.1 hz.2
  exact (Set.infinite_univ) this

end UndergradKB.Topology
