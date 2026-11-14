import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-! # Course layer, Morris: exercises of Chapters 8 to 12 (wave 4, part g)

Thin theorems for standard facts that Morris, *Topology Without Tears*, sets as exercises in Chapter 8
(finite products), Chapter 9 (countable products, separability, Lindelof's theorem), Chapter 10
(Tychonoff spaces, first countability, sigma-compactness), Chapter 11 (quotient maps) and Chapter 12
(uniform convergence, Dini's theorem, spaces of continuous functions).
-/

open _root_.Topology

namespace UndergradKB.Topology.Course

open Set Filter TopologicalSpace

section Chapter8

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Morris, Topology Without Tears, Exercises 8.1 #2. The product of two discrete spaces is
discrete. -/
@[kb "morris2024" "Exercises 8.1 #2, p. 197"]
theorem morris_exercise_8_1_2 [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.1 #5. The product of two Hausdorff spaces is
Hausdorff. -/
@[kb "morris2024" "Exercises 8.1 #5, p. 197"]
theorem morris_exercise_8_1_5 [T2Space X] [T2Space Y] : T2Space (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.1 #6. A space `X` is Hausdorff iff the diagonal is
closed in `X × X`. -/
@[kb "morris2024" "Exercises 8.1 #6, p. 197"]
theorem morris_exercise_8_1_6 : T2Space X ↔ IsClosed {p : X × X | p.1 = p.2} :=
  t2_iff_isClosed_diagonal

/-- Morris, Topology Without Tears, Exercises 8.1 #7. Iterated binary products associate up to
homeomorphism. -/
@[kb "morris2024" "Exercises 8.1 #7, p. 197"]
theorem morris_exercise_8_1_7 : Nonempty ((X × Y) × Z ≃ₜ X × Y × Z) :=
  ⟨Homeomorph.prodAssoc X Y Z⟩

/-- Morris, Topology Without Tears, Exercises 8.1 #8(i). Binary products commute up to
homeomorphism. -/
@[kb "morris2024" "Exercises 8.1 #8(i), p. 197"]
theorem morris_exercise_8_1_8_i : Nonempty (X × Y ≃ₜ Y × X) :=
  ⟨Homeomorph.prodComm X Y⟩

/-- Morris, Topology Without Tears, Exercises 8.1 #9(ii). The closure of a product of subsets is the
product of the closures. -/
@[kb "morris2024" "Exercises 8.1 #9(ii), p. 198"]
theorem morris_exercise_8_1_9_ii (C₁ : Set X) (C₂ : Set Y) :
    closure (C₁ ×ˢ C₂) = closure C₁ ×ˢ closure C₂ :=
  closure_prod_eq

/-- Morris, Topology Without Tears, Exercises 8.1 #9(iii). A product of dense subsets is dense in the
product space. -/
@[kb "morris2024" "Exercises 8.1 #9(iii), p. 198"]
theorem morris_exercise_8_1_9_iii {C₁ : Set X} {C₂ : Set Y} (h₁ : Dense C₁) (h₂ : Dense C₂) :
    Dense (C₁ ×ˢ C₂) :=
  h₁.prod h₂

/-- Morris, Topology Without Tears, Exercises 8.1 #9(iv). The product of two separable spaces is
separable. -/
@[kb "morris2024" "Exercises 8.1 #9(iv), p. 198"]
theorem morris_exercise_8_1_9_iv [SeparableSpace X] [SeparableSpace Y] : SeparableSpace (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.1 #9(v). Euclidean `n`-space is separable. -/
@[kb "morris2024" "Exercises 8.1 #9(v), p. 198"]
theorem morris_exercise_8_1_9_v (n : ℕ) : SeparableSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.1 #10. The product of two T1-spaces is a
T1-space. -/
@[kb "morris2024" "Exercises 8.1 #10, p. 198"]
theorem morris_exercise_8_1_10 [T1Space X] [T1Space Y] : T1Space (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.1 #11. The product of two spaces satisfying the second
axiom of countability satisfies it as well. -/
@[kb "morris2024" "Exercises 8.1 #11, p. 198"]
theorem morris_exercise_8_1_11 [SecondCountableTopology X] [SecondCountableTopology Y] :
    SecondCountableTopology (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.2 #2(i). If a product of two spaces is connected, each
factor is connected. -/
@[kb "morris2024" "Exercises 8.2 #2(i), p. 203"]
theorem morris_exercise_8_2_2_i [ConnectedSpace (X × Y)] : ConnectedSpace X := by
  have : Nonempty Y := ⟨(Classical.choice ConnectedSpace.toNonempty : X × Y).2⟩
  exact Function.Surjective.connectedSpace (α := X × Y) (β := X) (f := Prod.fst)
    Prod.fst_surjective continuous_fst

/-- Morris, Topology Without Tears, Exercises 8.2 #2(ii). If a product of two spaces is compact, each
factor is compact. -/
@[kb "morris2024" "Exercises 8.2 #2(ii), p. 203"]
theorem morris_exercise_8_2_2_ii [CompactSpace (X × Y)] [Nonempty Y] : CompactSpace X :=
  Function.Surjective.compactSpace (X := X × Y) (Y := X) (f := Prod.fst) continuous_fst
    Prod.fst_surjective

/-- Morris, Topology Without Tears, Exercises 8.2 #2(iv). If a product of two (non-empty) spaces is
Hausdorff, each factor is Hausdorff. -/
@[kb "morris2024" "Exercises 8.2 #2(iv), p. 203"]
theorem morris_exercise_8_2_2_iv [T2Space (X × Y)] [Nonempty Y] : T2Space X := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  exact T2Space.of_injective_continuous (f := fun x : X => (x, y))
    (fun a b h => (Prod.ext_iff.1 h).1) (by fun_prop)

/-- Morris, Topology Without Tears, Exercises 8.2 #3. A map into a product is continuous iff each
coordinate map is continuous. -/
@[kb "morris2024" "Exercises 8.2 #3, p. 203"]
theorem morris_exercise_8_2_3 (f₁ : Z → X) (f₂ : Z → Y) :
    Continuous (fun z => (f₁ z, f₂ z)) ↔ Continuous f₁ ∧ Continuous f₂ :=
  continuous_prodMk

/-- Morris, Topology Without Tears, Exercises 8.3 #1(i). A compact space is locally compact (every
point has a compact neighbourhood). -/
@[kb "morris2024" "Exercises 8.3 #1(i), p. 208"]
theorem morris_exercise_8_3_1_i [CompactSpace X] : WeaklyLocallyCompactSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.3 #1(iii). A discrete space is locally compact. -/
@[kb "morris2024" "Exercises 8.3 #1(iii), p. 208"]
theorem morris_exercise_8_3_1_iii [DiscreteTopology X] : WeaklyLocallyCompactSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.3 #1(iv). The product of two locally compact spaces
is locally compact. -/
@[kb "morris2024" "Exercises 8.3 #1(iv), p. 208"]
theorem morris_exercise_8_3_1_iv [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Y] :
    WeaklyLocallyCompactSpace (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.3 #1(v). A closed subspace of a locally compact space
is locally compact. -/
@[kb "morris2024" "Exercises 8.3 #1(v), p. 208"]
theorem morris_exercise_8_3_1_v [WeaklyLocallyCompactSpace X] {S : Set X} (hS : IsClosed S) :
    WeaklyLocallyCompactSpace S :=
  hS.weaklyLocallyCompactSpace

/-- Morris, Topology Without Tears, Exercises 8.4 #2(i). The distance function of a metric space is a
continuous map from the product `X × X` to `ℝ`. -/
@[kb "morris2024" "Exercises 8.4 #2(i), p. 216"]
theorem morris_exercise_8_4_2_i {W : Type*} [PseudoMetricSpace W] : Continuous fun p : W × W => dist p.1 p.2 :=
  continuous_dist

/-- Morris, Topology Without Tears, Exercises 8.4 #3. The product of two path-connected spaces is
path-connected. -/
@[kb "morris2024" "Exercises 8.4 #3, p. 216"]
theorem morris_exercise_8_4_3 [PathConnectedSpace X] [PathConnectedSpace Y] : PathConnectedSpace (X × Y) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 8.4 #6(i). The intersection of two connected subsets of
`ℝ` with non-empty intersection is connected. -/
@[kb "morris2024" "Exercises 8.4 #6(i), p. 217"]
theorem morris_exercise_8_4_6_i {A B : Set ℝ} (hA : IsPreconnected A) (hB : IsPreconnected B) :
    IsPreconnected (A ∩ B) := by
  rw [isPreconnected_iff_ordConnected] at *
  exact hA.inter hB

end Chapter8

section Chapter9

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Morris, Topology Without Tears, Exercises 9.2 #1. A product of closed subsets of the factors is
closed in the product space. -/
@[kb "morris2024" "Exercises 9.2 #1, p. 227"]
theorem morris_exercise_9_2_1 {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)] (C : ∀ i, Set (A i))
    (hC : ∀ i, IsClosed (C i)) : IsClosed (Set.pi univ C) :=
  isClosed_set_pi fun i _ => hC i

/-- Morris, Topology Without Tears, Exercises 9.2 #4(a)(i). A product of Hausdorff spaces is
Hausdorff. -/
@[kb "morris2024" "Exercises 9.2 #4(a)(i), p. 228"]
theorem morris_exercise_9_2_4_a_i {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, T2Space (A i)] : T2Space (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.2 #4(a)(ii). A product of T1-spaces is a
T1-space. -/
@[kb "morris2024" "Exercises 9.2 #4(a)(ii), p. 228"]
theorem morris_exercise_9_2_4_a_ii {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, T1Space (A i)] : T1Space (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.2 #4(a)(iii). A product of T0-spaces is a
T0-space. -/
@[kb "morris2024" "Exercises 9.2 #4(a)(iii), p. 228"]
theorem morris_exercise_9_2_4_a_iii {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, T0Space (A i)] : T0Space (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.3 #3. A map into a product is continuous iff each
composition with a projection is continuous. -/
@[kb "morris2024" "Exercises 9.3 #3, p. 235"]
theorem morris_exercise_9_3_3 {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)] (f : Y → ∀ i, A i) :
    Continuous f ↔ ∀ i, Continuous fun y => f y i :=
  continuous_pi_iff

/-- Morris, Topology Without Tears, Exercises 9.3 #4(a)(i). A Hausdorff topology on a finite set is the
discrete topology. -/
@[kb "morris2024" "Exercises 9.3 #4(a)(i), p. 235"]
theorem morris_exercise_9_3_4_a_i [Finite X] [T2Space X] : DiscreteTopology X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.3 #6(i). A countable product of spaces satisfying the
second axiom of countability satisfies it. -/
@[kb "morris2024" "Exercises 9.3 #6(i), p. 236"]
theorem morris_exercise_9_3_6_i {A : ℕ → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, SecondCountableTopology (A i)] : SecondCountableTopology (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.4 #1. A continuous image of a separable space is
separable. -/
@[kb "morris2024" "Exercises 9.4 #1, p. 243"]
theorem morris_exercise_9_4_1 [SeparableSpace X] {f : X → Y} (hf : Continuous f)
    (hs : Function.Surjective f) : SeparableSpace Y :=
  hs.denseRange.separableSpace hf

/-- Morris, Topology Without Tears, Exercises 9.4 #2. A countable product of separable spaces is
separable. -/
@[kb "morris2024" "Exercises 9.4 #2, p. 244"]
theorem morris_exercise_9_4_2 {A : ℕ → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, SeparableSpace (A i)] :
    SeparableSpace (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 9.4 #7 (Lindelof's theorem). Every open covering of a
second countable space has a countable subcovering. -/
@[kb "morris2024" "Exercises 9.4 #7, p. 244"]
theorem morris_exercise_9_4_7 [SecondCountableTopology X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    ∃ T : Set ι, T.Countable ∧ ⋃ i ∈ T, U i = univ := by
  obtain ⟨T, hT, h⟩ := isOpen_iUnion_countable U hU
  exact ⟨T, hT, h.trans hcov⟩

/-- Morris, Topology Without Tears, Exercises 9.4 #12(i). A separable space satisfies the countable
chain condition: every family of pairwise disjoint non-empty open sets is countable. -/
@[kb "morris2024" "Exercises 9.4 #12(i), p. 245"]
theorem morris_exercise_9_4_12_i [SeparableSpace X] (𝒰 : Set (Set X)) (hd : 𝒰.PairwiseDisjoint id)
    (ho : ∀ u ∈ 𝒰, IsOpen u) (hne : ∀ u ∈ 𝒰, u.Nonempty) : 𝒰.Countable :=
  hd.countable_of_isOpen ho hne

end Chapter9

section Chapter10

variable {X : Type*} [TopologicalSpace X]

/-- Morris, Topology Without Tears, Exercises 10.3 #2. Any product of regular spaces is regular. -/
@[kb "morris2024" "Exercises 10.3 #2, p. 299"]
theorem morris_exercise_10_3_2 {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, RegularSpace (A i)] : RegularSpace (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #3. A closed subspace of a normal space is
normal. -/
@[kb "morris2024" "Exercises 10.3 #3, p. 299"]
theorem morris_exercise_10_3_3 [NormalSpace X] {S : Set X} (hS : IsClosed S) : NormalSpace S :=
  hS.isClosedEmbedding_subtypeVal.normalSpace

/-- Morris, Topology Without Tears, Exercises 10.3 #6. A Tychonoff (completely regular T1) space is a
regular T1-space. -/
@[kb "morris2024" "Exercises 10.3 #6, p. 300"]
theorem morris_exercise_10_3_6 [T35Space X] : T3Space X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #8(i). Every metrizable space is first countable. -/
@[kb "morris2024" "Exercises 10.3 #8(i), p. 301"]
theorem morris_exercise_10_3_8_i {W : Type*} [PseudoMetricSpace W] : FirstCountableTopology W :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #8(ii). Every second countable space is first
countable. -/
@[kb "morris2024" "Exercises 10.3 #8(ii), p. 301"]
theorem morris_exercise_10_3_8_ii [SecondCountableTopology X] : FirstCountableTopology X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #8(iii). A countable product of first countable
spaces is first countable. -/
@[kb "morris2024" "Exercises 10.3 #8(iii), p. 301"]
theorem morris_exercise_10_3_8_iii {A : ℕ → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, FirstCountableTopology (A i)] : FirstCountableTopology (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #8(iv). Every subspace of a first countable space
is first countable. -/
@[kb "morris2024" "Exercises 10.3 #8(iv), p. 301"]
theorem morris_exercise_10_3_8_iv [FirstCountableTopology X] (S : Set X) : FirstCountableTopology S :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #10. Every subspace of a Tychonoff space is
Tychonoff. -/
@[kb "morris2024" "Exercises 10.3 #10, p. 301"]
theorem morris_exercise_10_3_10 [T35Space X] (S : Set X) : T35Space S :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #11. A topological group is a regular space. -/
@[kb "morris2024" "Exercises 10.3 #11, p. 301"]
theorem morris_exercise_10_3_11 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    RegularSpace G :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #12. Any product of connected spaces is
connected. -/
@[kb "morris2024" "Exercises 10.3 #12, p. 302"]
theorem morris_exercise_10_3_12 {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    [∀ i, ConnectedSpace (A i)] : ConnectedSpace (∀ i, A i) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #22(ii). Every compact space is sigma-compact. -/
@[kb "morris2024" "Exercises 10.3 #22(ii), p. 304"]
theorem morris_exercise_10_3_22_ii [CompactSpace X] : SigmaCompactSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #22(iii). Euclidean `n`-space is sigma-compact. -/
@[kb "morris2024" "Exercises 10.3 #22(iii), p. 304"]
theorem morris_exercise_10_3_22_iii (n : ℕ) : SigmaCompactSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #22(vi). Every sigma-compact space is a Lindelof
space. -/
@[kb "morris2024" "Exercises 10.3 #22(vi), p. 304"]
theorem morris_exercise_10_3_22_vi [SigmaCompactSpace X] : LindelofSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 10.3 #22(vii). The product of two sigma-compact spaces
is sigma-compact. -/
@[kb "morris2024" "Exercises 10.3 #22(vii), p. 304"]
theorem morris_exercise_10_3_22_vii {Y : Type*} [TopologicalSpace Y] [SigmaCompactSpace X]
    [SigmaCompactSpace Y] : SigmaCompactSpace (X × Y) :=
  inferInstance

end Chapter10

section Chapter11

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Morris, Topology Without Tears, Exercises 11.1 #4. The composite of two quotient maps is a
quotient map. -/
@[kb "morris2024" "Exercises 11.1 #4, p. 342"]
theorem morris_exercise_11_1_4 {f : X → Y} {g : Y → Z} (hg : IsQuotientMap g) (hf : IsQuotientMap f) :
    IsQuotientMap (g ∘ f) :=
  hg.comp hf

/-- Morris, Topology Without Tears, Exercises 11.1 #8. A quotient space of a sequential space is
sequential. -/
@[kb "morris2024" "Exercises 11.1 #8, p. 342"]
theorem morris_exercise_11_1_8 [SequentialSpace X] {f : X → Y} (hf : IsQuotientMap f) :
    SequentialSpace Y :=
  hf.sequentialSpace

/-- Morris, Topology Without Tears, Exercises 11.1 #12(ii). A quotient space of a first countable space
is sequential. -/
@[kb "morris2024" "Exercises 11.1 #12(ii), p. 343"]
theorem morris_exercise_11_1_12_ii [FirstCountableTopology X] {f : X → Y} (hf : IsQuotientMap f) :
    SequentialSpace Y :=
  hf.sequentialSpace

end Chapter11

section Chapter12

/-- Morris, Topology Without Tears, Exercises 12.1 #7(i). A uniform limit of continuous real functions
on a set is continuous. -/
@[kb "morris2024" "Exercises 12.1 #7(i), p. 371"]
theorem morris_exercise_12_1_7_i {S : Set ℝ} {p : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hp : ∀ n, ContinuousOn (p n) S) (hu : TendstoUniformlyOn p f atTop S) : ContinuousOn f S :=
  hu.continuousOn (Eventually.of_forall hp).frequently

/-- Morris, Topology Without Tears, Exercises 12.1 #7(ii). The space `C[0, 1]` of continuous real
functions on `[0, 1]` with the sup norm is complete. -/
@[kb "morris2024" "Exercises 12.1 #7(ii), p. 371"]
theorem morris_exercise_12_1_7_ii : CompleteSpace C(Icc (0 : ℝ) 1, ℝ) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 12.1 #7(iii). For a compact space `X`, the space of
continuous real functions on `X` with the sup norm is complete. -/
@[kb "morris2024" "Exercises 12.1 #7(iii), p. 371"]
theorem morris_exercise_12_1_7_iii {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    CompleteSpace C(X, ℝ) :=
  inferInstance

/-- Morris, Topology Without Tears, Exercises 12.1 #8 (Dini's theorem). On a compact set, a decreasing
sequence of continuous functions converging pointwise to a continuous function converges uniformly. -/
@[kb "morris2024" "Exercises 12.1 #8, p. 371"]
theorem morris_exercise_12_1_8 {K : Set ℝ} (hK : IsCompact K) {p : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hp : ∀ n, ContinuousOn (p n) K) (hanti : ∀ x ∈ K, Antitone fun n => p n x)
    (hf : ContinuousOn f K) (hconv : ∀ x ∈ K, Tendsto (fun n => p n x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn p f atTop K :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hK hp hanti hf hconv

end Chapter12

end UndergradKB.Topology.Course
