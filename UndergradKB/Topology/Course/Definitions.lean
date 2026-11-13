import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import UndergradKB.Common.Attr

/-! # Course layer: definition rows with a Mathlib counterpart

Characterising theorems, in the book's words, for definitions of Morris, *Topology Without Tears*, which
Mathlib has under other packaging. -/

open Filter Topology Set Cardinal
open scoped Uniformity

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition 1.3.4 (TP-012). Injective, surjective and bijective maps in
the usual sense. -/
@[kb "morris2024" "Definition 1.3.4, p. 41"]
theorem morris_1_3_4 {X Y : Type*} (f : X → Y) :
    (Function.Injective f ↔ ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂) ∧
      (Function.Surjective f ↔ ∀ y, ∃ x, f x = y) ∧
      (Function.Bijective f ↔ Function.Injective f ∧ Function.Surjective f) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Morris, Topology Without Tears, Definition 1.3.5 (TP-013). A map has a two-sided inverse function
exactly when it is bijective. -/
@[kb "morris2024" "Definition 1.3.5, p. 41"]
theorem morris_1_3_5 {X Y : Type*} (f : X → Y) :
    (∃ g : Y → X, (∀ x, g (f x) = x) ∧ ∀ y, f (g y) = y) ↔ Function.Bijective f :=
  Function.bijective_iff_has_inverse.symm

/-- Morris, Topology Without Tears, Definition 6.3.5 (TP-125). A sequence of indices defines a subsequence
when it is strictly increasing, i.e. each index is smaller than the next. -/
@[kb "morris2024" "Definition 6.3.5, p. 151"]
theorem morris_6_3_5 (φ : ℕ → ℕ) : StrictMono φ ↔ ∀ n, φ n < φ (n + 1) :=
  ⟨fun h n => h n.lt_succ_self, strictMono_nat_of_lt_succ⟩

/-- Morris, Topology Without Tears, Definition 6.3.6 (TP-126). A real sequence is increasing iff each term
is at most the next. -/
@[kb "morris2024" "Definition 6.3.6, p. 151"]
theorem morris_6_3_6_a (u : ℕ → ℝ) : Monotone u ↔ ∀ n, u n ≤ u (n + 1) :=
  ⟨fun h n => h n.le_succ, monotone_nat_of_le_succ⟩

/-- Morris, Topology Without Tears, Definition 6.3.6 (TP-126). A real sequence is decreasing iff each term
is at least the next. -/
@[kb "morris2024" "Definition 6.3.6, p. 151"]
theorem morris_6_3_6_b (u : ℕ → ℝ) : Antitone u ↔ ∀ n, u (n + 1) ≤ u n :=
  ⟨fun h n => h n.le_succ, antitone_nat_of_succ_le⟩

/-- Morris, Topology Without Tears, Definition 6.4.1 (TP-144). A point `x` is a fixed point of `f` iff
`f x = x`. -/
@[kb "morris2024" "Definition 6.4.1, p. 162"]
theorem morris_6_4_1 {X : Type*} (f : X → X) (x : X) : Function.IsFixedPt f x ↔ f x = x :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition 6.5.14 (TP-158). A subset of a real vector space is convex
iff it contains the open segment between any two of its points. -/
@[kb "morris2024" "Definition 6.5.14, p. 168"]
theorem morris_6_5_14 {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) :
    Convex ℝ s ↔ ∀ x ∈ s, ∀ y ∈ s, openSegment ℝ x y ⊆ s :=
  ⟨fun h x hx y hy => convex_iff_openSegment_subset.1 h hx hy,
    fun h => convex_iff_openSegment_subset.2 fun x hx y hy => h x hx y hy⟩

/-- Morris, Topology Without Tears, Definition 12.2.7 (TP-351). A subset of a (unital) algebra `A` that
contains `1` and is closed under addition, scalar multiplication and product is exactly the underlying set
of a subalgebra. -/
@[kb "morris2024" "Definition 12.2.7, p. 378"]
theorem morris_12_2_7 {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (S : Set A) :
    (∃ B : Subalgebra R A, (B : Set A) = S) ↔
      (1 ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) ∧ (∀ (c : R), ∀ x ∈ S, c • x ∈ S) ∧
        ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.one_mem, fun x hx y hy => B.add_mem hx hy, fun c x hx => B.smul_mem hx c,
      fun x hx y hy => B.mul_mem hx hy⟩
  · rintro ⟨h1, hadd, hsmul, hmul⟩
    refine ⟨{ carrier := S
              mul_mem' := fun {x y} hx hy => hmul x hx y hy
              one_mem' := h1
              add_mem' := fun {x y} hx hy => hadd x hx y hy
              zero_mem' := by simpa using hsmul 0 1 h1
              algebraMap_mem' := fun r => by
                rw [Algebra.algebraMap_eq_smul_one]
                exact hsmul r 1 h1 }, rfl⟩

/-- Morris, Topology Without Tears, Definition 12.2.9 (TP-352). In a normed algebra over a normed field the
norm is submultiplicative and homogeneous. -/
@[kb "morris2024" "Definition 12.2.9, p. 378"]
theorem morris_12_2_9 {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] :
    (∀ x y : A, ‖x * y‖ ≤ ‖x‖ * ‖y‖) ∧ ∀ (c : 𝕜) (x : A), ‖c • x‖ = ‖c‖ * ‖x‖ :=
  ⟨fun x y => norm_mul_le x y, fun c x => norm_smul c x⟩

/-- Morris, Topology Without Tears, Definition 12.2.13 (TP-356). A partial order is reflexive,
antisymmetric and transitive. -/
@[kb "morris2024" "Definition 12.2.13, p. 379"]
theorem morris_12_2_13 {P : Type*} [PartialOrder P] :
    (∀ a : P, a ≤ a) ∧ (∀ a b : P, a ≤ b → b ≤ a → a = b) ∧ (∀ a b c : P, a ≤ b → b ≤ c → a ≤ c) :=
  ⟨fun _ => le_rfl, fun _ _ => le_antisymm, fun _ _ _ => le_trans⟩

/-- Morris, Topology Without Tears, Definition A1.1.30 (TP-391). The power set of `S` is the set of all
subsets of `S`: a set is a member iff it is a subset, and the power set of the whole of `S` is every subset. -/
@[kb "morris2024" "Definition A1.1.30, p. 402"]
theorem morris_A1_1_30 (S : Type u) :
    (∀ s t : Set S, t ∈ s.powerset ↔ t ⊆ s) ∧ (Set.univ : Set S).powerset = Set.univ :=
  ⟨fun _ _ => Iff.rfl, Set.powerset_univ⟩

/-- Morris, Topology Without Tears, Definition A1.2.2 (TP-399). Two sets have the same cardinal number iff
they are equipotent, and `ℵ₀` is the cardinal number of `ℕ`. -/
@[kb "morris2024" "Definition A1.2.2, p. 407"]
theorem morris_A1_2_2 (A B : Type u) : (#A = #B ↔ Nonempty (A ≃ B)) ∧ #ℕ = ℵ₀ :=
  ⟨Cardinal.eq, Cardinal.mk_nat⟩

/-- Morris, Topology Without Tears, Definition A1.4.19 (TP-425). The successor of an ordinal `o` is `o + 1`,
and a limit ordinal is a nonzero ordinal that is not a successor. -/
@[kb "morris2024" "Definition A1.4.19, p. 422"]
theorem morris_A1_4_19 :
    (∀ o : Ordinal, Order.succ o = o + 1) ∧
      ∀ o : Ordinal, Order.IsSuccLimit o ↔ o ≠ 0 ∧ ∀ a, Order.succ a ≠ o :=
  ⟨fun o => Order.succ_eq_add_one o, fun o => by
    rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_ne]⟩

/-- Morris, Topology Without Tears, Remark A5.6.3 (TP-556). On a topological group the topologies arising
from the right and the left uniformity (whose entourages are the preimages of neighbourhoods of the identity
under `(x, y) ↦ y x⁻¹`, resp. `(x, y) ↦ x⁻¹ y`) are the given topology. -/
@[kb "morris2024" "Remark A5.6.3, p. 552"]
theorem morris_A5_6_3 (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (𝓤[IsTopologicalGroup.rightUniformSpace G] = comap (fun p : G × G => p.2 * p.1⁻¹) (𝓝 1) ∧
      (IsTopologicalGroup.rightUniformSpace G).toTopologicalSpace = ‹TopologicalSpace G›) ∧
    (𝓤[IsTopologicalGroup.leftUniformSpace G] = comap (fun p : G × G => p.1⁻¹ * p.2) (𝓝 1) ∧
      (IsTopologicalGroup.leftUniformSpace G).toTopologicalSpace = ‹TopologicalSpace G›) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end UndergradKB.Topology.Course
