import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Order.Sublattice
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Chapter 12.2 (Stone-Weierstrass)

Thin wrappers of Mathlib results in the terms of Morris, *Topology Without Tears*.
-/

open Filter Set
open scoped Topology Polynomial

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition 12.2.1 (TP-344). A family `S` of functions on `X`
separates points when any two distinct points are given different values by some member. -/
@[kb "morris2024" "Definition 12.2.1, p. 375"]
theorem morris_12_2_1 {X Y : Type*} (S : Set (X → Y)) :
    S.SeparatesPoints ↔ ∀ x y : X, x ≠ y → ∃ f ∈ S, f x ≠ f y :=
  Iff.rfl

/-- Morris, Topology Without Tears, Example 12.2.6 (TP-350). `C(X, ℝ)` carries the pointwise
sum, product, scalar multiple and unit, making it a commutative associative unital `ℝ`-algebra. -/
@[kb "morris2024" "Example 12.2.6, p. 377"]
theorem morris_ex_12_2_6 {X : Type*} [TopologicalSpace X] :
    (∀ (f g : C(X, ℝ)) (x : X), (f + g) x = f x + g x ∧ (f * g) x = f x * g x) ∧
      (∀ (c : ℝ) (f : C(X, ℝ)) (x : X), (c • f) x = c * f x) ∧
      (∀ x : X, (1 : C(X, ℝ)) x = 1) ∧
      Nonempty (Algebra ℝ C(X, ℝ)) ∧ (∀ f g : C(X, ℝ), f * g = g * f) :=
  ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => by simp, fun _ => rfl, ⟨inferInstance⟩, mul_comm⟩

/-- Morris, Topology Without Tears, Remark 12.2.10 (TP-354). In a normed algebra, multiplication
`A × A → A` is continuous. -/
@[kb "morris2024" "Remark 12.2.10, p. 378"]
theorem morris_12_2_10 {A : Type*} [NormedRing A] :
    Continuous (fun p : A × A => p.1 * p.2) :=
  continuous_mul

/-- Morris, Topology Without Tears, Proposition 12.2.12 (TP-355). For `X` compact Hausdorff
(nonempty) and `F = ℝ` or `ℂ`, `C(X, F)` with the sup norm is a unital Banach algebra: complete,
submultiplicative norm, and `‖1‖ = 1`. -/
@[kb "morris2024" "Proposition 12.2.12, p. 379"]
theorem morris_12_2_12 {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    {F : Type*} [RCLike F] :
    CompleteSpace C(X, F) ∧ (∀ f g : C(X, F), ‖f * g‖ ≤ ‖f‖ * ‖g‖) ∧ ‖(1 : C(X, F))‖ = 1 :=
  ⟨inferInstance, fun f g => norm_mul_le f g, norm_one⟩

/-- Morris, Topology Without Tears, Definition 12.2.14 (TP-357). Upper and lower bounds of a
subset of a partially ordered set. -/
@[kb "morris2024" "Definition 12.2.14, p. 380"]
theorem morris_12_2_14_a {P : Type*} [PartialOrder P] (s : Set P) :
    upperBounds s = {u | ∀ a ∈ s, a ≤ u} ∧ lowerBounds s = {l | ∀ a ∈ s, l ≤ a} :=
  ⟨rfl, rfl⟩

/-- Morris, Topology Without Tears, Definition 12.2.14 (TP-358). Least upper bound and greatest
lower bound: the least element of the upper bounds, the greatest element of the lower bounds. -/
@[kb "morris2024" "Definition 12.2.14, p. 380"]
theorem morris_12_2_14_b {P : Type*} [PartialOrder P] (s : Set P) (u : P) :
    (IsLUB s u ↔ u ∈ upperBounds s ∧ ∀ v ∈ upperBounds s, u ≤ v) ∧
      (IsGLB s u ↔ u ∈ lowerBounds s ∧ ∀ v ∈ lowerBounds s, v ≤ u) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-- Morris, Topology Without Tears, Definition 12.2.14 (TP-359). In a lattice, the join `x ∨ y`
and meet `x ∧ y` are the least upper bound and greatest lower bound of `{x, y}`. -/
@[kb "morris2024" "Definition 12.2.14, p. 380"]
theorem morris_12_2_14_c {L : Type*} [Lattice L] (x y : L) :
    IsLUB {x, y} (x ⊔ y) ∧ IsGLB {x, y} (x ⊓ y) :=
  ⟨isLUB_pair, isGLB_pair⟩

/-- Morris, Topology Without Tears, Definition 12.2.14 (TP-360). A subset of a lattice closed
under join and meet is itself a lattice (a sublattice). -/
@[kb "morris2024" "Definition 12.2.14, p. 380"]
theorem morris_12_2_14_d {L : Type*} [Lattice L] (S : Set L)
    (hsup : ∀ x ∈ S, ∀ y ∈ S, x ⊔ y ∈ S) (hinf : ∀ x ∈ S, ∀ y ∈ S, x ⊓ y ∈ S) :
    ∃ T : Sublattice L, (T : Set L) = S :=
  ⟨{ carrier := S, supClosed' := hsup, infClosed' := hinf }, rfl⟩

/-- Morris, Topology Without Tears, Example 12.2.15 (TP-361). `C(X, ℝ)` with the pointwise order
is a lattice whose join and meet are the pointwise maximum and minimum. -/
@[kb "morris2024" "Example 12.2.15, p. 380"]
theorem morris_ex_12_2_15 {X : Type*} [TopologicalSpace X] (f g : C(X, ℝ)) (x : X) :
    (f ⊔ g) x = max (f x) (g x) ∧ (f ⊓ g) x = min (f x) (g x) :=
  ⟨rfl, rfl⟩

/-- Morris, Topology Without Tears, Proposition 12.2.17 (TP-362). A closed sublattice `L` of
`C(X, ℝ)`, `X` compact Hausdorff, that for any two points and any prescribed values at them
contains a function with those values, is all of `C(X, ℝ)`. -/
@[kb "morris2024" "Proposition 12.2.17, p. 381"]
theorem morris_12_2_17 {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (L : Set C(X, ℝ)) (hL : IsClosed L)
    (inf_mem : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L) (sup_mem : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L)
    (hsep : ∀ (x y : X) (a b : ℝ), ∃ f ∈ L, f x = a ∧ f y = b) (hne : L.Nonempty) :
    L = Set.univ := by
  have := ContinuousMap.sublattice_closure_eq_top L hne inf_mem sup_mem
    (fun v x y => by simpa using hsep x y (v x) (v y))
  rw [hL.closure_eq] at this
  exact this

/-- Morris, Topology Without Tears, Proposition 12.2.19 (TP-364). A closed subalgebra of
`C(X, ℝ)`, `X` compact Hausdorff, is closed under pointwise maximum and minimum (and absolute
value), i.e. is a closed sublattice. -/
@[kb "morris2024" "Proposition 12.2.19, p. 382"]
theorem morris_12_2_19 {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : IsClosed (A : Set C(X, ℝ))) :
    (∀ f ∈ A, ∀ g ∈ A, f ⊓ g ∈ A) ∧ (∀ f ∈ A, ∀ g ∈ A, f ⊔ g ∈ A) ∧ (∀ f ∈ A, |f| ∈ A) := by
  refine ⟨fun f hf g hg => ContinuousMap.inf_mem_closed_subalgebra A hA ⟨f, hf⟩ ⟨g, hg⟩,
    fun f hf g hg => ContinuousMap.sup_mem_closed_subalgebra A hA ⟨f, hf⟩ ⟨g, hg⟩, fun f hf => ?_⟩
  have := ContinuousMap.abs_mem_subalgebra_closure A ⟨f, hf⟩
  have h2 : A.topologicalClosure = A := SetLike.ext' (by simp)
  rwa [h2] at this

/-- Morris, Topology Without Tears, Remark 12.2.23 (TP-367). Weierstrass approximation as the case
`X = [a, b]` of Stone-Weierstrass: real polynomials are dense in `C([a, b], ℝ)`. -/
@[kb "morris2024" "Remark 12.2.23, p. 384"]
theorem morris_12_2_23 (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f ε hε
  refine ⟨p, fun x => ?_⟩
  have := (ContinuousMap.norm_lt_iff _ hε).mp hp x
  simpa using this

/-- Morris, Topology Without Tears, Section 12.2 (TP-376). Gelfand-Naimark: a commutative unital
C-star algebra is star-isomorphic to `C(X, ℂ)` for a compact Hausdorff space `X` (the character
space), and the isomorphism is the Gelfand transform. -/
@[kb "morris2024" "Section 12.2, p. 389"]
theorem morris_12_2_gelfand_naimark (A : Type u) [CommCStarAlgebra A] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : CompactSpace X) (_ : T2Space X),
      Nonempty (A ≃⋆ₐ[ℂ] C(X, ℂ)) :=
  ⟨_, inferInstance, inferInstance, inferInstance, ⟨gelfandStarTransform A⟩⟩

end UndergradKB.Topology.Course
