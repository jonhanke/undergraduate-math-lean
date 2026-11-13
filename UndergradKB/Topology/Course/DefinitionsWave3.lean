import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.GroupTheory.SemidirectProduct
import UndergradKB.Common.Attr

/-! # Course layer (wave 3): definition rows with a Mathlib counterpart

Characterising theorems, in the book's words, for further definitions of Morris, *Topology Without
Tears*, which Mathlib has under other packaging.
-/

open Filter Topology Set

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Definition 1.2.1 (TP-005). The open sets of a topology on `X`
contain `∅` and `X` and are closed under arbitrary unions and finite intersections; a topology is
determined by its open sets. -/
@[kb "morris2024" "Definition 1.2.1, p. 32"]
theorem morris_1_2_1 {X : Type*} (t : TopologicalSpace X) :
    IsOpen[t] (∅ : Set X) ∧ IsOpen[t] (univ : Set X) ∧
      (∀ S : Set (Set X), (∀ U ∈ S, IsOpen[t] U) → IsOpen[t] (⋃₀ S)) ∧
      (∀ U V : Set X, IsOpen[t] U → IsOpen[t] V → IsOpen[t] (U ∩ V)) ∧
      (∀ t' : TopologicalSpace X, (∀ U, IsOpen[t] U ↔ IsOpen[t'] U) → t = t') :=
  ⟨@isOpen_empty X t, @isOpen_univ X t, fun _ h => @isOpen_sUnion X t _ h,
    fun U V hU hV => by
      let _ := t
      exact hU.inter hV, fun _ h => TopologicalSpace.ext (funext fun U => propext (h U))⟩

/-- Morris, Topology Without Tears, Definition 6.3.25 (TP-143). A normed space is a Banach space exactly
when it is complete, that is, when every Cauchy sequence converges. -/
@[kb "morris2024" "Definition 6.3.25, p. 159"]
theorem morris_6_3_25 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CompleteSpace E ↔ ∀ u : ℕ → E, CauchySeq u → ∃ x, Tendsto u atTop (𝓝 x) :=
  ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu, fun h => Metric.complete_of_cauchySeq_tendsto h⟩

/-- Morris, Topology Without Tears, Definition 12.2.4 (TP-347). In a real algebra the multiplication has
a two-sided identity element `1`. -/
@[kb "morris2024" "Definition 12.2.4, p. 377"]
theorem morris_12_2_4_a (A : Type*) [Ring A] [Algebra ℝ A] : ∀ x : A, 1 * x = x ∧ x * 1 = x :=
  fun x => ⟨one_mul x, mul_one x⟩

/-- Morris, Topology Without Tears, Definition 12.2.4 (TP-348). In a real algebra the multiplication is
associative: `x (y z) = (x y) z`. -/
@[kb "morris2024" "Definition 12.2.4, p. 377"]
theorem morris_12_2_4_b (A : Type*) [Ring A] [Algebra ℝ A] :
    ∀ x y z : A, x * (y * z) = (x * y) * z :=
  fun x y z => (mul_assoc x y z).symm

/-- Morris, Topology Without Tears, Definition 12.2.4 (TP-349). A commutative real algebra satisfies
`x y = y x`. -/
@[kb "morris2024" "Definition 12.2.4, p. 377"]
theorem morris_12_2_4_c (A : Type*) [CommRing A] [Algebra ℝ A] : ∀ x y : A, x * y = y * x :=
  fun x y => mul_comm x y

/-- Morris, Topology Without Tears, Definition 12.2.4 (TP-347). The compatibility of the multiplication of
a real algebra with the vector space structure: it is bilinear, `α (x y) = (α x) y = x (α y)`. -/
@[kb "morris2024" "Definition 12.2.4, p. 377"]
theorem morris_12_2_4_d (A : Type*) [Ring A] [Algebra ℝ A] (α : ℝ) (x y z : A) :
    (x + y) * z = x * z + y * z ∧ x * (y + z) = x * y + x * z ∧
      α • (x * y) = (α • x) * y ∧ α • (x * y) = x * (α • y) :=
  ⟨add_mul x y z, mul_add x y z, (smul_mul_assoc α x y).symm, (mul_smul_comm α x y).symm⟩

/-- Morris, Topology Without Tears, Section 12.2 (TP-374). In a C-star algebra the norm satisfies the
C-star identity `‖x* x‖ = ‖x‖²`. -/
@[kb "morris2024" "Section 12.2, p. 389"]
theorem morris_12_2_cstar_a (A : Type*) [NormedRing A] [StarRing A] [CStarRing A] (x : A) :
    ‖star x * x‖ = ‖x‖ ^ 2 := by
  rw [CStarRing.norm_star_mul_self, sq]

/-- Morris, Topology Without Tears, Section 12.2 (TP-375). An isomorphism of C-star algebras is a bijective
linear multiplicative map that preserves the involution. -/
@[kb "morris2024" "Section 12.2, p. 389"]
theorem morris_12_2_cstar_b {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [Ring B] [Algebra ℂ B] [StarRing B] (e : A ≃⋆ₐ[ℂ] B) :
    Function.Bijective e ∧ (∀ x y, e (x * y) = e x * e y) ∧ (∀ (c : ℂ) x, e (c • x) = c • e x) ∧
      (∀ x, e (star x) = star (e x)) :=
  ⟨e.bijective, map_mul e, map_smul e, map_star e⟩

/-- Morris, Topology Without Tears, Definition A1.4.1 (TP-416). In a linearly (totally) ordered set any two
elements are comparable. -/
@[kb "morris2024" "Definition A1.4.1, p. 416"]
theorem morris_A1_4_1 (X : Type*) [LinearOrder X] : ∀ x y : X, x ≤ y ∨ y ≤ x :=
  fun x y => le_total x y

/-- Morris, Topology Without Tears, Definition A5.0.1 (TP-476). The projective space `P(V)` has as points
the one-dimensional subspaces of `V`: two nonzero vectors give the same point iff they differ by a nonzero
scalar, and each point is a one-dimensional subspace. -/
@[kb "morris2024" "Definition A5.0.1, p. 491"]
theorem morris_A5_0_1 (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :
    (∀ (v w : V) (hv : v ≠ 0) (hw : w ≠ 0),
      Projectivization.mk K v hv = Projectivization.mk K w hw ↔ ∃ a : Kˣ, a • w = v) ∧
    (∀ p : Projectivization K V, Module.finrank K p.submodule = 1) :=
  ⟨fun v w hv hw => Projectivization.mk_eq_mk_iff K v w hv hw, fun p => Projectivization.finrank_submodule p⟩

/-- Morris, Topology Without Tears, Definition A5.0.7 (TP-481). In a semidirect product `N ⋊ H` the factor
`N` is normal and every element is written uniquely as `n h`. -/
@[kb "morris2024" "Definition A5.0.7, p. 496"]
theorem morris_A5_0_7_b {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N) :
    (SemidirectProduct.inl : N →* N ⋊[φ] H).range.Normal ∧
    ∀ g : N ⋊[φ] H, ∃! p : N × H, g = SemidirectProduct.inl p.1 * SemidirectProduct.inr p.2 := by
  refine ⟨?_, fun g => ⟨(g.left, g.right), ?_, ?_⟩⟩
  · exact (by rw [SemidirectProduct.range_inl_eq_ker_rightHom]; exact MonoidHom.normal_ker _)
  · exact (SemidirectProduct.inl_left_mul_inr_right g).symm
  · rintro ⟨n, h⟩ hg
    rw [← SemidirectProduct.mk_eq_inl_mul_inr] at hg
    subst hg
    rfl

/-- Morris, Topology Without Tears, Definition A5.6.4 (TP-557). A net of functions converges in the
topology of uniform convergence on the family `M` exactly when it converges uniformly on each member of
`M`. -/
@[kb "morris2024" "Definition A5.6.4, p. 553"]
theorem morris_A5_6_4 {E F ι : Type*} [UniformSpace F] (M : Set (Set E)) (G : ι → UniformOnFun E F M)
    (f : UniformOnFun E F M) (p : Filter ι) :
    Tendsto G p (𝓝 f) ↔
      ∀ s ∈ M, TendstoUniformlyOn (fun i => UniformOnFun.toFun M (G i)) (UniformOnFun.toFun M f) p s :=
  UniformOnFun.tendsto_iff_tendstoUniformlyOn

end UndergradKB.Topology.Course
