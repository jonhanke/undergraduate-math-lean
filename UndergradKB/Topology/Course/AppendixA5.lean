import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Complex.Circle
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Appendix 5 (topological groups, duality)

Thin wrappers of Mathlib results in the terms of Morris, *Topology Without Tears*.
-/

open Set Filter
open scoped Topology Uniformity commutatorElement

namespace UndergradKB.Topology.Course

/-- Morris, Topology Without Tears, Definition A5.0.2 (TP-477). The circle group consists of the
complex numbers of modulus one. -/
@[kb "morris2024" "Definition A5.0.2, p. 494"]
theorem morris_A5_0_2 (z : Circle) : ‖(z : ℂ)‖ = 1 := by simp

/-- Morris, Topology Without Tears, Definition A5.0.4 (TP-478). A complex `n × n` matrix lies in
`GL(n, ℂ)` exactly when its determinant is nonzero. -/
@[kb "morris2024" "Definition A5.0.4, p. 495"]
theorem morris_A5_0_4 (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (∃ g : Matrix.GeneralLinearGroup (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) = M) ↔
      M.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun ⟨g, hg⟩ => hg ▸ g.isUnit, fun h => ⟨h.unit, h.unit_spec⟩⟩

/-- Morris, Topology Without Tears, Definition A5.0.6 (TP-479). The product group multiplies
coordinatewise. -/
@[kb "morris2024" "Definition A5.0.6, p. 495"]
theorem morris_A5_0_6 {G H : Type*} [Group G] [Group H] (g g' : G) (h h' : H) :
    (g, h) * (g', h') = (g * g', h * h') :=
  rfl

/-- Morris, Topology Without Tears, Definition A5.0.7 (TP-480). The quotient of a group by the
kernel of a homomorphism is isomorphic to the image (first isomorphism theorem). -/
@[kb "morris2024" "Definition A5.0.7, p. 495"]
theorem morris_A5_0_7 {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty ((G ⧸ f.ker) ≃* f.range) :=
  ⟨QuotientGroup.quotientKerEquivRange f⟩

/-- Morris, Topology Without Tears, Definition A5.0.8 (TP-483). A topological group is a group
whose multiplication and inversion are continuous. -/
@[kb "morris2024" "Definition A5.0.8, p. 496"]
theorem morris_A5_0_8 (G : Type*) [Group G] [TopologicalSpace G] :
    IsTopologicalGroup G ↔
      Continuous (fun p : G × G => p.1 * p.2) ∧ Continuous (fun x : G => x⁻¹) :=
  ⟨fun _ => ⟨continuous_mul, continuous_inv⟩, fun ⟨h1, h2⟩ =>
    { toContinuousMul := ⟨h1⟩, toContinuousInv := ⟨h2⟩ }⟩

/-- Morris, Topology Without Tears, Definition A5.0.10 (TP-484). A group isomorphism which is a
homeomorphism is a topological isomorphism. -/
@[kb "morris2024" "Definition A5.0.10, p. 497"]
theorem morris_A5_0_10 {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] (e : G ≃* H) (h1 : Continuous e) (h2 : Continuous e.symm) :
    ∃ f : G ≃ₜ* H, ∀ x, f x = e x :=
  ⟨{ e with continuous_toFun := h1, continuous_invFun := h2 }, fun _ => rfl⟩

/-- Morris, Topology Without Tears, Definition A5.0.15 (TP-489). The dual group of a compact
abelian group (continuous homomorphisms to the circle) is discrete. -/
@[kb "morris2024" "Definition A5.0.15, p. 503"]
theorem morris_A5_0_15 (G : Type*) [CommGroup G] [TopologicalSpace G] [CompactSpace G] :
    DiscreteTopology (PontryaginDual G) :=
  inferInstance

/-- Morris, Topology Without Tears, Definition A5.0.29 (TP-501). The commutator is
`g h g⁻¹ h⁻¹`, and commutators lie in the commutator subgroup. -/
@[kb "morris2024" "Definition A5.0.29, p. 511"]
theorem morris_A5_0_29 {G : Type*} [Group G] (g h : G) :
    ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ ∧ ⁅g, h⁆ ∈ commutator G :=
  ⟨commutatorElement_def g h, Subgroup.commutator_mem_commutator trivial trivial⟩

/-- Morris, Topology Without Tears, Proposition A5.1.5 (TP-506). Left translation in a
topological group is a homeomorphism. -/
@[kb "morris2024" "Proposition A5.1.5, p. 515"]
theorem morris_A5_1_5_a {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : G) : ∃ h : G ≃ₜ G, ∀ x, h x = a * x :=
  ⟨Homeomorph.mulLeft a, fun _ => rfl⟩

/-- Morris, Topology Without Tears, Proposition A5.1.5 (TP-506). Right translation in a
topological group is a homeomorphism. -/
@[kb "morris2024" "Proposition A5.1.5, p. 515"]
theorem morris_A5_1_5_b {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : G) : ∃ h : G ≃ₜ G, ∀ x, h x = x * a :=
  ⟨Homeomorph.mulRight a, fun _ => rfl⟩

/-- Morris, Topology Without Tears, Proposition A5.1.5 (TP-506). Inversion in a topological group
is a homeomorphism. -/
@[kb "morris2024" "Proposition A5.1.5, p. 515"]
theorem morris_A5_1_5_c {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ h : G ≃ₜ G, ∀ x, h x = x⁻¹ :=
  ⟨Homeomorph.inv G, fun _ => rfl⟩

/-- Morris, Topology Without Tears, Definition A5.1.7 (TP-508). A space is `T₁` when every point
is closed. -/
@[kb "morris2024" "Definition A5.1.7, p. 516"]
theorem morris_A5_1_7 (X : Type*) [TopologicalSpace X] :
    T1Space X ↔ ∀ x : X, IsClosed ({x} : Set X) :=
  ⟨fun _ _ => isClosed_singleton, fun h => ⟨h⟩⟩

/-- Morris, Topology Without Tears, Proposition A5.1.9 (TP-510). A `T₁` topological group is
Hausdorff, and a topological group is Hausdorff iff `{1}` is closed. -/
@[kb "morris2024" "Proposition A5.1.9, p. 517"]
theorem morris_A5_1_9 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (T1Space G → T2Space G) ∧ (T2Space G ↔ IsClosed ({1} : Set G)) :=
  ⟨fun _ => inferInstance, IsTopologicalGroup.t2Space_iff_one_closed⟩

/-- Morris, Topology Without Tears, Proposition A5.2.3 (TP-512). A subgroup of a topological group
is a topological group in the subspace topology. -/
@[kb "morris2024" "Proposition A5.2.3, p. 520"]
theorem morris_A5_2_3 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) : IsTopologicalGroup S :=
  inferInstance

/-- Morris, Topology Without Tears, Proposition A5.2.5 (TP-513). The closure of a subgroup is a
subgroup (with underlying set the closure), normality is preserved, and so is commutativity
in a Hausdorff group. -/
@[kb "morris2024" "Proposition A5.2.5, p. 520"]
theorem morris_A5_2_5 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (S : Subgroup G) :
    ((S.topologicalClosure : Set G) = closure (S : Set G)) ∧
      (S.Normal → S.topologicalClosure.Normal) ∧
      (T2Space G → IsMulCommutative S → IsMulCommutative S.topologicalClosure) := by
  refine ⟨Subgroup.topologicalClosure_coe, fun h => ?_, fun _ h => ?_⟩
  · exact Subgroup.is_normal_topologicalClosure S
  · exact Subgroup.isMulCommutative_topologicalClosure S

/-- Morris, Topology Without Tears, Proposition A5.2.7 (TP-515). Every open subgroup of a
topological group is closed. -/
@[kb "morris2024" "Proposition A5.2.7, p. 521"]
theorem morris_A5_2_7 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G) :=
  Subgroup.isClosed_of_isOpen U h

/-- Morris, Topology Without Tears, Proposition A5.2.16 (TP-520). The quotient of a topological
group by a normal subgroup is a topological group and the quotient map is open. -/
@[kb "morris2024" "Proposition A5.2.16, p. 524"]
theorem morris_A5_2_16 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] :
    IsTopologicalGroup (G ⧸ N) ∧ IsOpenMap ((↑) : G → G ⧸ N) :=
  ⟨inferInstance, QuotientGroup.isOpenMap_coe⟩

/-- Morris, Topology Without Tears, Proposition A5.2.18 (TP-521). If `N` is a compact normal
subgroup, the quotient map `G → G/N` is closed. -/
@[kb "morris2024" "Proposition A5.2.18, p. 525"]
theorem morris_A5_2_18 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (hN : IsCompact (N : Set G)) :
    IsClosedMap ((↑) : G → G ⧸ N) :=
  QuotientGroup.isClosedMap_coe hN

/-- Morris, Topology Without Tears, Proposition A5.2.21 (TP-522). A quotient of a locally compact
group by a normal subgroup is locally compact. -/
@[kb "morris2024" "Proposition A5.2.21, p. 526"]
theorem morris_A5_2_21 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (N : Subgroup G) [N.Normal] : LocallyCompactSpace (G ⧸ N) :=
  inferInstance

/-- Morris, Topology Without Tears, Definition A5.2.19 (TP-524). A space is totally disconnected
when every connected component is a single point. -/
@[kb "morris2024" "Definition A5.2.19, p. 525"]
theorem morris_A5_2_19 (X : Type*) [TopologicalSpace X] :
    TotallyDisconnectedSpace X ↔ ∀ x : X, connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton

/-- Morris, Topology Without Tears, Definition A5.3.4 (TP-527). A group is divisible when every
element has an `n`-th root for every `n ≥ 1`. -/
@[kb "morris2024" "Definition A5.3.4, p. 531"]
theorem morris_A5_3_4 (G : Type*) [Group G] :
    Nonempty (RootableBy G ℕ) ↔ ∀ (a : G) (n : ℕ), n ≠ 0 → ∃ b : G, b ^ n = a := by
  classical
  refine ⟨fun ⟨h⟩ a n hn => ⟨RootableBy.root a n, RootableBy.root_cancel a hn⟩, fun h => ?_⟩
  exact ⟨⟨fun a n => if hn : n = 0 then 1 else (h a n hn).choose, fun a => by simp,
    fun a hn => by simpa [hn] using (h a _ hn).choose_spec⟩⟩

/-- Morris, Topology Without Tears, Theorem A5.4.1 (TP-534). A locally compact regular space is a
Baire space. -/
@[kb "morris2024" "Theorem A5.4.1, p. 535"]
theorem morris_A5_4_1 (X : Type*) [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X] :
    BaireSpace X :=
  inferInstance

/-- Morris, Topology Without Tears, Theorem A5.4.4 (TP-536). Open mapping theorem: a continuous
surjective homomorphism from a sigma-compact group onto a locally compact Hausdorff group is
open. -/
@[kb "morris2024" "Theorem A5.4.4, p. 536"]
theorem morris_A5_4_4 {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] (f : G →* H) (hf : Function.Surjective f) (hc : Continuous f) :
    IsOpenMap f :=
  f.isOpenMap_of_sigmaCompact hf hc

/-- Morris, Topology Without Tears, Proposition A5.5.1 (TP-538). A non-discrete subgroup of `ℝ`
is dense. -/
@[kb "morris2024" "Proposition A5.5.1, p. 538"]
theorem morris_A5_5_1 (S : AddSubgroup ℝ) (hS : ¬ DiscreteTopology S) : Dense (S : Set ℝ) :=
  S.dense_or_isCyclic.resolve_right fun h => hS (AddSubgroup.isAddCyclic_iff_discreteTopology.1 h)

/-- Morris, Topology Without Tears, Definition A5.6.1 (TP-555). The entourages of a uniformity
contain the diagonal, are closed under inversion, and have square roots. -/
@[kb "morris2024" "Definition A5.6.1, p. 552"]
theorem morris_A5_6_1 {X : Type*} [UniformSpace X] :
    (∀ U ∈ 𝓤 X, ∀ x, (x, x) ∈ U) ∧ (∀ U ∈ 𝓤 X, Prod.swap ⁻¹' U ∈ 𝓤 X) ∧
      ∀ U ∈ 𝓤 X, ∃ V ∈ 𝓤 X, ∀ x y z, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ U :=
  ⟨fun _ hU x => refl_mem_uniformity hU, fun _ hU => tendsto_swap_uniformity hU,
    fun _ hU => by
      obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
      exact ⟨V, hV, fun x y z hxy hyz => hVU ⟨y, hxy, hyz⟩⟩⟩

/-- Morris, Topology Without Tears, Definition A5.6.5 (TP-558). For a locally compact `E`, the
compact-open topology on `C(E, F)` is jointly continuous: evaluation is continuous. -/
@[kb "morris2024" "Definition A5.6.5, p. 553"]
theorem morris_A5_6_5 {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [LocallyCompactPair E F] :
    Continuous (fun p : C(E, F) × E => p.1 p.2) :=
  continuous_eval

/-- Morris, Topology Without Tears, Definition A5.6.8 (TP-561). Equicontinuity at a point of a
family of maps into a uniform space. -/
@[kb "morris2024" "Definition A5.6.8, p. 555"]
theorem morris_A5_6_8 {ι X α : Type*} [TopologicalSpace X] [UniformSpace α] (F : ι → X → α)
    (x₀ : X) :
    EquicontinuousAt F x₀ ↔ ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition A5.7.1 (TP-564). A character of a topological group
is a continuous homomorphism to the circle group. -/
@[kb "morris2024" "Definition A5.7.1, p. 557"]
theorem morris_A5_7_1_a {G : Type*} [CommGroup G] [TopologicalSpace G]
    (χ : PontryaginDual G) :
    Continuous χ ∧ ∀ x y, χ (x * y) = χ x * χ y :=
  ⟨map_continuous χ, map_mul χ⟩

/-- Morris, Topology Without Tears, Definition A5.7.1 (TP-565). The dual group multiplies
characters pointwise. -/
@[kb "morris2024" "Definition A5.7.1, p. 557"]
theorem morris_A5_7_1_b {G : Type*} [CommGroup G] [TopologicalSpace G]
    (χ ψ : PontryaginDual G) (x : G) : (χ * ψ) x = χ x * ψ x :=
  rfl

/-- Morris, Topology Without Tears, Proposition A5.7.5 (TP-568). The dual group of an abelian
topological group is a Hausdorff abelian topological group. -/
@[kb "morris2024" "Proposition A5.7.5, p. 559"]
theorem morris_A5_7_5 (G : Type*) [CommGroup G] [TopologicalSpace G] :
    T2Space (PontryaginDual G) ∧ IsTopologicalGroup (PontryaginDual G) :=
  ⟨inferInstance, inferInstance⟩

/-- Morris, Topology Without Tears, Definition A5.13 (TP-614). A group is simple when it is
nontrivial and its only normal subgroups are the trivial one and itself. -/
@[kb "morris2024" "Definition A5.13, p. 601"]
theorem morris_A5_13 (G : Type*) [Group G] :
    IsSimpleGroup G ↔ Nontrivial G ∧ ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ := by
  rw [isSimpleGroup_iff]

end UndergradKB.Topology.Course
