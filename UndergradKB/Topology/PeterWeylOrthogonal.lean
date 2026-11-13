import UndergradKB.Topology.PeterWeylGeneral2
import UndergradKB.Topology.NSSGroups
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import UndergradKB.Common.Attr

/-!
# Compact groups are closed subgroups of products of orthogonal groups (Theorem A5.0.12; TP-486)

Morris, *Topology Without Tears*, Theorem A5.0.12 (Peter-Weyl): every compact (Hausdorff) group is
topologically isomorphic to a closed subgroup of a product of orthogonal groups.

From Theorem A5.10.1 (`exists_unitaryMatrixRep_ne_one`) each `g ≠ e` is moved by a continuous
homomorphism into some `U(n)`; the realification `X + iY ↦ [[X, -Y], [Y, X]]` is a continuous
injective homomorphism `U(n) → O(2n)`; the product over all `g ≠ e` of these homomorphisms is a
continuous injective homomorphism of the compact group into a Hausdorff group, hence a closed
embedding. (The abelian case with `SO(2)` factors is `exists_isClosedEmbedding_specialOrthogonal_pow`.)
-/

open Topology Matrix

set_option linter.unusedSectionVars false

namespace UndergradKB.Topology

universe u

section Realify

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real form `[[X, -Y], [Y, X]]` of a complex matrix `X + iY`. -/
noncomputable def realifyMat (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (A.map Complex.re) (-(A.map Complex.im)) (A.map Complex.im) (A.map Complex.re)

theorem map_re_mul (A B : Matrix n n ℂ) :
    (A * B).map Complex.re = A.map Complex.re * B.map Complex.re - A.map Complex.im * B.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

theorem map_im_mul (A B : Matrix n n ℂ) :
    (A * B).map Complex.im = A.map Complex.re * B.map Complex.im + A.map Complex.im * B.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

theorem realifyMat_mul (A B : Matrix n n ℂ) : realifyMat (A * B) = realifyMat A * realifyMat B := by
  rw [realifyMat, realifyMat, realifyMat, fromBlocks_multiply, map_re_mul, map_im_mul]
  congr 1 <;> first | noncomm_ring | abel

theorem realifyMat_one : realifyMat (1 : Matrix n n ℂ) = 1 := by
  rw [realifyMat, ← fromBlocks_one]
  congr 1 <;> ext i j <;> rcases eq_or_ne i j with rfl | h <;> simp [Matrix.one_apply_ne, *]

theorem realifyMat_star (A : Matrix n n ℂ) : realifyMat (star A) = star (realifyMat A) := by
  rw [star_eq_conjTranspose, star_eq_conjTranspose, realifyMat, realifyMat, fromBlocks_conjTranspose]
  congr 1
  ext i j
  simp [conjTranspose_apply]

theorem realifyMat_injective : Function.Injective (realifyMat : Matrix n n ℂ → _) := by
  intro A B h
  rw [realifyMat, realifyMat, fromBlocks_inj] at h
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun h.1 i) j
  · exact congrFun (congrFun h.2.2.1 i) j

theorem continuous_realifyMat : Continuous (realifyMat : Matrix n n ℂ → _) := by
  unfold realifyMat
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.map_apply, Matrix.neg_apply] <;> fun_prop

/-- The realification `U(n) → O(2n)` (orthogonal matrices indexed by `n ⊕ n`). -/
noncomputable def realifyUnitary : unitaryGroup n ℂ →* orthogonalGroup (n ⊕ n) ℝ where
  toFun A := ⟨realifyMat (A : Matrix n n ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, ← realifyMat_star, ← realifyMat_mul,
      Matrix.mem_unitaryGroup_iff.1 A.2, realifyMat_one]⟩
  map_one' := Subtype.ext realifyMat_one
  map_mul' _ _ := Subtype.ext (realifyMat_mul _ _)

theorem continuous_realifyUnitary : Continuous (realifyUnitary (n := n)) :=
  continuous_induced_rng.2 (continuous_realifyMat.comp continuous_subtype_val)

theorem realifyUnitary_injective : Function.Injective (realifyUnitary (n := n)) :=
  fun _ _ h => Subtype.ext (realifyMat_injective (congrArg Subtype.val h))

end Realify

/-- Morris, Topology Without Tears, Theorem A5.0.12 (TP-486), Peter-Weyl theorem. Every compact
Hausdorff group `K` is topologically isomorphic to a closed subgroup of a product of orthogonal
groups: there is a family of orthogonal groups `O(2 nᵢ)` (orthogonal real matrices indexed by
`Fin nᵢ ⊕ Fin nᵢ`) and a homomorphism of `K` into their product that is a closed embedding. -/
@[kb "morris2024" "Theorem A5.0.12, p. 502"]
theorem exists_isClosedEmbedding_orthogonal_pi (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] :
    ∃ (ι : Type u) (d : ι → ℕ)
      (f : K →* ((i : ι) → orthogonalGroup (Fin (d i) ⊕ Fin (d i)) ℝ)), IsClosedEmbedding f := by
  classical
  have h : ∀ g : {g : K // g ≠ 1}, ∃ (n : ℕ) (π : K →* unitaryGroup (Fin n) ℂ),
      Continuous π ∧ π g ≠ 1 := fun g => exists_unitaryMatrixRep_ne_one g.2
  choose d π hπc hπg using h
  let f : K →* ((i : {g : K // g ≠ 1}) → orthogonalGroup (Fin (d i) ⊕ Fin (d i)) ℝ) :=
    MonoidHom.pi fun i => realifyUnitary.comp (π i)
  refine ⟨{g : K // g ≠ 1}, d, f, ?_⟩
  have hc : Continuous f :=
    continuous_pi fun i => continuous_realifyUnitary.comp (hπc i)
  refine hc.isClosedEmbedding ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hne
  apply hπg ⟨x, hne⟩
  apply realifyUnitary_injective
  rw [map_one]
  exact congrFun hx ⟨x, hne⟩

/-- Morris, Topology Without Tears, Theorem A5.0.28 (TP-500), the step from "no small subgroups"
towards "Lie group": a compact Hausdorff group with no small subgroups is topologically isomorphic
to a closed subgroup of a finite product of unitary groups `U(nᵢ)`. (Finitely many of the
Peter-Weyl representations already have kernels meeting only inside the NSS neighbourhood, by
compactness of its complement; their common kernel is a subgroup inside that neighbourhood, hence
trivial.) -/
@[kb "morris2024" "Theorem A5.0.28, p. 510"]
theorem exists_isClosedEmbedding_unitary_of_isNSS (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (hK : IsNSS K) :
    ∃ (ι : Type u) (_ : Fintype ι) (d : ι → ℕ)
      (f : K →* ((i : ι) → unitaryGroup (Fin (d i)) ℂ)), IsClosedEmbedding f := by
  classical
  obtain ⟨O, hOo, hO1, hO⟩ := hK
  have h : ∀ g : {g : K // g ≠ 1}, ∃ (n : ℕ) (π : K →* unitaryGroup (Fin n) ℂ),
      Continuous π ∧ π g ≠ 1 := fun g => exists_unitaryMatrixRep_ne_one g.2
  choose d π hπc hπg using h
  -- finitely many representations move every point outside `O`
  have hC : IsCompact (Oᶜ) := hOo.isClosed_compl.isCompact
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : {g : K // g ≠ 1} => (π g) ⁻¹' {1}ᶜ)
    (fun g => isOpen_compl_singleton.preimage (hπc g)) (by
      intro x hx
      have hx1 : x ≠ 1 := fun h1 => hx (h1 ▸ hO1)
      exact Set.mem_iUnion.2 ⟨⟨x, hx1⟩, hπg ⟨x, hx1⟩⟩)
  let f : K →* ((i : t) → unitaryGroup (Fin (d i)) ℂ) := MonoidHom.pi fun i => π i
  refine ⟨t, inferInstance, fun i => d i, f, ?_⟩
  have hc : Continuous f := continuous_pi fun i => hπc i
  refine hc.isClosedEmbedding ?_
  rw [injective_iff_map_eq_one]
  have hker : (f.ker : Set K) ⊆ O := by
    intro x hx
    by_contra hxO
    obtain ⟨i, hit, hix⟩ := Set.mem_iUnion₂.1 (ht hxO)
    exact hix (congrFun (MonoidHom.mem_ker.1 hx) ⟨i, hit⟩)
  have hbot := hO f.ker hker
  intro x hx
  have : x ∈ f.ker := hx
  rw [hbot] at this
  exact this

end UndergradKB.Topology
