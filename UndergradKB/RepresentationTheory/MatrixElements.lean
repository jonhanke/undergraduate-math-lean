import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import UndergradKB.RepresentationTheory.Characters

/-! # Orthogonality of matrix elements (Etingof et al., Proposition 3.14)

Let `G` be a finite group and `k` an algebraically closed field whose characteristic does not divide `|G|`.
For irreducible finite-dimensional representations `ρ`, `σ` with bases, the matrix elements are the entries
`toMatrix b b (ρ g) i j`, viewed as functions of `g`. We prove the orthogonality relations in the
characteristic-free bilinear form, with `g⁻¹` in place of complex conjugation:

* if `ρ` and `σ` are not isomorphic, `∑ g, ρ(g)ᵢⱼ σ(g⁻¹)ₗₘ = 0`;
* for a single irreducible `ρ`, `∑ g, ρ(g)ᵢⱼ ρ(g⁻¹)ₗₘ = δᵢₘ δⱼₗ |G| / dim ρ`.

The proof averages a rank-one operator `A` over the group, `T = ∑ g, ρ g ∘ A ∘ σ g⁻¹`, which intertwines
`σ` and `ρ`, and applies Schur's lemma.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module

section Averaging

variable {k G V W : Type*} [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] (ρ : Representation k G V) (σ : Representation k G W)

/-- The average `∑ g, ρ g ∘ A ∘ σ g⁻¹` of a linear map `A : W → V` over the group. -/
noncomputable def averageMap (A : W →ₗ[k] V) : W →ₗ[k] V := ∑ g : G, ρ g ∘ₗ A ∘ₗ σ g⁻¹

theorem averageMap_comp (A : W →ₗ[k] V) (h : G) :
    averageMap ρ σ A ∘ₗ σ h = ρ h ∘ₗ averageMap ρ σ A := by
  ext x
  simp only [averageMap, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g ↦ ?_)
  simp only [Equiv.coe_mulLeft, map_mul, mul_apply_eq_comp, mul_inv_rev, inv_inv,
    Representation.self_inv_apply]

theorem averageMap_entry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι k V) (c : Module.Basis κ k W) (j : κ) (l : ι) (i : ι) (m : κ) :
    b.repr (averageMap ρ σ ((c.coord j).smulRight (b l)) (c m)) i =
      ∑ g : G, LinearMap.toMatrix b b (ρ g) i l * LinearMap.toMatrix c c (σ g⁻¹) j m := by
  simp [averageMap, LinearMap.sum_apply, LinearMap.toMatrix_apply, mul_comm]

theorem trace_averageMap [FiniteDimensional k V] [Invertible (Nat.card G : k)] (A : V →ₗ[k] V) :
    LinearMap.trace k V (averageMap ρ ρ A) = (Nat.card G : k) * LinearMap.trace k V A := by
  simp only [averageMap, map_sum]
  have : ∀ g : G, LinearMap.trace k V (ρ g ∘ₗ A ∘ₗ ρ g⁻¹) = LinearMap.trace k V A := by
    intro g
    have hid : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by ext; simp
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hid, LinearMap.comp_id]
  simp [this, Nat.card_eq_fintype_card]

end Averaging

section Main

variable {k G V W ι κ : Type*} [Field k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [IsAlgClosed k] [Invertible (Nat.card G : k)]
  {ρ : Representation k G V} {σ : Representation k G W} [FiniteDimensional k V] [FiniteDimensional k W]

omit [IsAlgClosed k] [Invertible (Nat.card G : k)] [FiniteDimensional k V] [FiniteDimensional k W] in
/-- **Etingof et al., Proposition 3.14** (non-isomorphic case): matrix elements of two non-isomorphic
irreducible representations are orthogonal for the bilinear pairing `(f₁, f₂) ↦ ∑ g, f₁ g * f₂ g⁻¹`. -/
@[kb "etingof2011" "Proposition 3.14, p. 39"]
theorem sum_matrix_mul_matrix_inv_eq_zero [IsIrreducible ρ] [IsIrreducible σ]
    (hne : ¬ Nonempty (Representation.Equiv ρ σ))
    (b : Module.Basis ι k V) (c : Module.Basis κ k W) (i j : ι) (l m : κ) :
    ∑ g : G, LinearMap.toMatrix b b (ρ g) i j * LinearMap.toMatrix c c (σ g⁻¹) l m = 0 := by
  have hempty : IsEmpty (Representation.Equiv σ ρ) := ⟨fun e ↦ hne ⟨e.symm⟩⟩
  have hint : ∀ (g : G) (v : W), averageMap ρ σ ((c.coord l).smulRight (b j)) (σ g v) =
      ρ g (averageMap ρ σ ((c.coord l).smulRight (b j)) v) := fun g v ↦
    congrArg (fun φ : W →ₗ[k] V ↦ φ v) (averageMap_comp ρ σ ((c.coord l).smulRight (b j)) g)
  let f : IntertwiningMap σ ρ :=
    LinearMap.intertwiningMap_of_isIntertwiningMap (ρ := σ) (σ := ρ)
      (averageMap ρ σ ((c.coord l).smulRight (b j))) hint
  have h0 : f = 0 := Subsingleton.elim _ _
  have hz : averageMap ρ σ ((c.coord l).smulRight (b j)) (c m) = 0 :=
    congrArg (fun f : IntertwiningMap σ ρ ↦ f (c m)) h0
  have := averageMap_entry ρ σ b c l j i m
  rw [hz] at this
  simpa using this.symm

/-- **Etingof et al., Proposition 3.14** (single representation): for an irreducible representation `ρ` with
basis `b`, `∑ g, ρ(g)ᵢⱼ ρ(g⁻¹)ₗₘ` is `|G| / dim ρ` if `i = m` and `j = l`, and `0` otherwise. -/
@[kb "etingof2011" "Proposition 3.14, p. 39"]
theorem sum_matrix_mul_matrix_inv [IsIrreducible ρ] (b : Module.Basis ι k V) (i j l m : ι) :
    ∑ g : G, LinearMap.toMatrix b b (ρ g) i j * LinearMap.toMatrix b b (ρ g⁻¹) l m =
      if i = m ∧ j = l then (Nat.card G : k) / finrank k V else 0 := by
  set A : V →ₗ[k] V := (b.coord l).smulRight (b j) with hA
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_commute (ρ := ρ) (averageMap ρ ρ A)
    (fun g ↦ averageMap_comp ρ ρ A g)
  have hdim := finrank_ne_zero_of_isIrreducible (ρ := ρ) (k := k)
  have htr := trace_averageMap ρ A
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hA, LinearMap.trace_smulRight] at htr
  have hent := averageMap_entry ρ ρ b b l j i m
  rw [hc] at hent
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply] at hent
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at htr
  have hcv : c = if j = l then (Nat.card G : k) / finrank k V else 0 := by
    by_cases hjl : j = l
    · simp only [hjl, ↓reduceIte]
      rw [eq_div_iff hdim]
      simpa [hjl] using htr
    · simp only [hjl, ↓reduceIte]
      simp only [hjl, ↓reduceIte, mul_zero] at htr
      exact (mul_eq_zero.mp htr).resolve_right hdim
  rw [← hent, hcv]
  by_cases him : i = m
  · simp [him]
  · simp [him, Ne.symm him]
