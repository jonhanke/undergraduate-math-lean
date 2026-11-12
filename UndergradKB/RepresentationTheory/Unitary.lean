import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import UndergradKB.Common.Attr

/-! # Unitary representations (Etingof et al., Section 3.6)

* Definition 3.10: a unitary representation on a complex inner product space.
* Theorem 3.11: for a finite group the averaged inner product `∑_g ⟪ρ g v, ρ g w⟫` is an invariant
  positive definite Hermitian form.
* Theorem 3.12: a finite-dimensional unitary representation is completely reducible: the orthogonal
  complement of a subrepresentation is a complementary subrepresentation.
-/

namespace UndergradKB.RepresentationTheory

open scoped ComplexConjugate InnerProductSpace

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Etingof et al., Definition 3.10**: a complex representation on an inner product space is
unitary if every `ρ g` preserves the inner product. (Finite-dimensionality, part of the book's
setting, is assumed separately in the theorems below.) -/
@[kb "etingof2011" "Definition 3.10, p. 38"]
def IsUnitaryRepresentation (ρ : Representation ℂ G V) : Prop :=
  ∀ (g : G) (v w : V), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ

section Averaging

variable [Fintype G] (ρ : Representation ℂ G V)

/-- The `G`-average of the inner product: `B(v, w) = ∑_g ⟪ρ g v, ρ g w⟫`, conjugate-linear in the first
and linear in the second argument. -/
noncomputable def averagedForm : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v w => ∑ g : G, ⟪ρ g v, ρ g w⟫_ℂ)
    (fun x y z => by simp [inner_add_left, Finset.sum_add_distrib])
    (fun c x y => by simp [inner_smul_left, Finset.mul_sum])
    (fun x y z => by simp [inner_add_right, Finset.sum_add_distrib])
    (fun c x y => by simp [inner_smul_right, Finset.mul_sum])

theorem averagedForm_apply (v w : V) : averagedForm ρ v w = ∑ g : G, ⟪ρ g v, ρ g w⟫_ℂ := rfl

/-- The averaged form is invariant under `G`. -/
theorem averagedForm_invariant (h : G) (v w : V) :
    averagedForm ρ (ρ h v) (ρ h w) = averagedForm ρ v w := by
  have key : ∀ (g : G) (x : V), ρ g (ρ h x) = ρ (g * h) x := fun g x => by rw [map_mul]; rfl
  simp only [averagedForm_apply, key]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => rfl)

/-- The averaged form is conjugate-symmetric (Hermitian). -/
theorem averagedForm_conj_symm (v w : V) :
    conj (averagedForm ρ v w) = averagedForm ρ w v := by
  simp only [averagedForm_apply, map_sum, inner_conj_symm]

/-- The averaged form is positive definite: `B(v, v)` is a positive real number for `v ≠ 0`. -/
theorem averagedForm_self_pos {v : V} (hv : v ≠ 0) :
    (averagedForm ρ v v).im = 0 ∧ 0 < (averagedForm ρ v v).re := by
  have h : averagedForm ρ v v = ((∑ g : G, ‖ρ g v‖ ^ 2 : ℝ) : ℂ) := by
    simp only [averagedForm_apply, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  apply Finset.sum_pos'
  · intro g _; positivity
  · refine ⟨1, Finset.mem_univ _, ?_⟩
    simp [hv]

/-- **Etingof et al., Theorem 3.11**: a finite-dimensional complex representation of a finite group
carries an invariant positive definite Hermitian form, namely the average of the inner product.
This gives a sesquilinear form `B` (`averagedForm`) with all three properties. -/
@[kb "etingof2011" "Theorem 3.11, p. 39"]
theorem exists_invariant_posDef_form [FiniteDimensional ℂ V] :
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ,
      (∀ (h : G) (v w : V), B (ρ h v) (ρ h w) = B v w) ∧
      (∀ v w : V, conj (B v w) = B w v) ∧
      (∀ v : V, v ≠ 0 → (B v v).im = 0 ∧ 0 < (B v v).re) :=
  ⟨averagedForm ρ, averagedForm_invariant ρ, averagedForm_conj_symm ρ,
    fun _ hv => averagedForm_self_pos ρ hv⟩

end Averaging

section Complement

/-- In a unitary representation the orthogonal complement of a subrepresentation is again a
subrepresentation. -/
noncomputable def orthogonalSubrepresentation {ρ : Representation ℂ G V} (hρ : IsUnitaryRepresentation ρ)
    (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule := W.toSubmodule.orthogonal
  apply_mem_toSubmodule g u hu := by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    have h1 : ρ g⁻¹ w ∈ W.toSubmodule := W.apply_mem_toSubmodule g⁻¹ hw
    have h2 : ρ g (ρ g⁻¹ w) = w := by
      calc ρ g (ρ g⁻¹ w) = ρ (g * g⁻¹) w := by rw [map_mul]; rfl
        _ = w := by simp
    rw [← h2, hρ g]
    exact hu _ h1

/-- **Etingof et al., Theorem 3.12**: a finite-dimensional unitary representation is completely
reducible: every subrepresentation has a complementary subrepresentation (its orthogonal complement). -/
@[kb "etingof2011" "Theorem 3.12, p. 39"]
theorem IsUnitaryRepresentation.exists_isCompl [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsUnitaryRepresentation ρ) (W : Subrepresentation ρ) :
    ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  refine ⟨orthogonalSubrepresentation hρ W, ?_⟩
  have h := Submodule.isCompl_orthogonal (K := W.toSubmodule)
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h ⊢
  constructor
  · apply Subrepresentation.toSubmodule_injective
    exact h.1
  · apply Subrepresentation.toSubmodule_injective
    exact h.2

end Complement

end UndergradKB.RepresentationTheory
