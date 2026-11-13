import UndergradKB.Common.Attr
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RepresentationTheory.Maschke
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-! # Problem 4.15(a): a number field over which all complex representations are realized

For a finite group `G` there is a finite Galois extension `K ⊂ ℂ` of `ℚ` such that every finite-dimensional
complex representation of `G` has a basis in which all matrices `ρ(g)` have entries in `K`.

The proof: `Q̄[G]` (`Q̄` the algebraic numbers) is semisimple (Maschke), hence by Wedderburn-Artin over the
algebraically closed field `Q̄` isomorphic to a product of matrix algebras.  The images of the matrix units in
`End_ℂ V` have the relations of matrix units, which yields a basis of `V` in which every element of the
product of matrix algebras acts through its entries.  `K` is the splitting field of the minimal polynomials of
the finitely many entries of the images of the elements of `G`.
-/

universe u

namespace UndergradKB.RepresentationTheory

open Module

section Basis

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} [∀ i, NeZero (d i)]
  {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (E : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ V)

/-- A family of operators satisfying the relations of matrix units, summing to the identity, gives a basis of
`V` indexed by `(i, a, s)` on which `E i a c` acts by `(j, c', s) ↦ δ_{ij} δ_{c c'} (i, a, s)`. -/
theorem exists_basis_of_matrix_units
    (hmul : ∀ i (a b c e : Fin (d i)), E i a b * E i c e = if b = c then E i a e else 0)
    (hmul' : ∀ i j, i ≠ j → ∀ (a b : Fin (d i)) (c e : Fin (d j)), E i a b * E j c e = 0)
    (hone : ∑ i, ∑ a, E i a a = 1) :
    ∃ (k : ι → ℕ) (b : Basis (Σ i, Fin (d i) × Fin (k i)) ℂ V),
      (∀ i a c (s : Fin (k i)), E i a c (b ⟨i, c, s⟩) = b ⟨i, a, s⟩) ∧
      (∀ i a c c' (s : Fin (k i)), c ≠ c' → E i a c (b ⟨i, c', s⟩) = 0) ∧
      (∀ i j, i ≠ j → ∀ (a c : Fin (d i)) (c' : Fin (d j)) (s : Fin (k j)),
        E i a c (b ⟨j, c', s⟩) = 0) := by
  classical
  let W : ι → Submodule ℂ V := fun i ↦ LinearMap.range (E i 0 0)
  let k : ι → ℕ := fun i ↦ finrank ℂ (W i)
  let B : ∀ i, Basis (Fin (k i)) ℂ (W i) := fun i ↦ Module.finBasis ℂ (W i)
  let w : ∀ i, Fin (k i) → V := fun i s ↦ (B i s : V)
  have hEE : ∀ i a b c, E i a b * E i b c = E i a c := by
    intro i a b c; rw [hmul]; simp
  have hww : ∀ i s, E i 0 0 (w i s) = w i s := by
    intro i s
    obtain ⟨u, hu⟩ := (B i s).2
    show E i 0 0 ((B i s : W i) : V) = ((B i s : W i) : V)
    rw [← hu, ← Module.End.mul_apply, hEE]
  let v : (Σ i, Fin (d i) × Fin (k i)) → V := fun t ↦ E t.1 t.2.1 0 (w t.1 t.2.2)
  have hv : ∀ i a s, v ⟨i, a, s⟩ = E i a 0 (w i s) := fun _ _ _ ↦ rfl
  have hact : ∀ i (a c c' : Fin (d i)) (s : Fin (k i)),
      E i a c (v ⟨i, c', s⟩) = if c = c' then v ⟨i, a, s⟩ else 0 := by
    intro i a c c' s
    rw [hv, ← Module.End.mul_apply, hmul]
    by_cases h : c = c'
    · simp [h, hv]
    · simp [h]
  have hact' : ∀ i j, i ≠ j → ∀ (a c : Fin (d i)) (c' : Fin (d j)) (s : Fin (k j)),
      E i a c (v ⟨j, c', s⟩) = 0 := by
    intro i j hij a c c' s
    rw [hv, ← Module.End.mul_apply, hmul' i j hij]
    rfl
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg t
    obtain ⟨j, c, s0⟩ := t
    have h1 := congrArg (E j 0 c) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul] at h1
    rw [Fintype.sum_sigma] at h1
    simp_rw [Fintype.sum_prod_type] at h1
    rw [Finset.sum_eq_single j] at h1
    · rw [Finset.sum_eq_single c] at h1
      · have h2 : ∑ s, g ⟨j, c, s⟩ • B j s = 0 := by
          apply Subtype.ext
          rw [Submodule.coe_sum, Submodule.coe_zero]
          refine Eq.trans (Finset.sum_congr rfl fun s _ ↦ ?_) h1
          rw [hact, if_pos rfl, Submodule.coe_smul, hv, hww]
        exact Fintype.linearIndependent_iff.mp (B j).linearIndependent (fun s ↦ g ⟨j, c, s⟩) h2 s0
      · intro c' _ hc'
        refine Finset.sum_eq_zero fun s _ ↦ ?_
        rw [hact, if_neg (Ne.symm hc'), smul_zero]
      · simp
    · intro j' _ hj'
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun s _ ↦ ?_
      rw [hact' j j' (Ne.symm hj'), smul_zero]
    · simp
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro x _
    have hx : x = ∑ i, ∑ a, E i a a x := by
      conv_lhs => rw [← Module.End.one_apply (R := ℂ) x, ← hone]
      simp [LinearMap.sum_apply]
    rw [hx]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun a _ ↦ ?_
    have hy : E i 0 a x ∈ W i := ⟨E i 0 a x, by rw [← Module.End.mul_apply, hEE]⟩
    have hrepr := (B i).sum_repr ⟨E i 0 a x, hy⟩
    have : E i a a x = ∑ s, (B i).repr ⟨E i 0 a x, hy⟩ s • v ⟨i, a, s⟩ := by
      have h3 : E i a a x = E i a 0 (E i 0 a x) := by
        rw [← Module.End.mul_apply, hEE]
      rw [h3]
      have h4 : E i 0 a x = ∑ s, (B i).repr ⟨E i 0 a x, hy⟩ s • w i s := by
        have := congrArg (fun z : W i ↦ (z : V)) hrepr
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      conv_lhs => rw [h4]
      rw [map_sum]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul]
    rw [this]
    exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine ⟨k, Basis.mk hli hsp, ?_, ?_, ?_⟩
  · intro i a c s
    rw [Basis.mk_apply, Basis.mk_apply, hact, if_pos rfl]
  · intro i a c c' s h
    rw [Basis.mk_apply, hact, if_neg h]
  · intro i j hij a c c' s
    rw [Basis.mk_apply, hact' i j hij]

end Basis

section Algebra

variable {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)] {F : Type} [Field F] [Algebra F ℂ]
  {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The matrix unit `e_{ac}` in the `i`-th factor of `∏ M_{d i}(F)`. -/
def mu (d : Fin n → ℕ) (F : Type) [Field F] (i : Fin n) (a c : Fin (d i)) :
    Π j, Matrix (Fin (d j)) (Fin (d j)) F :=
  Pi.single i (Matrix.single a c (1 : F))

theorem mu_mul_same (i : Fin n) (a b c e : Fin (d i)) :
    mu d F i a b * mu d F i c e = if b = c then mu d F i a e else 0 := by
  by_cases h : b = c
  · subst h
    ext j p q
    simp only [mu, Pi.mul_apply, if_true]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  · rw [if_neg h]
    ext j p q
    simp only [mu, Pi.mul_apply, Pi.zero_apply]
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [Pi.single_apply, hj]

theorem mu_mul_ne (i j : Fin n) (hij : i ≠ j) (a b : Fin (d i)) (c e : Fin (d j)) :
    mu d F i a b * mu d F j c e = 0 := by
  ext k p q
  simp only [mu, Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, hij]
  · simp [Pi.single_apply, hk]

theorem sum_mu_diag : ∑ i, ∑ a, mu d F i a a = 1 := by
  ext j p q
  simp only [mu, Finset.sum_apply, Pi.one_apply]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h; simp
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact h (h1.symm.trans h2)
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem eq_sum_mu (x : Π j, Matrix (Fin (d j)) (Fin (d j)) F) :
    x = ∑ i, ∑ a, ∑ c, x i a c • mu d F i a c := by
  funext j
  have : (∑ i, ∑ a, ∑ c, x i a c • mu d F i a c) j = ∑ a, ∑ c, x j a c • Matrix.single a c (1 : F) := by
    simp only [Finset.sum_apply, Pi.smul_apply, mu]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun c _ ↦ ?_
      rw [Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
    · simp
  rw [this]
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  · intro a _ ha
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    simp [ha]
  · simp

/-- If `ψ` is a ring homomorphism from `∏ M_{d i}(F)` to `End_ℂ V` compatible with scalars, there is a
`ℂ`-basis of `V` in which `ψ x` has all matrix entries in any subfield containing the entries of `x`. -/
theorem exists_basis_entries (ψ : (Π j, Matrix (Fin (d j)) (Fin (d j)) F) →+* Module.End ℂ V)
    (hscal : ∀ (r : F) (x : Π j, Matrix (Fin (d j)) (Fin (d j)) F),
      ψ (r • x) = (algebraMap F ℂ r) • ψ x) :
    ∃ (T : Type) (_ : Fintype T) (b : Basis T ℂ V), ∀ (K : Subfield ℂ)
      (x : Π j, Matrix (Fin (d j)) (Fin (d j)) F), (∀ i a c, algebraMap F ℂ (x i a c) ∈ K) →
        ∀ t t', b.repr (ψ x (b t)) t' ∈ K := by
  classical
  obtain ⟨k, b, h1, h2, h3⟩ := exists_basis_of_matrix_units (fun i a c ↦ ψ (mu d F i a c))
    (fun i a b c e ↦ by rw [← map_mul, mu_mul_same]; split_ifs <;> simp)
    (fun i j hij a b c e ↦ by rw [← map_mul, mu_mul_ne i j hij, map_zero])
    (by simp only [← map_sum]; rw [sum_mu_diag, map_one])
  refine ⟨_, inferInstance, b, fun K x hx ↦ ?_⟩
  intro t t'
  obtain ⟨j, c', s⟩ := t
  have hψ : ψ x = ∑ i, ∑ a, ∑ c, algebraMap F ℂ (x i a c) • ψ (mu d F i a c) := by
    conv_lhs => rw [eq_sum_mu x]
    simp only [map_sum, hscal]
  have key : ψ x (b ⟨j, c', s⟩) = ∑ a, algebraMap F ℂ (x j a c') • b ⟨j, a, s⟩ := by
    rw [hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_eq_single c']
      · rw [h1]
      · intro c _ hc
        rw [h2 j a c c' s hc, smul_zero]
      · simp
    · intro i _ hij
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun c _ ↦ ?_
      rw [h3 i j hij a c c' s, smul_zero]
    · simp
  rw [key, map_sum, Finsupp.finsetSum_apply]
  refine Subfield.sum_mem _ fun a _ ↦ ?_
  rw [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs
  · simpa using hx j a c'
  · simp

end Algebra

section Main

open Polynomial

/-- The field `K`: the splitting field in `ℂ` of the product of the minimal polynomials of a finite set `S`
of algebraic numbers.  It is a finite Galois extension of `ℚ` containing `S`. -/
theorem exists_galois_containing (S : Finset ℂ) (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧ ∀ s ∈ S, s ∈ K := by
  classical
  let p : ℚ[X] := ∏ s ∈ S, minpoly ℚ s
  have hmon : p.Monic := Polynomial.monic_prod_of_monic _ _ fun s hs ↦ minpoly.monic (hS s hs).isIntegral
  have hp0 : p ≠ 0 := hmon.ne_zero
  have hsplit : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  have hK : IsSplittingField ℚ K p := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K p
  have hnormal : Normal ℚ K := Normal.of_isSplittingField p
  refine ⟨K, hfin, ?_, fun s hs ↦ ?_⟩
  · exact IsGalois.mk
  · apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp0, ?_⟩
    show aeval s (∏ s ∈ S, minpoly ℚ s) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero hs (minpoly.aeval ℚ s)

/-- The main construction, for any algebraically closed subfield-like field `F` of algebraic numbers. -/
theorem exists_galois_realization_aux (F : Type) [Field F] [Algebra F ℂ] [IsAlgClosed F]
    (hF : ∀ x : F, IsAlgebraic ℚ (algebraMap F ℂ x)) (G : Type*) [Group G] [Finite G] :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ G V),
        ∃ b : Basis (Fin (finrank ℂ V)) ℂ V, ∀ g i j, LinearMap.toMatrix b b (ρ g) i j ∈ K := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : CharZero F := (RingHom.charZero_iff (algebraMap F ℂ).injective).mpr inferInstance
  haveI : NeZero (Nat.card G : F) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  obtain ⟨m, d, hd, ⟨Φ⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed F (MonoidAlgebra F G)
  let S : Finset ℂ := (Finset.univ : Finset (G × Σ i, Fin (d i) × Fin (d i))).image
    fun q ↦ algebraMap F ℂ (Φ (MonoidAlgebra.single q.1 1) q.2.1 q.2.2.1 q.2.2.2)
  obtain ⟨K, hfin, hgal, hSK⟩ := exists_galois_containing S (by
    intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hs
    exact hF _)
  refine ⟨K, hfin, hgal, ?_⟩
  intro V _ _ _ ρ
  letI : Module F V := Module.compHom V (algebraMap F ℂ)
  haveI : IsScalarTower F ℂ V := IsScalarTower.of_algebraMap_smul fun r x ↦ rfl
  let ψ' : MonoidAlgebra F G →ₐ[F] Module.End ℂ V := MonoidAlgebra.lift F (Module.End ℂ V) G ρ
  let ψ'' : (Π j, Matrix (Fin (d j)) (Fin (d j)) F) →ₐ[F] Module.End ℂ V :=
    ψ'.comp Φ.symm.toAlgHom
  obtain ⟨T, hT, b, hb⟩ := exists_basis_entries (V := V) (ψ''.toRingHom) (by
    intro r x
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul]
    exact LinearMap.ext fun v ↦ rfl)
  have hcard : Fintype.card T = finrank ℂ V := (Module.finrank_eq_card_basis b).symm
  let e : T ≃ Fin (finrank ℂ V) := Fintype.equivFinOfCardEq hcard
  refine ⟨b.reindex e, fun g i j ↦ ?_⟩
  have hρ : ρ g = ψ''.toRingHom (Φ (MonoidAlgebra.single g 1)) := by
    simp [ψ'', ψ']
  rw [LinearMap.toMatrix_apply, Basis.repr_reindex_apply, hρ]
  simp only [Basis.reindex_apply]
  exact hb K.toSubfield _ (fun i a c ↦ hSK _ (Finset.mem_image.mpr ⟨(g, ⟨i, a, c⟩), Finset.mem_univ _, rfl⟩))
    _ _

/-- **Etingof et al., Problem 4.15(a)**: for a finite group `G` there is a finite Galois extension `K ⊂ ℂ` of
`ℚ` such that every finite-dimensional complex representation of `G` has a basis in which all the matrices
`ρ(g)` have entries in `K`. -/
@[kb "etingof2011" "Problem 4.15, p. 51"]
theorem exists_galois_realization_field (G : Type*) [Group G] [Finite G] :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ IsGalois ℚ K ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ G V),
        ∃ b : Basis (Fin (finrank ℂ V)) ℂ V, ∀ g i j, LinearMap.toMatrix b b (ρ g) i j ∈ K := by
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := IsAlgClosure.isAlgClosed ℚ
  exact exists_galois_realization_aux (algebraicClosure ℚ ℂ)
    (fun x ↦ (mem_algebraicClosure_iff).mp x.2) G

end Main

end UndergradKB.RepresentationTheory
