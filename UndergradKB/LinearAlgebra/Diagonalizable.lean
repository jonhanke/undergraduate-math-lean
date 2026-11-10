import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Algebra.DirectSum.Module
import UndergradKB.Common.Attr

/-! # Diagonalizable operators (Axler 5.50 - 5.65, Exercises 5D)

Mathlib has no predicate "diagonalizable"; `IsDiagonalizable` below is Axler's definition 5.50
(a diagonal matrix in some basis).  The main result is the equivalence 5.55 with eigenbases and
the eigenspace decomposition, and the minimal polynomial criterion 5.62.
-/

open Module Polynomial

namespace UndergradKB.LinearAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Axler Definition 5.50** (also Hefferon Definition Five.II.2.1, operator version): an operator
is diagonalizable if its matrix with respect to some basis is diagonal. -/
@[kb "axler2024" "5.50, p. 181"]
def IsDiagonalizable (T : Module.End K V) : Prop :=
  ∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.toMatrix b b T).IsDiag

/-- The matrix of `T` in the basis `b` is diagonal iff every basis vector is an eigenvector. -/
theorem isDiag_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (T : Module.End K V) :
    (LinearMap.toMatrix b b T).IsDiag ↔ ∀ j, ∃ μ : K, T (b j) = μ • b j := by
  constructor
  · intro h j
    refine ⟨LinearMap.toMatrix b b T j j, ?_⟩
    conv_lhs => rw [← b.sum_repr (T (b j))]
    rw [Finset.sum_eq_single j]
    · simp [LinearMap.toMatrix_apply]
    · intro i _ hij
      rw [← LinearMap.toMatrix_apply, h hij, zero_smul]
    · simp
  · intro h i j hij
    obtain ⟨μ, hμ⟩ := h j
    rw [LinearMap.toMatrix_apply, hμ, map_smul]
    simp [Basis.repr_self, Finsupp.single_apply, hij.symm]

/-- If `q = ∏_{a ∈ s} (X - a)` kills `T` (distinct roots `s`), the eigenspaces of `T` span `V`
(Lagrange interpolation). -/
theorem iSup_eigenspace_eq_top_of_aeval_prod_eq_zero (T : Module.End K V) (s : Finset K)
    (h : aeval T (∏ a ∈ s, (X - C a)) = 0) : ⨆ μ, T.eigenspace μ = ⊤ := by
  classical
  rw [eq_top_iff]
  intro v _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have h1 := congrArg (fun f => f v) h
    simp at h1
    rw [h1]
    exact Submodule.zero_mem _
  · have hsum : ∑ j ∈ s, Lagrange.basis s id j = 1 :=
      Lagrange.sum_basis Function.injective_id.injOn hs
    have hv : v = ∑ j ∈ s, aeval T (Lagrange.basis s id j) v := by
      have := congrArg (fun p => aeval T p v) hsum
      simpa [map_sum, LinearMap.sum_apply] using this.symm
    rw [hv]
    refine Submodule.sum_mem _ fun j hj => Submodule.mem_iSup_of_mem j ?_
    rw [Module.End.mem_eigenspace_iff]
    have hdvd : (∏ a ∈ s, (X - C a)) ∣ (X - C j) * Lagrange.basis s id j := by
      have hb : Lagrange.basis s id j = ∏ i ∈ s.erase j, (C ((j - i)⁻¹) * (X - C i)) := rfl
      refine ⟨∏ i ∈ s.erase j, C ((j - i)⁻¹), ?_⟩
      rw [hb, Finset.prod_mul_distrib, ← Finset.mul_prod_erase s (fun a => X - C a) hj]
      ring
    obtain ⟨r, hr⟩ := hdvd
    have h0 : aeval T ((X - C j) * Lagrange.basis s id j) = 0 := by
      rw [hr, map_mul, h, zero_mul]
    have h1 := congrArg (fun f => f v) h0
    simp only [map_mul, map_sub, aeval_X, aeval_C, mul_apply_eq_comp, LinearMap.sub_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1

/-- The supremum over eigenvalues (a subtype) equals the supremum over all scalars, since the
eigenspaces of non-eigenvalues are trivial. -/
theorem iSup_eigenvalues_eq (T : Module.End K V) :
    ⨆ μ : T.Eigenvalues, T.eigenspace (μ : K) = ⨆ μ : K, T.eigenspace μ := by
  apply le_antisymm
  · exact iSup_le fun μ => le_iSup (fun μ : K => T.eigenspace μ) μ
  · refine iSup_le fun μ => ?_
    by_cases h : T.HasEigenvalue μ
    · exact le_iSup (fun μ : T.Eigenvalues => T.eigenspace (μ : K)) ⟨μ, h⟩
    · rw [Module.End.hasEigenvalue_iff, not_not] at h
      rw [h]
      exact bot_le

/-- Dimension of the supremum of an independent finite family of subspaces is the sum of the
dimensions. -/
theorem finrank_iSup_eq_sum {ι : Type*} [Fintype ι] (t : ι → Submodule K V)
    (ht : iSupIndep t) :
    finrank K (⨆ i, t i : Submodule K V) = ∑ i, finrank K (t i) := by
  classical
  have key : ∀ s : Finset ι,
      finrank K (⨆ i ∈ s, t i : Submodule K V) = ∑ i ∈ s, finrank K (t i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih]
      have hd : Disjoint (t a) (⨆ i ∈ s, t i) := by
        have := ht.disjoint_biSup (x := a) (y := (s : Set ι)) (by simpa using ha)
        simpa using this
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq (t a) (⨆ i ∈ s, t i)
      rw [disjoint_iff.mp hd, finrank_bot] at h2
      rw [Finset.iSup_insert]
      omega
  have e : (⨆ i ∈ (Finset.univ : Finset ι), t i : Submodule K V) = ⨆ i, t i :=
    le_antisymm (iSup₂_le fun i _ => le_iSup t i)
      (iSup_le fun i => le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset ι)) => t i) i
        (Finset.mem_univ i))
  rw [← e, key Finset.univ]

/-- **Axler 5.54**: eigenspaces for distinct eigenvalues form a direct sum (independent family),
and the sum of their dimensions is at most `dim V`. -/
@[kb "axler2024" "5.54, p. 182"]
theorem axler_5_54 (T : Module.End K V) :
    iSupIndep (fun μ : T.Eigenvalues => T.eigenspace (μ : K)) ∧
      ∑ μ : T.Eigenvalues, finrank K (T.eigenspace (μ : K)) ≤ finrank K V := by
  have hind : iSupIndep (fun μ : T.Eigenvalues => T.eigenspace (μ : K)) :=
    T.eigenspaces_iSupIndep.comp Subtype.val_injective
  refine ⟨hind, ?_⟩
  rw [← finrank_iSup_eq_sum _ hind]
  exact Submodule.finrank_le _

theorem finrank_eq_sum_iff_iSup_eq_top (T : Module.End K V) :
    finrank K V = ∑ μ : T.Eigenvalues, finrank K (T.eigenspace (μ : K)) ↔
      ⨆ μ : K, T.eigenspace μ = ⊤ := by
  have hind := (axler_5_54 T).1
  rw [← iSup_eigenvalues_eq, ← finrank_iSup_eq_sum _ hind]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq h.symm
  · intro h
    rw [h]
    simp

open scoped Classical in
theorem finrank_eq_sum_of_isInternal (T : Module.End K V)
    (h : DirectSum.IsInternal (fun μ : T.Eigenvalues => T.eigenspace (μ : K))) :
    finrank K V = ∑ μ : T.Eigenvalues, finrank K (T.eigenspace (μ : K)) := by
  have e := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun μ : T.Eigenvalues => T.eigenspace (μ : K))) h
  rw [← e.finrank_eq, Module.finrank_directSum]

open scoped Classical in
/-- **Axler 5.55**: for an operator `T` the following are equivalent: `T` is diagonalizable;
`V` has a basis of eigenvectors; the eigenspaces form an internal direct sum decomposition of `V`;
the eigenspaces span `V`; `dim V` equals the sum of the dimensions of the eigenspaces. -/
@[kb "axler2024" "5.55, p. 183"]
theorem axler_5_55 (T : Module.End K V) :
    List.TFAE [IsDiagonalizable T,
      ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, ∃ μ, T.HasEigenvector μ (b i),
      DirectSum.IsInternal (fun μ : T.Eigenvalues => T.eigenspace (μ : K)),
      ⨆ μ : K, T.eigenspace μ = ⊤,
      finrank K V = ∑ μ : T.Eigenvalues, finrank K (T.eigenspace (μ : K))] := by
  classical
  tfae_have 1 → 2 := by
    rintro ⟨b, hb⟩
    refine ⟨b, fun i => ?_⟩
    obtain ⟨μ, hμ⟩ := (isDiag_toMatrix_iff b T).1 hb i
    exact ⟨μ, Module.End.mem_eigenspace_iff.mpr hμ, b.ne_zero i⟩
  tfae_have 2 → 1 := by
    rintro ⟨b, hb⟩
    refine ⟨b, (isDiag_toMatrix_iff b T).2 fun i => ?_⟩
    obtain ⟨μ, hμ⟩ := hb i
    exact ⟨μ, hμ.apply_eq_smul⟩
  tfae_have 2 → 4 := by
    rintro ⟨b, hb⟩
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨μ, hμ⟩ := hb i
    exact Submodule.mem_iSup_of_mem μ hμ.1
  tfae_have 4 → 3 := by
    intro h
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (axler_5_54 T).1
      (by rw [iSup_eigenvalues_eq]; exact h)
  tfae_have 3 → 5 := finrank_eq_sum_of_isInternal T
  tfae_have 5 → 4 := (finrank_eq_sum_iff_iSup_eq_top T).1
  tfae_have 3 → 2 := by
    intro hint
    have h5 := finrank_eq_sum_of_isInternal T hint
    let v : ∀ μ : T.Eigenvalues, Basis (Fin (finrank K (T.eigenspace (μ : K)))) K
        (T.eigenspace (μ : K)) := fun μ => Module.finBasis K _
    have hcard : Fintype.card (Σ μ : T.Eigenvalues, Fin (finrank K (T.eigenspace (μ : K)))) =
        finrank K V := by
      rw [Fintype.card_sigma, h5]
      simp
    let e := Fintype.equivFinOfCardEq hcard
    refine ⟨(hint.collectedBasis v).reindex e, fun i => ?_⟩
    rw [Basis.reindex_apply]
    exact ⟨((e.symm i).1 : K), hint.collectedBasis_mem v (e.symm i),
      (hint.collectedBasis v).ne_zero _⟩
  tfae_finish

/-- **Hefferon Theorem Five.II.2.4**: an operator is diagonalizable iff there is a basis of
eigenvectors. -/
@[kb "hefferon2020" "Five.II.2.4, p. 419"]
theorem hefferon_Five_II_2_4 (T : Module.End K V) :
    IsDiagonalizable T ↔
      ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, ∃ μ, T.HasEigenvector μ (b i) :=
  (axler_5_55 T).out 1 2

/-- **Axler 5.58** (and Hefferon Five.II.3.20): an operator with `dim V` distinct eigenvalues is
diagonalizable. -/
@[kb "axler2024" "5.58, p. 184"]
theorem axler_5_58 (T : Module.End K V)
    (h : finrank K V ≤ Fintype.card T.Eigenvalues) : IsDiagonalizable T := by
  refine ((axler_5_55 T).out 1 5).2 ?_
  have h1 : Fintype.card T.Eigenvalues ≤ ∑ μ : T.Eigenvalues, finrank K (T.eigenspace (μ : K)) := by
    rw [Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun μ _ => ?_
    exact Submodule.one_le_finrank_iff.mpr μ.2
  have h2 := (axler_5_54 T).2
  omega

/-- A squarefree nonzero polynomial has no repeated root. -/
theorem nodup_roots_of_squarefree {p : K[X]} (hp : p ≠ 0) (hsq : Squarefree p) :
    p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  by_contra hlt
  rw [not_le] at hlt
  have hle : Multiset.replicate 2 a ≤ p.roots := Multiset.le_count_iff_replicate_le.mp hlt
  have hd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp _).2 hle
  simp only [Multiset.map_replicate, Multiset.prod_replicate] at hd
  exact not_isUnit_X_sub_C a (hsq (X - C a) (by rw [← sq]; exact hd))

/-- **Axler 5.62**: `T` is diagonalizable iff its minimal polynomial is a product of linear
factors `X - a` for a finite set `s` of distinct scalars. -/
@[kb "axler2024" "5.62, p. 187"]
theorem axler_5_62 (T : Module.End K V) :
    IsDiagonalizable T ↔ ∃ s : Finset K, minpoly K T = ∏ a ∈ s, (X - C a) := by
  classical
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := ((axler_5_55 T).out 1 2).1 hd
    let s : Finset K := Finset.univ.image (fun μ : T.Eigenvalues => (μ : K))
    have hs : ∀ a, a ∈ s ↔ T.HasEigenvalue a := by
      intro a
      constructor
      · intro hmem
        obtain ⟨μ, _, rfl⟩ := Finset.mem_image.mp hmem
        exact μ.2
      · intro h
        exact Finset.mem_image.mpr ⟨⟨a, h⟩, Finset.mem_univ _, rfl⟩
    have hne : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hker : aeval T (∏ a ∈ s, (X - C a)) = 0 := by
      refine b.ext fun i => ?_
      obtain ⟨μ, hμ⟩ := hb i
      have hμs : μ ∈ s := (hs μ).2 (Module.End.hasEigenvalue_of_hasEigenvector hμ)
      rw [← Finset.mul_prod_erase s (fun a => X - C a) hμs, mul_comm, map_mul,
        mul_apply_eq_comp]
      have : aeval T (X - C μ) (b i) = 0 := by
        simp [sub_eq_zero.mpr hμ.apply_eq_smul]
      rw [this, map_zero]
      rfl
    have hdvd1 : minpoly K T ∣ ∏ a ∈ s, (X - C a) := minpoly.dvd K T hker
    have hdvd2 : (∏ a ∈ s, (X - C a)) ∣ minpoly K T := by
      rw [Finset.prod_eq_multiset_prod]
      refine (Multiset.prod_X_sub_C_dvd_iff_le_roots hne s.val).2 ?_
      rw [Multiset.le_iff_subset s.nodup]
      intro a ha
      rw [mem_roots hne]
      exact Module.End.isRoot_of_hasEigenvalue ((hs a).1 ha)
    exact ⟨s, eq_of_monic_of_associated (minpoly.monic (Algebra.IsIntegral.isIntegral T))
      (monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a) (associated_of_dvd_dvd hdvd1 hdvd2)⟩
  · rintro ⟨s, hs⟩
    refine ((axler_5_55 T).out 4 1).1
      (iSup_eigenspace_eq_top_of_aeval_prod_eq_zero T s ?_)
    rw [← hs]
    exact minpoly.aeval K T

/-- Diagonalizable iff the minimal polynomial splits and is squarefree (no repeated roots). -/
theorem isDiagonalizable_iff_splits_squarefree (T : Module.End K V) :
    IsDiagonalizable T ↔ (minpoly K T).Splits ∧ Squarefree (minpoly K T) := by
  rw [axler_5_62]
  constructor
  · rintro ⟨s, hs⟩
    rw [hs]
    exact ⟨Splits.prod fun a _ => Splits.X_sub_C a,
      (separable_prod_X_sub_C_iff'.2 (fun x _ y _ h => h)).squarefree⟩
  · rintro ⟨hsp, hsq⟩
    classical
    have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) T)
    have hnd := nodup_roots_of_squarefree hm.ne_zero hsq
    refine ⟨(minpoly K T).roots.toFinset, ?_⟩
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    exact hsp.eq_prod_roots_of_monic hm

/-- The minimal polynomial of the restriction of `T` to an invariant subspace divides the minimal
polynomial of `T`. -/
theorem minpoly_restrict_dvd (T : Module.End K V) (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) :
    minpoly K (T.restrict hU) ∣ minpoly K T := by
  apply minpoly.dvd
  have key : ∀ q : K[X], ∀ x : U,
      ((aeval (T.restrict hU) q x : U) : V) = aeval T q (x : V) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro x; simp [hp x, hq x]
    | monomial n a =>
      intro x
      simp [aeval_monomial, Module.End.pow_restrict _ hU]
  ext x
  rw [key, minpoly.aeval]
  rfl

/-- **Axler 5.65**: the restriction of a diagonalizable operator to an invariant subspace is
diagonalizable. -/
@[kb "axler2024" "5.65, p. 188"]
theorem axler_5_65 (T : Module.End K V) (hT : IsDiagonalizable T) (U : Submodule K V)
    (hU : ∀ x ∈ U, T x ∈ U) : IsDiagonalizable (T.restrict hU) := by
  obtain ⟨hs, hsq⟩ := (isDiagonalizable_iff_splits_squarefree T).1 hT
  have hdvd := minpoly_restrict_dvd T U hU
  have hne : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  exact (isDiagonalizable_iff_splits_squarefree _).2
    ⟨hs.of_dvd hne hdvd, hsq.squarefree_of_dvd hdvd⟩

/-- The shift `(a, b, c) ↦ (b, c, 0)` on `K³`. -/
def shiftLeft3 : Module.End K (Fin 3 → K) where
  toFun x := ![x 1, x 2, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- **Axler 5.57**: the shift `(a, b, c) ↦ (b, c, 0)` on `K³` is not diagonalizable. -/
@[kb "axler2024" "5.57, p. 184"]
theorem axler_5_57 : ¬ IsDiagonalizable (shiftLeft3 (K := K)) := by
  intro hd
  have htop := ((axler_5_55 (shiftLeft3 (K := K))).out 1 4).1 hd
  let P : Submodule K (Fin 3 → K) :=
    LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 1) ⊓
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 3 => K) 2)
  have hle : (⨆ μ : K, (shiftLeft3 (K := K)).eigenspace μ) ≤ P := by
    refine iSup_le fun μ x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx
    have h1 : x 2 = μ * x 1 := congrFun hx 1
    have h2 : (0 : K) = μ * x 2 := congrFun hx 2
    have h0 : x 1 = μ * x 0 := congrFun hx 0
    by_cases hμ : μ = 0
    · subst hμ
      exact ⟨by simpa using h0, by simpa using h1⟩
    · have e2 : x 2 = 0 := (mul_eq_zero.mp h2.symm).resolve_left hμ
      have e1 : x 1 = 0 := by
        have : μ * x 1 = 0 := by rw [← h1, e2]
        exact (mul_eq_zero.mp this).resolve_left hμ
      exact ⟨e1, e2⟩
  have hmem : (Pi.single 1 1 : Fin 3 → K) ∈ P := by
    apply hle
    rw [htop]
    trivial
  have := LinearMap.mem_ker.mp hmem.1
  simp at this

/-- Algebraic multiplicity of an eigenvalue: its multiplicity as a root of the characteristic
polynomial (Hefferon Definition Five.II.3.17, Axler 8.x). -/
noncomputable def algebraicMultiplicity (T : Module.End K V) (μ : K) : ℕ :=
  T.charpoly.rootMultiplicity μ

/-- **Hefferon Definition Five.II.3.17**: geometric multiplicity of an eigenvalue: the dimension
of its eigenspace. -/
@[kb "hefferon2020" "Five.II.3.17, p. 428"]
noncomputable def geometricMultiplicity (T : Module.End K V) (μ : K) : ℕ :=
  finrank K (T.eigenspace μ)

/-- Geometric multiplicity is at most algebraic multiplicity. -/
theorem geometricMultiplicity_le_algebraicMultiplicity (T : Module.End K V) (μ : K) :
    geometricMultiplicity T μ ≤ algebraicMultiplicity T μ :=
  LinearMap.finrank_eigenspace_le T μ

/-- The algebraic multiplicity equals the dimension of the generalized eigenspace. -/
theorem algebraicMultiplicity_eq_finrank_maxGenEigenspace (T : Module.End K V) (μ : K) :
    algebraicMultiplicity T μ = finrank K (T.maxGenEigenspace μ) :=
  (LinearMap.finrank_maxGenEigenspace_eq T μ).symm

section AlgClosed

variable [IsAlgClosed K]

/-- **Axler Exercise 5D.15**: over an algebraically closed field, `T` is diagonalizable iff its
minimal polynomial is squarefree iff it has no repeated root iff `gcd(p, p') = 1` (expressed as
`IsCoprime p p'`). -/
@[kb "axler2024" "Ex5D.15, p. 191"]
theorem axler_ex5D_15 (T : Module.End K V) :
    List.TFAE [IsDiagonalizable T, Squarefree (minpoly K T), (minpoly K T).roots.Nodup,
      IsCoprime (minpoly K T) (derivative (minpoly K T))] := by
  have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) T)
  have hsp := IsAlgClosed.splits (minpoly K T)
  tfae_have 1 ↔ 2 := by
    rw [isDiagonalizable_iff_splits_squarefree]
    exact ⟨fun h => h.2, fun h => ⟨hsp, h⟩⟩
  tfae_have 2 → 3 := nodup_roots_of_squarefree hm.ne_zero
  tfae_have 3 → 4 := fun h => (nodup_roots_iff_of_splits hm.ne_zero hsp).1 h
  tfae_have 4 → 2 := fun h => Polynomial.Separable.squarefree h
  tfae_finish

/-- **Axler Exercise 5D.5**: over an algebraically closed field, `T` is diagonalizable iff for
every `μ`, `V` is the direct sum (complementary pair) of `null (T - μ I)` and `range (T - μ I)`. -/
@[kb "axler2024" "Ex5D.5, p. 190"]
theorem axler_ex5D_5 (T : Module.End K V) :
    IsDiagonalizable T ↔ ∀ μ : K,
      IsCompl (LinearMap.ker (T - μ • (1 : Module.End K V)))
        (LinearMap.range (T - μ • (1 : Module.End K V))) := by
  constructor
  · intro hd μ
    obtain ⟨hs, hsq⟩ := (isDiagonalizable_iff_splits_squarefree T).1 hd
    have hsemi : T.IsSemisimple :=
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (minpoly.aeval K T)
    set S : Module.End K V := T - μ • (1 : Module.End K V) with hS
    have hdisj : Disjoint (LinearMap.ker S) (LinearMap.range S) := by
      rw [Submodule.disjoint_def]
      rintro x hx ⟨y, rfl⟩
      have h2 : S (S y) = 0 := LinearMap.mem_ker.mp hx
      have hy : y ∈ T.maxGenEigenspace μ :=
        (Module.End.mem_maxGenEigenspace T μ y).2 ⟨2, by rw [pow_two, mul_apply_eq_comp]; exact h2⟩
      rw [hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hy
      have := Module.End.mem_eigenspace_iff.mp hy
      simp [hS, this]
    refine ⟨hdisj, codisjoint_iff.mpr (Submodule.eq_top_of_disjoint _ _ ?_ hdisj)⟩
    have := LinearMap.finrank_range_add_finrank_ker S
    omega
  · intro h
    refine ((axler_5_55 T).out 4 1).1 ?_
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_mono fun μ x hx => ?_
    rw [Module.End.mem_maxGenEigenspace] at hx
    obtain ⟨k, hk⟩ := hx
    rw [Module.End.mem_eigenspace_iff]
    set S : Module.End K V := T - μ • (1 : Module.End K V) with hS
    have hdis := (h μ).disjoint
    have key : ∀ k : ℕ, ∀ x, (S ^ (k + 1)) x = 0 → S x = 0 := by
      intro k
      induction k with
      | zero => intro x hx; simpa using hx
      | succ k ih =>
        intro x hx
        refine ih x ?_
        refine Submodule.disjoint_def.mp hdis _ ?_ ?_
        · rw [LinearMap.mem_ker, ← mul_apply_eq_comp, ← pow_succ']
          exact hx
        · refine ⟨(S ^ k) x, ?_⟩
          rw [← mul_apply_eq_comp, ← pow_succ']
    have hS0 : S x = 0 := by
      refine key k x ?_
      rw [pow_succ', mul_apply_eq_comp, hk, map_zero]
    simpa [hS, sub_eq_zero] using hS0

end AlgClosed

/-- **Axler Exercise 5D.22**: if the matrix of `T` (over a normed field, e.g. `ℝ` or `ℂ`) is
strictly diagonally dominant by rows, then `T` is invertible. -/
@[kb "axler2024" "Ex5D.22, p. 192"]
theorem axler_ex5D_22 {𝕜 W ι : Type*} [NormedField 𝕜] [AddCommGroup W] [Module 𝕜 W] [Fintype ι]
    [DecidableEq ι] (b : Basis ι 𝕜 W) (T : Module.End 𝕜 W)
    (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖LinearMap.toMatrix b b T k j‖ <
      ‖LinearMap.toMatrix b b T k k‖) :
    Function.Bijective T := by
  have hdet := det_ne_zero_of_sum_row_lt_diag h
  rw [LinearMap.det_toMatrix] at hdet
  haveI := Module.Finite.of_basis b
  exact (Module.End.isUnit_iff T).1 ((LinearMap.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet))

/-! ### Simultaneous diagonalization (Axler 5.76, Exercise 5E.2) -/

/-- Restrictions of commuting operators to a common invariant subspace commute. -/
theorem commute_restrict {T₁ T₂ : Module.End K V} (h : Commute T₁ T₂) (U : Submodule K V)
    (h₁ : ∀ x ∈ U, T₁ x ∈ U) (h₂ : ∀ x ∈ U, T₂ x ∈ U) :
    Commute (T₁.restrict h₁) (T₂.restrict h₂) := by
  show T₁.restrict h₁ * T₂.restrict h₂ = T₂.restrict h₂ * T₁.restrict h₁
  ext x
  have := congrArg (fun f => f (x : V)) h.eq
  simpa using this

/-- A commuting family of diagonalizable operators has a common eigenbasis (induction on the
dimension: split `V` into the eigenspaces of a non-scalar member of the family). -/
theorem exists_common_eigenbasis {ι : Type*} : ∀ (n : ℕ) (V : Type v) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V], finrank K V = n → ∀ (T : ι → Module.End K V),
    (∀ i, IsDiagonalizable (T i)) → (∀ i j, Commute (T i) (T j)) →
      ∃ b : Basis (Fin n) K V, ∀ i k, ∃ μ : K, T i (b k) = μ • b k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn T hd hc
  by_cases hsc : ∀ i, ∃ c : K, T i = c • (1 : Module.End K V)
  · refine ⟨Module.finBasisOfFinrankEq K V hn, fun i k => ?_⟩
    obtain ⟨c, hci⟩ := hsc i
    exact ⟨c, by rw [hci]; simp⟩
  · have hex : ∃ j, ∀ c : K, T j ≠ c • (1 : Module.End K V) := by
      by_contra hcon
      apply hsc
      intro i
      by_contra hi
      exact hcon ⟨i, fun c hc => hi ⟨c, hc⟩⟩
    obtain ⟨j, hj⟩ := hex
    classical
    have hint := ((axler_5_55 (T j)).out 1 3).1 (hd j)
    have h5 := finrank_eq_sum_of_isInternal (T j) hint
    have hlt : ∀ μ : (T j).Eigenvalues, finrank K ((T j).eigenspace (μ : K)) < n := by
      intro μ
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hj μ
      ext x
      have : x ∈ (T j).eigenspace (μ : K) := by rw [htop]; trivial
      simpa using Module.End.mem_eigenspace_iff.mp this
    have hinv : ∀ i (μ : K), ∀ x ∈ (T j).eigenspace μ, T i x ∈ (T j).eigenspace μ := by
      intro i μ x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have := congrArg (fun f => f x) (hc j i).eq
      simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
      rw [this, hx, map_smul]
    have hch : ∀ μ : (T j).Eigenvalues, ∃ c : Basis (Fin (finrank K ((T j).eigenspace (μ : K))))
        K ((T j).eigenspace (μ : K)),
        ∀ i k, ∃ ν : K, ((T i).restrict (hinv i (μ : K))) (c k) = ν • c k := by
      intro μ
      exact ih _ (hlt μ) ((T j).eigenspace (μ : K)) rfl
        (fun i => (T i).restrict (hinv i (μ : K)))
        (fun i => axler_5_65 (T i) (hd i) _ (hinv i (μ : K)))
        (fun i i' => commute_restrict (hc i i') _ _ _)
    choose c hc' using hch
    have hcard : Fintype.card (Σ μ : (T j).Eigenvalues,
        Fin (finrank K ((T j).eigenspace (μ : K)))) = n := by
      rw [Fintype.card_sigma, ← hn, h5]
      simp
    let e := Fintype.equivFinOfCardEq hcard
    refine ⟨(hint.collectedBasis c).reindex e, fun i k => ?_⟩
    rw [Basis.reindex_apply, DirectSum.IsInternal.collectedBasis_coe]
    obtain ⟨ν, hν⟩ := hc' (e.symm k).1 i (e.symm k).2
    exact ⟨ν, by simpa using congrArg Subtype.val hν⟩

/-- **Axler Exercise 5E.2** (family version of 5.76): a family of operators is simultaneously
diagonalizable (some basis makes every matrix diagonal) iff each member is diagonalizable and the
members pairwise commute. -/
@[kb "axler2024" "Ex5E.2, p. 197"]
theorem axler_ex5E_2 {ι : Type*} (T : ι → Module.End K V) :
    ((∀ i, IsDiagonalizable (T i)) ∧ ∀ i j, Commute (T i) (T j)) ↔
      ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, (LinearMap.toMatrix b b (T i)).IsDiag := by
  classical
  constructor
  · rintro ⟨hd, hc⟩
    obtain ⟨b, hb⟩ := exists_common_eigenbasis (finrank K V) V rfl T hd hc
    exact ⟨b, fun i => (isDiag_toMatrix_iff b (T i)).2 fun k => hb i k⟩
  · rintro ⟨b, hb⟩
    refine ⟨fun i => ⟨b, hb i⟩, fun i i' => ?_⟩
    show T i * T i' = T i' * T i
    refine b.ext fun k => ?_
    obtain ⟨μ, hμ⟩ := (isDiag_toMatrix_iff b (T i)).1 (hb i) k
    obtain ⟨ν, hν⟩ := (isDiag_toMatrix_iff b (T i')).1 (hb i') k
    simp only [mul_apply_eq_comp, LinearMap.comp_apply, hμ, hν, map_smul, smul_smul, mul_comm]

/-- **Axler 5.76**: two diagonalizable operators have diagonal matrices in a common basis iff they
commute. -/
@[kb "axler2024" "5.76, p. 194"]
theorem axler_5_76 (S T : Module.End K V) (hS : IsDiagonalizable S) (hT : IsDiagonalizable T) :
    (∃ b : Basis (Fin (finrank K V)) K V,
      (LinearMap.toMatrix b b S).IsDiag ∧ (LinearMap.toMatrix b b T).IsDiag) ↔ Commute S T := by
  have key := axler_ex5E_2 (![S, T] : Fin 2 → Module.End K V)
  constructor
  · rintro ⟨b, hbS, hbT⟩
    have := key.2 ⟨b, fun i => by fin_cases i <;> simpa⟩
    simpa using this.2 0 1
  · intro h
    obtain ⟨b, hb⟩ := key.1 ⟨fun i => by fin_cases i <;> simpa,
      fun i j => by fin_cases i <;> fin_cases j <;> simp [h, h.symm]⟩
    exact ⟨b, by simpa using hb 0, by simpa using hb 1⟩

/-- **Axler 5.55 (c)**: `T` is diagonalizable iff `V` is an internal direct sum of `dim V`
one-dimensional `T`-invariant subspaces. -/
@[kb "axler2024" "5.55, p. 183"]
theorem axler_5_55_c (T : Module.End K V) :
    IsDiagonalizable T ↔ ∃ U : Fin (finrank K V) → Submodule K V,
      (∀ i, finrank K (U i) = 1) ∧ (∀ i, ∀ x ∈ U i, T x ∈ U i) ∧ DirectSum.IsInternal U := by
  classical
  constructor
  · intro hd
    obtain ⟨b, hb⟩ := ((axler_5_55 T).out 1 2).1 hd
    refine ⟨fun i => K ∙ b i, fun i => finrank_span_singleton (b.ne_zero i), ?_, ?_⟩
    · intro i x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨μ, hμ⟩ := hb i
      rw [map_smul, hμ.apply_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
      exact ⟨b.linearIndependent.iSupIndep_span_singleton,
        by rw [← Submodule.span_range_eq_iSup, b.span_eq]⟩
  · rintro ⟨U, h1, hT, hint⟩
    refine ((axler_5_55 T).out 4 1).1 ?_
    rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp (h1 i)
    obtain ⟨μ, hμ⟩ := hv ⟨T v, hT i v v.2⟩
    refine le_trans ?_ (le_iSup (fun μ : K => T.eigenspace μ) μ)
    intro w hw
    obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
    rw [Module.End.mem_eigenspace_iff]
    have hw' : w = c • (v : V) := (congrArg Subtype.val hc).symm
    have hTv : T (v : V) = μ • (v : V) := (congrArg Subtype.val hμ).symm
    rw [hw', map_smul, hTv, smul_comm]

/-- A square matrix is diagonalizable (Hefferon): similar to a diagonal matrix, i.e.
`P⁻¹ A P` is diagonal for some invertible `P`. -/
def IsDiagonalizableMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
    (((P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) * A *
      (P : Matrix (Fin n) (Fin n) K)).IsDiag

/-- **Hefferon Definition Five.II.2.1** (matrix version): a matrix is diagonalizable iff the map
it represents (`Matrix.toLin'`) is diagonalizable. -/
@[kb "hefferon2020" "Five.II.2.1, p. 418"]
theorem hefferon_Five_II_2_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    IsDiagonalizableMatrix A ↔ IsDiagonalizable (Matrix.toLin' A) := by
  classical
  have hrank : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  refine Iff.trans ?_ ((axler_5_55 (Matrix.toLin' A)).out 2 1)
  constructor
  · rintro ⟨P, hD⟩
    set D : Matrix (Fin n) (Fin n) K := ((P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
      Matrix (Fin n) (Fin n) K) * A * (P : Matrix (Fin n) (Fin n) K) with hDdef
    have hAP : A * (P : Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K) * D := by
      rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    haveI : Invertible (P : Matrix (Fin n) (Fin n) K) := P.invertible
    let c : Basis (Fin n) K (Fin n → K) :=
      (Pi.basisFun K (Fin n)).map (Matrix.toLinearEquiv' (P : Matrix (Fin n) (Fin n) K) inferInstance)
    have key : ∀ k : Fin n, (Matrix.toLin' A) (c k) = D k k • c k := by
      intro k
      have hck : c k = Matrix.mulVec (P : Matrix (Fin n) (Fin n) K) (Pi.single k 1) := by
        simp only [c, Basis.map_apply, Pi.basisFun_apply]
        rfl
      have hDk : Matrix.mulVec D (Pi.single k 1 : Fin n → K) = D k k • Pi.single k 1 := by
        funext i
        by_cases hik : i = k
        · subst hik; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
        · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hD hik, hik]
      rw [hck, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hAP, ← Matrix.mulVec_mulVec, hDk,
        Matrix.mulVec_smul]
    refine ⟨c.reindex (finCongr hrank.symm), fun j => ?_⟩
    refine ⟨D ((finCongr hrank.symm).symm j) ((finCongr hrank.symm).symm j),
      Module.End.mem_eigenspace_iff.mpr ?_, Basis.ne_zero _ _⟩
    simpa using key ((finCongr hrank.symm).symm j)
  · rintro ⟨b, hb⟩
    let c : Basis (Fin n) K (Fin n → K) := b.reindex (finCongr hrank)
    have hc : ∀ k, ∃ μ : K, Matrix.toLin' A (c k) = μ • c k := by
      intro k
      obtain ⟨μ, hμ⟩ := hb ((finCongr hrank).symm k)
      exact ⟨μ, by simpa [c] using Module.End.HasEigenvector.apply_eq_smul hμ⟩
    choose μ hμ using hc
    let e := Pi.basisFun K (Fin n)
    haveI : Invertible (e.toMatrix c) := e.invertibleToMatrix c
    have hAP : A * e.toMatrix c = e.toMatrix c * Matrix.diagonal μ := by
      ext i j
      have := congrFun (hμ j) i
      simp only [Matrix.toLin'_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Basis.toMatrix_apply, e, Pi.basisFun_repr]
      have hR : ∑ x, c x i * Matrix.diagonal μ x j = c j i * μ j := by
        simp [Matrix.diagonal_apply]
      rw [hR, mul_comm]
      exact this
    refine ⟨unitOfInvertible (e.toMatrix c), ?_⟩
    have : (((unitOfInvertible (e.toMatrix c))⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
        Matrix (Fin n) (Fin n) K) * A * (unitOfInvertible (e.toMatrix c) : Matrix (Fin n) (Fin n) K)
        = Matrix.diagonal μ := by
      rw [Matrix.mul_assoc]
      change _ * (A * e.toMatrix c) = _
      rw [hAP]
      exact Units.inv_mul_cancel_left (unitOfInvertible (e.toMatrix c)) _
    rw [this]
    exact Matrix.isDiag_diagonal μ

/-- **Hefferon Example Five.II.2.3**: the nilpotent matrix `[[0,0],[1,0]]` is not diagonalizable
(over any field). -/
@[kb "hefferon2020" "Five.II.2.3, p. 418"]
theorem hefferon_Five_II_2_3 :
    ¬ IsDiagonalizableMatrix (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
  rw [hefferon_Five_II_2_1]
  intro hd
  have htop := ((axler_5_55 (Matrix.toLin' (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K))).out 1 4).1
    hd
  let P : Submodule K (Fin 2 → K) :=
    LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ : Fin 2 => K) 0)
  have hle : (⨆ μ : K, Module.End.eigenspace
      (Matrix.toLin' (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K)) μ) ≤ P := by
    refine iSup_le fun μ x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx
    have hT0 : (Matrix.toLin' (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K)) x 0 = 0 := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hT1 : (Matrix.toLin' (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K)) x 1 = x 0 := by
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h0 : μ * x 0 = 0 := by
      rw [← hT0]; exact (congrFun hx 0).symm
    have h1 : x 0 = μ * x 1 := by
      rw [← hT1]; exact congrFun hx 1
    by_cases hμ : μ = 0
    · subst hμ
      show x 0 = 0
      simpa using h1
    · show x 0 = 0
      exact (mul_eq_zero.mp h0).resolve_left hμ
  have hmem : (Pi.single 0 1 : Fin 2 → K) ∈ P := by
    apply hle
    rw [htop]
    trivial
  have := LinearMap.mem_ker.mp hmem
  simp at this

end UndergradKB.LinearAlgebra
