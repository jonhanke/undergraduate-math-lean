import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Generalized eigenspaces, the Fitting decomposition and the characteristic polynomial

Axler 8.4-8.41 and Hefferon Five.III.1-2, Five.IV.1-2.
-/

open Module Set Submodule

namespace UndergradKB.LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

namespace GenEigen

variable (T : Module.End K V)

lemma ker_pow_mono : Monotone fun k : ℕ => LinearMap.ker (T ^ k) := by
  refine monotone_nat_of_le_succ fun k x hx => ?_
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pow_succ', mul_apply_eq_comp, hx, map_zero]

lemma range_pow_anti : Antitone fun k : ℕ => LinearMap.range (T ^ k) := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [pow_succ]
  exact LinearMap.range_comp_le_range _ _

lemma ker_eq_iff_range_eq (k : ℕ) :
    LinearMap.ker (T ^ k) = LinearMap.ker (T ^ (k + 1)) ↔
      LinearMap.range (T ^ (k + 1)) = LinearMap.range (T ^ k) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (T ^ k)
  have h2 := LinearMap.finrank_range_add_finrank_ker (T ^ (k + 1))
  have hk : LinearMap.ker (T ^ k) ≤ LinearMap.ker (T ^ (k + 1)) := ker_pow_mono T (Nat.le_succ k)
  have hr : LinearMap.range (T ^ (k + 1)) ≤ LinearMap.range (T ^ k) :=
    range_pow_anti T (Nat.le_succ k)
  constructor
  · intro h
    apply Submodule.eq_of_le_of_finrank_le hr
    rw [h] at h1
    omega
  · intro h
    apply Submodule.eq_of_le_of_finrank_le hk
    rw [h] at h2
    omega

lemma range_pow_eq_of_ge {k : ℕ} (hk : finrank K V ≤ k) :
    LinearMap.range (T ^ k) = LinearMap.range (T ^ finrank K V) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    apply (ker_eq_iff_range_eq T k).mp
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hk,
      Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_succ_of_le hk)]

end GenEigen

open GenEigen

/-- Hefferon Lemma Five.III.1.4: the ranges of the powers descend, the null spaces ascend, both
strictly until the first power `k` (at most `dim V`) from which both are constant. -/
@[kb "hefferon2020" "Five.III.1.4, p. 435"]
theorem hefferon_Five_III_1_4 (T : Module.End K V) :
    Antitone (fun j : ℕ => LinearMap.range (T ^ j)) ∧
    Monotone (fun j : ℕ => LinearMap.ker (T ^ j)) ∧
    ∃ k ≤ finrank K V,
      (∀ j < k, LinearMap.range (T ^ (j + 1)) < LinearMap.range (T ^ j) ∧
        LinearMap.ker (T ^ j) < LinearMap.ker (T ^ (j + 1))) ∧
      ∀ j, k ≤ j → LinearMap.range (T ^ j) = LinearMap.range (T ^ k) ∧
        LinearMap.ker (T ^ j) = LinearMap.ker (T ^ k) := by
  classical
  refine ⟨range_pow_anti T, ker_pow_mono T, ?_⟩
  have hex : ∃ j, LinearMap.ker (T ^ j) = LinearMap.ker (T ^ (j + 1)) :=
    ⟨finrank K V, by
      rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_succ _)]⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by
      rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_succ _)]), ?_, ?_⟩
  · intro j hj
    have hne := Nat.find_min hex hj
    refine ⟨lt_of_le_of_ne (range_pow_anti T (Nat.le_succ j)) fun h => hne ?_,
      lt_of_le_of_ne (ker_pow_mono T (Nat.le_succ j)) hne⟩
    exact (ker_eq_iff_range_eq T j).mpr h
  · intro j hj
    have hk := Nat.find_spec hex
    have hR : ∀ i, LinearMap.range (T ^ (Nat.find hex + i)) =
        LinearMap.range (T ^ Nat.find hex) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [← ih, ← add_assoc]
        apply (ker_eq_iff_range_eq T (Nat.find hex + i)).mp
        have e1 := Module.End.ker_pow_constant hk i
        have e2 := Module.End.ker_pow_constant hk (i + 1)
        rw [← add_assoc] at e2
        exact e1.symm.trans e2
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact ⟨hR i, (Module.End.ker_pow_constant hk i).symm⟩

/-- Hefferon Lemma Five.III.1.8 (and Axler 8.4-8.5 for the null space): on an `n`-dimensional space
the generalized range `⨅ k, range (T^k)` is `range (T^n)` and the generalized null space
`⨆ k, ker (T^k)` is `ker (T^n)` (which is the generalized eigenspace of `0`). -/
@[kb "hefferon2020" "Five.III.1.8, p. 437"]
theorem hefferon_Five_III_1_8 (T : Module.End K V) :
    (⨅ k : ℕ, LinearMap.range (T ^ k)) = LinearMap.range (T ^ finrank K V) ∧
    (⨆ k : ℕ, LinearMap.ker (T ^ k)) = LinearMap.ker (T ^ finrank K V) ∧
    T.maxGenEigenspace 0 = LinearMap.ker (T ^ finrank K V) := by
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · exact iInf_le _ _
    · refine le_iInf fun k => ?_
      rcases le_total k (finrank K V) with h | h
      · exact range_pow_anti T h
      · rw [range_pow_eq_of_ge T h]
  · apply le_antisymm
    · refine iSup_le fun k => ?_
      exact Module.End.ker_pow_le_ker_pow_finrank T k
    · exact le_iSup (fun k : ℕ => LinearMap.ker (T ^ k)) _
  · rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]
    simp

/-- Fitting decomposition: `V` is the direct sum of `ker (T^n)` and `range (T^n)`, `n = dim V`. -/
theorem isCompl_ker_pow_range_pow (T : Module.End K V) :
    IsCompl (LinearMap.ker (T ^ finrank K V)) (LinearMap.range (T ^ finrank K V)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow T)
  have h := hN (max N (finrank K V)) (le_max_left _ _)
  rwa [Module.End.ker_pow_eq_ker_pow_finrank_of_le (le_max_right _ _),
    range_pow_eq_of_ge T (le_max_right _ _)] at h

/-- Axler 8.4/8.5: `V = null T^(dim V) ⊕ range T^(dim V)`. -/
@[kb "axler2024" "8.5, p. 317"]
theorem axler_8_5 (T : Module.End K V) :
    IsCompl (LinearMap.ker (T ^ finrank K V)) (LinearMap.range (T ^ finrank K V)) :=
  isCompl_ker_pow_range_pow T

/-- Hefferon Lemma Five.III.2.2: `V = R∞(T) ⊕ N∞(T)`, the generalized range and null spaces. -/
@[kb "hefferon2020" "Five.III.2.2, p. 439"]
theorem hefferon_Five_III_2_2 (T : Module.End K V) :
    IsCompl (⨅ k : ℕ, LinearMap.range (T ^ k)) (⨆ k : ℕ, LinearMap.ker (T ^ k)) := by
  obtain ⟨h1, h2, -⟩ := hefferon_Five_III_1_8 T
  rw [h1, h2]
  exact (isCompl_ker_pow_range_pow T).symm

/-- Hefferon Lemma Five.III.2.1: `T` restricted to the generalized range space `range (T^n)` is
one-to-one, hence an automorphism. -/
@[kb "hefferon2020" "Five.III.2.1, p. 438"]
theorem hefferon_Five_III_2_1 (T : Module.End K V) :
    ∃ h : ∀ x ∈ LinearMap.range (T ^ finrank K V), T x ∈ LinearMap.range (T ^ finrank K V),
      Function.Injective (T.restrict h) ∧ Function.Surjective (T.restrict h) := by
  have hmem : ∀ x ∈ LinearMap.range (T ^ finrank K V), T x ∈ LinearMap.range (T ^ finrank K V) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T y, by rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← pow_succ, ← pow_succ']⟩
  have hinj : Function.Injective (T.restrict hmem) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ h0
    have hT : T x = 0 := congrArg Subtype.val h0
    have hker : x ∈ LinearMap.ker (T ^ finrank K V) := by
      rcases Nat.eq_zero_or_pos (finrank K V) with h | h
      · have := Module.finrank_zero_iff.mp h
        rw [Subsingleton.elim x 0]; exact zero_mem _
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
        rw [LinearMap.mem_ker, hj, pow_succ, mul_apply_eq_comp, hT, map_zero]
    have := (isCompl_ker_pow_range_pow T).disjoint
    exact Subtype.ext ((Submodule.disjoint_def.mp this) x hker hx)
  exact ⟨hmem, hinj, LinearMap.injective_iff_surjective.mp hinj⟩

section complex

variable [IsAlgClosed K]

/-- Axler 8.9: over `ℂ` (any algebraically closed field) there is a basis of `V` consisting of
generalized eigenvectors of `T`. -/
@[kb "axler2024" "8.9, p. 319"]
theorem axler_8_9 (T : Module.End K V) :
    ∃ b : Module.Basis (Fin (finrank K V)) K V, ∀ i, ∃ (μ : K) (k : ℕ),
      ((T - μ • (1 : Module.End K V)) ^ k) (b i) = 0 := by
  let s : Set V := {x | x ≠ 0 ∧ ∃ (μ : K) (k : ℕ), ((T - μ • (1 : Module.End K V)) ^ k) x = 0}
  have hspan : span K s = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ x hx => ?_
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact subset_span ⟨hx0, μ, (Module.End.mem_maxGenEigenspace _ _ _).mp hx⟩
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent K s
  let hb : Module.Basis b K V :=
    Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := hb.indexEquiv (Module.finBasis K V)
  refine ⟨hb.reindex e, fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  have hx : hb (e.symm i) = ((e.symm i : b) : V) := by simp [hb]
  rw [hx]
  obtain ⟨-, μ, k, hk⟩ := hbs (e.symm i).2
  exact ⟨μ, k, hk⟩

lemma maxGenEigenspace_eq_bot_of_not (T : Module.End K V) {μ : K} (h : ¬ T.HasEigenvalue μ) :
    T.maxGenEigenspace μ = ⊥ := by
  rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
    Polynomial.rootMultiplicity_eq_zero]
  rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly] at h

open Classical in
/-- Axler 8.22: over `ℂ`, each generalized eigenspace is `T`-invariant, `T - μ` is nilpotent on
it, and `V` is the (internal) direct sum of the generalized eigenspaces of `T`. -/
@[kb "axler2024" "8.22, p. 327"]
theorem axler_8_22 (T : Module.End K V) :
    (∀ μ : K, ∀ x ∈ T.maxGenEigenspace μ, T x ∈ T.maxGenEigenspace μ) ∧
    (∀ μ : K, ∃ k : ℕ, ∀ x ∈ T.maxGenEigenspace μ,
      ((T - μ • (1 : Module.End K V)) ^ k) x = 0) ∧
    DirectSum.IsInternal (fun μ : T.Eigenvalues => T.maxGenEigenspace μ.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
    have hc : Commute T ((T - μ • (1 : Module.End K V)) ^ k) :=
      ((Commute.refl T).sub_right ((Commute.one_right T).smul_right μ)).pow_right k
    rw [← mul_apply_eq_comp, ← hc.eq, mul_apply_eq_comp, hk, map_zero]
  · intro μ
    refine ⟨finrank K V, fun x hx => ?_⟩
    have hx' : x ∈ T.maxGenEigenspace μ := hx
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hx'
    simpa [Module.End.genEigenspace_nat] using hx'
  · classical
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact T.independent_maxGenEigenspace.comp Subtype.val_injective
    · have := Module.End.iSup_maxGenEigenspace_eq_top T
      rw [eq_top_iff, ← this]
      refine iSup_le fun μ => ?_
      by_cases hμ : T.HasEigenvalue μ
      · exact le_iSup (fun μ : T.Eigenvalues => T.maxGenEigenspace μ.1) ⟨μ, hμ⟩
      · rw [maxGenEigenspace_eq_bot_of_not T hμ]; exact bot_le

end complex

/-- The multiplicity of an eigenvalue in the sense of Axler 8.23: the dimension of the generalized
eigenspace. -/
noncomputable def multiplicity (T : Module.End K V) (μ : K) : ℕ :=
  finrank K (T.maxGenEigenspace μ)

/-- Axler 8.23: the multiplicity of `μ` is `dim null (T - μ I)^(dim V)`; it equals the multiplicity of
`μ` as a root of the characteristic polynomial. -/
@[kb "axler2024" "8.23, p. 328"]
theorem axler_8_23 (T : Module.End K V) (μ : K) :
    multiplicity T μ = finrank K (LinearMap.ker ((T - μ • (1 : Module.End K V)) ^ finrank K V)) ∧
    multiplicity T μ = T.charpoly.rootMultiplicity μ := by
  refine ⟨?_, LinearMap.finrank_maxGenEigenspace_eq T μ⟩
  unfold multiplicity
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]

section complex2

variable [IsAlgClosed K]

/-- Axler 8.25: over `ℂ` the multiplicities of the eigenvalues add up to `dim V`. -/
@[kb "axler2024" "8.25, p. 329"]
theorem axler_8_25 (T : Module.End K V) :
    ∑ μ : T.Eigenvalues, multiplicity T μ.1 = finrank K V := by
  classical
  have h := (axler_8_22 T).2.2
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun μ : T.Eigenvalues => T.maxGenEigenspace μ.1)) h
  rw [← e.finrank_eq, Module.finrank_directSum]
  rfl

/-- Axler 8.26: over `ℂ` the characteristic polynomial is `∏ (z - λ_k)^(d_k)`, the product over
the distinct eigenvalues with their multiplicities. -/
@[kb "axler2024" "8.26, p. 329"]
theorem axler_8_26 (T : Module.End K V) :
    T.charpoly = ∏ μ : T.Eigenvalues, (Polynomial.X - Polynomial.C μ.1) ^ multiplicity T μ.1 := by
  classical
  have h := (IsAlgClosed.splits T.charpoly).eq_prod_roots_of_monic T.charpoly_monic
  have hne : T.charpoly ≠ 0 := T.charpoly_monic.ne_zero
  conv_lhs => rw [h]
  rw [Finset.prod_multiset_map_count]
  rw [Finset.prod_subtype (T.charpoly.roots.toFinset) (p := fun μ => T.HasEigenvalue μ)]
  · refine Finset.prod_congr rfl fun μ _ => ?_
    rw [multiplicity, LinearMap.finrank_maxGenEigenspace_eq, Polynomial.count_roots]
  · intro μ
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne,
      Module.End.hasEigenvalue_iff_isRoot_charpoly]

end complex2

/-- Hefferon Lemma Five.IV.1.8: the minimal and characteristic polynomial have the same roots,
and at every root the multiplicity `q` in the minimal polynomial satisfies `1 ≤ q ≤ p`, `p` the
multiplicity in the characteristic polynomial. -/
@[kb "hefferon2020" "Five.IV.1.8, p. 453"]
theorem hefferon_Five_IV_1_8 (T : Module.End K V) :
    minpoly K T ∣ T.charpoly ∧
    (∀ μ : K, (minpoly K T).IsRoot μ ↔ T.charpoly.IsRoot μ) ∧
    ∀ μ : K, T.charpoly.IsRoot μ →
      1 ≤ (minpoly K T).rootMultiplicity μ ∧
      (minpoly K T).rootMultiplicity μ ≤ T.charpoly.rootMultiplicity μ := by
  have hdvd : minpoly K T ∣ T.charpoly := LinearMap.minpoly_dvd_charpoly T
  have hroot : ∀ μ : K, (minpoly K T).IsRoot μ ↔ T.charpoly.IsRoot μ := fun μ => by
    rw [← Module.End.hasEigenvalue_iff_isRoot, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine ⟨hdvd, hroot, fun μ hμ => ⟨?_, ?_⟩⟩
  · exact (Polynomial.rootMultiplicity_pos (minpoly.ne_zero (Algebra.IsIntegral.isIntegral T))).mpr
      ((hroot μ).mpr hμ)
  · exact Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd T.charpoly_monic.ne_zero hdvd μ

/-- Axler 8.31: if `T` has an upper-triangular matrix in a basis, each `μ` appears on the diagonal
exactly `dim G(μ, T)` times. -/
@[kb "axler2024" "8.31, p. 331"]
theorem axler_8_31 [DecidableEq K] {ι : Type*} [Fintype ι] [LinearOrder ι] (T : Module.End K V)
    (b : Module.Basis ι K V) (hM : (LinearMap.toMatrix b b T).IsUpperTriangular) (μ : K) :
    (Finset.univ.filter fun i => LinearMap.toMatrix b b T i i = μ).card =
      finrank K (T.maxGenEigenspace μ) := by
  classical
  rw [LinearMap.finrank_maxGenEigenspace_eq, ← Polynomial.count_roots, ← LinearMap.charpoly_toMatrix T b,
    Matrix.charpoly_of_isUpperTriangular _ hM]
  have : ∏ i : ι, (Polynomial.X - Polynomial.C (LinearMap.toMatrix b b T i i)) =
      ((Finset.univ.val.map fun i => LinearMap.toMatrix b b T i i).map
        fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro x _
  exact eq_comm

/-- Hefferon Lemma Five.IV.2.11: a subspace is `T`-invariant iff it is `(T - lam)`-invariant (for
any scalar `lam`); the generalized null space and range of `T - lam` are invariant under every
`T - mu`. -/
@[kb "hefferon2020" "Five.IV.2.11, p. 466"]
theorem hefferon_Five_IV_2_11 (T : Module.End K V) :
    (∀ (W : Submodule K V) (lam : K), (∀ x ∈ W, T x ∈ W) ↔
      ∀ x ∈ W, (T - lam • (1 : Module.End K V)) x ∈ W) ∧
    (∀ lam mu : K, ∀ x ∈ (⨆ k : ℕ, LinearMap.ker ((T - lam • (1 : Module.End K V)) ^ k)),
      (T - mu • (1 : Module.End K V)) x ∈
        (⨆ k : ℕ, LinearMap.ker ((T - lam • (1 : Module.End K V)) ^ k))) ∧
    (∀ lam mu : K, ∀ x ∈ (⨅ k : ℕ, LinearMap.range ((T - lam • (1 : Module.End K V)) ^ k)),
      (T - mu • (1 : Module.End K V)) x ∈
        (⨅ k : ℕ, LinearMap.range ((T - lam • (1 : Module.End K V)) ^ k))) := by
  have hc : ∀ lam mu : K, Commute (T - mu • (1 : Module.End K V)) (T - lam • (1 : Module.End K V)) := by
    intro lam mu
    exact (((Commute.refl T).sub_right ((Commute.one_right T).smul_right lam)).sub_left
      (((Commute.one_left T).smul_left mu).sub_right
        (((Commute.one_left (1 : Module.End K V)).smul_left mu).smul_right lam)))
  refine ⟨fun W lam => ⟨fun h x hx => ?_, fun h x hx => ?_⟩, ?_, ?_⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact W.sub_mem (h x hx) (W.smul_mem lam hx)
  · have := W.add_mem (h x hx) (W.smul_mem lam hx)
    simpa using this
  · intro lam mu x hx
    have hle : (⨆ k : ℕ, LinearMap.ker ((T - lam • (1 : Module.End K V)) ^ k)) ≤
        (⨆ k : ℕ, LinearMap.ker ((T - lam • (1 : Module.End K V)) ^ k)).comap
          (T - mu • (1 : Module.End K V)) := by
      refine iSup_le fun k y hy => ?_
      refine Submodule.mem_iSup_of_mem k ?_
      rw [LinearMap.mem_ker] at hy ⊢
      rw [← mul_apply_eq_comp, ← ((hc lam mu).pow_right k).eq, mul_apply_eq_comp, hy, map_zero]
    exact hle hx
  · intro lam mu x hx
    rw [Submodule.mem_iInf] at hx ⊢
    intro k
    obtain ⟨y, rfl⟩ := hx k
    refine ⟨(T - mu • (1 : Module.End K V)) y, ?_⟩
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ((hc lam mu).pow_right k).eq]

section sqrt

open Polynomial in
lemma exists_sqrt_poly (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∃ p : K[X], (X ^ (n + 1) ∣ p ^ 2 - (1 + X)) ∧ X ∣ p - 1 := by
  induction n with
  | zero => exact ⟨1, ⟨-1, by ring⟩, by simp⟩
  | succ n ih =>
    obtain ⟨p, ⟨q, hq⟩, ⟨r, hr⟩⟩ := ih
    have hC : C (2⁻¹ : K) * 2 = 1 := by
      have : (2 : K[X]) = C 2 := (map_ofNat C 2).symm
      rw [this, ← C_mul, inv_mul_cancel₀ h2, C_1]
    refine ⟨p - C (2⁻¹ : K) * (X ^ (n + 1) * q),
      ⟨-(q * r) + C (2⁻¹ : K) ^ 2 * X ^ n * q ^ 2, ?_⟩, ⟨r - C (2⁻¹ : K) * X ^ n * q, ?_⟩⟩
    · linear_combination hq - (X ^ (n + 1) * q) * hr - (X ^ (n + 1) * q * p) * hC
    · linear_combination hr

/-- Axler 8.39: if `N` is nilpotent, then `1 + N` has a square root (in characteristic `≠ 2`, e.g.
over `ℝ` or `ℂ`); this holds in any algebra, in particular for operators. -/
@[kb "axler2024" "8.39, p. 337"]
theorem axler_8_39 {A : Type*} [Ring A] [Algebra K A] (h2 : (2 : K) ≠ 0) {N : A}
    (hN : IsNilpotent N) : ∃ S : A, S ^ 2 = 1 + N := by
  obtain ⟨k, hk⟩ := hN
  obtain ⟨p, ⟨q, hq⟩, -⟩ := exists_sqrt_poly K h2 k
  refine ⟨Polynomial.aeval N p, ?_⟩
  have : p ^ 2 = 1 + Polynomial.X + Polynomial.X ^ (k + 1) * q := by linear_combination hq
  rw [← map_pow, this]
  simp [pow_succ, hk]

end sqrt

universe v

section sqrt2

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- Core of Axler 8.41: an injective operator on a complex space has a square root, by induction
on the dimension, splitting off the generalized eigenspace of one eigenvalue (Fitting). -/
theorem exists_sqrt_of_injective :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ T : Module.End K V, Function.Injective T →
        ∃ S : Module.End K V, S * S = T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn T hT
  by_cases hV : Subsingleton V
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue T
  obtain ⟨x, hx⟩ := hlam.exists_hasEigenvector
  have hx0 : x ≠ 0 := hx.2
  have hTx : T x = lam • x := hx.apply_eq_smul
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    apply hx0
    apply hT
    rw [hTx]; simp
  set φ : Module.End K V := T - lam • (1 : Module.End K V) with hφ
  set n0 := finrank K V with hn0
  have hn0pos : 0 < n0 := Module.finrank_pos
  have hGR : IsCompl (LinearMap.ker (φ ^ n0)) (LinearMap.range (φ ^ n0)) :=
    isCompl_ker_pow_range_pow φ
  set G := LinearMap.ker (φ ^ n0) with hG
  set R := LinearMap.range (φ ^ n0) with hR
  have hcomm : Commute T (φ ^ n0) :=
    ((Commute.refl T).sub_right ((Commute.one_right T).smul_right lam)).pow_right n0
  have hxG : x ∈ G := by
    rw [hG, LinearMap.mem_ker]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0pos.ne'
    rw [hj, pow_succ, mul_apply_eq_comp]
    have : φ x = 0 := by rw [hφ]; simp [hTx]
    rw [this, map_zero]
  have hTG : ∀ y ∈ G, T y ∈ G := by
    intro y hy
    rw [hG, LinearMap.mem_ker] at hy ⊢
    rw [← mul_apply_eq_comp, ← hcomm.eq, mul_apply_eq_comp, hy, map_zero]
  have hTR : ∀ y ∈ R, T y ∈ R := by
    rintro _ ⟨z, rfl⟩
    exact ⟨T z, by rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hcomm.eq]⟩
  have hGpos : finrank K G ≠ 0 := by
    intro h
    rw [Submodule.finrank_eq_zero] at h
    rw [h] at hxG
    exact hx0 (by simpa using hxG)
  have hsum := Submodule.finrank_add_eq_of_isCompl hGR
  have hlt : finrank K R < n := by omega
  -- the part on `R`
  let TR : Module.End K R := T.restrict hTR
  have hTRinj : Function.Injective TR := fun a b hab => Subtype.ext (hT (congrArg Subtype.val hab))
  obtain ⟨S2, hS2⟩ := ih (finrank K R) hlt R rfl TR hTRinj
  -- the part on `G`
  let TG : Module.End K G := T.restrict hTG
  let NG : Module.End K G := TG - lam • 1
  have hNGpow : ∀ (k : ℕ) (y : G), (((NG ^ k) y : G) : V) = (φ ^ k) (y : V) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp, ← ih y]
      simp [NG, TG, hφ]
  have hNG : NG ^ n0 = 0 := by
    ext y
    rw [LinearMap.zero_apply]
    rw [hNGpow]
    simpa using LinearMap.mem_ker.mp y.2
  have hN' : IsNilpotent (lam⁻¹ • NG) := ⟨n0, by rw [smul_pow, hNG, smul_zero]⟩
  obtain ⟨R1, hR1⟩ := axler_8_39 (K := K) (two_ne_zero) hN'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq lam (by norm_num : 0 < 2)
  have hS1 : (c • R1) * (c • R1) = TG := by
    have h1 : R1 * R1 = 1 + lam⁻¹ • NG := by rw [← sq]; exact hR1
    have hcc : c * c = lam := by rw [← sq]; exact hc
    rw [smul_mul_smul_comm, h1, hcc, smul_add, smul_smul,
      mul_inv_cancel₀ hlam0, one_smul]
    simp [NG]
  let S : Module.End K V := LinearMap.ofIsCompl hGR (G.subtype ∘ₗ (c • R1)) (R.subtype ∘ₗ S2)
  refine ⟨S, ?_⟩
  apply LinearMap.ext_on_codisjoint hGR.codisjoint
  · intro y hy
    have h1 : S y = (((c • R1) ⟨y, hy⟩ : G) : V) :=
      LinearMap.ofIsCompl_left_apply hGR (⟨y, hy⟩ : G)
    have h2 : S (((c • R1) ⟨y, hy⟩ : G) : V) = ((((c • R1) * (c • R1)) ⟨y, hy⟩ : G) : V) :=
      LinearMap.ofIsCompl_left_apply hGR ((c • R1) ⟨y, hy⟩)
    rw [Module.End.mul_apply, h1, h2, hS1]
    rfl
  · intro y hy
    have h1 : S y = ((S2 ⟨y, hy⟩ : R) : V) :=
      LinearMap.ofIsCompl_right_apply hGR (⟨y, hy⟩ : R)
    have h2 : S ((S2 ⟨y, hy⟩ : R) : V) = (((S2 * S2) ⟨y, hy⟩ : R) : V) :=
      LinearMap.ofIsCompl_right_apply hGR (S2 ⟨y, hy⟩)
    rw [Module.End.mul_apply, h1, h2, hS2]
    rfl

/-- Axler 8.41: over `ℂ`, every invertible operator has a square root. -/
@[kb "axler2024" "8.41, p. 338"]
theorem axler_8_41 {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Module.End K V} (hT : IsUnit T) : ∃ S : Module.End K V, S ^ 2 = T := by
  have hinj : Function.Injective T := (Module.End.isUnit_iff T).mp hT |>.1
  obtain ⟨S, hS⟩ := exists_sqrt_of_injective _ V rfl T hinj
  exact ⟨S, by rw [sq]; exact hS⟩

end sqrt2

end UndergradKB.LinearAlgebra
