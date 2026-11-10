import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Triangular form of operators (Axler 5.39 - 5.47, Exercises 5C)

Matrices of an operator `T` with respect to a basis `b` are `LinearMap.toMatrix b b T`; "upper
triangular" is `Matrix.BlockTriangular id` (entry `M i j` vanishes for `j < i`).  The statements
about a basis indexed by an arbitrary finite linear order are special-cased to `Fin n` where the book
speaks of `v₁, …, vₙ`.
-/

open Module Polynomial

namespace UndergradKB.LinearAlgebra

universe u v

section Flags

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- Upper triangularity of the matrix of `T` is equivalent to `T v_k ∈ span (v_j, j ≤ k)` for
all `k`. -/
theorem blockTriangular_toMatrix_iff_apply_mem_span (b : Basis ι K V) (T : Module.End K V) :
    (LinearMap.toMatrix b b T).BlockTriangular id ↔
      ∀ k, T (b k) ∈ Submodule.span K (b '' Set.Iic k) := by
  classical
  simp only [Matrix.BlockTriangular, id, LinearMap.toMatrix_apply, Basis.mem_span_image,
    Finsupp.support_subset_iff, Set.mem_Iic]
  constructor
  · intro h k i hik
    exact h (not_le.mp hik)
  · intro h i j hij
    exact h j i (not_le.mpr hij)

/-- Lower triangularity of the matrix of `T` is equivalent to `T v_k ∈ span (v_j, k ≤ j)`. -/
theorem blockTriangular_toDual_toMatrix_iff_apply_mem_span (b : Basis ι K V)
    (T : Module.End K V) :
    (LinearMap.toMatrix b b T).BlockTriangular OrderDual.toDual ↔
      ∀ k, T (b k) ∈ Submodule.span K (b '' Set.Ici k) := by
  classical
  simp only [Matrix.BlockTriangular, LinearMap.toMatrix_apply, Basis.mem_span_image,
    Finsupp.support_subset_iff, Set.mem_Ici, OrderDual.toDual_lt_toDual]
  constructor
  · intro h k i hik
    exact h (not_le.mp hik)
  · intro h i j hij
    exact h j i (not_le.mpr hij)

/-- **Axler 5.39** (upper triangular case): for a basis `v`, the following are equivalent:
the matrix of `T` is upper triangular; each `span (v_1..v_k)` is `T`-invariant;
`T v_k ∈ span (v_1..v_k)` for each `k`. -/
@[kb "axler2024" "5.39, p. 174"]
theorem axler_5_39 (b : Basis ι K V) (T : Module.End K V) :
    List.TFAE [(LinearMap.toMatrix b b T).BlockTriangular id,
      ∀ k, (Submodule.span K (b '' Set.Iic k)).map T ≤ Submodule.span K (b '' Set.Iic k),
      ∀ k, T (b k) ∈ Submodule.span K (b '' Set.Iic k)] := by
  tfae_have 1 ↔ 3 := blockTriangular_toMatrix_iff_apply_mem_span b T
  tfae_have 2 → 3 := fun h k =>
    h k (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, Set.mem_Iic.mpr le_rfl, rfl⟩))
  tfae_have 3 → 2 := fun h k => by
    rw [Submodule.map_span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr hj)) (h j)
  tfae_finish

/-- **Axler Exercise 5C.10**: lower-triangular analogue of 5.39 (with `v_k, …, v_n`). -/
@[kb "axler2024" "Ex5C.10, p. 180"]
theorem axler_ex5C_10 (b : Basis ι K V) (T : Module.End K V) :
    List.TFAE [(LinearMap.toMatrix b b T).BlockTriangular OrderDual.toDual,
      ∀ k, (Submodule.span K (b '' Set.Ici k)).map T ≤ Submodule.span K (b '' Set.Ici k),
      ∀ k, T (b k) ∈ Submodule.span K (b '' Set.Ici k)] := by
  tfae_have 1 ↔ 3 := blockTriangular_toDual_toMatrix_iff_apply_mem_span b T
  tfae_have 2 → 3 := fun h k =>
    h k (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, Set.mem_Ici.mpr le_rfl, rfl⟩))
  tfae_have 3 → 2 := fun h k => by
    rw [Submodule.map_span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Ici_subset_Ici.mpr hj)) (h j)
  tfae_finish

end Flags

section MatrixAlgebra

variable {R : Type*} [Semiring R] {m : Type*} [LinearOrder m]

/-- **Axler Exercise 5C.2** (sum): the sum of upper triangular matrices is upper triangular and its
diagonal is the sum of the diagonals. -/
@[kb "axler2024" "Ex5C.2, p. 179"]
theorem axler_ex5C_2_add {A B : Matrix m m R} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) :
    (A + B).BlockTriangular id ∧ ∀ i, (A + B) i i = A i i + B i i :=
  ⟨hA.add hB, fun _ => rfl⟩

/-- **Axler Exercise 5C.2** (product): the product of upper triangular matrices is upper
triangular and its diagonal is the entrywise product of the diagonals. -/
@[kb "axler2024" "Ex5C.2, p. 179"]
theorem axler_ex5C_2_mul [Fintype m] {A B : Matrix m m R} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) :
    (A * B).BlockTriangular id ∧ ∀ i, (A * B) i i = A i i * B i i := by
  refine ⟨hA.mul hB, fun i => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hA (show id k < id i from h), zero_mul]
    · rw [hB (show id i < id k from h), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

end MatrixAlgebra

section Existence

variable {K : Type u} [Field K]

/-- If an operator on a nontrivial space is killed by a nonzero polynomial that splits, it has an
eigenvalue. -/
theorem exists_hasEigenvalue_of_aeval_eq_zero {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (T : Module.End K V) (p : K[X]) (hp : p ≠ 0)
    (hs : p.Splits) (h : aeval T p = 0) : ∃ μ, T.HasEigenvalue μ := by
  have hd : minpoly K T ∣ p := minpoly.dvd K T h
  have hs' := hs.of_dvd hp hd
  have hdeg : (minpoly K T).degree ≠ 0 :=
    (minpoly.degree_pos (Algebra.IsIntegral.isIntegral T)).ne'
  obtain ⟨μ, hμ⟩ := hs'.exists_eval_eq_zero hdeg
  exact ⟨μ, Module.End.hasEigenvalue_of_isRoot hμ⟩

/-- Core of the triangularization theorem: an operator annihilated by a nonzero split polynomial
has a basis `b` (indexed by `Fin n`) with `T (b k) ∈ span (b j, j ≤ k)`.  Induction on the
dimension, splitting off an eigenvector `y` and a complement `N` of its line; the induced operator
`π ∘ T` on `N` is again annihilated by `p`. -/
theorem exists_flag_basis : ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], finrank K V = n → ∀ (T : Module.End K V) (p : K[X]), p ≠ 0 →
      p.Splits → aeval T p = 0 →
      ∃ b : Basis (Fin n) K V, ∀ k, T (b k) ∈ Submodule.span K (b '' Set.Iic k) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ hn T p _ _ _
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact ⟨Basis.empty V, fun k => k.elim0⟩
  | succ n ih =>
    intro V _ _ _ hn T p hp hs hT
    have : Nontrivial V := Module.finrank_pos_iff (R := K).mp (by omega)
    obtain ⟨μ, hμ⟩ := exists_hasEigenvalue_of_aeval_eq_zero T p hp hs hT
    obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
    obtain ⟨N, hN⟩ := Submodule.exists_isCompl (K ∙ y)
    have hc : IsCompl N (K ∙ y) := hN.symm
    have hfin : finrank K N = n := by
      have := Submodule.finrank_add_eq_of_isCompl hN
      rw [finrank_span_singleton hy.2] at this
      omega
    let π : V →ₗ[K] N := Submodule.projectionOnto N (K ∙ y) hc
    let T' : Module.End K N := π ∘ₗ T ∘ₗ N.subtype
    have hπN : ∀ x : N, π x = x := fun x => Submodule.projectionOnto_apply_left hc x
    have hker : LinearMap.ker π = K ∙ y := Submodule.ker_projectionOnto hc
    have hdiff : ∀ v, v - (π v : V) ∈ K ∙ y := by
      intro v
      have h0 : π (v - (π v : V)) = 0 := by rw [map_sub, hπN (π v), sub_self]
      rw [← hker]
      exact LinearMap.mem_ker.mpr h0
    have hTy : T y = μ • y := hy.apply_eq_smul
    have hTspan : ∀ v ∈ K ∙ y, T v ∈ K ∙ y := by
      intro v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, hTy]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
    have hπy : ∀ v ∈ K ∙ y, π v = 0 := fun v hv =>
      LinearMap.mem_ker.mp (by rw [hker]; exact hv)
    have key : ∀ v, π (T v) = π (T (π v : V)) := by
      intro v
      have : π (T v - T (π v : V)) = 0 := hπy _ (by rw [← map_sub]; exact hTspan _ (hdiff v))
      rwa [map_sub, sub_eq_zero] at this
    have hpow : ∀ (k : ℕ) (x : N), (T' ^ k) x = π ((T ^ k) (x : V)) := by
      intro k
      induction k with
      | zero => intro x; simp [hπN]
      | succ k ihk =>
        intro x
        rw [pow_succ', mul_apply_eq_comp, ihk, pow_succ', mul_apply_eq_comp]
        show π (T ((π ((T ^ k) (x : V)) : N) : V)) = _
        rw [← key]
    have haeval : aeval T' p = 0 := by
      ext x
      have : ∀ q : K[X], aeval T' q x = π (aeval T q (x : V)) := by
        intro q
        rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply,
          map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hpow]
      rw [this, hT]
      simp
    obtain ⟨c, hc'⟩ := ih N hfin T' p hp hs haeval
    have hli : ∀ (a : K), ∀ x ∈ N, a • y + x = 0 → a = 0 := by
      intro a x hx hax
      have h1 : a • y = 0 := by
        refine Submodule.disjoint_def.mp hN.disjoint _
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)) ?_
        rw [eq_neg_of_add_eq_zero_left hax]
        exact N.neg_mem hx
      exact (smul_eq_zero.mp h1).resolve_right hy.2
    have hsp : ∀ z : V, ∃ a : K, z + a • y ∈ N := by
      intro z
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hdiff z)
      refine ⟨-a, ?_⟩
      rw [neg_smul, ha]
      simp
    let b : Basis (Fin (n + 1)) K V := Basis.mkFinCons y c hli hsp
    have hb0 : b 0 = y := by simp [b]
    have hbs : ∀ i, b i.succ = (c i : V) := by intro i; simp [b]
    refine ⟨b, fun k => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [hb0, hTy]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, hb0⟩)
    · set S := Submodule.span K (b '' Set.Iic i.succ) with hS
      have hyS : y ∈ S :=
        Submodule.subset_span ⟨0, Set.mem_Iic.mpr (Fin.zero_le _), hb0⟩
      have hci : ∀ j ∈ Set.Iic i, (c j : V) ∈ S := fun j hj =>
        Submodule.subset_span ⟨j.succ, Set.mem_Iic.mpr (Fin.succ_le_succ_iff.mpr hj), hbs j⟩
      have h1 : ((T' (c i) : N) : V) ∈ S := by
        have h := Submodule.mem_map_of_mem (f := N.subtype) (hc' i)
        rw [Submodule.map_span] at h
        refine (Submodule.span_le.mpr ?_) h
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact hci j hj
      have h2 : T (c i : V) - ((T' (c i) : N) : V) ∈ S := by
        have := hdiff (T (c i : V))
        exact (Submodule.span_singleton_le_iff_mem y S |>.mpr hyS) this
      rw [hbs]
      have := S.add_mem h1 h2
      simpa using this

end Existence

section Theorems

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- The characteristic polynomial of an operator with an upper triangular matrix is the product of
`X - (diagonal entry)`. -/
theorem charpoly_eq_prod_of_blockTriangular (b : Basis ι K V) (T : Module.End K V)
    (h : (LinearMap.toMatrix b b T).BlockTriangular id) :
    T.charpoly = ∏ i, (X - C ((LinearMap.toMatrix b b T) i i)) := by
  rw [← LinearMap.charpoly_toMatrix T b]
  exact Matrix.charpoly_of_isUpperTriangular _ h

/-- **Axler 5.40**: if `T` has an upper triangular matrix with diagonal `l₁, …, lₙ`, then
`(T - l₁ I) ⋯ (T - lₙ I) = 0` (the factors commute, so we write the product as a polynomial
evaluated at `T`). -/
@[kb "axler2024" "5.40, p. 174"]
theorem axler_5_40 (b : Basis ι K V) (T : Module.End K V)
    (h : (LinearMap.toMatrix b b T).BlockTriangular id) :
    aeval T (∏ i, (X - C ((LinearMap.toMatrix b b T) i i))) = 0 := by
  rw [← charpoly_eq_prod_of_blockTriangular b T h]
  exact LinearMap.aeval_self_charpoly T

/-- **Axler 5.41**: when the matrix of `T` is upper triangular, its eigenvalues are exactly the
diagonal entries. -/
@[kb "axler2024" "5.41, p. 175"]
theorem axler_5_41 (b : Basis ι K V) (T : Module.End K V)
    (h : (LinearMap.toMatrix b b T).BlockTriangular id) (μ : K) :
    T.HasEigenvalue μ ↔ ∃ i, (LinearMap.toMatrix b b T) i i = μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_eq_prod_of_blockTriangular b T h,
    Polynomial.IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C, sub_eq_zero]
  exact exists_congr fun i => eq_comm

/-- **Axler 5.44**: `T` has an upper triangular matrix in some basis if and only if its minimal
polynomial is a product of linear factors over `K` (it splits). -/
@[kb "axler2024" "5.44, p. 177"]
theorem axler_5_44 (T : Module.End K V) :
    (∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.toMatrix b b T).BlockTriangular id) ↔
      (minpoly K T).Splits := by
  constructor
  · rintro ⟨b, hb⟩
    have hs : T.charpoly.Splits := by
      rw [charpoly_eq_prod_of_blockTriangular b T hb]
      exact Splits.prod fun i _ => Splits.X_sub_C _
    exact hs.of_dvd T.charpoly_monic.ne_zero (LinearMap.minpoly_dvd_charpoly T)
  · intro hs
    obtain ⟨b, hb⟩ := exists_flag_basis (finrank K V) V rfl T (minpoly K T)
      (minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)) hs (minpoly.aeval K T)
    exact ⟨b, (blockTriangular_toMatrix_iff_apply_mem_span b T).2 hb⟩

/-- **Axler 5.47**: over an algebraically closed field (in particular `ℂ`), every operator on a
finite-dimensional space has an upper triangular matrix in some basis. -/
@[kb "axler2024" "5.47, p. 178"]
theorem axler_5_47 [IsAlgClosed K] (T : Module.End K V) :
    ∃ b : Basis (Fin (finrank K V)) K V, (LinearMap.toMatrix b b T).BlockTriangular id :=
  (axler_5_44 T).2 (IsAlgClosed.splits _)

end Theorems

section Commuting

variable {K : Type u} [Field K] [IsAlgClosed K]

private theorem commute_restrict' {V : Type v} [AddCommGroup V] [Module K V]
    {T₁ T₂ : Module.End K V} (h : Commute T₁ T₂)
    (U : Submodule K V) (h₁ : ∀ x ∈ U, T₁ x ∈ U) (h₂ : ∀ x ∈ U, T₂ x ∈ U) :
    Commute (T₁.restrict h₁) (T₂.restrict h₂) := by
  show T₁.restrict h₁ * T₂.restrict h₂ = T₂.restrict h₂ * T₁.restrict h₁
  ext x
  have := congrArg (fun f => f (x : V)) h.eq
  simpa using this

/-- (Private copy of the common eigenvector theorem of `Commuting.lean`; each file is
self-contained.) -/
private theorem exists_common_eigenvector' {ι : Type*} :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → Nontrivial V → ∀ (T : ι → Module.End K V),
      (∀ i j, Commute (T i) (T j)) → ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : K, T i v = μ • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn hV T hc
  by_cases hsc : ∀ i, ∃ c : K, T i = c • (1 : Module.End K V)
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun i => ?_⟩
    obtain ⟨c, hci⟩ := hsc i
    exact ⟨c, by rw [hci]; simp⟩
  · have hex : ∃ j, ∀ c : K, T j ≠ c • (1 : Module.End K V) := by
      by_contra hcon
      apply hsc
      intro i
      by_contra hi
      exact hcon ⟨i, fun c hc => hi ⟨c, hc⟩⟩
    obtain ⟨j, hj⟩ := hex
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (T j)
    have hlt : finrank K ((T j).eigenspace l) < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hj l
      ext x
      have : x ∈ (T j).eigenspace l := by rw [htop]; trivial
      simpa using Module.End.mem_eigenspace_iff.mp this
    have hinv : ∀ i, ∀ x ∈ (T j).eigenspace l, T i x ∈ (T j).eigenspace l := by
      intro i x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have := congrArg (fun f => f x) (hc j i).eq
      simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
      rw [this, hx, map_smul]
    have hnt : Nontrivial ((T j).eigenspace l) := Submodule.nontrivial_iff_ne_bot.mpr hl
    obtain ⟨v, hv0, hv⟩ := ih _ hlt ((T j).eigenspace l) rfl hnt
      (fun i => (T i).restrict (hinv i)) (fun i i' => commute_restrict' (hc i i') _ _ _)
    refine ⟨v, fun h => hv0 (Subtype.ext h), fun i => ?_⟩
    obtain ⟨μ, hμ⟩ := hv i
    exact ⟨μ, by simpa using congrArg Subtype.val hμ⟩

/-- Simultaneous version of `exists_flag_basis` for a commuting family over an algebraically
closed field: one basis whose flag is invariant under every member. -/
theorem exists_flag_basis_family {ι : Type*} : ∀ (n : ℕ) (V : Type v) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V], finrank K V = n → ∀ (T : ι → Module.End K V),
    (∀ i j, Commute (T i) (T j)) →
      ∃ b : Basis (Fin n) K V, ∀ i k, T i (b k) ∈ Submodule.span K (b '' Set.Iic k) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ hn T _
    have : Subsingleton V := Module.finrank_zero_iff.mp hn
    exact ⟨Basis.empty V, fun i k => k.elim0⟩
  | succ n ih =>
    intro V _ _ _ hn T hc
    have : Nontrivial V := Module.finrank_pos_iff (R := K).mp (by omega)
    obtain ⟨y, hy0, hy⟩ := exists_common_eigenvector' (finrank K V) V rfl ‹_› T hc
    obtain ⟨N, hN⟩ := Submodule.exists_isCompl (K ∙ y)
    have hcN : IsCompl N (K ∙ y) := hN.symm
    have hfin : finrank K N = n := by
      have := Submodule.finrank_add_eq_of_isCompl hN
      rw [finrank_span_singleton hy0] at this
      omega
    let π : V →ₗ[K] N := Submodule.projectionOnto N (K ∙ y) hcN
    let T' : ι → Module.End K N := fun i => π ∘ₗ T i ∘ₗ N.subtype
    have hπN : ∀ x : N, π x = x := fun x => Submodule.projectionOnto_apply_left hcN x
    have hker : LinearMap.ker π = K ∙ y := Submodule.ker_projectionOnto hcN
    have hdiff : ∀ v, v - (π v : V) ∈ K ∙ y := by
      intro v
      have h0 : π (v - (π v : V)) = 0 := by rw [map_sub, hπN (π v), sub_self]
      rw [← hker]
      exact LinearMap.mem_ker.mpr h0
    have hTspan : ∀ i, ∀ v ∈ K ∙ y, T i v ∈ K ∙ y := by
      intro i v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      obtain ⟨μ, hμ⟩ := hy i
      rw [map_smul, hμ]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
    have hπy : ∀ v ∈ K ∙ y, π v = 0 := fun v hv =>
      LinearMap.mem_ker.mp (by rw [hker]; exact hv)
    have key : ∀ i v, π (T i v) = π (T i (π v : V)) := by
      intro i v
      have : π (T i v - T i (π v : V)) = 0 :=
        hπy _ (by rw [← map_sub]; exact hTspan i _ (hdiff v))
      rwa [map_sub, sub_eq_zero] at this
    have hcomm : ∀ i j, Commute (T' i) (T' j) := by
      intro i j
      show T' i * T' j = T' j * T' i
      ext x
      have h1 : π (T i (T j (x : V))) = π (T j (T i (x : V))) := by
        have := congrArg (fun f => f (x : V)) (hc i j).eq
        simp only [mul_apply_eq_comp] at this
        rw [this]
      have e1 := key i (T j (x : V))
      have e2 := key j (T i (x : V))
      simp only [T', mul_apply_eq_comp, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← e1, ← e2, h1]
    obtain ⟨c, hc'⟩ := ih N hfin T' hcomm
    have hli : ∀ (a : K), ∀ x ∈ N, a • y + x = 0 → a = 0 := by
      intro a x hx hax
      have h1 : a • y = 0 := by
        refine Submodule.disjoint_def.mp hN.disjoint _
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)) ?_
        rw [eq_neg_of_add_eq_zero_left hax]
        exact N.neg_mem hx
      exact (smul_eq_zero.mp h1).resolve_right hy0
    have hsp : ∀ z : V, ∃ a : K, z + a • y ∈ N := by
      intro z
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hdiff z)
      refine ⟨-a, ?_⟩
      rw [neg_smul, ha]
      simp
    let b : Basis (Fin (n + 1)) K V := Basis.mkFinCons y c hli hsp
    have hb0 : b 0 = y := by simp [b]
    have hbs : ∀ i, b i.succ = (c i : V) := by intro i; simp [b]
    refine ⟨b, fun i k => ?_⟩
    refine Fin.cases ?_ (fun m => ?_) k
    · obtain ⟨μ, hμ⟩ := hy i
      rw [hb0, hμ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, hb0⟩)
    · set S := Submodule.span K (b '' Set.Iic m.succ) with hS
      have hyS : y ∈ S :=
        Submodule.subset_span ⟨0, Set.mem_Iic.mpr (Fin.zero_le _), hb0⟩
      have hci : ∀ j ∈ Set.Iic m, (c j : V) ∈ S := fun j hj =>
        Submodule.subset_span ⟨j.succ, Set.mem_Iic.mpr (Fin.succ_le_succ_iff.mpr hj), hbs j⟩
      have h1 : ((T' i (c m) : N) : V) ∈ S := by
        have h := Submodule.mem_map_of_mem (f := N.subtype) (hc' i m)
        rw [Submodule.map_span] at h
        refine (Submodule.span_le.mpr ?_) h
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact hci j hj
      have h2 : T i (c m : V) - ((T' i (c m) : N) : V) ∈ S := by
        have := hdiff (T i (c m : V))
        exact (Submodule.span_singleton_le_iff_mem y S |>.mpr hyS) this
      rw [hbs]
      have := S.add_mem h1 h2
      simpa using this

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Axler 5.80** (in the generality of Exercise 5E.9): commuting operators (any family) on a
finite-dimensional space over an algebraically closed field (e.g. `ℂ`) are simultaneously upper
triangularizable: there is one basis in which all their matrices are upper triangular. -/
@[kb "axler2024" "5.80, p. 196"]
theorem axler_5_80 {ι : Type*} (T : ι → Module.End K V) (hc : ∀ i j, Commute (T i) (T j)) :
    ∃ b : Basis (Fin (finrank K V)) K V, ∀ i, (LinearMap.toMatrix b b (T i)).BlockTriangular id := by
  obtain ⟨b, hb⟩ := exists_flag_basis_family (finrank K V) V rfl T hc
  exact ⟨b, fun i => (blockTriangular_toMatrix_iff_apply_mem_span b (T i)).2 (hb i)⟩

/-- **Axler Exercise 5E.9**: a commuting family of operators on a nonzero finite-dimensional
space over an algebraically closed field has a common eigenvector, and the family is
simultaneously upper triangularizable. -/
@[kb "axler2024" "Ex5E.9, p. 198"]
theorem axler_ex5E_9 [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hc : ∀ i j, Commute (T i) (T j)) :
    (∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : K, T i v = μ • v) ∧
      ∃ b : Basis (Fin (finrank K V)) K V,
        ∀ i, (LinearMap.toMatrix b b (T i)).BlockTriangular id :=
  ⟨exists_common_eigenvector' (finrank K V) V rfl ‹_› T hc, axler_5_80 T hc⟩

end Commuting

end UndergradKB.LinearAlgebra
