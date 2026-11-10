import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fintype
import UndergradKB.Common.Attr

/-! # Linear systems over a field, matrix equivalence and the rank normal form

Hefferon, Chapter One Section I.3 (solution sets as particular solution plus homogeneous solutions) and
Chapter Three Section V.2 (matrix equivalence and the rank normal form), over an arbitrary field `K`. -/

namespace UndergradKB.LinearAlgebra

open Matrix Module

variable {K : Type*} [Field K] {m n : ℕ}

/-! ### Homogeneous systems and the shape of solution sets -/

/-- The zero vector solves every homogeneous system, and the solution set of the homogeneous system with
coefficient matrix `A` is the kernel of `x ↦ A x`. -/
@[kb "hefferon2020" "One.I.3.2, p. 34"]
theorem hefferon_One_I_3_2 (A : Matrix (Fin m) (Fin n) K) :
    A *ᵥ (0 : Fin n → K) = 0 ∧
      {x | A *ᵥ x = 0} = (LinearMap.ker A.mulVecLin : Set (Fin n → K)) := by
  refine ⟨Matrix.mulVec_zero A, ?_⟩
  ext x
  simp [LinearMap.mem_ker]

/-- A linear system has no solution, exactly one solution, or infinitely many (over an infinite field). -/
@[kb "hefferon2020" "One.I.3.10, p. 39"]
theorem hefferon_One_I_3_10 [Infinite K] (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    {x | A *ᵥ x = b} = ∅ ∨ (∃ p, {x | A *ᵥ x = b} = {p}) ∨ {x | A *ᵥ x = b}.Infinite := by
  by_cases h : ∃ p, A *ᵥ p = b
  · obtain ⟨p, hp⟩ := h
    by_cases hk : ∀ v, A *ᵥ v = 0 → v = 0
    · right; left
      refine ⟨p, ?_⟩
      ext x
      constructor
      · intro hx
        have : A *ᵥ (x - p) = 0 := by
          rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr (hx.trans hp.symm)
        exact sub_eq_zero.mp (hk _ this)
      · intro hx
        have : x = p := hx
        rw [this]; exact hp
    · right; right
      push Not at hk
      obtain ⟨v, hv, hv0⟩ := hk
      refine Set.infinite_of_injective_forall_mem (f := fun t : K => p + t • v) ?_ ?_
      · intro s t hst
        have : s • v = t • v := add_left_cancel hst
        exact smul_left_injective K hv0 this
      · intro t
        show A *ᵥ (p + t • v) = b
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hv, smul_zero, add_zero, hp]
  · left
    ext x
    constructor
    · intro hx; exact absurd ⟨x, hx⟩ h
    · intro hx; exact hx.elim

/-- A square matrix is nonsingular (its homogeneous system has only the zero solution) exactly when it is
invertible, equivalently when its determinant is nonzero. -/
@[kb "hefferon2020" "One.I.3.11, p. 40"]
theorem hefferon_One_I_3_11 (A : Matrix (Fin n) (Fin n) K) :
    ((∀ x, A *ᵥ x = 0 → x = 0) ↔ IsUnit A) ∧ (IsUnit A ↔ A.det ≠ 0) := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    constructor
    · intro h x y hxy
      have : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
      exact sub_eq_zero.mp (h _ this)
    · intro h x hx
      exact h (by rw [hx, Matrix.mulVec_zero])
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-! ### Matrix equivalence -/

/-- Hefferon's matrix equivalence: `H'` is obtained from `H` by multiplying with nonsingular matrices on both
sides. -/
def MatrixEquivalent (H H' : Matrix (Fin m) (Fin n) K) : Prop :=
  ∃ (P : Matrix (Fin m) (Fin m) K) (Q : Matrix (Fin n) (Fin n) K), IsUnit P ∧ IsUnit Q ∧
    H' = P * H * Q

theorem MatrixEquivalent.refl (H : Matrix (Fin m) (Fin n) K) : MatrixEquivalent H H :=
  ⟨1, 1, isUnit_one, isUnit_one, by simp⟩

theorem MatrixEquivalent.symm {H H' : Matrix (Fin m) (Fin n) K} (h : MatrixEquivalent H H') :
    MatrixEquivalent H' H := by
  obtain ⟨P, Q, ⟨u, rfl⟩, ⟨v, rfl⟩, rfl⟩ := h
  refine ⟨↑u⁻¹, ↑v⁻¹, (u⁻¹).isUnit, (v⁻¹).isUnit, ?_⟩
  have e1 : ∀ X : Matrix (Fin m) (Fin n) K,
      (↑u⁻¹ : Matrix (Fin m) (Fin m) K) * ((↑u : Matrix (Fin m) (Fin m) K) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin m) (Fin n) K,
      X * (↑v : Matrix (Fin n) (Fin n) K) * (↑v⁻¹ : Matrix (Fin n) (Fin n) K) = X := fun X => by
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_assoc (↑u : Matrix (Fin m) (Fin m) K) H, e1, e2]

theorem MatrixEquivalent.trans {H H' H'' : Matrix (Fin m) (Fin n) K} (h : MatrixEquivalent H H')
    (h' : MatrixEquivalent H' H'') : MatrixEquivalent H H'' := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  obtain ⟨P', Q', hP', hQ', rfl⟩ := h'
  exact ⟨P' * P, Q * Q', hP'.mul hP, hQ.mul hQ', by simp [Matrix.mul_assoc]⟩

/-- Matrix equivalence is an equivalence relation on matrices of a given size. -/
@[kb "hefferon2020" "Three.V.2.4, p. 280"]
theorem hefferon_Three_V_2_4 :
    Equivalence (fun H H' : Matrix (Fin m) (Fin n) K => MatrixEquivalent H H') :=
  ⟨MatrixEquivalent.refl, MatrixEquivalent.symm, MatrixEquivalent.trans⟩

theorem MatrixEquivalent.rank_eq {H H' : Matrix (Fin m) (Fin n) K} (h : MatrixEquivalent H H') :
    H.rank = H'.rank := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Q _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ),
    Matrix.rank_mul_eq_right_of_isUnit_det P _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]

/-- Similar matrices are matrix equivalent, but the identity matrix and any invertible matrix other than the
identity are equivalent without being similar (such matrices exist as soon as `2 ≤ n`). -/
@[kb "hefferon2020" "Five.II.1.equiv, p. 415"]
theorem hefferon_Five_II_1_equiv :
    (∀ H H' : Matrix (Fin n) (Fin n) K,
      (∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
        H' = (P : Matrix (Fin n) (Fin n) K) * H * ((P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K)) → MatrixEquivalent H H') ∧
    (∀ M : Matrix (Fin n) (Fin n) K, IsUnit M → M ≠ 1 →
      MatrixEquivalent 1 M ∧ ¬ ∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
        M = (P : Matrix (Fin n) (Fin n) K) * 1 * ((P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) :
          Matrix (Fin n) (Fin n) K)) ∧
    (2 ≤ n → ∃ M : Matrix (Fin n) (Fin n) K, IsUnit M ∧ M ≠ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro H H' ⟨P, rfl⟩
    exact ⟨P, ↑P⁻¹, P.isUnit, (P⁻¹).isUnit, rfl⟩
  · intro M hM hne
    refine ⟨⟨M, 1, hM, isUnit_one, by simp⟩, ?_⟩
    rintro ⟨P, hP⟩
    apply hne
    rw [hP, Matrix.mul_one, Units.mul_inv]
  · intro hn
    refine ⟨Matrix.transvection (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ 1, ?_, ?_⟩
    · exact (Matrix.GeneralLinearGroup.transvection (R := K) _ _ (by simp [Fin.ext_iff]) 1).isUnit
    · intro h
      have := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
      simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, Fin.ext_iff] at this

/-! ### Rank normal form -/

theorem exists_basis_extending {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {m r : ℕ} (hm : finrank K W = m) (w : Fin r → W) (hw : LinearIndependent K w)
    (g : Fin r → Fin m) (hg : Function.Injective g) :
    ∃ D : Basis (Fin m) K W, ∀ i, D (g i) = w i := by
  classical
  have hs : LinearIndepOn K id (Set.range w) := hw.linearIndepOn_id
  let b := Basis.extend hs
  have hsub : Set.range w ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend _
  have : Finite (hs.extend (Set.subset_univ (Set.range w))) := Module.Finite.finite_basis b
  have := Fintype.ofFinite (hs.extend (Set.subset_univ (Set.range w)))
  have hcard : Fintype.card (hs.extend (Set.subset_univ (Set.range w))) = m := by
    rw [← hm, finrank_eq_card_basis b]
  let eE := Fintype.equivFinOfCardEq hcard
  let f1 : Fin r → Fin m := fun i => eE ⟨w i, hsub ⟨i, rfl⟩⟩
  have hf1 : Function.Injective f1 := by
    intro i j h
    have := eE.injective h
    exact hw.injective (congrArg Subtype.val this)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f1 g hf1 hg
  refine ⟨b.reindex (eE.trans π), fun i => ?_⟩
  rw [Basis.reindex_apply]
  have h1 : (eE.trans π).symm (g i) = eE.symm (f1 i) := by
    simp only [Equiv.symm_trans_apply]
    rw [← hπ i]; simp
  rw [h1]
  simp [b, f1]

/-- Every linear map of rank `r` between finite-dimensional spaces is a coordinate projection: there are
bases `B` of the domain and `D` of the codomain such that `B i` goes to `D i` for the first `r` indices and
to `0` for the rest. -/
theorem exists_adapted_bases {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {m n : ℕ}
    (hn : finrank K V = n) (hm : finrank K W = m) (f : V →ₗ[K] W) :
    ∃ (B : Basis (Fin n) K V) (D : Basis (Fin m) K W),
      (∀ (i : Fin n) (j : Fin m), (i : ℕ) = j → (i : ℕ) < finrank K (LinearMap.range f) →
        f (B i) = D j) ∧
      (∀ i : Fin n, finrank K (LinearMap.range f) ≤ i → f (B i) = 0) := by
  classical
  set r := finrank K (LinearMap.range f) with hr
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hn] at hrn
  have hrm : r ≤ m := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [hm] at this
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hCn := Submodule.finrank_add_eq_of_isCompl hC.symm
  rw [hn] at hCn
  have hCr : finrank K C = r := by omega
  have hKn : finrank K (LinearMap.ker f) = n - r := by omega
  have hrn' : r ≤ n := by omega
  let bC := Module.finBasisOfFinrankEq K C hCr
  let bK := Module.finBasisOfFinrankEq K (LinearMap.ker f) hKn
  let e := Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hC.symm
  let Bd : Basis (Fin r ⊕ Fin (n - r)) K V := (bC.prod bK).map e
  have hBl : ∀ a, Bd (Sum.inl a) = (bC a : V) := by
    intro a; simp [Bd, e]
  have hBr : ∀ b, Bd (Sum.inr b) = (bK b : V) := by
    intro b; simp [Bd, e]
  have hinj : Function.Injective (f.domRestrict C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (x : V) ∈ LinearMap.ker f := hx
    have h2 : (x : V) ∈ C := x.2
    have := (Submodule.disjoint_def.mp hC.disjoint) _ h1 h2
    exact Subtype.ext this
  have hw : LinearIndependent K (fun a : Fin r => f (bC a)) :=
    bC.linearIndependent.map' (f.domRestrict C) (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨D, hD⟩ := exists_basis_extending hm (fun a : Fin r => f (bC a)) hw
    (Fin.castLE hrm) (Fin.castLE_injective _)
  let edom : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have hB : ∀ s, (Bd.reindex edom) (edom s) = Bd s := by
    intro s; simp
  refine ⟨Bd.reindex edom, D, ?_, ?_⟩
  · intro i j hij hi
    obtain ⟨s, rfl⟩ := edom.surjective i
    rcases s with a | b
    · rw [hB, hBl]
      have : j = Fin.castLE hrm a := by
        apply Fin.ext
        rw [← hij]; simp [edom]
      rw [this, hD a]
    · exfalso
      have : ((edom (Sum.inr b) : Fin n) : ℕ) = r + b := by simp [edom]
      omega
  · intro i hi
    obtain ⟨s, rfl⟩ := edom.surjective i
    rcases s with a | b
    · exfalso
      have : ((edom (Sum.inl a) : Fin n) : ℕ) = a := by simp [edom]
      have := a.2
      omega
    · rw [hB, hBr]
      exact (bK b).2

/-- The `m × n` matrix with ones in the first `r` diagonal positions and zeros elsewhere. -/
def rankNormalForm (m n r : ℕ) : Matrix (Fin m) (Fin n) K :=
  Matrix.of fun i j => if (i : ℕ) = j ∧ (i : ℕ) < r then 1 else 0

theorem toMatrix_std_mulVecLin (M : Matrix (Fin m) (Fin n) K) :
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m)) M.mulVecLin = M := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.mulVec_single_one]

theorem isUnit_toMatrix (b b' : Basis (Fin m) K (Fin m → K)) : IsUnit (b.toMatrix b') := by
  have := Basis.invertibleToMatrix b b'
  exact isUnit_of_invertible _

/-- Rank normal form: a matrix of rank `r` is matrix equivalent to the matrix with `r` ones on the leading
diagonal and zeros elsewhere. -/
@[kb "hefferon2020" "Three.V.2.7, p. 281"]
theorem hefferon_Three_V_2_7 (M : Matrix (Fin m) (Fin n) K) :
    MatrixEquivalent M (rankNormalForm m n M.rank) := by
  obtain ⟨B, D, h1, h2⟩ :=
    exists_adapted_bases (Module.finrank_fin_fun K) (Module.finrank_fin_fun K) M.mulVecLin
  have hrank : finrank K (LinearMap.range M.mulVecLin) = M.rank := rfl
  rw [hrank] at h1 h2
  refine ⟨D.toMatrix (Pi.basisFun K (Fin m)), (Pi.basisFun K (Fin n)).toMatrix B,
    isUnit_toMatrix _ _, isUnit_toMatrix _ _, ?_⟩
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B (Pi.basisFun K (Fin n)) D
    (Pi.basisFun K (Fin m)) M.mulVecLin
  rw [toMatrix_std_mulVecLin] at key
  rw [key]
  ext i j
  rw [LinearMap.toMatrix_apply]
  by_cases hj : (j : ℕ) < M.rank
  · have hjm : (j : ℕ) < m := lt_of_lt_of_le hj (by
      have := Submodule.finrank_le (LinearMap.range M.mulVecLin)
      rw [Module.finrank_fin_fun] at this
      exact this)
    rw [h1 j ⟨j, hjm⟩ rfl hj]
    simp only [rankNormalForm, Matrix.of_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases hij : (i : ℕ) = j
    · have : (⟨j, hjm⟩ : Fin m) = i := Fin.ext hij.symm
      simp [this, hij, hj]
    · have : (⟨j, hjm⟩ : Fin m) ≠ i := fun h => hij (by rw [← h])
      simp [this, hij]
  · rw [h2 j (not_lt.mp hj)]
    simp only [rankNormalForm, Matrix.of_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with h
    · exact absurd h.2 (by rw [h.1]; exact hj)
    · rfl

/-- Matrix equivalence is classified by rank: two matrices of the same size are matrix equivalent exactly when
they have the same rank. -/
@[kb "hefferon2020" "Three.V.2.9, p. 282"]
theorem hefferon_Three_V_2_9 (H H' : Matrix (Fin m) (Fin n) K) :
    MatrixEquivalent H H' ↔ H.rank = H'.rank := by
  refine ⟨fun h => h.rank_eq, fun h => ?_⟩
  have h1 := hefferon_Three_V_2_7 H
  have h2 := hefferon_Three_V_2_7 H'
  rw [h] at h1
  exact h1.trans h2.symm

/-- Every linear map of rank `k` between finite-dimensional spaces has, in suitable bases, the matrix that
sends the first `k` basis vectors of the domain to those of the codomain and the rest to zero. -/
@[kb "hefferon2020" "Three.V.2.u1, p. 282"]
theorem hefferon_Three_V_2_u1 {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {m n : ℕ}
    (hn : finrank K V = n) (hm : finrank K W = m) (f : V →ₗ[K] W) :
    ∃ (B : Basis (Fin n) K V) (D : Basis (Fin m) K W),
      (∀ (i : Fin n) (j : Fin m), (i : ℕ) = j → (i : ℕ) < finrank K (LinearMap.range f) →
        f (B i) = D j) ∧
      (∀ i : Fin n, finrank K (LinearMap.range f) ≤ i → f (B i) = 0) :=
  exists_adapted_bases hn hm f

theorem toLinearEquiv'_apply_eq {k : ℕ} (Q : Matrix (Fin k) (Fin k) K) (h : Invertible Q)
    (v : Fin k → K) : Q.toLinearEquiv' h v = Q *ᵥ v := by
  have := LinearMap.congr_fun (Matrix.toLinearEquiv'_apply Q h) v
  exact this.trans (Matrix.toLin'_apply Q v)

/-- Matrix equivalent matrices represent one linear map with respect to suitable pairs of bases. -/
@[kb "hefferon2020" "Three.V.2.5, p. 280"]
theorem hefferon_Three_V_2_5 {H H' : Matrix (Fin m) (Fin n) K} (h : MatrixEquivalent H H') :
    ∃ (f : (Fin n → K) →ₗ[K] (Fin m → K)) (B B' : Basis (Fin n) K (Fin n → K))
      (D D' : Basis (Fin m) K (Fin m → K)),
      LinearMap.toMatrix B D f = H ∧ LinearMap.toMatrix B' D' f = H' := by
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  obtain ⟨hPi⟩ := hP.nonempty_invertible
  obtain ⟨hQi⟩ := hQ.nonempty_invertible
  let B' := (Pi.basisFun K (Fin n)).map (Q.toLinearEquiv' hQi)
  let D' := (Pi.basisFun K (Fin m)).map ((⅟P : Matrix (Fin m) (Fin m) K).toLinearEquiv' invertibleInvOf)
  refine ⟨H.mulVecLin, Pi.basisFun K (Fin n), B', Pi.basisFun K (Fin m), D',
    toMatrix_std_mulVecLin H, ?_⟩
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix B' (Pi.basisFun K (Fin n)) D'
    (Pi.basisFun K (Fin m)) H.mulVecLin
  rw [toMatrix_std_mulVecLin] at key
  rw [← key]
  have hQm : (Pi.basisFun K (Fin n)).toMatrix B' = Q := by
    ext i j
    simp [Basis.toMatrix_apply, B', toLinearEquiv'_apply_eq]
  have hPm' : (Pi.basisFun K (Fin m)).toMatrix D' = ⅟P := by
    ext i j
    simp [Basis.toMatrix_apply, D', toLinearEquiv'_apply_eq]
  have hflip := Basis.toMatrix_mul_toMatrix_flip D' (Pi.basisFun K (Fin m))
  rw [hPm'] at hflip
  have hPm : D'.toMatrix (Pi.basisFun K (Fin m)) = P := by
    calc D'.toMatrix (Pi.basisFun K (Fin m))
        = D'.toMatrix (Pi.basisFun K (Fin m)) * ⅟P * P := by simp
      _ = P := by rw [hflip, Matrix.one_mul]
  rw [hPm, hQm]

end UndergradKB.LinearAlgebra
