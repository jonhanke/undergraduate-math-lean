import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Group.Conj
import UndergradKB.Common.Attr

/-! # Linear maps and matrices (Axler 3, Hefferon Three)

Linearity, rank and nullity, injectivity criteria, invertibility, matrices of maps and change of basis,
similarity, and the dual map. -/

open Module Matrix

namespace UndergradKB.LinearAlgebra

section Linearity

variable {K V W : Type*} [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- A function is linear iff it preserves combinations `a u + b v` of two vectors iff it preserves all
finite linear combinations. -/
@[kb "hefferon2020" "Three.I.1.11, p. 189"]
theorem hefferon_Three_I_1_11 (f : V → W) :
    List.TFAE [IsLinearMap K f,
      ∀ (a b : K) (u v : V), f (a • u + b • v) = a • f u + b • f v,
      ∀ (s : Finset ℕ) (c : ℕ → K) (v : ℕ → V), f (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • f (v i)] := by
  tfae_have 1 → 3 := fun h s c v => by
    let g : V →ₗ[K] W := IsLinearMap.mk' f h
    have : ∀ x, g x = f x := fun _ => rfl
    simp only [← this, map_sum, map_smul]
  tfae_have 3 → 2 := fun h a b u v => by
    have := h {0, 1} (fun i => if i = 0 then a else b) (fun i => if i = 0 then u else v)
    simpa using this
  tfae_have 2 → 1 := fun h => by
    have h0 : f 0 = 0 := by simpa using h 0 0 0 0
    refine ⟨fun u v => ?_, fun c u => ?_⟩
    · simpa using h 1 1 u v
    · simpa [h0] using h c 0 u 0
  tfae_finish

end Linearity

section RankNullity

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The nullity of a linear map: the dimension of its null space. (The rank is
`finrank K (LinearMap.range f)`, i.e. `LinearMap.rank`.) -/
noncomputable def nullity (f : V →ₗ[K] W) : ℕ := finrank K (LinearMap.ker f)

/-- Rank and nullity of a linear map: the rank is the dimension of the range, which is what
`LinearMap.rank` says. -/
@[kb "hefferon2020" "Three.II.2.2, p. 210"]
theorem hefferon_Three_II_2_2 (f : V →ₗ[K] W) :
    LinearMap.rank f = Module.rank K (LinearMap.range f) := rfl

/-- Rank plus nullity is the dimension of the domain. -/
@[kb "hefferon2020" "Three.II.2.11, p. 214"]
theorem hefferon_Three_II_2_11 [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K (LinearMap.range f) + nullity f = finrank K V :=
  f.finrank_range_add_finrank_ker

/-- The rank is at most the dimension of the domain, with equality iff the nullity is zero. -/
@[kb "hefferon2020" "Three.II.2.17, p. 216"]
theorem hefferon_Three_II_2_17 [FiniteDimensional K V] (f : V →ₗ[K] W) :
    finrank K (LinearMap.range f) ≤ finrank K V ∧
      (finrank K (LinearMap.range f) = finrank K V ↔ nullity f = 0) := by
  have := hefferon_Three_II_2_11 f
  exact ⟨by omega, by omega⟩

/-- Equivalent conditions for a linear map on an `n`-dimensional space: injective; has a linear inverse
from its range; nullity `0`; rank `n`; carries every basis to a basis of the range. -/
@[kb "hefferon2020" "Three.II.2.20, p. 217"]
theorem hefferon_Three_II_2_20 [FiniteDimensional K V] (f : V →ₗ[K] W) :
    List.TFAE [Function.Injective f,
      ∃ g : LinearMap.range f →ₗ[K] V, g ∘ₗ f.rangeRestrict = LinearMap.id,
      nullity f = 0,
      finrank K (LinearMap.range f) = finrank K V,
      ∀ b : Basis (Fin (finrank K V)) K V,
        LinearIndependent K (f ∘ b) ∧ Submodule.span K (Set.range (f ∘ b)) = LinearMap.range f] := by
  tfae_have 1 ↔ 3 := by
    unfold nullity
    rw [← LinearMap.ker_eq_bot, Submodule.finrank_eq_zero]
  tfae_have 4 ↔ 3 := by
    have := hefferon_Three_II_2_11 f
    omega
  tfae_have 1 → 2 := fun h =>
    ⟨(LinearEquiv.ofInjective f h).symm.toLinearMap, by
      ext x
      exact (LinearEquiv.ofInjective f h).symm_apply_apply x⟩
  tfae_have 2 → 1 := fun ⟨g, hg⟩ x y hxy => by
    have : f.rangeRestrict x = f.rangeRestrict y := Subtype.ext hxy
    have := congrArg g this
    simpa [← LinearMap.comp_apply, hg] using this
  tfae_have 1 → 5 := fun h b => by
    refine ⟨LinearIndependent.map' b.linearIndependent f (LinearMap.ker_eq_bot.2 h), ?_⟩
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  tfae_have 5 → 1 := fun h => by
    set b := Module.finBasis K V
    have hli := (h b).1
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ∑ i, b.repr x i • (f ∘ b) i = 0 := by
      simp only [Function.comp, ← map_smul, ← map_sum]
      rw [b.sum_repr]; exact hx
    have h2 := Fintype.linearIndependent_iff.1 hli _ h1
    apply b.repr.injective
    ext i; simpa using h2 i
  tfae_finish

end RankNullity

section Inj

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear map is one-to-one iff it carries linearly independent families to linearly independent
families. -/
@[kb "hefferon2020" "Three.II.2.37, p. 219"]
theorem hefferon_Three_II_2_37 (f : V →ₗ[K] W) :
    Function.Injective f ↔
      ∀ (ι : Type) (v : ι → V), LinearIndependent K v → LinearIndependent K (f ∘ v) := by
  constructor
  · intro h ι v hv
    exact hv.map' f (LinearMap.ker_eq_bot.2 h)
  · intro h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 : LinearIndependent K (fun _ : Unit => x) := linearIndependent_unique_iff.2 hx0
    have h2 := linearIndependent_unique_iff.1 (h Unit _ h1)
    exact h2 (by simpa using hx)

/-- An inverse of a linear map, if there is one, is unique. -/
@[kb "axler2024" "3.61, p. 100"]
theorem axler_3_61 (T : V →ₗ[K] W) (S₁ S₂ : W →ₗ[K] V)
    (h1 : S₁ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₁ = LinearMap.id)
    (h2 : S₂ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₂ = LinearMap.id) : S₁ = S₂ :=
  calc S₁ = S₁ ∘ₗ (T ∘ₗ S₂) := by rw [h2.2, LinearMap.comp_id]
    _ = (S₁ ∘ₗ T) ∘ₗ S₂ := by rw [LinearMap.comp_assoc]
    _ = S₂ := by rw [h1.1, LinearMap.id_comp]

/-- A function out of a nonempty set has a left inverse iff it is one-to-one. (Nonemptiness of the domain
is needed; the book leaves it implicit.) -/
@[kb "hefferon2020" "Appendix.1, p. 504"]
theorem hefferon_Appendix_1 {A B : Type*} [Nonempty A] (f : A → B) :
    Function.Injective f ↔ ∃ g : B → A, g ∘ f = id :=
  Function.injective_iff_hasLeftInverse.trans
    ⟨fun ⟨g, hg⟩ => ⟨g, funext hg⟩, fun ⟨g, hg⟩ => ⟨g, congrFun hg⟩⟩

/-- A linear map is nonsingular (one-to-one and onto) iff it is an isomorphism, i.e. it is the
underlying map of a linear equivalence. -/
@[kb "hefferon2020" "Three.III.2.7, p. 237"]
theorem hefferon_Three_III_2_7 (f : V →ₗ[K] W) :
    Function.Bijective f ↔ ∃ e : V ≃ₗ[K] W, (e : V →ₗ[K] W) = f :=
  ⟨fun h => ⟨LinearEquiv.ofBijective f h, rfl⟩, fun ⟨e, he⟩ => he ▸ e.bijective⟩

/-- Between finite-dimensional spaces of equal dimension, nonsingular is the same as having trivial
null space. -/
theorem nonsingular_iff_ker_eq_bot [FiniteDimensional K V] [FiniteDimensional K W]
    (hd : finrank K V = finrank K W) (f : V →ₗ[K] W) :
    Function.Bijective f ↔ LinearMap.ker f = ⊥ :=
  ⟨fun h => LinearMap.ker_eq_bot.2 h.1, fun h =>
    ⟨LinearMap.ker_eq_bot.1 h,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (LinearMap.ker_eq_bot.1 h)⟩⟩

/-- Isomorphism of vector spaces is reflexive, symmetric and transitive. -/
@[kb "hefferon2020" "Three.I.2.2, p. 194"]
theorem hefferon_Three_I_2_2 :
    (∀ (V : Type*) [AddCommGroup V] [Module K V], Nonempty (V ≃ₗ[K] V)) ∧
    (∀ (V W : Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
      Nonempty (V ≃ₗ[K] W) → Nonempty (W ≃ₗ[K] V)) ∧
    (∀ (U V W : Type*) [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
      [AddCommGroup W] [Module K W],
      Nonempty (U ≃ₗ[K] V) → Nonempty (V ≃ₗ[K] W) → Nonempty (U ≃ₗ[K] W)) :=
  ⟨fun V _ _ => ⟨LinearEquiv.refl K V⟩,
    by intro V W _ _ _ _ h; exact h.elim fun e => ⟨e.symm⟩,
    by intro U V W _ _ _ _ _ _ h h'; exact h.elim fun e => h'.elim fun e' => ⟨e.trans e'⟩⟩

private lemma comp_eq_id_aux [FiniteDimensional K V] [FiniteDimensional K W]
    (hd : finrank K V = finrank K W) (S : W →ₗ[K] V) (T : V →ₗ[K] W) (h : S ∘ₗ T = LinearMap.id) :
    T ∘ₗ S = LinearMap.id := by
  have hS : ∀ v, S (T v) = v := fun v => LinearMap.congr_fun h v
  have hinj : Function.Injective T := fun x y hxy => by
    rw [← hS x, ← hS y, hxy]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hinj
  ext w
  obtain ⟨v, rfl⟩ := hsurj w
  simp [hS]

/-- For finite-dimensional spaces of the same dimension, `S T = I` iff `T S = I`. -/
@[kb "axler2024" "3.68, p. 103"]
theorem axler_3_68 [FiniteDimensional K V] [FiniteDimensional K W]
    (hd : finrank K V = finrank K W) (S : W →ₗ[K] V) (T : V →ₗ[K] W) :
    S ∘ₗ T = LinearMap.id ↔ T ∘ₗ S = LinearMap.id := by
  exact ⟨comp_eq_id_aux hd S T, comp_eq_id_aux hd.symm T S⟩

/-- Relative to a basis, a linear relation among vectors holds iff the same relation holds among their
coordinate columns. -/
@[kb "hefferon2020" "Two.III.1.18, p. 135"]
theorem hefferon_Two_III_1_18 {ι : Type*} [Fintype ι] (B : Basis ι K V) {k : ℕ} (a : Fin k → K)
    (v : Fin k → V) :
    ∑ i, a i • v i = 0 ↔ ∑ i, a i • B.equivFun (v i) = 0 := by
  rw [← B.equivFun.map_eq_zero_iff]
  simp [map_sum, map_smul]

/-- The dual map: its null space is the annihilator of the range, and its nullity is
`nullity T + dim W - dim V`. -/
@[kb "axler2024" "3.128, p. 129"]
theorem axler_3_128 [FiniteDimensional K V] [FiniteDimensional K W] (T : V →ₗ[K] W) :
    LinearMap.ker T.dualMap = (LinearMap.range T).dualAnnihilator ∧
      finrank K (LinearMap.ker T.dualMap) =
        finrank K (LinearMap.ker T) + finrank K W - finrank K V := by
  have ha := LinearMap.ker_dualMap_eq_dualAnnihilator_range (f := T)
  refine ⟨ha, ?_⟩
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range T)
  have h2 := T.finrank_range_add_finrank_ker
  rw [ha]
  omega

end Inj

section Products

variable {K : Type*} {l m n : Type*}

/-- Matrix multiplication is not commutative: for every size at least `2` and every nontrivial ring there
are `A`, `B` with `A B ≠ B A`. (For non-square sizes, one of the products is not even defined.) -/
@[kb "hefferon2020" "Three.IV.2.9, p. 250"]
theorem hefferon_Three_IV_2_9 [Ring K] [Nontrivial K] (k : ℕ) :
    ∃ A B : Matrix (Fin (k + 2)) (Fin (k + 2)) K, A * B ≠ B * A := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have := congrFun (congrFun h 0) 0
  simp [Matrix.single_apply] at this

/-- Each column of a product `C R` is a combination of the columns of `C`, and each row is a
combination of the rows of `R`. -/
@[kb "axler2024" "3.51, p. 94"]
theorem axler_3_51 [CommSemiring K] [Fintype m] (C : Matrix l m K) (R : Matrix m n K) :
    (∀ j, (C * R).col j = ∑ k, R k j • C.col k) ∧
      (∀ i, (C * R).row i = ∑ k, C i k • R.row k) := by
  refine ⟨fun j => ?_, fun i => ?_⟩
  · ext i
    simp [Matrix.col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  · ext j
    simp [Matrix.row, Matrix.mul_apply, Finset.sum_apply]

/-- Column-row factorization: a `m × n` matrix of rank `c` is a product of an `m × c` matrix and a
`c × n` matrix. -/
@[kb "axler2024" "3.56, p. 96"]
theorem axler_3_56 [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (c : ℕ) (hc : A.rank = c) :
    ∃ (C : Matrix (Fin m) (Fin c) K) (R : Matrix (Fin c) (Fin n) K), A = C * R := by
  set S := Submodule.span K (Set.range A.col) with hSdef
  have hS : finrank K S = c := by rw [← hc, A.rank_eq_finrank_span_cols]
  let b : Basis (Fin c) K S := Module.finBasisOfFinrankEq K S hS
  have hmem : ∀ j, A.col j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨Matrix.of fun i k => (b k : Fin m → K) i,
    Matrix.of fun k j => b.repr ⟨A.col j, hmem j⟩ k, ?_⟩
  ext i j
  have h1 := b.sum_repr ⟨A.col j, hmem j⟩
  have h2 := congrArg (fun s : S => (s : Fin m → K) i) h1
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h2
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have h3 : A i j = (A.col j) i := rfl
  rw [h3, ← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end Products

section MatrixOfMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

private lemma rank_toMatrix (bv : Basis n K V) (bw : Basis m K W) (f : V →ₗ[K] W) :
    (LinearMap.toMatrix bv bw f).rank = finrank K (LinearMap.range f) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ bw bv, Matrix.toLin_toMatrix]

/-- A map is onto iff the rank of its matrix is the number of rows, and one-to-one iff the rank is the
number of columns. -/
@[kb "hefferon2020" "Three.III.2.6, p. 236"]
theorem hefferon_Three_III_2_6 (bv : Basis n K V) (bw : Basis m K W) (f : V →ₗ[K] W) :
    (Function.Surjective f ↔ (LinearMap.toMatrix bv bw f).rank = Fintype.card m) ∧
      (Function.Injective f ↔ (LinearMap.toMatrix bv bw f).rank = Fintype.card n) := by
  haveI := Module.Finite.of_basis bv
  haveI := Module.Finite.of_basis bw
  rw [rank_toMatrix, ← Module.finrank_eq_card_basis bw, ← Module.finrank_eq_card_basis bv]
  have h := f.finrank_range_add_finrank_ker
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.range_eq_top]
    exact ⟨fun h => by rw [h, finrank_top], Submodule.eq_top_of_finrank_eq⟩
  · rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    omega

/-- A nonsingular map is represented by a square matrix. -/
@[kb "hefferon2020" "Three.III.2.9, p. 237"]
theorem hefferon_Three_III_2_9 (bv : Basis n K V) (bw : Basis m K W) (f : V →ₗ[K] W)
    (hf : Function.Bijective f) : Fintype.card n = Fintype.card m := by
  rw [← Module.finrank_eq_card_basis bv, ← Module.finrank_eq_card_basis bw]
  exact (LinearEquiv.ofBijective f hf).finrank_eq

/-- A square matrix represents nonsingular maps iff it is an invertible matrix: for bases with the same
index set, a map is bijective iff its matrix is invertible. -/
@[kb "hefferon2020" "Three.III.2.9, p. 237"]
theorem hefferon_Three_III_2_9_matrix (bv : Basis n K V) (bw : Basis n K W) (f : V →ₗ[K] W) :
    Function.Bijective f ↔ IsUnit (LinearMap.toMatrix bv bw f) := by
  obtain ⟨hs, hi⟩ := hefferon_Three_III_2_6 bv bw f
  rw [← Matrix.mulVec_surjective_iff_isUnit, Matrix.mulVec_surjective_iff_rank_eq_card]
  constructor
  · exact fun h => hs.1 h.2
  · exact fun h => ⟨hi.2 h, hs.2 h⟩

/-- The change-of-basis matrix converts coordinates, and any matrix that does so for all vectors is
that matrix. -/
@[kb "hefferon2020" "Three.V.1.3, p. 273"]
theorem hefferon_Three_V_1_3 (B : Basis n K V) (D : Basis m K V) :
    (∀ v : V, D.toMatrix B *ᵥ B.equivFun v = D.equivFun v) ∧
      ∀ M : Matrix m n K, (∀ v : V, M *ᵥ B.equivFun v = D.equivFun v) → M = D.toMatrix B := by
  refine ⟨fun v => ?_, fun M h => ?_⟩
  · simpa using Basis.toMatrix_mulVec_repr B D v
  · ext i j
    have e1 : B.equivFun (B j) = Pi.single j 1 := by
      ext k; simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
    have := congrFun (h (B j)) i
    rw [e1, Matrix.mulVec_single_one] at this
    simpa [Basis.toMatrix_apply, Basis.equivFun_apply, Matrix.col] using this

/-- A matrix changes bases (from a given basis `B` to some basis `D`) iff it is invertible. -/
@[kb "hefferon2020" "Three.V.1.5, p. 274"]
theorem hefferon_Three_V_1_5 (B : Basis n K V) (P : Matrix n n K) :
    (∃ D : Basis n K V, D.toMatrix B = P) ↔ IsUnit P := by
  constructor
  · rintro ⟨D, rfl⟩
    haveI := Basis.invertibleToMatrix D B
    exact isUnit_of_invertible _
  · intro hP
    have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
    let e := Matrix.toLinearEquiv B P hdet
    refine ⟨B.map e.symm, ?_⟩
    rw [Basis.toMatrix_map, LinearEquiv.symm_symm]
    have h := LinearMap.toMatrix_eq_basisToMatrix B B (Matrix.toLin B B P)
    rw [LinearMap.toMatrix_toLin] at h
    exact h.symm

/-- For an invertible operator, the matrix of the inverse is the inverse of the matrix. -/
@[kb "axler2024" "3.86, p. 111"]
theorem axler_3_86 (B : Basis n K V) (T : V ≃ₗ[K] V) :
    LinearMap.toMatrix B B (T.symm : V →ₗ[K] V) = (LinearMap.toMatrix B B (T : V →ₗ[K] V))⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← LinearMap.toMatrix_mul]
  have : (T.symm : V →ₗ[K] V) * (T : V →ₗ[K] V) = 1 := by
    ext x; simp
  rw [this, LinearMap.toMatrix_one]

end MatrixOfMap

section Similar

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Similarity of square matrices (Hefferon Definition Five.II.1.2): `T'` is similar to `T` if
`T' = P T P⁻¹` for some nonsingular `P`. -/
def Similar (T T' : Matrix n n K) : Prop := ∃ P : Matrix n n K, IsUnit P ∧ T' = P * T * P⁻¹

private lemma inv_mul_self_of_isUnit {P : Matrix n n K} (hP : IsUnit P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hP)

private lemma self_mul_inv_of_isUnit {P : Matrix n n K} (hP : IsUnit P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hP)

/-- Similarity is conjugacy in the monoid of square matrices. -/
@[kb "hefferon2020" "Five.II.1.2, p. 414"]
theorem hefferon_Five_II_1_2 (T T' : Matrix n n K) : Similar T T' ↔ IsConj T T' := by
  constructor
  · rintro ⟨P, ⟨u, rfl⟩, h⟩
    refine ⟨u, ?_⟩
    show (u : Matrix n n K) * T = T' * u
    rw [h, Matrix.mul_assoc, Matrix.mul_assoc, inv_mul_self_of_isUnit u.isUnit, Matrix.mul_one]
  · rintro ⟨u, hu⟩
    have hu' : (u : Matrix n n K) * T = T' * u := hu
    refine ⟨u, u.isUnit, ?_⟩
    rw [hu', Matrix.mul_assoc, self_mul_inv_of_isUnit u.isUnit, Matrix.mul_one]

/-- The matrices of one operator with respect to two bases are similar. -/
@[kb "hefferon2020" "Five.II.1.2, p. 414"]
theorem similar_toMatrix (B D : Basis n K V) (f : V →ₗ[K] V) :
    Similar (LinearMap.toMatrix B B f) (LinearMap.toMatrix D D f) := by
  haveI := Basis.invertibleToMatrix D B
  have hu : IsUnit (D.toMatrix B) := isUnit_of_invertible _
  refine ⟨D.toMatrix B, hu, ?_⟩
  have hinv : (D.toMatrix B)⁻¹ = B.toMatrix D :=
    Matrix.inv_eq_right_inv (Basis.toMatrix_mul_toMatrix_flip D B)
  rw [hinv]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix D B D B f).symm

/-- The zero matrix and the identity matrix are each similar only to themselves. -/
@[kb "hefferon2020" "Five.II.1.4, p. 414"]
theorem hefferon_Five_II_1_4 (T : Matrix n n K) :
    (Similar (0 : Matrix n n K) T ↔ T = 0) ∧ (Similar (1 : Matrix n n K) T ↔ T = 1) := by
  constructor
  · constructor
    · rintro ⟨P, _, h⟩; simpa using h
    · rintro rfl; exact ⟨1, isUnit_one, by simp⟩
  · constructor
    · rintro ⟨P, hP, h⟩
      rw [h, Matrix.mul_one, self_mul_inv_of_isUnit hP]
    · rintro rfl; exact ⟨1, isUnit_one, by simp⟩

end Similar

end UndergradKB.LinearAlgebra
