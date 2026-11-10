import Mathlib.LinearAlgebra.Matrix.Rank
import UndergradKB.LinearAlgebra.Jordan
import UndergradKB.Common.Attr

/-! # Uniqueness of the Jordan form

Hefferon Remark Five.IV.2.9 (and the uniqueness half of Theorem Five.III.2.17): the Jordan blocks
of an operator are determined by the operator, up to order. The invariant used is the sequence of
ranks of the powers `(T - μ)^k`: in a Jordan basis, the range of `(T - μ)^k` is spanned by the basis
vectors of the blocks with eigenvalue `≠ μ` together with the first `size - k` vectors of each block
with eigenvalue `μ`, so `rank (T - μ)^k - rank (T - μ)^(k+1)` is the number of blocks with eigenvalue
`μ` and size `> k`.
-/

open Module Set Submodule

namespace UndergradKB.LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section jordanRank

variable {p : ℕ} {n : Fin p → ℕ} (T : Module.End K V) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V)
  (lam : Fin p → K)

open Classical in
/-- The number of Jordan blocks with eigenvalue `μ` and size `> k`. -/
noncomputable def jordanCount (lam : Fin p → K) (n : Fin p → ℕ) (μ : K) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => lam i = μ ∧ k < n i).card

/-- The block of basis vectors with first index `i`. -/
noncomputable def blockSpan (i : Fin p) : Submodule K V :=
  span K (range fun r : Fin (n i) => b ⟨i, r⟩)

variable {T b lam}

lemma jordan_sub_apply (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) (μ : K) (i : Fin p)
    (r : Fin (n i)) :
    (T - μ • 1) (b ⟨i, r⟩) = (lam i - μ) • b ⟨i, r⟩ +
      (if _h : 0 < (r : ℕ) then b ⟨i, ⟨r - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.2⟩⟩
        else 0) := by
  rw [LinearMap.sub_apply, (toMatrix_jordan_iff T b lam).mp hb i r, sub_smul]
  simp only [LinearMap.smul_apply, one_apply_eq_self]
  abel

lemma jordan_pow_apply_of_eq (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) {μ : K} {i : Fin p}
    (hl : lam i = μ) (j : ℕ) : ∀ (r : ℕ) (hr : r < n i),
    ((T - μ • 1) ^ j) (b ⟨i, ⟨r, hr⟩⟩) = if h : j ≤ r then b ⟨i, ⟨r - j, by omega⟩⟩ else 0 := by
  induction j with
  | zero => intro r hr; simp
  | succ j ih =>
    intro r hr
    have hv : ((⟨r, hr⟩ : Fin (n i)) : ℕ) = r := rfl
    rw [pow_succ, mul_apply_eq_comp, jordan_sub_apply hb, hl, sub_self, zero_smul, zero_add]
    by_cases h0 : 0 < r
    · rw [dif_pos (by omega), ih]
      by_cases hj : j + 1 ≤ r
      · rw [dif_pos (by omega), dif_pos hj]
        congr 3
        omega
      · rw [dif_neg (by omega), dif_neg hj]
    · rw [dif_neg (by omega), map_zero, dif_neg (by omega)]

lemma blockSpan_le_comap (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) (μ : K) (i : Fin p) :
    ∀ x ∈ blockSpan b i, (T - μ • 1) x ∈ blockSpan b i := by
  have : blockSpan b i ≤ (blockSpan b i).comap (T - μ • 1) := by
    refine span_le.mpr ?_
    rintro _ ⟨r, rfl⟩
    show (T - μ • 1) (b ⟨i, r⟩) ∈ blockSpan b i
    rw [jordan_sub_apply hb]
    refine add_mem (smul_mem _ _ (subset_span ⟨r, rfl⟩)) ?_
    split_ifs
    · exact subset_span ⟨_, rfl⟩
    · exact zero_mem _
  exact fun x hx => this hx

lemma blockSpan_le_map (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) {μ : K} {i : Fin p}
    (hl : lam i ≠ μ) : blockSpan b i ≤ (blockSpan b i).map (T - μ • 1) := by
  have hc : lam i - μ ≠ 0 := sub_ne_zero.mpr hl
  have hmem : ∀ r : Fin (n i), (T - μ • 1) (b ⟨i, r⟩) ∈ (blockSpan b i).map (T - μ • 1) :=
    fun r => mem_map_of_mem (subset_span ⟨r, rfl⟩)
  have key : ∀ (r : ℕ) (hr : r < n i), b ⟨i, ⟨r, hr⟩⟩ ∈ (blockSpan b i).map (T - μ • 1) := by
    intro r
    induction r with
    | zero =>
      intro hr
      have h := hmem ⟨0, hr⟩
      rw [jordan_sub_apply hb, dif_neg (lt_irrefl 0), add_zero] at h
      have := smul_mem _ (lam i - μ)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    | succ r ih =>
      intro hr
      have h := hmem ⟨r + 1, hr⟩
      rw [jordan_sub_apply hb, dif_pos (Nat.succ_pos r)] at h
      have h2 := sub_mem h (ih (by omega))
      simp only [Nat.add_sub_cancel, add_sub_cancel_right] at h2
      have := smul_mem _ (lam i - μ)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  refine span_le.mpr ?_
  rintro _ ⟨r, rfl⟩
  exact key r r.2

lemma blockSpan_le_map_pow (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) {μ : K} {i : Fin p}
    (hl : lam i ≠ μ) (k : ℕ) : blockSpan b i ≤ (blockSpan b i).map ((T - μ • 1) ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih =>
    refine (blockSpan_le_map hb hl).trans ?_
    rw [pow_succ', Module.End.mul_eq_comp, Submodule.map_comp]
    exact Submodule.map_mono ih

/-- In a Jordan basis, the range of `(T - μ)^k` is spanned by the basis vectors of the blocks with
eigenvalue `≠ μ` and the first `n i - k` vectors of the blocks with eigenvalue `μ`. -/
lemma range_jordan_pow (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) (μ : K) (k : ℕ) :
    LinearMap.range ((T - μ • 1) ^ k) =
      span K (range fun x : {x : Σ i : Fin p, Fin (n i) // lam x.1 ≠ μ ∨ (x.2 : ℕ) + k < n x.1} =>
        b x.1) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, span_le]
    rintro _ ⟨_, ⟨⟨i, r⟩, rfl⟩, rfl⟩
    by_cases hl : lam i = μ
    · have := jordan_pow_apply_of_eq hb hl k r r.2
      simp only [Fin.eta] at this
      rw [SetLike.mem_coe, this]
      split_ifs with h
      · exact subset_span ⟨⟨⟨i, _⟩, Or.inr (by simp only; omega)⟩, rfl⟩
      · exact zero_mem _
    · have h1 : ((T - μ • 1) ^ k) (b ⟨i, r⟩) ∈ blockSpan b i :=
        pow_apply_mem _ (blockSpan_le_comap hb μ i) k _ (subset_span ⟨r, rfl⟩)
      refine span_mono ?_ h1
      rintro _ ⟨r', rfl⟩
      exact ⟨⟨⟨i, r'⟩, Or.inl hl⟩, rfl⟩
  · refine span_le.mpr ?_
    rintro _ ⟨⟨⟨i, r⟩, hx⟩, rfl⟩
    by_cases hl : lam i = μ
    · have hr : (r : ℕ) + k < n i := hx.resolve_left (not_not.mpr hl)
      have := jordan_pow_apply_of_eq hb hl k ((r : ℕ) + k) hr
      rw [dif_pos (by omega)] at this
      refine ⟨b ⟨i, ⟨(r : ℕ) + k, hr⟩⟩, ?_⟩
      rw [this]
      congr 3
      simp
    · have h1 : b ⟨i, r⟩ ∈ blockSpan b i := subset_span ⟨r, rfl⟩
      exact LinearMap.map_le_range (blockSpan_le_map_pow hb hl k h1)

lemma card_fin_add_lt (m k : ℕ) : Fintype.card {r : Fin m // (r : ℕ) + k < m} = m - k := by
  rw [← Fintype.card_fin (m - k)]
  exact Fintype.card_congr
    { toFun := fun r => ⟨r.1, by have := r.2; omega⟩
      invFun := fun s => ⟨⟨s, by omega⟩, by have := s.2; simp only; omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open Classical in
/-- The rank of `(T - μ)^k` read off a Jordan basis: blocks with eigenvalue `≠ μ` count fully,
a block of size `n i` with eigenvalue `μ` contributes `n i - k`. -/
lemma finrank_range_jordan_pow (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) (μ : K) (k : ℕ) :
    finrank K (LinearMap.range ((T - μ • 1) ^ k)) =
      ∑ i, if lam i = μ then n i - k else n i := by
  classical
  rw [range_jordan_pow hb μ k]
  erw [finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)]
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hl : lam i = μ
  · simp only [hl, ne_eq, not_true_eq_false, false_or, ite_true]
    rw [← Finset.card_filter, ← Fintype.card_subtype, card_fin_add_lt]
  · simp [hl]

open Classical in
lemma finrank_range_jordan_pow_succ (hb : LinearMap.toMatrix b b T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))) (μ : K) (k : ℕ) :
    finrank K (LinearMap.range ((T - μ • 1) ^ k)) =
      finrank K (LinearMap.range ((T - μ • 1) ^ (k + 1))) + jordanCount lam n μ k := by
  classical
  rw [finrank_range_jordan_pow hb, finrank_range_jordan_pow hb, jordanCount, Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : lam i = μ <;> by_cases h2 : k < n i <;> simp [h1, h2] <;> omega

end jordanRank

section multiset

variable {p : ℕ} {n : Fin p → ℕ}

omit [Field K] [AddCommGroup V] [Module K V] in
open Classical in
lemma count_jordan_multiset (lam : Fin p → K) (hn : ∀ i, 0 < n i) (μ : K) (m : ℕ) :
    Multiset.count (μ, m) (Multiset.map (fun i => (lam i, n i)) Finset.univ.val) =
      jordanCount lam n μ (m - 1) - jordanCount lam n μ m := by
  classical
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  rcases m with _ | j
  · rw [Finset.card_eq_zero.mpr]
    · simp
    · rw [Finset.filter_eq_empty_iff]
      intro i _ h
      have := hn i
      simp only [Prod.mk.injEq] at h
      omega
  · have : (Finset.univ.filter fun i => (μ, j + 1) = (lam i, n i)).card +
        jordanCount lam n μ (j + 1) = jordanCount lam n μ j := by
      rw [jordanCount, jordanCount, Finset.card_filter, Finset.card_filter, Finset.card_filter,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : lam i = μ
      · simp only [Prod.mk.injEq, h1, true_and]
        split_ifs <;> omega
      · simp [h1, Ne.symm h1]
    simp only [Nat.add_sub_cancel]
    omega

variable {V' : Type*} [AddCommGroup V'] [Module K V']

/-- Two operators with Jordan bases whose powers `(T - μ)^k` have the same ranks have the same
Jordan blocks (as a multiset of pairs eigenvalue, size). -/
theorem jordan_multiset_eq_of_finrank_eq {T : Module.End K V} {T' : Module.End K V'}
    {p' : ℕ} {n' : Fin p' → ℕ}
    (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V) (b' : Module.Basis (Σ i : Fin p', Fin (n' i)) K V')
    (lam : Fin p → K) (lam' : Fin p' → K) (hn : ∀ i, 0 < n i) (hn' : ∀ i, 0 < n' i)
    (hb : LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i)))
    (hb' : LinearMap.toMatrix b' b' T' =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam' i) (n' i)))
    (hr : ∀ (μ : K) (k : ℕ), finrank K (LinearMap.range ((T - μ • 1) ^ k)) =
      finrank K (LinearMap.range ((T' - μ • 1) ^ k))) :
    Multiset.map (fun i => (lam i, n i)) Finset.univ.val =
      Multiset.map (fun i => (lam' i, n' i)) Finset.univ.val := by
  have hc : ∀ μ k, jordanCount lam n μ k = jordanCount lam' n' μ k := by
    intro μ k
    have h1 := finrank_range_jordan_pow_succ hb μ k
    have h2 := finrank_range_jordan_pow_succ hb' μ k
    rw [hr μ k, hr μ (k + 1)] at h1
    omega
  classical
  refine Multiset.ext.mpr fun ⟨μ, m⟩ => ?_
  rw [count_jordan_multiset lam hn, count_jordan_multiset lam' hn', hc, hc]

/-- Hefferon Remark Five.IV.2.9 (uniqueness of the Jordan form): if `b` and `b'` are two Jordan bases
of the same operator `T` (blocks of positive sizes `n i`, `n' i` with eigenvalues `lam i`, `lam' i`),
then the two lists of blocks agree up to order: the multisets of pairs (eigenvalue, size) are equal. -/
@[kb "hefferon2020" "Five.IV.2.9, p. 466"]
theorem hefferon_Five_IV_2_9 {T : Module.End K V} {p' : ℕ} {n' : Fin p' → ℕ}
    (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V) (b' : Module.Basis (Σ i : Fin p', Fin (n' i)) K V)
    (lam : Fin p → K) (lam' : Fin p' → K) (hn : ∀ i, 0 < n i) (hn' : ∀ i, 0 < n' i)
    (hb : LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i)))
    (hb' : LinearMap.toMatrix b' b' T =
      Matrix.blockDiagonal' (fun i => jordanBlock (lam' i) (n' i))) :
    Multiset.map (fun i => (lam i, n i)) Finset.univ.val =
      Multiset.map (fun i => (lam' i, n' i)) Finset.univ.val :=
  jordan_multiset_eq_of_finrank_eq b b' lam lam' hn hn' hb hb' fun _ _ => rfl

end multiset

section matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {n : Fin p → ℕ}

lemma toMatrix_toLin'_reindex (e : (Σ i : Fin p, Fin (n i)) ≃ ι)
    (M : Matrix (Σ i : Fin p, Fin (n i)) (Σ i : Fin p, Fin (n i)) K) :
    LinearMap.toMatrix ((Pi.basisFun K ι).reindex e.symm) ((Pi.basisFun K ι).reindex e.symm)
      (Matrix.toLin' (Matrix.reindex e e M)) = M := by
  ext x y
  have hs : (LinearMap.funLeft K K e) (Pi.single (e y) (1 : K)) = Pi.single y 1 := by
    ext z
    simp [LinearMap.funLeft_apply, Pi.single_apply, e.apply_eq_iff_eq]
  simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, hs, Matrix.mulVec_single]

lemma finrank_range_toLin'_pow (A : Matrix ι ι K) (μ : K) (k : ℕ) :
    finrank K (LinearMap.range ((Matrix.toLin' A - μ • 1) ^ k)) = ((A - μ • 1) ^ k).rank := by
  have : (Matrix.toLin' A - μ • 1) ^ k = Matrix.toLinAlgEquiv' ((A - μ • 1) ^ k) := by
    rw [map_pow, map_sub, map_smul, map_one]
    rfl
  rw [this, Matrix.rank]
  rfl

lemma rank_conj_pow (A : Matrix ι ι K) (P : (Matrix ι ι K)ˣ) (μ : K) (k : ℕ) :
    (((P : Matrix ι ι K) * A * (P⁻¹ : (Matrix ι ι K)ˣ) - μ • 1) ^ k).rank =
      ((A - μ • 1) ^ k).rank := by
  have h1 : (P : Matrix ι ι K) * A * (P⁻¹ : (Matrix ι ι K)ˣ) - μ • 1 =
      (P : Matrix ι ι K) * (A - μ • 1) * (P⁻¹ : (Matrix ι ι K)ˣ) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.mul_inv]
  have h2 : ∀ X : Matrix ι ι K, ((P : Matrix ι ι K) * X * (P⁻¹ : (Matrix ι ι K)ˣ)) ^ k =
      (P : Matrix ι ι K) * X ^ k * (P⁻¹ : (Matrix ι ι K)ˣ) := by
    intro X
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hP : IsUnit (P : Matrix ι ι K).det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
  have hQ : IsUnit ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (P⁻¹).isUnit
  rw [h1, h2, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]

/-- Hefferon Remark Five.IV.2.9, matrix form: two similar matrices that are both Jordan matrices
(block diagonal with Jordan blocks of positive sizes, after relabelling the rows and columns by `ι`)
have the same blocks up to order, so the Jordan form is a canonical form for similarity. -/
@[kb "hefferon2020" "Five.IV.2.9, p. 466"]
theorem hefferon_Five_IV_2_9_matrix {p' : ℕ} {n' : Fin p' → ℕ} (lam : Fin p → K)
    (lam' : Fin p' → K) (hn : ∀ i, 0 < n i) (hn' : ∀ i, 0 < n' i)
    (e : (Σ i : Fin p, Fin (n i)) ≃ ι) (e' : (Σ i : Fin p', Fin (n' i)) ≃ ι)
    (P : (Matrix ι ι K)ˣ)
    (h : Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (lam i) (n i)) =
      (P : Matrix ι ι K) *
        Matrix.reindex e' e' (Matrix.blockDiagonal' fun i => jordanBlock (lam' i) (n' i)) *
        ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K)) :
    Multiset.map (fun i => (lam i, n i)) Finset.univ.val =
      Multiset.map (fun i => (lam' i, n' i)) Finset.univ.val := by
  refine jordan_multiset_eq_of_finrank_eq ((Pi.basisFun K ι).reindex e.symm)
    ((Pi.basisFun K ι).reindex e'.symm) lam lam' hn hn' (toMatrix_toLin'_reindex e _)
    (toMatrix_toLin'_reindex e' _) fun μ k => ?_
  rw [finrank_range_toLin'_pow, finrank_range_toLin'_pow, h, rank_conj_pow]

/-- Hefferon Theorem Five.III.2.17, uniqueness half (Axler's superdiagonal convention): if a
nilpotent matrix is similar to two block diagonal matrices of zero-eigenvalue Jordan blocks (block
sizes `m i + 1` and `m' i + 1`), the multisets of block sizes are equal, so the nilpotent canonical
form is unique up to the order of the blocks. -/
@[kb "hefferon2020" "Five.III.2.17, p. 445"]
theorem hefferon_Five_III_2_17_unique {p' : ℕ} {m : Fin p → ℕ} {m' : Fin p' → ℕ}
    (A : Matrix ι ι K)
    (e : (Σ i : Fin p, Fin (m i + 1)) ≃ ι) (e' : (Σ i : Fin p', Fin (m' i + 1)) ≃ ι)
    (P P' : (Matrix ι ι K)ˣ)
    (h : A = (P : Matrix ι ι K) *
        Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) *
        ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K))
    (h' : A = (P' : Matrix ι ι K) *
        Matrix.reindex e' e' (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m' i + 1)) *
        ((P'⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K)) :
    Multiset.map (fun i => m i + 1) Finset.univ.val =
      Multiset.map (fun i => m' i + 1) Finset.univ.val := by
  have hsim : Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) =
      ((P⁻¹ * P' : (Matrix ι ι K)ˣ) : Matrix ι ι K) *
        Matrix.reindex e' e' (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m' i + 1)) *
        (((P⁻¹ * P')⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) := by
    have hh : (P : Matrix ι ι K) *
        Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) *
        ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) = (P' : Matrix ι ι K) *
        Matrix.reindex e' e' (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m' i + 1)) *
        ((P'⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) := h.symm.trans h'
    calc _ = ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K) * ((P : Matrix ι ι K) *
          Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) *
          ((P⁻¹ : (Matrix ι ι K)ˣ) : Matrix ι ι K)) * (P : Matrix ι ι K) := by
          simp [mul_assoc]
      _ = _ := by
          rw [hh]
          simp [mul_assoc, mul_inv_rev]
  have := hefferon_Five_IV_2_9_matrix (fun _ => (0 : K)) (fun _ => (0 : K))
    (fun _ => Nat.succ_pos _) (fun _ => Nat.succ_pos _) e e' (P⁻¹ * P') hsim
  have := congrArg (Multiset.map Prod.snd) this
  rw [Multiset.map_map, Multiset.map_map] at this
  exact this

end matrix

end UndergradKB.LinearAlgebra
