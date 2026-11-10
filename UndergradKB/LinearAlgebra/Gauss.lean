import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
import Mathlib.LinearAlgebra.Matrix.Transvection
import UndergradKB.Common.Attr

/-! # Gauss-Jordan reduction: existence of reduced echelon form

Over a field `K`, every matrix is row equivalent to a reduced row echelon matrix
(Hefferon, Chapter One, Section III). -/

namespace UndergradKB.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] {m n : ℕ}

/-- Left multiplication by an invertible matrix is a row equivalence. -/
theorem rowEquivalent_of_isUnit {T : Matrix (Fin m) (Fin m) K} (hT : IsUnit T)
    (A : Matrix (Fin m) (Fin n) K) : RowEquivalent A (T * A) := by
  obtain ⟨u, rfl⟩ := hT
  exact ⟨u, rfl⟩

theorem swap_mul_apply_eq (a b i : Fin m) (B : Matrix (Fin m) (Fin n) K) (j : Fin n) :
    (Matrix.swap K a b * B) i j = B (Equiv.swap a b i) j := by
  by_cases h1 : i = a
  · subst h1; simp
  · by_cases h2 : i = b
    · subst h2; simp
    · rw [swap_mul_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Invariant of the Gauss-Jordan sweep: the first `k` rows are finished rows with pivot columns `l`. -/
structure SweepInv (B : Matrix (Fin m) (Fin n) K) (k : ℕ) (l : Fin m → Fin n) : Prop where
  zero_before : ∀ i : Fin m, (i : ℕ) < k → ∀ j, j < l i → B i j = 0
  one_at : ∀ i : Fin m, (i : ℕ) < k → B i (l i) = 1
  col_zero : ∀ i : Fin m, (i : ℕ) < k → ∀ i', i' ≠ i → B i' (l i) = 0
  rest_zero : ∀ i : Fin m, (i : ℕ) < k → ∀ i' : Fin m, k ≤ (i' : ℕ) → ∀ j, j ≤ l i → B i' j = 0
  mono : ∀ i1 i2 : Fin m, (i1 : ℕ) < (i2 : ℕ) → (i2 : ℕ) < k → l i1 < l i2

theorem SweepInv.lead_eq {B : Matrix (Fin m) (Fin n) K} {k : ℕ} {l : Fin m → Fin n}
    (h : SweepInv B k l) {i : Fin m} (hi : (i : ℕ) < k) {c : Fin n} (hc : B.IsLeadingEntry i c) :
    c = l i := by
  rcases lt_trichotomy c (l i) with hlt | heq | hgt
  · exact absurd (h.zero_before i hi c hlt) hc.2
  · exact heq
  · have := hc.1 _ hgt
    rw [h.one_at i hi] at this
    exact absurd this one_ne_zero

theorem SweepInv.isReduced {B : Matrix (Fin m) (Fin n) K} {k : ℕ} {l : Fin m → Fin n}
    (h : SweepInv B k l) (hz : ∀ i : Fin m, k ≤ (i : ℕ) → B i = 0) : B.IsReducedRowEchelon where
  isRowEchelon := by
    intro i₁ i₂ h12 j₂ hj
    by_cases h2 : (i₂ : ℕ) < k
    · have h1 : (i₁ : ℕ) < k := lt_trans h12 h2
      by_contra hne
      have hle : j₂ ≤ l i₁ := by
        by_contra hgt
        have := hj _ (not_le.mp hgt)
        rw [h.one_at i₁ h1] at this
        exact one_ne_zero this
      have := h.mono i₁ i₂ h12 h2
      exact hne (h.zero_before i₂ h2 j₂ (lt_of_le_of_lt hle this))
    · have := hz i₂ (not_lt.mp h2)
      simp [this]
  eq_one := by
    intro i c hc
    by_cases hi : (i : ℕ) < k
    · rw [h.lead_eq hi hc]; exact h.one_at i hi
    · exact absurd (hz i (not_lt.mp hi)) hc.row_ne_zero
  eq_zero := by
    intro i₁ i₂ c hlt hc
    by_cases hi : (i₂ : ℕ) < k
    · rw [h.lead_eq hi hc]; exact h.col_zero i₂ hi i₁ (ne_of_lt hlt)
    · exact absurd (hz i₂ (not_lt.mp hi)) hc.row_ne_zero

theorem sweep_step (B : Matrix (Fin m) (Fin n) K) (k : ℕ) (l : Fin m → Fin n) (hI : SweepInv B k l)
    (hk : ∃ i : Fin m, k ≤ (i : ℕ) ∧ B i ≠ 0) :
    ∃ (B' : Matrix (Fin m) (Fin n) K) (l' : Fin m → Fin n),
      RowEquivalent B B' ∧ SweepInv B' (k + 1) l' := by
  classical
  obtain ⟨i₀', hi₀', hne⟩ := hk
  have hkm : k < m := lt_of_le_of_lt hi₀' i₀'.2
  obtain ⟨k', hk'⟩ : ∃ k' : Fin m, (k' : ℕ) = k := ⟨⟨k, hkm⟩, rfl⟩
  have hS : ∃ j, ∃ i : Fin m, k ≤ (i : ℕ) ∧ B i j ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact ⟨j, i₀', hi₀', hj⟩
  obtain ⟨j, ⟨i₀, hi₀, ha⟩, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min {j | ∃ i : Fin m, k ≤ (i : ℕ) ∧ B i j ≠ 0} hS
  have hpend : ∀ i : Fin m, k ≤ (i : ℕ) → ∀ j', j' < j → B i j' = 0 := by
    intro i hi j' hj'
    by_contra hb
    exact hmin j' ⟨i, hi, hb⟩ hj'
  have hlj : ∀ i : Fin m, (i : ℕ) < k → l i < j := by
    intro i hi
    by_contra hge
    exact ha (hI.rest_zero i hi i₀ hi₀ j (not_lt.mp hge))
  have hne_k : ∀ i : Fin m, (i : ℕ) < k → i ≠ k' := by
    intro i hi h; subst h; omega
  -- step 1: swap
  obtain ⟨B1, hB1⟩ : ∃ B1, B1 = Matrix.swap K k' i₀ * B := ⟨_, rfl⟩
  have hB1e : ∀ i j', B1 i j' = B (Equiv.swap k' i₀ i) j' := by
    intro i j'; rw [hB1]; exact swap_mul_apply_eq _ _ _ _ _
  have hσk : ∀ i : Fin m, (i : ℕ) < k → Equiv.swap k' i₀ i = i := by
    intro i hi
    apply Equiv.swap_apply_of_ne_of_ne (hne_k i hi)
    intro h; subst h; omega
  have hσp : ∀ i : Fin m, k ≤ (i : ℕ) → k ≤ ((Equiv.swap k' i₀ i : Fin m) : ℕ) := by
    intro i hi
    by_cases h1 : i = k'
    · subst h1; rw [Equiv.swap_apply_left]; exact hi₀
    · by_cases h2 : i = i₀
      · subst h2; rw [Equiv.swap_apply_right]; omega
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hi
  have hr1 : RowEquivalent B B1 := by rw [hB1]; exact rowEquivalent_swap _ _ _
  -- step 2: scale
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = (B i₀ j)⁻¹ := ⟨Units.mk0 _ (inv_ne_zero ha), rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B2, B2 = Matrix.rowScale k' (u : K) * B1 := ⟨_, rfl⟩
  have hr2 : RowEquivalent B1 B2 := by rw [hB2]; exact rowEquivalent_rowScale _ _ _
  have hB2e : ∀ i j', B2 i j' = (if i = k' then (B i₀ j)⁻¹ else 1) * B1 i j' := by
    intro i j'
    rw [hB2, rowScale_mul]
    by_cases h : i = k'
    · subst h; simp [hu]
    · simp [h, Matrix.updateRow_ne h]
  obtain ⟨p, hp⟩ : ∃ p : Fin n → K, p = B2 k' := ⟨_, rfl⟩
  have hpj : p j = 1 := by
    rw [hp, hB2e]; simp [hB1e, ha]
  have hpl : ∀ j', j' < j → p j' = 0 := by
    intro j' hj'
    rw [hp, hB2e]; simp [hB1e, hpend i₀ hi₀ j' hj']
  have hB2old : ∀ i : Fin m, (i : ℕ) < k → ∀ j', B2 i j' = B i j' := by
    intro i hi j'
    rw [hB2e, if_neg (hne_k i hi), one_mul, hB1e, hσk i hi]
  have hB2pend : ∀ i : Fin m, k ≤ (i : ℕ) → ∀ j', j' < j → B2 i j' = 0 := by
    intro i hi j' hj'
    rw [hB2e, hB1e, hpend _ (hσp i hi) j' hj']; simp
  -- step 3: clear the pivot column
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin m) (Fin m) K,
      N = Matrix.of fun i i' => if i' = k' ∧ i ≠ k' then B2 i j else 0 := ⟨_, rfl⟩
  have hNN : N * N = 0 := by
    ext i i'
    simp only [Matrix.mul_apply, hN, Matrix.of_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = k'
    · subst hx; simp
    · simp [hx]
  have hT : IsUnit (1 - N) := by
    refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, rfl⟩
    · have : (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
      rw [this, hNN, sub_zero]
    · have : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      rw [this, hNN, sub_zero]
  obtain ⟨B3, hB3⟩ : ∃ B3, B3 = (1 - N) * B2 := ⟨_, rfl⟩
  have hr3 : RowEquivalent B2 B3 := by rw [hB3]; exact rowEquivalent_of_isUnit hT _
  have hB3e : ∀ i j', B3 i j' = B2 i j' - (if i = k' then 0 else B2 i j) * p j' := by
    intro i j'
    rw [hB3, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hp]
    congr 1
    simp only [Matrix.mul_apply, hN, Matrix.of_apply]
    rw [Finset.sum_eq_single k']
    · by_cases h : i = k' <;> simp [h]
    · intro x _ hx; simp [hx]
    · simp
  have hB3k : ∀ j', B3 k' j' = p j' := by
    intro j'; rw [hB3e]; simp [hp]
  have hB3c : ∀ i : Fin m, i ≠ k' → ∀ j', B3 i j' = B2 i j' - B2 i j * p j' := by
    intro i hi j'; rw [hB3e, if_neg hi]
  have hB3old : ∀ i : Fin m, (i : ℕ) < k → ∀ j', B3 i j' = B i j' - B i j * p j' := by
    intro i hi j'; rw [hB3c i (hne_k i hi), hB2old i hi, hB2old i hi]
  have hclear : ∀ i : Fin m, i ≠ k' → B3 i j = 0 := by
    intro i hi; rw [hB3c i hi, hpj]; simp
  have hrest : ∀ i : Fin m, k + 1 ≤ (i : ℕ) → ∀ j', j' ≤ j → B3 i j' = 0 := by
    intro i hi j' hj'
    have hik : i ≠ k' := by intro h; subst h; omega
    rcases hj'.lt_or_eq with h | h
    · rw [hB3c i hik, hB2pend i (by omega) j' h, hpl j' h]; simp
    · subst h; exact hclear i hik
  refine ⟨B3, Function.update l k' j, hr1.trans (hr2.trans hr3), ?_⟩
  have hl_old : ∀ i : Fin m, (i : ℕ) < k → Function.update l k' j i = l i := by
    intro i hi; exact Function.update_of_ne (hne_k i hi) _ _
  have hl_new : Function.update l k' j k' = j := by simp
  have hcases : ∀ i : Fin m, (i : ℕ) < k + 1 → i = k' ∨ (i : ℕ) < k := by
    intro i hi
    by_cases h : (i : ℕ) < k
    · exact Or.inr h
    · left; apply Fin.ext; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j' hj'
    rcases hcases i hi with rfl | hi'
    · rw [hl_new] at hj'; rw [hB3k]; exact hpl j' hj'
    · rw [hl_old i hi'] at hj'
      rw [hB3old i hi', hpl j' (lt_trans hj' (hlj i hi')), hI.zero_before i hi' j' hj']; simp
  · intro i hi
    rcases hcases i hi with rfl | hi'
    · rw [hl_new, hB3k]; exact hpj
    · rw [hl_old i hi', hB3old i hi', hpl _ (hlj i hi'), hI.one_at i hi']; simp
  · intro i hi i' hi'
    rcases hcases i hi with rfl | hi2
    · rw [hl_new]; exact hclear i' hi'
    · rw [hl_old i hi2]
      by_cases h : i' = k'
      · subst h; rw [hB3k]; exact hpl _ (hlj i hi2)
      · rw [hB3c i' h, hpl _ (hlj i hi2)]
        have : B2 i' (l i) = 0 := by
          by_cases h3 : (i' : ℕ) < k
          · rw [hB2old i' h3]; exact hI.col_zero i hi2 i' hi'
          · exact hB2pend i' (not_lt.mp h3) _ (hlj i hi2)
        simp [this]
  · intro i hi i' hi' j' hj'
    rcases hcases i hi with rfl | hi2
    · rw [hl_new] at hj'; exact hrest i' hi' j' hj'
    · rw [hl_old i hi2] at hj'
      exact hrest i' hi' j' (le_of_lt (lt_of_le_of_lt hj' (hlj i hi2)))
  · intro i1 i2 h12 h2
    rcases hcases i2 h2 with rfl | h2'
    · rw [hl_new, hl_old i1 (by omega)]; exact hlj i1 (by omega)
    · rw [hl_old i1 (by omega), hl_old i2 h2']; exact hI.mono i1 i2 h12 h2'

theorem sweep_aux (d : ℕ) : ∀ (B : Matrix (Fin m) (Fin n) K) (k : ℕ) (l : Fin m → Fin n),
    m - k = d → SweepInv B k l → ∃ R, RowEquivalent B R ∧ R.IsReducedRowEchelon := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro B k l hd hI
    by_cases hk : ∃ i : Fin m, k ≤ (i : ℕ) ∧ B i ≠ 0
    · obtain ⟨B', l', hr, hI'⟩ := sweep_step B k l hI hk
      obtain ⟨i, hi, _⟩ := hk
      have : m - (k + 1) < d := by have := i.2; omega
      obtain ⟨R, hR1, hR2⟩ := ih _ this B' (k + 1) l' rfl hI'
      exact ⟨R, hr.trans hR1, hR2⟩
    · push Not at hk
      exact ⟨B, RowEquivalent.refl B, hI.isReduced hk⟩

/-- Gauss-Jordan reduction: every matrix over a field is row equivalent to a reduced echelon form
matrix (Hefferon's Gauss-Jordan reduction, which scales leading entries to one and clears
the columns above them). -/
@[kb "hefferon2020" "One.III.1.GaussJordan, p. 61"]
theorem hefferon_One_III_1_GaussJordan (A : Matrix (Fin m) (Fin n) K) :
    ∃ R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsReducedRowEchelon :=
  by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨A, RowEquivalent.refl A, ?_⟩
    exact ⟨fun _ _ _ j => j.elim0, fun _ c => c.elim0, fun _ _ c => c.elim0⟩
  · exact sweep_aux (m - 0) A 0 (fun _ => ⟨0, hn⟩) rfl
      { zero_before := fun i hi => absurd hi (Nat.not_lt_zero _)
        one_at := fun i hi => absurd hi (Nat.not_lt_zero _)
        col_zero := fun i hi => absurd hi (Nat.not_lt_zero _)
        rest_zero := fun i hi => absurd hi (Nat.not_lt_zero _)
        mono := fun _ _ _ hi => absurd hi (Nat.not_lt_zero _) }

/-! ### Uniqueness of the reduced echelon form -/

theorem exists_isPivotedBy {R : Matrix (Fin m) (Fin n) K} (hE : R.IsRowEchelon) :
    ∃ l : Fin m → WithTop (Fin n), R.IsPivotedBy l := by
  classical
  refine ⟨fun i => if h : R i = 0 then ⊤ else
    ((Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp h).choose : WithTop (Fin n)), hE, ?_⟩
  intro i
  by_cases h : R i = 0
  · simp only [h, dite_true]
    refine ⟨fun j _ => by simp, fun c hc => by simp at hc⟩
  · simp only [h, dite_false]
    have hc := (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp h).choose_spec
    refine ⟨fun j hj => hc.1 j (by exact_mod_cast hj), fun c hc' => ?_⟩
    have : (Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp h).choose = c := by exact_mod_cast hc'
    rw [← this]; exact hc.2

/-- In a reduced echelon matrix, the coefficient of a nonzero row in a combination of rows is read
off from the pivot column. -/
theorem vecMul_pivot_col {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon)
    {l : Fin m → WithTop (Fin n)} (hl : R.IsPivotedBy l) (c : Fin m → K) {i : Fin m} {col : Fin n}
    (hi : l i = ↑col) : (c ᵥ* R) col = c i := by
  have hlead := hl.isLeadingEntry hi
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hR.eq_one hlead]; simp
  · intro k _ hk
    rw [hR.eq_zero_of_ne_of_isLeadingEntry hk hlead]; simp
  · simp

/-- Leading positions of rows in the row space of an echelon matrix are leading positions of its rows. -/
theorem lead_mem_of_vecMul {R R' : Matrix (Fin m) (Fin n) K} {l' : Fin m → WithTop (Fin n)}
    (hl' : R'.IsPivotedBy l') {i : Fin m} {c : Fin m → K} (hRi : R i = c ᵥ* R') {c0 : Fin n}
    (hlead : R.IsLeadingEntry i c0) : ∃ k, l' k = ↑c0 := by
  have hne : R i ≠ 0 := hlead.row_ne_zero
  have hv : ∀ j, R i j = ∑ k, c k * R' k j := by
    intro j; rw [hRi]; simp [Matrix.vecMul, dotProduct]
  have hS : ∃ k, c k ≠ 0 ∧ R' k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext j
    rw [hv]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : c k = 0
    · simp [hk]
    · simp [h k hk]
  obtain ⟨k0, ⟨hck, hRk⟩, hmin⟩ :=
    (wellFounded_lt (α := Fin m)).has_min {k | c k ≠ 0 ∧ R' k ≠ 0} hS
  have hl'k0 : l' k0 ≠ ⊤ := fun h => hRk (hl'.eq_top_iff.mp h)
  obtain ⟨c1, hc1⟩ := WithTop.ne_top_iff_exists.mp hl'k0
  have lead1 : R'.IsLeadingEntry k0 c1 := hl'.isLeadingEntry hc1.symm
  have hterm_lt : ∀ k, ∀ j, j < c1 → c k * R' k j = 0 := by
    intro k j hj
    by_cases hk : c k = 0
    · simp [hk]
    by_cases hk' : R' k = 0
    · simp [hk']
    have hk0 : k0 ≤ k := not_lt.mp (fun h => hmin k ⟨hk, hk'⟩ h)
    have h1 : l' k0 ≤ l' k := hl'.monotone hk0
    have : (j : WithTop (Fin n)) < l' k := by
      refine lt_of_lt_of_le ?_ h1
      rw [← hc1]; exact_mod_cast hj
    rw [(hl'.isPivotEntry k).1 j this]; simp
  have hterm_at : ∀ k, k ≠ k0 → c k * R' k c1 = 0 := by
    intro k hkk
    by_cases hk : c k = 0
    · simp [hk]
    by_cases hk' : R' k = 0
    · simp [hk']
    have hk0 : k0 < k := lt_of_le_of_ne (not_lt.mp (fun h => hmin k ⟨hk, hk'⟩ h)) (Ne.symm hkk)
    have hk'' : l' k ≠ ⊤ := fun h => hk' (hl'.eq_top_iff.mp h)
    have h1 : l' k0 < l' k := hl'.strictMonoOn hl'k0 hk'' hk0
    have : (c1 : WithTop (Fin n)) < l' k := by rw [hc1]; exact h1
    rw [(hl'.isPivotEntry k).1 c1 this]; simp
  have hlead1 : R.IsLeadingEntry i c1 := by
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hv]; exact Finset.sum_eq_zero fun k _ => hterm_lt k j hj
    · rw [hv, Finset.sum_eq_single k0 (fun k _ hk => hterm_at k hk) (by simp)]
      exact mul_ne_zero hck lead1.2
  have := hlead.unique hlead1
  exact ⟨k0, by rw [← hc1, this]⟩

theorem pivots_eq_of_vecMul {R R' : Matrix (Fin m) (Fin n) K} {l l' : Fin m → WithTop (Fin n)}
    (hl : R.IsPivotedBy l) (hl' : R'.IsPivotedBy l')
    (h1 : ∀ i, ∃ c : Fin m → K, R i = c ᵥ* R') (h2 : ∀ i, ∃ c : Fin m → K, R' i = c ᵥ* R) :
    l = l' := by
  have A1 : ∀ i, l i ≠ ⊤ → ∃ k, l' k = l i := by
    intro i hi
    obtain ⟨c0, hc0⟩ := WithTop.ne_top_iff_exists.mp hi
    obtain ⟨c, hc⟩ := h1 i
    obtain ⟨k, hk⟩ := lead_mem_of_vecMul hl' hc (hl.isLeadingEntry hc0.symm)
    exact ⟨k, by rw [hk, hc0]⟩
  have A2 : ∀ i, l' i ≠ ⊤ → ∃ k, l k = l' i := by
    intro i hi
    obtain ⟨c0, hc0⟩ := WithTop.ne_top_iff_exists.mp hi
    obtain ⟨c, hc⟩ := h2 i
    obtain ⟨k, hk⟩ := lead_mem_of_vecMul hl hc (hl'.isLeadingEntry hc0.symm)
    exact ⟨k, by rw [hk, hc0]⟩
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rcases lt_trichotomy (l i) (l' i) with hlt | heq | hgt
    · exfalso
      have hi : l i ≠ ⊤ := hlt.ne_top
      obtain ⟨k, hk⟩ := A1 i hi
      have hki : k < i := by
        by_contra hnot
        have := hl'.monotone (not_lt.mp hnot)
        rw [hk] at this
        exact absurd hlt (not_lt.mpr this)
      have hlk : l k = l i := by rw [ih k hki, hk]
      have hk1 : l k ≠ ⊤ := by rw [hlk]; exact hi
      exact absurd hlk (hl.strictMonoOn hk1 hi hki).ne
    · exact heq
    · exfalso
      have hi : l' i ≠ ⊤ := hgt.ne_top
      obtain ⟨k, hk⟩ := A2 i hi
      have hki : k < i := by
        by_contra hnot
        have := hl.monotone (not_lt.mp hnot)
        rw [hk] at this
        exact absurd hgt (not_lt.mpr this)
      have hlk : l' k = l' i := by rw [← ih k hki, hk]
      have hk1 : l' k ≠ ⊤ := by rw [hlk]; exact hi
      exact absurd hlk (hl'.strictMonoOn hk1 hi hki).ne

theorem rowEquivalent_vecMul {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    ∀ i, ∃ c : Fin m → K, B i = c ᵥ* A := by
  obtain ⟨g, rfl⟩ := h
  intro i
  refine ⟨(g : Matrix (Fin m) (Fin m) K) i, ?_⟩
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- Row equivalent reduced echelon matrices are equal. -/
theorem eq_of_rowEquivalent_of_reduced {R R' : Matrix (Fin m) (Fin n) K}
    (hR : R.IsReducedRowEchelon) (hR' : R'.IsReducedRowEchelon) (h : RowEquivalent R R') :
    R = R' := by
  obtain ⟨l, hl⟩ := exists_isPivotedBy hR.isRowEchelon
  obtain ⟨l', hl'⟩ := exists_isPivotedBy hR'.isRowEchelon
  have hll := pivots_eq_of_vecMul hl hl' (rowEquivalent_vecMul h.symm) (rowEquivalent_vecMul h)
  subst hll
  ext i j
  obtain ⟨c, hc⟩ := rowEquivalent_vecMul h.symm i
  by_cases hi : l i = ⊤
  · rw [hl.eq_top_iff.mp hi]
    rw [hl'.eq_top_iff.mp hi]
  · rw [hc]
    simp only [Matrix.vecMul, dotProduct]
    have : ∀ k, c k * R' k j = (if k = i then 1 else 0) * R' k j := by
      intro k
      by_cases hk : l k = ⊤
      · rw [hl'.eq_top_iff.mp hk]; simp
      obtain ⟨col, hcol⟩ := WithTop.ne_top_iff_exists.mp hk
      have e1 : c k = R i col := by
        have := vecMul_pivot_col hR' hl' c hcol.symm
        rw [← hc] at this
        exact this.symm
      rw [e1]
      by_cases hki : k = i
      · subst hki; rw [hR.eq_one (hl.isLeadingEntry hcol.symm)]; simp
      · rw [hR.eq_zero_of_ne_of_isLeadingEntry (Ne.symm hki) (hl.isLeadingEntry hcol.symm)]; simp [hki]
    simp [this]

/-- Existence and uniqueness of the reduced echelon form: every matrix is row equivalent to exactly one
reduced echelon matrix. -/
@[kb "hefferon2020" "One.III.2.6, p. 69"]
theorem hefferon_One_III_2_6 (A : Matrix (Fin m) (Fin n) K) :
    ∃! R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsReducedRowEchelon := by
  obtain ⟨R, h1, h2⟩ := hefferon_One_III_1_GaussJordan A
  refine ⟨R, ⟨h1, h2⟩, ?_⟩
  rintro R' ⟨h1', h2'⟩
  exact (eq_of_rowEquivalent_of_reduced h2 h2' (h1.symm.trans h1')).symm

/-! ### Elementary matrices and products of them -/

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hefferon's elementary reduction matrices: the identity with one row operation applied (swap two rows,
scale a row by a nonzero constant, add a multiple of one row to a different row). -/
inductive IsElementary : Matrix ι ι K → Prop
  | swap (i j : ι) : IsElementary (Matrix.swap K i j)
  | scale (i : ι) (c : K) (hc : c ≠ 0) : IsElementary (Matrix.rowScale i c)
  | transvec (i j : ι) (h : i ≠ j) (c : K) : IsElementary (Matrix.transvection i j c)

theorem IsElementary.isUnit {E : Matrix ι ι K} (h : IsElementary E) : IsUnit E := by
  cases h with
  | swap i j => exact ⟨⟨_, _, swap_mul_self i j, swap_mul_self i j⟩, rfl⟩
  | scale i c hc => exact ⟨Matrix.GeneralLinearGroup.rowScale (R := K) i (Units.mk0 c hc), rfl⟩
  | transvec i j h c => exact ⟨Matrix.GeneralLinearGroup.transvection (R := K) i j h c, rfl⟩

theorem isUnit_list_prod {L : List (Matrix ι ι K)} (h : ∀ E ∈ L, IsElementary E) :
    IsUnit L.prod := by
  induction L with
  | nil => simp
  | cons E L ih =>
    rw [List.prod_cons]
    exact (h E (by simp)).isUnit.mul (ih fun E' hE' => h E' (by simp [hE']))

theorem diagonal_mem_elementary_prod (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    ∃ L : List (Matrix ι ι K), (∀ E ∈ L, IsElementary E) ∧ Matrix.diagonal D = L.prod := by
  classical
  have key : ∀ s : Finset ι, ∃ L : List (Matrix ι ι K), (∀ E ∈ L, IsElementary E) ∧
      Matrix.diagonal (fun i => if i ∈ s then D i else 1) = L.prod := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨[], by simp, by simp⟩
    | insert a s ha ih =>
      obtain ⟨L, hL, hLp⟩ := ih
      refine ⟨Matrix.rowScale a (D a) :: L, ?_, ?_⟩
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE
        · exact IsElementary.scale a _ (hD a)
        · exact hL E hE
      · rw [List.prod_cons, ← hLp, Matrix.rowScale, Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        by_cases hi : i = a
        · subst hi; simp [ha]
        · simp [hi, Pi.mulSingle_eq_of_ne hi]
  obtain ⟨L, hL, hLp⟩ := key Finset.univ
  exact ⟨L, hL, by simpa using hLp⟩

/-- A matrix over a field is invertible exactly when it is a product of elementary reduction matrices. -/
@[kb "hefferon2020" "Three.IV.4.7, p. 268"]
theorem hefferon_Three_IV_4_7 (M : Matrix ι ι K) :
    IsUnit M ↔ ∃ L : List (Matrix ι ι K), (∀ E ∈ L, IsElementary E) ∧ M = L.prod := by
  constructor
  · intro h
    have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp h).ne_zero
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun N => ∃ L : List (Matrix ι ι K), (∀ E ∈ L, IsElementary E) ∧ N = L.prod) M hdet ?_ ?_ ?_
    · intro D hD
      exact diagonal_mem_elementary_prod D
        (fun i => (Finset.prod_ne_zero_iff.mp (by simpa [Matrix.det_diagonal] using hD)) i
          (Finset.mem_univ i))
    · intro t
      refine ⟨[Matrix.transvection t.i t.j t.c], ?_, by simp [Matrix.TransvectionStruct.toMatrix]⟩
      intro E hE
      rw [List.mem_singleton] at hE
      subst hE
      exact IsElementary.transvec _ _ t.hij _
    · rintro A B - - ⟨L1, h1, rfl⟩ ⟨L2, h2, rfl⟩
      refine ⟨L1 ++ L2, ?_, by simp⟩
      intro E hE
      rcases List.mem_append.mp hE with hE | hE
      · exact h1 E hE
      · exact h2 E hE
  · rintro ⟨L, hL, rfl⟩
    exact isUnit_list_prod hL

end Elementary

/-- Every matrix over a field is turned into its reduced echelon form by multiplying on the left with a
product of elementary reduction matrices. -/
@[kb "hefferon2020" "Three.IV.3.23, p. 261"]
theorem hefferon_Three_IV_3_23 (H : Matrix (Fin m) (Fin n) K) :
    ∃ L : List (Matrix (Fin m) (Fin m) K), (∀ E ∈ L, IsElementary E) ∧
      (L.prod * H).IsReducedRowEchelon := by
  obtain ⟨R, ⟨g, rfl⟩, hR⟩ := hefferon_One_III_1_GaussJordan H
  obtain ⟨L, hL, hg⟩ := (hefferon_Three_IV_4_7 (g : Matrix (Fin m) (Fin m) K)).mp g.isUnit
  exact ⟨L, hL, by rw [← hg]; exact hR⟩

/-- Row equivalence is exactly the relation "obtained by a sequence of elementary row operations". -/
@[kb "hefferon2020" "One.III.1.7, p. 63"]
theorem hefferon_One_III_1_7 (A B : Matrix (Fin m) (Fin n) K) :
    RowEquivalent A B ↔
      ∃ L : List (Matrix (Fin m) (Fin m) K), (∀ E ∈ L, IsElementary E) ∧ B = L.prod * A := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨L, hL, hg⟩ := (hefferon_Three_IV_4_7 (g : Matrix (Fin m) (Fin m) K)).mp g.isUnit
    exact ⟨L, hL, by rw [← hg]; rfl⟩
  · rintro ⟨L, hL, rfl⟩
    exact rowEquivalent_of_isUnit (isUnit_list_prod hL) A

/-- Row reducibility is an equivalence relation on the matrices of a fixed size. -/
@[kb "hefferon2020" "One.III.1.6, p. 63"]
theorem hefferon_One_III_1_6 :
    Equivalence (fun A B : Matrix (Fin m) (Fin n) K => RowEquivalent A B) :=
  ⟨RowEquivalent.refl, RowEquivalent.symm, RowEquivalent.trans⟩

/-! ### Row operations and solution sets -/

theorem solutionSet_eq_of_isUnit {P : Matrix (Fin m) (Fin m) K} (hP : IsUnit P)
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    {x | A *ᵥ x = b} = {x | (P * A) *ᵥ x = P *ᵥ b} := by
  ext x
  simp only [Set.mem_setOf_eq, ← Matrix.mulVec_mulVec]
  exact ⟨fun h => by rw [h], fun h => Matrix.mulVec_injective_iff_isUnit.mpr hP h⟩

/-- Gauss's Method is safe: each of the three row operations leaves the solution set of the system
`A x = b` unchanged. -/
@[kb "hefferon2020" "One.I.1.5, p. 14"]
theorem hefferon_One_I_1_5 (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (i j : Fin m) :
    {x | A *ᵥ x = b} = {x | (Matrix.swap K i j * A) *ᵥ x = Matrix.swap K i j *ᵥ b} ∧
    (∀ c : K, c ≠ 0 →
      {x | A *ᵥ x = b} = {x | (Matrix.rowScale i c * A) *ᵥ x = Matrix.rowScale i c *ᵥ b}) ∧
    (i ≠ j → ∀ c : K,
      {x | A *ᵥ x = b} =
        {x | (Matrix.transvection i j c * A) *ᵥ x = Matrix.transvection i j c *ᵥ b}) :=
  ⟨solutionSet_eq_of_isUnit (IsElementary.swap i j).isUnit A b,
   fun c hc => solutionSet_eq_of_isUnit (IsElementary.scale i c hc).isUnit A b,
   fun h c => solutionSet_eq_of_isUnit (IsElementary.transvec i j h c).isUnit A b⟩

/-- Row operations are reversible: a swap is undone by the same swap, scaling by `c` by scaling by `c⁻¹`,
and adding `c` times row `i` to row `j` by adding `-c` times it. -/
@[kb "hefferon2020" "One.III.1.5, p. 62"]
theorem hefferon_One_III_1_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (c : K) :
    Matrix.swap K i j * Matrix.swap K i j = 1 ∧
    (c ≠ 0 → Matrix.rowScale i c * Matrix.rowScale i c⁻¹ = 1) ∧
    (i ≠ j → Matrix.transvection i j c * Matrix.transvection i j (-c) = 1) := by
  refine ⟨swap_mul_self i j, fun hc => ?_, fun h => ?_⟩
  · rw [Matrix.rowScale_mul_rowScale, mul_inv_cancel₀ hc, Matrix.rowScale_one]
  · simpa using Matrix.transvection_mul_transvection_same i j h c (-c)

/-- The three kinds of elementary reduction matrix act on the rows of a matrix as the corresponding row
operation: scaling row `i`, swapping rows `i` and `j`, adding `c` times row `j` to row `i`. -/
@[kb "hefferon2020" "Three.IV.3.19, p. 260"]
theorem hefferon_Three_IV_3_19 {ι : Type*} [Fintype ι] [DecidableEq ι] {p : Type*}
    (M : Matrix ι p K) (i j : ι) (c : K) :
    Matrix.rowScale i c * M = M.updateRow i (c • M i) ∧
    (Matrix.swap K i j * M) i = M j ∧ (Matrix.swap K i j * M) j = M i ∧
    (i ≠ j → Matrix.transvection i j c * M = M.updateRow i (M i + c • M j)) := by
  refine ⟨Matrix.rowScale_mul i c M, ?_, ?_, fun h => ?_⟩
  · funext b; simp
  · funext b; simp
  · ext a b
    by_cases ha : a = i
    · subst ha; simp
    · rw [Matrix.transvection_mul_apply_of_ne i j a b ha]; simp [ha]

/-! ### Row spaces and ranks -/

theorem vecMul_mem_span_rows (A : Matrix (Fin m) (Fin n) K) (c : Fin m → K) :
    c ᵥ* A ∈ Submodule.span K (Set.range A) := by
  have : c ᵥ* A = ∑ k, c k • A k := by
    ext j; simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Rows of a row-equivalent matrix are linear combinations of the rows of the original. -/
@[kb "hefferon2020" "One.III.2.4, p. 67"]
theorem hefferon_One_III_2_4 {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    ∀ i, ∃ c : Fin m → K, B i = ∑ k, c k • A k := by
  intro i
  obtain ⟨c, hc⟩ := rowEquivalent_vecMul h i
  refine ⟨c, ?_⟩
  rw [hc]; ext j; simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem span_rows_le_of_rowEquivalent {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    Submodule.span K (Set.range B) ≤ Submodule.span K (Set.range A) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := rowEquivalent_vecMul h i
  show B i ∈ _
  rw [hc]; exact vecMul_mem_span_rows A c

theorem rank_eq_of_rowEquivalent {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    A.rank = B.rank := by
  obtain ⟨g, rfl⟩ := h
  exact (Matrix.rank_mul_eq_right_of_isUnit_det (g : Matrix (Fin m) (Fin m) K) A
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)).symm

/-- Row operations do not change the row space; hence row equivalent matrices have equal row spaces and
equal row rank. -/
@[kb "hefferon2020" "Two.III.3.3, p. 146"]
theorem hefferon_Two_III_3_3 {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    Submodule.span K (Set.range A) = Submodule.span K (Set.range B) ∧
    Module.finrank K (Submodule.span K (Set.range A)) =
      Module.finrank K (Submodule.span K (Set.range B)) := by
  have : Submodule.span K (Set.range A) = Submodule.span K (Set.range B) :=
    le_antisymm (span_rows_le_of_rowEquivalent h.symm) (span_rows_le_of_rowEquivalent h)
  exact ⟨this, by rw [this]⟩

/-- Row operations do not change the column rank. -/
@[kb "hefferon2020" "Two.III.3.10, p. 149"]
theorem hefferon_Two_III_3_10 {A B : Matrix (Fin m) (Fin n) K} (h : RowEquivalent A B) :
    Module.finrank K (Submodule.span K (Set.range Aᵀ)) =
      Module.finrank K (Submodule.span K (Set.range Bᵀ)) ∧ A.rank = B.rank := by
  refine ⟨?_, rank_eq_of_rowEquivalent h⟩
  have h1 : Module.finrank K (Submodule.span K (Set.range Aᵀ)) = A.rank :=
    ((Matrix.rank_eq_finrank_span_row Aᵀ).symm.trans (Matrix.rank_transpose A))
  have h2 : Module.finrank K (Submodule.span K (Set.range Bᵀ)) = B.rank :=
    ((Matrix.rank_eq_finrank_span_row Bᵀ).symm.trans (Matrix.rank_transpose B))
  rw [h1, h2]; exact rank_eq_of_rowEquivalent h

/-! ### Independence of echelon rows -/

theorem nonzeroRows_linearIndependent {R : Matrix (Fin m) (Fin n) K} (hE : R.IsRowEchelon) :
    LinearIndependent K (fun i : {i : Fin m // R i ≠ 0} => R i) := by
  classical
  obtain ⟨l, hl⟩ := exists_isPivotedBy hE
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hspan : Submodule.span K (Set.range (fun i : {i : Fin m // R i ≠ 0} => R i)) =
      Submodule.span K (Set.range R) := by
    apply le_antisymm
    · exact Submodule.span_mono (Set.range_subset_iff.mpr fun i => ⟨i.1, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : R i = 0
      · rw [h]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩
  have hr : Module.finrank K (Submodule.span K (Set.range R)) = R.rank :=
    (Matrix.rank_eq_finrank_span_row R).symm
  show Fintype.card _ = Module.finrank K (Submodule.span K _)
  rw [hspan, hr, hl.rank_eq, Fintype.card_subtype]
  congr 1
  ext i
  simp [hl.eq_top_iff]

/-- The nonzero rows of an echelon form matrix are linearly independent. -/
@[kb "hefferon2020" "Two.III.3.4, p. 147"]
theorem hefferon_Two_III_3_4 {R : Matrix (Fin m) (Fin n) K} (hE : R.IsRowEchelon) :
    LinearIndependent K (fun i : {i : Fin m // R i ≠ 0} => R i) :=
  nonzeroRows_linearIndependent hE

/-- Gauss's Method yields a basis of the row space: the nonzero rows of an echelon form of `A` are
linearly independent and span the row space of `A`. -/
@[kb "hefferon2020" "Two.III.3.5, p. 147"]
theorem hefferon_Two_III_3_5 (A : Matrix (Fin m) (Fin n) K) :
    ∃ R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsRowEchelon ∧
      LinearIndependent K (fun i : {i : Fin m // R i ≠ 0} => R i) ∧
      Submodule.span K (Set.range (fun i : {i : Fin m // R i ≠ 0} => R i)) =
        Submodule.span K (Set.range A) := by
  obtain ⟨R, hAR, hR⟩ := hefferon_One_III_1_GaussJordan A
  refine ⟨R, hAR, hR.isRowEchelon, nonzeroRows_linearIndependent hR.isRowEchelon, ?_⟩
  rw [(hefferon_Two_III_3_3 hAR).1]
  apply le_antisymm
  · exact Submodule.span_mono (Set.range_subset_iff.mpr fun i => ⟨i.1, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases h : R i = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

/-- Two echelon forms of the same matrix have the same pivot columns, hence the same free variables. -/
@[kb "hefferon2020" "One.III.2.7, p. 70"]
theorem hefferon_One_III_2_7 {A R₁ R₂ : Matrix (Fin m) (Fin n) K} (h₁ : RowEquivalent A R₁)
    (h₂ : RowEquivalent A R₂) (e₁ : R₁.IsRowEchelon) (e₂ : R₂.IsRowEchelon) (j : Fin n) :
    (∃ i, R₁.IsLeadingEntry i j) ↔ (∃ i, R₂.IsLeadingEntry i j) := by
  obtain ⟨l₁, hl₁⟩ := exists_isPivotedBy e₁
  obtain ⟨l₂, hl₂⟩ := exists_isPivotedBy e₂
  have h12 : RowEquivalent R₁ R₂ := h₁.symm.trans h₂
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨c, hc⟩ := rowEquivalent_vecMul h12.symm i
    obtain ⟨k, hk⟩ := lead_mem_of_vecMul hl₂ hc hi
    exact ⟨k, hl₂.isLeadingEntry hk⟩
  · rintro ⟨i, hi⟩
    obtain ⟨c, hc⟩ := rowEquivalent_vecMul h12 i
    obtain ⟨k, hk⟩ := lead_mem_of_vecMul hl₁ hc hi
    exact ⟨k, hl₁.isLeadingEntry hk⟩

/-! ### Solving a reduced echelon system -/

section Free

open scoped Classical

/-- A column is a free-variable column when no row has its leading entry there. -/
def IsFreeColumn (R : Matrix (Fin m) (Fin n) K) (j : Fin n) : Prop :=
  ∀ i, ¬ R.IsLeadingEntry i j

theorem mulVec_eq_lead_add_free {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon)
    (x : Fin n → K) (i : Fin m) :
    (R *ᵥ x) i = (∑ j, if R.IsLeadingEntry i j then x j else 0) +
      ∑ j, if IsFreeColumn R j then R i j * x j else 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hf : IsFreeColumn R j
  · have : ¬ R.IsLeadingEntry i j := hf i
    simp [hf, this]
  · have hf' := hf
    unfold IsFreeColumn at hf'
    push Not at hf'
    obtain ⟨k, hk⟩ := hf'
    by_cases hi : R.IsLeadingEntry i j
    · simp [hf, hi, hR.eq_one hi]
    · have hik : i ≠ k := by rintro rfl; exact hi hk
      rw [hR.eq_zero_of_ne_of_isLeadingEntry hik hk]; simp [hi]

theorem lead_sum_eq {R : Matrix (Fin m) (Fin n) K} (x : Fin n → K) {i : Fin m} {c : Fin n}
    (hc : R.IsLeadingEntry i c) : (∑ j, if R.IsLeadingEntry i j then x j else 0) = x c := by
  rw [Finset.sum_eq_single c]
  · simp [hc]
  · intro j _ hj
    have : ¬ R.IsLeadingEntry i j := fun h => hj (h.unique hc)
    simp [this]
  · simp

theorem lead_sum_eq_zero {R : Matrix (Fin m) (Fin n) K} (x : Fin n → K) {i : Fin m}
    (hi : R i = 0) : (∑ j, if R.IsLeadingEntry i j then x j else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have : ¬ R.IsLeadingEntry i j := fun h => h.row_ne_zero hi
  simp [this]

theorem free_sum_eq_zero {R : Matrix (Fin m) (Fin n) K} (x : Fin n → K) {i : Fin m}
    (hi : R i = 0) : (∑ j, if IsFreeColumn R j then R i j * x j else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [hi]

/-- Solving a reduced echelon system: a vector solves `R x = b` exactly when `b` vanishes on the zero rows
of `R` and each leading variable equals the right-hand side minus the contribution of the free variables
(the leading variables are expressed through the free ones). -/
@[kb "hefferon2020" "One.I.2.2, p. 23"]
theorem hefferon_One_I_2_2 {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon)
    (b : Fin m → K) (x : Fin n → K) :
    R *ᵥ x = b ↔ (∀ i, R i = 0 → b i = 0) ∧
      ∀ i c, R.IsLeadingEntry i c →
        x c = b i - ∑ j, if IsFreeColumn R j then R i j * x j else 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i c hc => ?_⟩
    · rw [← congrFun h i, Matrix.mulVec, dotProduct]; simp [hi]
    · have := congrFun h i
      rw [mulVec_eq_lead_add_free hR, lead_sum_eq x hc] at this
      rw [← this]; ring
  · rintro ⟨h0, h1⟩
    funext i
    rw [mulVec_eq_lead_add_free hR]
    by_cases hi : R i = 0
    · rw [lead_sum_eq_zero x hi, free_sum_eq_zero x hi, h0 i hi]; simp
    · obtain ⟨c, hc⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hi
      rw [lead_sum_eq x hc, h1 i c hc]; ring

/-- Free-variable columns of a reduced echelon matrix: the free coordinates determine a solution. -/
theorem solution_unique_of_free_eq {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon)
    {b : Fin m → K} {x y : Fin n → K} (hx : R *ᵥ x = b) (hy : R *ᵥ y = b)
    (h : ∀ j, IsFreeColumn R j → x j = y j) : x = y := by
  funext j
  by_cases hj : IsFreeColumn R j
  · exact h j hj
  · unfold IsFreeColumn at hj
    push Not at hj
    obtain ⟨i, hi⟩ := hj
    have e1 := ((hefferon_One_I_2_2 hR b x).mp hx).2 i j hi
    have e2 := ((hefferon_One_I_2_2 hR b y).mp hy).2 i j hi
    rw [e1, e2]
    congr 1
    apply Finset.sum_congr rfl
    intro j' _
    by_cases hj' : IsFreeColumn R j'
    · simp [hj', h j' hj']
    · simp [hj']

/-- Any values of the free variables extend to a solution, provided the system is consistent on the zero
rows. -/
theorem exists_solution_of_free {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon)
    {b : Fin m → K} (hb : ∀ i, R i = 0 → b i = 0) (f : Fin n → K) :
    ∃ x, R *ᵥ x = b ∧ ∀ j, IsFreeColumn R j → x j = f j := by
  let x : Fin n → K := fun j =>
    if h : ∃ i, R.IsLeadingEntry i j then
      b h.choose - ∑ j', if IsFreeColumn R j' then R h.choose j' * f j' else 0
    else f j
  have hxfree : ∀ j, IsFreeColumn R j → x j = f j := by
    intro j hj
    have : ¬ ∃ i, R.IsLeadingEntry i j := by rintro ⟨i, hi⟩; exact hj i hi
    simp only [x, this, dite_false]
  have hxlead : ∀ i c, R.IsLeadingEntry i c →
      x c = b i - ∑ j', if IsFreeColumn R j' then R i j' * f j' else 0 := by
    intro i c hc
    have hex : ∃ i, R.IsLeadingEntry i c := ⟨i, hc⟩
    have hi : hex.choose = i := by
      by_contra hne
      exact hc.2 (hR.eq_zero_of_ne_of_isLeadingEntry (Ne.symm hne) hex.choose_spec)
    simp only [x, hex, dite_true, hi]
  refine ⟨x, ?_, hxfree⟩
  rw [hefferon_One_I_2_2 hR]
  refine ⟨hb, fun i c hc => ?_⟩
  rw [hxlead i c hc]
  congr 1
  apply Finset.sum_congr rfl
  intro j' _
  by_cases hj' : IsFreeColumn R j'
  · simp [hj', hxfree j' hj']
  · simp [hj']

theorem exists_homog_basis {R : Matrix (Fin m) (Fin n) K} (hR : R.IsReducedRowEchelon) :
    ∃ β : {j // IsFreeColumn R j} → (Fin n → K), LinearIndependent K β ∧
      {x | R *ᵥ x = 0} = {x | ∃ c : {j // IsFreeColumn R j} → K, x = ∑ j, c j • β j} := by
  choose β hβ using fun j : {j // IsFreeColumn R j} =>
    exists_solution_of_free hR (b := 0) (fun _ _ => rfl) (Pi.single j.1 1)
  have hcoord : ∀ j j' : {j // IsFreeColumn R j}, β j j'.1 = if j = j' then 1 else 0 := by
    intro j j'
    rw [(hβ j).2 j'.1 j'.2]
    by_cases h : j = j'
    · subst h; simp
    · have : j'.1 ≠ j.1 := fun h' => h (Subtype.ext h'.symm)
      simp [h, Pi.single_apply, this]
  have hsolve : ∀ c : {j // IsFreeColumn R j} → K, R *ᵥ (∑ j, c j • β j) = 0 := by
    intro c
    rw [Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.mulVec_smul, (hβ j).1, smul_zero]
  have hcoord2 : ∀ (c : {j // IsFreeColumn R j} → K) (j' : {j // IsFreeColumn R j}),
      (∑ j, c j • β j) j'.1 = c j' := by
    intro c j'
    rw [Finset.sum_apply, Finset.sum_eq_single j']
    · simp [hcoord]
    · intro j _ hj; simp [hcoord, hj]
    · simp
  refine ⟨β, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrFun hc i.1
    rw [hcoord2 c i] at this
    simpa using this
  · ext x
    constructor
    · intro hx
      refine ⟨fun j => x j.1, ?_⟩
      exact solution_unique_of_free_eq hR hx (hsolve _) (fun j hj => (hcoord2 (fun j => x j.1) ⟨j, hj⟩).symm)
    · rintro ⟨c, rfl⟩
      exact hsolve c

theorem homog_param (A : Matrix (Fin m) (Fin n) K) :
    ∃ R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsReducedRowEchelon ∧
      ∃ β : {j // IsFreeColumn R j} → (Fin n → K), LinearIndependent K β ∧
        {x | A *ᵥ x = 0} = {x | ∃ c : {j // IsFreeColumn R j} → K, x = ∑ j, c j • β j} := by
  obtain ⟨R, hAR, hR⟩ := hefferon_One_III_1_GaussJordan A
  obtain ⟨β, hli, hset⟩ := exists_homog_basis hR
  refine ⟨R, hAR, hR, β, hli, ?_⟩
  rw [← hset]
  obtain ⟨g, rfl⟩ := hAR
  have := solutionSet_eq_of_isUnit (P := (g : Matrix (Fin m) (Fin m) K)) g.isUnit A 0
  rw [this, Matrix.mulVec_zero]
  rfl

/-- The solution set of a homogeneous system is spanned by one vector for each free variable of a reduced
echelon form (and these vectors are linearly independent). -/
@[kb "hefferon2020" "One.I.3.6, p. 35"]
theorem hefferon_One_I_3_6 (A : Matrix (Fin m) (Fin n) K) :
    ∃ R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsReducedRowEchelon ∧
      ∃ β : {j // IsFreeColumn R j} → (Fin n → K), LinearIndependent K β ∧
        {x | A *ᵥ x = 0} = {x | ∃ c : {j // IsFreeColumn R j} → K, x = ∑ j, c j • β j} :=
  homog_param A

/-- The solution set of a linear system with a particular solution `p` is `p` plus the combinations of the
free-variable vectors `β j` of the associated homogeneous system. -/
@[kb "hefferon2020" "One.I.3.1, p. 34"]
theorem hefferon_One_I_3_1 (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (p : Fin n → K) (hp : A *ᵥ p = b) :
    ∃ R : Matrix (Fin m) (Fin n) K, RowEquivalent A R ∧ R.IsReducedRowEchelon ∧
      ∃ β : {j // IsFreeColumn R j} → (Fin n → K), LinearIndependent K β ∧
        {x | A *ᵥ x = b} = {x | ∃ c : {j // IsFreeColumn R j} → K, x = p + ∑ j, c j • β j} := by
  obtain ⟨R, hAR, hR, β, hli, hset⟩ := homog_param A
  refine ⟨R, hAR, hR, β, hli, ?_⟩
  ext x
  have key : A *ᵥ x = b ↔ x - p ∈ {x | A *ᵥ x = 0} := by
    simp only [Set.mem_ofPred_eq, Matrix.mulVec_sub, hp, sub_eq_zero]
  rw [Set.mem_ofPred_eq, key, hset]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc]; abel⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc]; abel⟩

/-- Summary of Gauss's Method for the system `A x = b`: row operations (an invertible `P`) bring it to a
reduced echelon system `R x = P b` with the same solutions; a zero row with nonzero constant means no
solution; otherwise there is a solution, and it is unique exactly when no variable is free. -/
@[kb "hefferon2020" "One.I.1.Summary, p. 19"]
theorem hefferon_One_I_1_Summary (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) :
    ∃ (P : Matrix (Fin m) (Fin m) K) (R : Matrix (Fin m) (Fin n) K), IsUnit P ∧ R = P * A ∧
      R.IsReducedRowEchelon ∧ {x | A *ᵥ x = b} = {x | R *ᵥ x = P *ᵥ b} ∧
      ((∃ i, R i = 0 ∧ (P *ᵥ b) i ≠ 0) → {x | A *ᵥ x = b} = ∅) ∧
      ((∀ i, R i = 0 → (P *ᵥ b) i = 0) →
        (∃ x, A *ᵥ x = b) ∧ ((∃! x, A *ᵥ x = b) ↔ ∀ j, ¬ IsFreeColumn R j)) := by
  obtain ⟨R, ⟨g, rfl⟩, hR⟩ := hefferon_One_III_1_GaussJordan A
  have hu : IsUnit (g : Matrix (Fin m) (Fin m) K) := g.isUnit
  have hset := solutionSet_eq_of_isUnit hu A b
  refine ⟨g, g • A, hu, rfl, hR, hset, ?_, ?_⟩
  · rintro ⟨i, hi, hb⟩
    ext x
    simp only [hset, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    apply hb
    rw [← congrFun hx i]
    show ((g • A) *ᵥ x) i = 0
    have : (g • A) i = 0 := hi
    rw [Matrix.mulVec, dotProduct]; simp [this]
  · intro hcons
    have hb : ∀ i, (g • A) i = 0 → (↑g *ᵥ b) i = 0 := hcons
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx, -⟩ := exists_solution_of_free hR hb 0
      exact ⟨x, by rw [Set.ext_iff] at hset; exact (hset x).mpr hx⟩
    · constructor
      · rintro ⟨x, hx, huniq⟩ j hj
        have hx' : (g • A) *ᵥ x = ↑g *ᵥ b := (Set.ext_iff.mp hset x).mp hx
        obtain ⟨y, hy, hy2⟩ := exists_solution_of_free hR hb (Function.update x j (x j + 1))
        have hy' : A *ᵥ y = b := (Set.ext_iff.mp hset y).mpr hy
        have hyx := huniq y hy'
        have := hy2 j hj
        rw [hyx] at this
        simp at this
      · intro hfree
        obtain ⟨x, hx, -⟩ := exists_solution_of_free hR hb 0
        refine ⟨x, (Set.ext_iff.mp hset x).mpr hx, fun y hy => ?_⟩
        exact solution_unique_of_free_eq hR ((Set.ext_iff.mp hset y).mp hy) hx
          (fun j hj => absurd hj (hfree j))

end Free

end UndergradKB.LinearAlgebra
