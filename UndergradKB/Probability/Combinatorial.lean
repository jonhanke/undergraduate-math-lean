import Mathlib.Algebra.Group.End
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.UniformOn
import UndergradKB.Common.Attr

/-! # Probability: counting arguments for random permutations and birthdays (Grinstead–Snell)

Expectations under the uniform measure on `Equiv.Perm (Fin n)` are written as averages
`(∑ σ, f σ) / n!`. -/

open Finset

namespace UndergradKB.Probability

/-! ### Fixed points -/

/-- The number of permutations of `Fin n` fixing a given point is `(n-1)!`. -/
theorem card_perm_fixing {n : ℕ} (i : Fin n) :
    #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i) = (n - 1).factorial := by
  classical
  have h1 : Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ (a ≠ i) → f a = a} =
      Fintype.card (Equiv.Perm {a : Fin n // a ≠ i}) :=
    (Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ≠ i)).symm)
  have h2 : Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ (a ≠ i) → f a = a} =
      #(univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    constructor
    · intro h; exact h i (by simp)
    · intro h a ha; push Not at ha; rw [ha]; exact h
  rw [← h2, h1, Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_fin]
  simp

/-- Grinstead–Snell Example 6.8 (PR-085). Summed over all permutations of `n ≥ 1` points, the number
of fixed points is `n!`; hence the expected number of fixed points of a uniformly random
permutation is `1`. -/
@[kb "grinsteadsnell2006" "Example 6.8, p. 240"]
theorem sum_fixedPoints_card {n : ℕ} (hn : 1 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), #(univ.filter fun i : Fin n => σ i = i) = n.factorial := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter, card_perm_fixing]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Nat.factorial_succ]

/-- Grinstead–Snell Example 6.8 (PR-085), as an average: the mean number of fixed points over all
`n!` permutations of `n ≥ 1` points equals `1`, i.e. the expected value under the uniform
distribution on permutations. -/
@[kb "grinsteadsnell2006" "Example 6.8, p. 240"]
theorem average_fixedPoints_card {n : ℕ} (hn : 1 ≤ n) :
    (∑ σ : Equiv.Perm (Fin n), (#(univ.filter fun i : Fin n => σ i = i) : ℝ)) /
      (n.factorial : ℝ) = 1 := by
  have h := sum_fixedPoints_card hn
  have h' : (∑ σ : Equiv.Perm (Fin n), (#(univ.filter fun i : Fin n => σ i = i) : ℝ)) =
      (n.factorial : ℝ) := by exact_mod_cast h
  rw [h', div_self (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))]

/-! ### Records -/

/-- Grinstead–Snell Definition 3.4 (PR-023). Position `i` is a record of the arrangement `σ` when
its value is larger than every value at an earlier position. -/
@[kb "grinsteadsnell2006" "Definition 3.4, p. 91"]
def IsRecord {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ k : Fin n, k < i → σ k < σ i

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Decidable (IsRecord σ i) :=
  inferInstanceAs (Decidable (∀ k : Fin n, k < i → σ k < σ i))

section Records

variable {n : ℕ}

/-- The permutations whose value at `k` is the maximum over positions `≤ i`. -/
private def maxAt (i k : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun σ => ∀ m, m ≤ i → σ m ≤ σ k

private lemma maxAt_swap {i a b : Fin n} (ha : a ≤ i) (hb : b ≤ i) {σ : Equiv.Perm (Fin n)}
    (h : σ ∈ maxAt i a) : σ * Equiv.swap a b ∈ maxAt i b := by
  simp only [maxAt, mem_filter, mem_univ, true_and] at h ⊢
  intro m hm
  have hb' : (σ * Equiv.swap a b) b = σ a := by simp
  rw [hb']
  apply h
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at *
  split_ifs <;> assumption

private lemma card_maxAt {i k : Fin n} (hk : k ≤ i) : #(maxAt i k) = #(maxAt i i) := by
  refine Finset.card_bij' (fun σ _ => σ * Equiv.swap k i) (fun σ _ => σ * Equiv.swap k i)
    ?_ ?_ ?_ ?_
  · intro σ hσ; exact maxAt_swap hk le_rfl hσ
  · intro σ hσ
    have := maxAt_swap (le_rfl : i ≤ i) hk hσ
    rwa [Equiv.swap_comm] at this
  · intro σ _; simp [mul_assoc]
  · intro σ _; simp [mul_assoc]

private lemma isRecord_iff {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    IsRecord σ i ↔ σ ∈ maxAt i i := by
  simp only [IsRecord, maxAt, mem_filter, mem_univ, true_and]
  constructor
  · intro h m hm
    rcases hm.lt_or_eq with hm | rfl
    · exact (h m hm).le
    · exact le_rfl
  · intro h m hm
    exact lt_of_le_of_ne (h m hm.le) (fun e => hm.ne (σ.injective e))

/-- Number of arrangements of `n` values in which position `i` (counted from `0`) is a record:
`(i+1)` times this count is `n!`. -/
theorem succ_mul_card_isRecord (i : Fin n) :
    (i.val + 1) * #(univ.filter fun σ : Equiv.Perm (Fin n) => IsRecord σ i) = n.factorial := by
  have hcover : (univ : Finset (Equiv.Perm (Fin n))) = (Iic i).biUnion (maxAt i) := by
    ext σ
    simp only [mem_univ, mem_biUnion, mem_Iic, true_iff]
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Iic i) σ ⟨i, mem_Iic.2 le_rfl⟩
    refine ⟨k, mem_Iic.1 hk, ?_⟩
    simp only [maxAt, mem_filter, mem_univ, true_and]
    exact fun m hm => hmax m (mem_Iic.2 hm)
  have hdisj : ∀ k ∈ (Iic i : Finset (Fin n)), ∀ k' ∈ (Iic i : Finset (Fin n)), k ≠ k' →
      Disjoint (maxAt i k) (maxAt i k') := by
    intro k hk k' hk' hne
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [maxAt, mem_filter, mem_univ, true_and] at h1 h2
    exact hne (σ.injective (le_antisymm (h2 k (mem_Iic.1 hk)) (h1 k' (mem_Iic.1 hk'))))
  have : n.factorial = ∑ k ∈ Iic i, #(maxAt i k) := by
    rw [← Finset.card_biUnion hdisj, ← hcover]
    simp [Fintype.card_perm]
  rw [this]
  have h2 : ∑ k ∈ Iic i, #(maxAt i k) = ∑ _k ∈ Iic i, #(maxAt i i) :=
    Finset.sum_congr rfl fun k hk => card_maxAt (mem_Iic.1 hk)
  rw [h2, sum_const, Fin.card_Iic, smul_eq_mul]
  have : (univ.filter fun σ : Equiv.Perm (Fin n) => IsRecord σ i) = maxAt i i := by
    ext σ; simp [isRecord_iff, maxAt]
  rw [this]

/-- Grinstead–Snell Example 6.11 (PR-084). Summed over all permutations, the number of records is
`∑_{i<n} n!/(i+1)`, i.e. position `i` is a record for `n!/(i+1)` permutations. -/
@[kb "grinsteadsnell2006" "Example 6.11, p. 242"]
theorem sum_records_card :
    ∑ σ : Equiv.Perm (Fin n), (#(univ.filter fun i : Fin n => IsRecord σ i) : ℝ) =
      ∑ i : Fin n, (n.factorial : ℝ) / ((i : ℕ) + 1) := by
  simp_rw [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcount : (∑ σ : Equiv.Perm (Fin n), (((if IsRecord σ i then 1 else 0 : ℕ)) : ℝ)) =
      (#(univ.filter fun σ : Equiv.Perm (Fin n) => IsRecord σ i) : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.card_filter]
  rw [hcount, eq_div_iff (by positivity)]
  have := succ_mul_card_isRecord i
  have h' : (((i : ℕ) + 1 : ℕ) : ℝ) * (#(univ.filter fun σ : Equiv.Perm (Fin n) => IsRecord σ i) : ℝ)
      = n.factorial := by exact_mod_cast this
  push_cast at h'
  linarith

/-- Grinstead–Snell Example 6.11 (PR-084). The expected number of records of a uniformly random
permutation of `n` values is `1 + 1/2 + ... + 1/n`. -/
@[kb "grinsteadsnell2006" "Example 6.11, p. 242"]
theorem average_records_card :
    (∑ σ : Equiv.Perm (Fin n), (#(univ.filter fun i : Fin n => IsRecord σ i) : ℝ)) /
      (n.factorial : ℝ) = ((harmonic n : ℚ) : ℝ) := by
  rw [sum_records_card]
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have : ∀ i : Fin n, (n.factorial : ℝ) / ((i : ℕ) + 1) / n.factorial = ((i : ℕ) + 1 : ℝ)⁻¹ := by
    intro i; field_simp
  rw [Finset.sum_div]
  simp_rw [this]
  rw [harmonic, Rat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

end Records

/-! ### The birthday problem -/

/-- Grinstead–Snell Example 3.3 (PR-024). Among the `365^23` equally likely assignments of
birthdays to 23 people, fewer than half have all birthdays different. -/
@[kb "grinsteadsnell2006" "Example 3.3, p. 85"]
theorem birthday_distinct_lt_half :
    (#(univ.filter fun f : Fin 23 → Fin 365 => Function.Injective f) : ℝ) / 365 ^ 23 < 1 / 2 := by
  have h1 : #(univ.filter fun f : Fin 23 → Fin 365 => Function.Injective f) =
      Fintype.card (Fin 23 ↪ Fin 365) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _)
  rw [h1, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  have h2 : (Nat.descFactorial 365 23) * 2 < 365 ^ 23 := by
    norm_num [Nat.descFactorial_succ]
  have h3 : ((Nat.descFactorial 365 23 : ℕ) : ℝ) * 2 < (365 : ℝ) ^ 23 := by exact_mod_cast h2
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- Non-injective maps are the complement of the injective ones. -/
theorem card_not_injective_real {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] :
    (#(univ.filter fun f : α → β => ¬ Function.Injective f) : ℝ) =
      (Fintype.card β : ℝ) ^ Fintype.card α - #(univ.filter fun f : α → β => Function.Injective f) := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (α → β)))
    (fun f => Function.Injective f)
  rw [Finset.card_univ, Fintype.card_fun] at h
  rw [eq_sub_iff_add_eq, add_comm]
  exact_mod_cast h

/-- Grinstead–Snell Example 3.3 (PR-024). The probability that two of 23 people share a birthday
(among 365 equally likely days) exceeds `1/2`. -/
@[kb "grinsteadsnell2006" "Example 3.3, p. 85"]
theorem birthday_shared_gt_half :
    1 / 2 < (#(univ.filter fun f : Fin 23 → Fin 365 => ¬ Function.Injective f) : ℝ) / 365 ^ 23 := by
  have h := birthday_distinct_lt_half
  have hc' : (#(univ.filter fun f : Fin 23 → Fin 365 => ¬ Function.Injective f) : ℝ) =
      365 ^ 23 - #(univ.filter fun f : Fin 23 → Fin 365 => Function.Injective f) := by
    have := card_not_injective_real (α := Fin 23) (β := Fin 365)
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using this
  rw [hc', sub_div, div_self (by positivity)]
  linarith

end UndergradKB.Probability
