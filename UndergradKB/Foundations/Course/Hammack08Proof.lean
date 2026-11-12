import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Order
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import UndergradKB.Common

/-!
# Course layer: Hammack, Chapter 8 (proofs about sets)
-/

namespace UndergradKB.Foundations.Course

open Set

/-- FO-145. `A ⊆ B` means every element of `A` is in `B`; proper subset adds `A ≠ B`. -/
@[kb "hammack2018" "Prop §8.2, p. 171", kb "levin2025" "Definition 1.5.2, p. 105"]
theorem hammack_s8_2_subset_def {α : Type*} (A B : Set α) :
    (A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B) ∧ (A ⊂ B ↔ A ⊆ B ∧ A ≠ B) :=
  ⟨Iff.rfl, Set.ssubset_iff_subset_ne⟩

/-- FO-146. Subset is transitive. -/
@[kb "hammack2018" "Prop §8.2, p. 173", kb "levin2025" "Proposition 1.5.4, p. 106"]
theorem hammack_s8_2_subset_trans {α : Type*} {A B C : Set α} (h : A ⊆ B) (h' : B ⊆ C) :
    A ⊆ C :=
  Set.Subset.trans h h'

/-- FO-147. Some obvious subset facts. -/
@[kb "hammack2018" "Prop §8.2, p. 173"]
theorem hammack_s8_2_basic_subsets {α : Type*} (A B X : Set α) :
    A ∩ B ⊆ A ∧ A ⊆ A ∪ B ∧ A \ B ⊆ A ∧ (X ⊆ A → X ⊆ A ∪ B) :=
  ⟨Set.inter_subset_left, Set.subset_union_left, Set.sdiff_subset,
    fun h => h.trans Set.subset_union_left⟩

/-- FO-149. Two sets are equal iff each is a subset of the other. -/
@[kb "hammack2018" "Prop §8.3, p. 174"]
theorem hammack_s8_3_set_eq_iff {α : Type*} (A B : Set α) : A = B ↔ A ⊆ B ∧ B ⊆ A :=
  Set.Subset.antisymm_iff

/-- FO-152. If `𝒫(A) ⊆ 𝒫(B)` then `A ⊆ B`. -/
@[kb "hammack2018" "Example 8.9, p. 174"]
theorem hammack_ex_8_9_powerset_subset {α : Type*} {A B : Set α} (h : 𝒫 A ⊆ 𝒫 B) : A ⊆ B :=
  Set.powerset_mono.mp h

/-- FO-153. If `C ≠ ∅` and `A × C = B × C` then `A = B`. -/
@[kb "hammack2018" "Example 8.11, p. 175"]
theorem hammack_ex_8_11_prod_cancel {α β : Type*} {A B : Set α} {C : Set β} (hC : C.Nonempty)
    (h : A ×ˢ C = B ×ˢ C) : A = B :=
  (Set.prod_eq_iff_eq hC).mp h

/-- FO-154. `A × (B ∩ C) = (A × B) ∩ (A × C)`. -/
@[kb "hammack2018" "Example 8.12, p. 175", kb "hammack2018" "Example 8.13, p. 176"]
theorem hammack_ex_8_12_prod_inter {α β : Type*} (A : Set α) (B C : Set β) :
    A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext ⟨x, y⟩
  simp only [Set.mem_prod, Set.mem_inter_iff]
  tauto

/-- FO-155. De Morgan laws, the two distributive laws, and `×` distributing over `∪`. -/
@[kb "hammack2018" "Prop §8.3, p. 177"]
theorem hammack_s8_3_set_laws {α β : Type*} (A B C : Set α) (D : Set β) :
    (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ ∧ (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ ∧
      A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) ∧ A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) ∧
      D ×ˢ (A ∪ B) = (D ×ˢ A) ∪ (D ×ˢ B) := by
  refine ⟨Set.compl_inter A B, Set.compl_union A B, Set.inter_union_distrib_left A B C,
    Set.union_inter_distrib_left A B C, ?_⟩
  ext ⟨x, y⟩
  simp only [Set.mem_prod, Set.mem_union]
  tauto

/-- FO-156. If `a` and `b` are coprime and both divide `n`, then `a b ∣ n`; hence
`35 ∣ n` iff `5 ∣ n` and `7 ∣ n`. -/
@[kb "hammack2018" "Example 8.10, p. 174"]
theorem hammack_ex_8_10_coprime_dvd :
    (∀ a b n : ℕ, Nat.Coprime a b → a ∣ n → b ∣ n → a * b ∣ n) ∧
      {n : ℕ | 35 ∣ n} = {n : ℕ | 5 ∣ n} ∩ {n : ℕ | 7 ∣ n} := by
  refine ⟨fun a b n h ha hb => Nat.Coprime.mul_dvd_of_dvd_of_dvd h ha hb, ?_⟩
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  omega

/-- FO-157. A positive `n` is perfect iff its proper divisors sum to `n`, iff all its
divisors sum to `2 n`. -/
@[kb "hammack2018" "Definition 8.1, p. 177"]
theorem hammack_def_8_1_perfect (n : ℕ) (hn : 0 < n) :
    (Nat.Perfect n ↔ ∑ i ∈ n.properDivisors, i = n) ∧
      (Nat.Perfect n ↔ ∑ i ∈ n.divisors, i = 2 * n) :=
  ⟨Nat.perfect_iff_sum_properDivisors hn, Nat.perfect_iff_sum_divisors_eq_two_mul hn⟩

/-- FO-158. Geometric sum `∑_{k=0}^{n} r^k = (r^(n+1) - 1)/(r - 1)` for `r ≠ 1`, and
`∑ 2^k = 2^(n+1) - 1`. -/
@[kb "hammack2018" "Eq (8.1) §8.4, p. 179"]
theorem hammack_eq_8_1_geom_sum (r : ℝ) (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), r ^ k = (r ^ (n + 1) - 1) / (r - 1) ∧
      ∑ k ∈ Finset.range (n + 1), (2 : ℝ) ^ k = 2 ^ (n + 1) - 1 := by
  refine ⟨geom_sum_eq hr (n + 1), ?_⟩
  rw [geom_sum_eq (by norm_num)]
  norm_num

/-- FO-161. If `2^n - 1` is prime then `n` is prime. -/
@[kb "hammack2018" "Prop §8.4, p. 182"]
theorem hammack_s8_4_mersenne_prime_exponent (n : ℕ) (h : (2 ^ n - 1).Prime) : n.Prime :=
  Nat.Prime.of_mersenne h

end UndergradKB.Foundations.Course
