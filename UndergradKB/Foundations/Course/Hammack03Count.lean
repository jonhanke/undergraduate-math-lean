import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Card
import Mathlib.Data.Multiset.Count
import UndergradKB.Common

/-! # Course layer: Hammack, Chapter 3 (counting)
Thin theorems in the book's terms for the rows of the checklist section "Counting" that are `in Mathlib`
and stated by Hammack (possibly also by Levin). Levin-only rows are in `Levin03Count.lean`. -/

namespace UndergradKB.Foundations.Course

open Finset

/-- FO-213. A list is determined by its length and its entries; the empty list has length 0. -/
@[kb "hammack2018" "Def §3.1, p. 77"]
theorem hammack_s3_1_list_ext {α : Type*} (l₁ l₂ : List α) :
    l₁ = l₂ ↔ l₁.length = l₂.length ∧
      ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = l₂[i] :=
  List.ext_getElem_iff

/-- FO-213 (empty list). A list has length 0 exactly when it is the empty list. -/
@[kb "hammack2018" "Def §3.1, p. 77"]
theorem hammack_s3_1_list_length_zero {α : Type*} (l : List α) : l.length = 0 ↔ l = [] :=
  List.length_eq_zero_iff

/-- FO-214. Multiplication principle: `|A × B| = |A| |B|`. -/
@[kb "hammack2018" "Fact 3.1, p. 81", kb "levin2025" "Principle 3.2.8, p. 229"]
theorem hammack_fact_3_1_card_prod {α β : Type*} (A : Finset α) (B : Finset β) :
    (A ×ˢ B).card = A.card * B.card :=
  Finset.card_product A B

/-- FO-214 (n steps). The number of choices from a family of finite sets, one per position, is the
product of their sizes. -/
@[kb "hammack2018" "Fact 3.1, p. 81", kb "levin2025" "Principle 3.2.8, p. 229"]
theorem hammack_fact_3_1_card_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → Type*)
    [∀ i, Fintype (β i)] : Fintype.card (∀ i, β i) = ∏ i, Fintype.card (β i) :=
  Fintype.card_pi

/-- FO-215. Addition principle: for disjoint finite sets the size of the union is the sum of sizes. -/
@[kb "hammack2018" "Fact 3.2, p. 86", kb "levin2025" "Principle 3.2.3, p. 227"]
theorem hammack_fact_3_2_card_union {α : Type*} [DecidableEq α] (A B : Finset α)
    (h : Disjoint A B) : (A ∪ B).card = A.card + B.card :=
  Finset.card_union_of_disjoint h

/-- FO-215 (many sets). The same for a pairwise disjoint family of finite sets. -/
@[kb "hammack2018" "Fact 3.2, p. 86", kb "levin2025" "Principle 3.3.2, p. 239"]
theorem hammack_fact_3_2_card_biUnion {ι α : Type*} [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) (h : (s : Set ι).PairwiseDisjoint t) :
    (s.biUnion t).card = ∑ i ∈ s, (t i).card :=
  Finset.card_biUnion h

/-- FO-216. Subtraction principle: if `X ⊆ U` then `|U \ X| = |U| - |X|`. -/
@[kb "hammack2018" "Fact 3.3, p. 88", kb "levin2025" "Ex 3.2.6, p. 229"]
theorem hammack_fact_3_3_card_sdiff {α : Type*} [DecidableEq α] (X U : Finset α) (h : X ⊆ U) :
    (U \ X).card = U.card - X.card :=
  Finset.card_sdiff_of_subset h

/-- FO-217. There are `k^n` lists of length `n` with entries from a `k`-element set
(functions from an `n`-set to a `k`-set). -/
@[kb "hammack2018" "Ex 3.3, p. 82", kb "levin2025" "Ex 3.2.14, p. 233"]
theorem hammack_ex_3_3_card_fun (n k : ℕ) : Fintype.card (Fin n → Fin k) = k ^ n := by
  simp

/-- FO-224. The number of `k`-element subsets of an `n`-element set is `C(n,k)`. -/
@[kb "hammack2018" "Def 3.2, p. 97", kb "levin2025" "Ex 3.1.8, p. 220"]
theorem hammack_def_3_2_card_powersetCard {α : Type*} (S : Finset α) (k : ℕ) :
    (S.powersetCard k).card = S.card.choose k :=
  Finset.card_powersetCard k S

/-- FO-225. For `0 ≤ k ≤ n`, `C(n,k) = n! / (k! (n-k)!)`. -/
@[kb "hammack2018" "Fact 3.5, p. 99", kb "levin2025" "Thm 3.4.10, p. 256"]
theorem hammack_fact_3_5_choose_formula {n k : ℕ} (h : k ≤ n) :
    n.choose k = n.factorial / (k.factorial * (n - k).factorial) :=
  Nat.choose_eq_factorial_div_factorial h

/-- FO-226. Factorial: `0! = 1` and `n! = n (n-1)!`. -/
@[kb "hammack2018" "Def 3.1, p. 90", kb "levin2025" "Text §3.4.2, p. 252"]
theorem hammack_def_3_1_factorial : Nat.factorial 0 = 1 ∧ ∀ n : ℕ, (n + 1).factorial = (n + 1) * n.factorial :=
  ⟨Nat.factorial_zero, fun n => Nat.factorial_succ n⟩

/-- FO-227. An `n`-element set has `n!` permutations. -/
@[kb "hammack2018" "Text §3.4, p. 92", kb "levin2025" "Thm 3.4.3, p. 252"]
theorem hammack_s3_4_card_perm (n : ℕ) : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- FO-228. The number of non-repeating lists of length `k` from an `n`-set (injections from a
`k`-set into an `n`-set) is `n (n-1) ... (n-k+1)`. -/
@[kb "hammack2018" "Fact 3.4, p. 95", kb "levin2025" "Thm 3.4.7, p. 254"]
theorem hammack_fact_3_4_card_embedding (n k : ℕ) :
    Fintype.card (Fin k ↪ Fin n) = n.descFactorial k := by
  simp

/-- FO-228 (factorial form). For `k ≤ n`, `P(n,k) = n! / (n-k)!`. -/
@[kb "hammack2018" "Fact 3.4, p. 95", kb "levin2025" "Thm 3.4.7, p. 254"]
theorem hammack_fact_3_4_descFactorial_div {n k : ℕ} (h : k ≤ n) :
    n.descFactorial k = n.factorial / (n - k).factorial :=
  Nat.descFactorial_eq_div h

/-- FO-229. `P(n,k) = C(n,k) k!`. -/
@[kb "hammack2018" "Text §3.5, p. 98", kb "levin2025" "Ex 3.4.9, p. 255"]
theorem hammack_s3_5_descFactorial_eq_choose_mul (n k : ℕ) :
    n.descFactorial k = n.choose k * k.factorial := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]

/-- FO-231. Pascal's rule: `C(n+1,k+1) = C(n,k) + C(n,k+1)`. -/
@[kb "hammack2018" "Eq 3.3, p. 102", kb "levin2025" "Ex 3.6.2, p. 279"]
theorem hammack_eq_3_3_pascal (n k : ℕ) :
    (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
  Nat.choose_succ_succ' n k

/-- FO-232. Symmetry: `C(n,k) = C(n,n-k)` for `k ≤ n`. -/
@[kb "hammack2018" "Eq 3.4, p. 103", kb "levin2025" "Ex 3.6.5, p. 281"]
theorem hammack_eq_3_4_choose_symm {n k : ℕ} (h : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm h).symm

/-- FO-233. Boundary values `C(n,0) = C(n,n) = 1`. -/
@[kb "hammack2018" "Text §3.5, p. 98", kb "levin2025" "Ex 3.6.3, p. 280"]
theorem hammack_s3_5_choose_boundary (n : ℕ) : n.choose 0 = 1 ∧ n.choose n = 1 :=
  ⟨Nat.choose_zero_right n, Nat.choose_self n⟩

/-- FO-234. Binomial theorem: `(x+y)^n = ∑ C(n,k) x^k y^(n-k)`. -/
@[kb "hammack2018" "Thm 3.1, p. 104", kb "levin2025" "Thm 3.1.10, p. 222"]
theorem hammack_thm_3_1_binomial (x y : ℤ) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * x ^ k * y ^ (n - k) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- FO-236. `C(n,0)^2 + ... + C(n,n)^2 = C(2n,n)`. -/
@[kb "hammack2018" "Ex 3.28, p. 121", kb "levin2025" "Ex 3.6.8, p. 285"]
theorem hammack_ex_3_28_sum_choose_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k ^ 2 = (2 * n).choose n :=
  Nat.sum_range_choose_sq n

/-- FO-239. Inclusion-exclusion for two sets: `|A ∪ B| = |A| + |B| - |A ∩ B|`. -/
@[kb "hammack2018" "Fact 3.6, p. 105", kb "levin2025" "Thm 3.3.5, p. 243"]
theorem hammack_fact_3_6_inclusion_exclusion {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  have := Finset.card_union_add_card_inter A B
  omega

/-- FO-242. A finite set, viewed as a multiset, has every member with multiplicity one; the
cardinality of a multiset is the sum of the multiplicities. -/
@[kb "hammack2018" "Text §3.8, p. 108", kb "levin2025" "Def 3.5.2, p. 265"]
theorem hammack_s3_8_multiset {α : Type*} [DecidableEq α] (S : Finset α) (m : Multiset α) :
    (∀ a ∈ S, S.val.count a = 1) ∧ ∑ a ∈ m.toFinset, m.count a = Multiset.card m :=
  ⟨fun _ ha => Multiset.count_eq_one_of_mem S.nodup ha, Multiset.toFinset_sum_count_eq m⟩

/-- FO-243. Stars and bars: the number of `k`-element multisets from an `n`-element set is
`C(k+n-1, k)`. -/
@[kb "hammack2018" "Fact 3.7, p. 110", kb "levin2025" "Text §3.5.3, p. 269"]
theorem hammack_fact_3_7_multisets (n k : ℕ) :
    Fintype.card (Sym (Fin n) k) = (k + n - 1).choose k := by
  rw [Sym.card_sym_eq_choose]
  simp [Nat.add_comm]

/-- FO-244. The number of non-negative integer solutions of `x₁ + ... + xₙ = k` is `C(k+n-1, k)`. -/
@[kb "hammack2018" "Ex 3.20, p. 112", kb "levin2025" "Text §3.5.2, p. 267"]
theorem hammack_ex_3_20_nonneg_solutions (n k : ℕ) :
    ((Finset.univ : Finset (Fin n)).finsuppAntidiag k).card = (n + k - 1).choose k := by
  simpa using Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) k

/-- FO-247. Strong pigeonhole: if `|β| m < |α|` then some box receives more than `m` objects. -/
@[kb "hammack2018" "Fact 3.9, p. 116"]
theorem hammack_fact_3_9_pigeonhole_strong {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (m : ℕ) (h : Fintype.card β * m < Fintype.card α) :
    ∃ y : β, m < (Finset.univ.filter fun x => f x = y).card :=
  Fintype.exists_lt_card_fiber_of_mul_lt_card f h

/-- FO-248. Pigeonhole principle: with more objects than boxes, two objects share a box. -/
@[kb "hammack2018" "Fact 3.10, p. 116"]
theorem hammack_fact_3_10_pigeonhole {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card β < Fintype.card α) : ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

/-- FO-248 (empty box). With fewer objects than boxes, some box is empty. -/
@[kb "hammack2018" "Fact 3.10, p. 116"]
theorem hammack_fact_3_10_empty_box {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (h : Fintype.card α < Fintype.card β) : ∃ y, ∀ x, f x ≠ y := by
  by_contra hcon
  push Not at hcon
  exact absurd (Fintype.card_le_of_surjective f hcon) (by omega)

end UndergradKB.Foundations.Course
