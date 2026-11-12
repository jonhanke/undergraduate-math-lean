import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.Linarith
import UndergradKB.Common

/-!
# Counting (gap rows)

Bit strings and their weights, the quotient principle, a binomial identity, three-set
inclusion-exclusion, and uniform probability on a finite sample space.
-/

namespace UndergradKB.Foundations

open Finset

/-- FO-221. An `n`-bit string is a function `Fin n → Bool`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- The weight of a bit string is its number of `1`s (entries equal to `true`). -/
def BitString.weight {n : ℕ} (s : BitString n) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card

/-- The set `B_k^n` of `n`-bit strings of weight `k`. -/
def BitString.ofWeight (n k : ℕ) : Finset (BitString n) :=
  Finset.univ.filter fun s => s.weight = k

/-- FO-221. The number of `n`-bit strings is `2 ^ n`, and the number of weight-`k` strings
is `C(n, k)`. -/
@[kb "levin2025" "Def 3.1.4, p. 218"]
theorem levin_def_3_1_4_bitstring_count (n k : ℕ) :
    Fintype.card (BitString n) = 2 ^ n ∧ (BitString.ofWeight n k).card = n.choose k := by
  refine ⟨by simp, ?_⟩
  have : (BitString.ofWeight n k).card = (powersetCard k (univ : Finset (Fin n))).card := by
    refine Finset.card_nbij' (fun s => univ.filter fun i => s i = true)
      (fun S i => decide (i ∈ S)) ?_ ?_ ?_ ?_
    · intro s hs
      rw [Finset.mem_coe] at hs ⊢
      rw [mem_powersetCard]
      exact ⟨subset_univ _, (Finset.mem_filter.mp hs).2⟩
    · intro S hS
      rw [Finset.mem_coe, mem_powersetCard] at hS
      rw [Finset.mem_coe]
      refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
      show (Finset.univ.filter fun i => decide (i ∈ S) = true).card = k
      simpa using hS.2
    · intro s _
      funext i
      simp
    · intro S _
      ext i
      simp
  rw [this, card_powersetCard]
  simp

/-- FO-230. Quotient principle: if a finite set is split into classes (fibres of `f` over `t`)
that all have `m` elements, then `|s| = |t| * m`; for `m > 0` the number of classes is
`|s| / m`. -/
@[kb "levin2025" "text §3.4.4, p. 259", kb "levin2025" "Ex 3.4.13, p. 260"]
theorem levin_s3_4_4_quotient_principle {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : Finset β) (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (m : ℕ)
    (hm : ∀ b ∈ t, (s.filter fun a => f a = b).card = m) :
    s.card = t.card * m ∧ (0 < m → t.card = s.card / m) := by
  have h : s.card = t.card * m := by
    rw [Finset.card_eq_sum_card_fiberwise hf, Finset.sum_congr rfl hm, sum_const, smul_eq_mul]
  refine ⟨h, fun hpos => ?_⟩
  rw [h, Nat.mul_div_cancel _ hpos]

/-- FO-237. `1·n + 2·(n-1) + ... + n·1 = C(n+2, 3)`. -/
@[kb "levin2025" "Ex 3.6.7, p. 284"]
theorem levin_ex_3_6_7_weighted_sum (n : ℕ) :
    ∑ i ∈ range (n + 1), i * (n + 1 - i) = (n + 2).choose 3 := by
  have hc : ∀ n : ℕ, 6 * (n + 2).choose 3 = n * (n + 1) * (n + 2) := by
    intro n
    have h1 : (n + 1) * n.choose 1 = (n + 1).choose 2 * 2 := Nat.add_one_mul_choose_eq n 1
    have h2 : (n + 2) * (n + 1).choose 2 = (n + 2).choose 3 * 3 :=
      Nat.add_one_mul_choose_eq (n + 1) 2
    rw [Nat.choose_one_right] at h1
    nlinarith [h1, h2]
  have hs : ∀ n : ℕ, 6 * ∑ i ∈ range (n + 1), i * (n + 1 - i) = n * (n + 1) * (n + 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ range (n + 1 + 1), i * (n + 1 + 1 - i)
          = ∑ i ∈ range (n + 1), i * (n + 1 - i) + ∑ i ∈ range (n + 2), i := by
        rw [sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
        have : ∑ i ∈ range (n + 1), i * (n + 1 + 1 - i)
            = ∑ i ∈ range (n + 1), (i * (n + 1 - i) + i) := by
          refine sum_congr rfl fun i hi => ?_
          have := mem_range.mp hi
          have e2 : n + 1 + 1 - i = (n + 1 - i) + 1 := by omega
          rw [e2]; ring
        rw [this, sum_add_distrib]
        have e3 : n + 1 + 1 - (n + 1) = 1 := by omega
        rw [e3]
        ring
      rw [e, mul_add, ih]
      have := Finset.sum_range_id_mul_two (n + 2)
      have h' : n + 2 - 1 = n + 1 := by omega
      rw [h'] at this
      nlinarith [this]
  have := hc n
  have := hs n
  omega

/-- FO-240. Inclusion-exclusion for three finite sets, written without subtraction:
`|A ∪ B ∪ C| + |A ∩ B| + |A ∩ C| + |B ∩ C| = |A| + |B| + |C| + |A ∩ B ∩ C|`. -/
@[kb "hammack2018" "Eq 3.5, p. 106", kb "levin2025" "Thm 3.3.7, p. 243"]
theorem hammack_eq_3_5_inclusion_exclusion_three {α : Type*} [DecidableEq α]
    (A B C : Finset α) :
    (A ∪ B ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card =
      A.card + B.card + C.card + (A ∩ B ∩ C).card := by
  have h1 := Finset.card_union_add_card_inter (A ∪ B) C
  have h2 := Finset.card_union_add_card_inter A B
  have h3 := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have e1 : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have e2 : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x; simp only [mem_inter]; tauto
  rw [e1] at h1
  rw [e2] at h3
  omega

/-- FO-240 (integer form). The same identity with subtraction, in `ℤ`. -/
@[kb "hammack2018" "Eq 3.5, p. 106", kb "levin2025" "Thm 3.3.7, p. 243"]
theorem hammack_eq_3_5_inclusion_exclusion_three_int {α : Type*} [DecidableEq α]
    (A B C : Finset α) :
    ((A ∪ B ∪ C).card : ℤ) = A.card + B.card + C.card - (A ∩ B).card - (A ∩ C).card
      - (B ∩ C).card + (A ∩ B ∩ C).card := by
  have := hammack_eq_3_5_inclusion_exclusion_three A B C
  omega

/-- FO-253. Uniform probability on a finite sample space `S`: the probability of an event `E`
(a subset of `S`) is `|E| / |S|`; the whole space has probability 1. -/
@[kb "levin2025" "text §3.7.2, p. 295", kb "levin2025" "Note 3.7.2, p. 295"]
theorem levin_s3_7_2_uniform_probability {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [DecidableEq Ω] (S E : Finset Ω) (hE : E ⊆ S)
    (hS : S.Nonempty) :
    ProbabilityTheory.uniformOn (S : Set Ω) (E : Set Ω) = (E.card : ENNReal) / S.card ∧
      ProbabilityTheory.uniformOn (S : Set Ω) (S : Set Ω) = 1 := by
  refine ⟨?_, ProbabilityTheory.uniformOn_self S.finite_toSet (by simpa using hS)⟩
  rw [ProbabilityTheory.uniformOn_apply_finset, Finset.inter_eq_right.mpr hE]

end UndergradKB.Foundations
