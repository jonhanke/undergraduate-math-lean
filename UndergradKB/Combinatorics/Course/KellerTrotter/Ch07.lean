import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Data.Nat.Totient
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 7 (Inclusion–Exclusion): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

open Finset Filter Topology

/-- CO-183. Inclusion–exclusion: if `S i` is the set of elements with property `i`, the number
of elements with none of the properties in `s` is `∑_{t ⊆ s} (-1)^{|t|} N(t)`, where `N(t)` is
the number of elements having all properties in `t`. -/
@[kb "kellertrotter2017" "Theorem 7.7, p. 169"]
theorem thm_7_7 {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α] (s : Finset ι)
    (S : ι → Finset α) :
    #(s.inf fun i ↦ (S i)ᶜ) = ∑ t ∈ s.powerset, (-1 : ℤ) ^ #t * #(t.inf S) :=
  Finset.inclusion_exclusion_card_inf_compl s S

/-- CO-187. The proportion `d_n / n!` of permutations that are derangements tends to `1/e`. -/
@[kb "kellertrotter2017" "Theorem 7.12, p. 172"]
theorem thm_7_12 :
    Tendsto (fun n : ℕ => (numDerangements n : ℝ) / n.factorial) atTop
      (𝓝 (Real.exp (-1))) :=
  numDerangements_tendsto_inv_e

/-- CO-189. Euler's product formula `φ(n) = n ∏_{p ∣ n} (1 - 1/p)`. -/
@[kb "kellertrotter2017" "Theorem 7.14, p. 174"]
theorem thm_7_14 (n : ℕ) :
    (Nat.totient n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
  Nat.totient_eq_mul_prod_factors n

/-- CO-191. Derangement recursion `d_{n+2} = (n+1)(d_n + d_{n+1})`. -/
@[kb "kellertrotter2017" "Exercise 7.22, p. 178"]
theorem ex_7_22_rec (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements n + numDerangements (n + 1)) :=
  numDerangements_add_two n

/-- CO-191. Derangement recursion `d_n = n d_{n-1} + (-1)^n` for `n ≥ 1`. -/
@[kb "kellertrotter2017" "Exercise 7.22, p. 178"]
theorem ex_7_22_alt (n : ℕ) :
    (numDerangements (n + 1) : ℤ) = (n + 1) * numDerangements n + (-1) ^ (n + 1) := by
  have := numDerangements_succ n
  rw [pow_succ]
  linarith


/-! ### Definitions of Chapter 7 in the book's terms -/

/-- CO-185. A derangement is a permutation with no fixed point. -/
@[kb "kellertrotter2017" "Definition (unnumbered) derangement, p. 171"]
theorem def_p171_derangement {α : Type*} (f : Equiv.Perm α) :
    f ∈ derangements α ↔ ∀ x, f x ≠ x :=
  Iff.rfl

/-- CO-188. Euler's `φ(n)` counts the integers in `1..n` that are relatively prime to `n`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Euler phi, p. 173"]
theorem def_p173_totient (n : ℕ) (hn : 1 ≤ n) :
    Nat.totient n = #{k ∈ Finset.Icc 1 n | Nat.Coprime k n} := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    decide
  · rw [Nat.totient_eq_card_coprime]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨⟨?_, by omega⟩, hc.symm⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp at hc; omega
      · exact hk0
    · rintro ⟨⟨hk1, hk2⟩, hc⟩
      refine ⟨?_, hc.symm⟩
      rcases Nat.lt_or_ge k n with h' | h'
      · exact h'
      · obtain rfl : k = n := by omega
        simp at hc; omega

end UndergradKB.Combinatorics.Course.KellerTrotter
