import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import UndergradKB.Topology.Sharkovskii
import UndergradKB.Topology.SharkovskiiConverse
import UndergradKB.Topology.SharkovskiiOdd6
import UndergradKB.Common.Attr

/-!
# The converse of Sharkovskii's theorem for odd periods

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.6 (`morris2024`).  The Štefan map
`stefanMap n` (a continuous map of the real line with a cycle of prime period `m = 2 n + 1` and no point of odd
prime period `l` with `3 ≤ l < m`) gives, with the doubling construction of `SharkovskiiConverse`, a continuous
map with a point of prime period `2^k · m` and none of prime period `l` for any `l` preceding `2^k · m` in
Sharkovskii's ordering.  Together with the cases `2^k` this proves the converse for every `n`.
-/

open Function Set

namespace UndergradKB.Topology

/-- The Štefan map, packaged for the doubling construction: its periodic points lie in `[0, 2 n]` and have
prime period different from the odd numbers `l` with `3 ≤ l < 2 n + 1`. -/
theorem dblDataS_stefan {n : ℕ} (hn : 1 ≤ n) :
    DblDataS {p | ¬ (3 ≤ p ∧ p < 2 * n + 1 ∧ p % 2 = 1)} (2 * n + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨stefanMap n, 0, 2 * n, continuous_stefanMap hn, by linarith, fun x _ => stefanMap_mem hn x,
    ⟨n, ⟨by positivity, by linarith⟩, minimalPeriod_stefan_center hn⟩, ?_⟩
  intro x hpos
  have hxI : x ∈ Icc (0 : ℝ) (2 * n) := by
    obtain ⟨p, hp⟩ : ∃ p, minimalPeriod (stefanMap n) x = p + 1 := ⟨minimalPeriod (stefanMap n) x - 1, by omega⟩
    have := (isPeriodicPt_minimalPeriod (stefanMap n) x).eq
    rw [hp, iterate_succ_apply'] at this
    rw [← this]
    exact stefanMap_mem hn _
  refine ⟨hxI, fun h => ?_⟩
  exact not_odd_period_stefan hn h.2.2 h.1 h.2.1 ⟨x, rfl⟩

private theorem not_sharkovskiiLT_two_pow_mul_odd (j k : ℕ) {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    ¬ SharkovskiiLT (2 ^ j) (2 ^ k * m) := by
  have h1 := factorization_two_pow_mul_odd j 1 (by norm_num) one_ne_zero
  have h2 := factorization_two_pow_mul_odd k m (by omega) (by omega)
  rw [mul_one] at h1
  unfold SharkovskiiLT sharkovskiiAux
  rw [h1.1, h1.2, h2.1, h2.2]
  omega

private theorem not_sharkovskiiLT_mul_two_pow_mul_odd (k : ℕ) {s m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1)
    (hs : s ≠ 0) (hS : ¬ (3 ≤ s ∧ s < m ∧ s % 2 = 1)) : ¬ SharkovskiiLT (2 ^ k * s) (2 ^ k * m) := by
  obtain ⟨c, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs
  have ht' : t % 2 = 1 := Nat.odd_iff.mp ht
  have h1 := factorization_two_pow_mul_odd (k + c) t (by omega) (by omega)
  have h2 := factorization_two_pow_mul_odd k m (by omega) (by omega)
  have e : 2 ^ k * (2 ^ c * t) = 2 ^ (k + c) * t := by ring
  rw [e]
  unfold SharkovskiiLT sharkovskiiAux
  rw [h1.1, h1.2, h2.1, h2.2]
  by_cases hc : c = 0
  · subst hc
    simp only [pow_zero, one_mul] at hS
    omega
  · omega

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 2^k · m`, `m ≥ 3` odd: there is a
continuous `f : ℝ → ℝ` with a point of prime period `2^k · m` and none of prime period `l` for any `l`
preceding `2^k · m` in Sharkovskii's ordering (the Štefan map doubled `k` times). -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_two_pow_mul_odd (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 2 ^ k * (2 * n + 1)) ∧
      ∀ l, 0 < l → SharkovskiiLT l (2 ^ k * (2 * n + 1)) → ¬ ∃ x, minimalPeriod f x = l := by
  obtain ⟨f, a, b, hf, -, -, ⟨x0, -, hx0⟩, hper⟩ :=
    dblDataS_iterate (by omega) (dblDataS_stefan hn) k
  refine ⟨f, hf, ⟨x0, hx0⟩, ?_⟩
  rintro l hl h ⟨x, hx⟩
  obtain ⟨-, hS⟩ := hper x (hx ▸ hl)
  rw [hx] at hS
  rcases mem_dblSet_iterate k hS with ⟨j, hj, rfl⟩ | ⟨s, hs, rfl⟩
  · exact not_sharkovskiiLT_two_pow_mul_odd j k (by omega) (by omega) h
  · exact not_sharkovskiiLT_mul_two_pow_mul_odd k (by omega) (by omega)
      (by rintro rfl; simp at hl) hs h

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), the Converse of Sharkovskii's Theorem: for
every `n ≥ 1` there is a continuous `f : ℝ → ℝ` with a point of prime period `n` and no point of prime period
`l` for any `l` preceding `n` in Sharkovskii's ordering. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii {n : ℕ} (hn : 0 < n) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = n) ∧
      ∀ l, 0 < l → SharkovskiiLT l n → ¬ ∃ x, minimalPeriod f x = l := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one]
    exact converse_sharkovskii_two_pow a
  · obtain ⟨n', rfl⟩ : ∃ n', m = 2 * n' + 1 := ⟨m / 2, by omega⟩
    exact converse_sharkovskii_two_pow_mul_odd a (by omega)

end UndergradKB.Topology
