import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 16 (extremal set theory, partitions): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-327. An intersecting family of subsets of an `n`-set has at most `2^(n-1)` members
(for `n ≥ 1`). -/
@[kb "kellertrotter2017" "Exercise 16.6, p. 342"]
theorem ex_16_6 {n : ℕ} (hn : 1 ≤ n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) : 𝒜.card ≤ 2 ^ (n - 1) := by
  have h := h𝒜.card_le
  simp only [Fintype.card_finset, Fintype.card_fin] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ] at h
  omega

/-- CO-328. Sperner's theorem: an antichain of subsets of an `n`-set has at most
`C(n, ⌊n/2⌋)` members. -/
@[kb "kellertrotter2017" "Exercise 16.7, p. 343"]
theorem ex_16_7 {n : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset (Fin n)))) :
    𝒜.card ≤ n.choose (n / 2) := by
  simpa using h𝒜.sperner

/-- CO-330. Erdős–Ko–Rado: for `n ≥ 2k`, an intersecting family of `k`-subsets of an `n`-set has at
most `C(n-1, k-1)` members. -/
@[kb "kellertrotter2017" "Theorem 16.8, p. 343"]
theorem thm_16_8 {n k : ℕ} (hnk : 2 * k ≤ n) {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) (hk : (𝒜 : Set (Finset (Fin n))).Sized k) :
    𝒜.card ≤ (n - 1).choose (k - 1) :=
  Finset.erdos_ko_rado h𝒜 hk (by omega)

/-- CO-333. The dual (conjugate) of the dual of a partition is the partition itself. -/
@[kb "kellertrotter2017" "text (dual partition), p. 348"]
theorem text_p348_dual_dual {n : ℕ} (p : Nat.Partition n) : p.conjugate.conjugate = p :=
  Nat.Partition.conjugate_conjugate p

end UndergradKB.Combinatorics.Course.KellerTrotter
