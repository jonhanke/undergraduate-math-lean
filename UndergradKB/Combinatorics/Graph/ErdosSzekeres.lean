import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Card
import UndergradKB.Common.Attr

/-!
# The Erdős–Szekeres theorem (Keller–Trotter, Theorem 4.2) and its sharpness

A sequence is a function `f : Fin N → α`; a subsequence is a finset of indices `s`, increasing if
`StrictMonoOn f s`, decreasing if `StrictAntiOn f s`.
-/

namespace UndergradKB.Combinatorics

open Finset

section Aux

variable {N : ℕ} {β : Type*} [LinearOrder β]

open scoped Classical in
/-- Length of a longest increasing subsequence of `f` ending exactly at index `i`. -/
noncomputable def incLen (f : Fin N → β) (i : Fin N) : ℕ :=
  ((univ : Finset (Finset (Fin N))).filter
    (fun s : Finset (Fin N) => i ∈ s ∧ (∀ j ∈ s, j ≤ i) ∧ StrictMonoOn f s)).sup Finset.card

private lemma exists_incLen (f : Fin N → β) (i : Fin N) :
    ∃ s : Finset (Fin N), i ∈ s ∧ (∀ j ∈ s, j ≤ i) ∧ StrictMonoOn f s ∧ s.card = incLen f i := by
  classical
  have hne : ((univ : Finset (Finset (Fin N))).filter
      (fun s : Finset (Fin N) => i ∈ s ∧ (∀ j ∈ s, j ≤ i) ∧ StrictMonoOn f s)).Nonempty :=
    ⟨{i}, by simp [StrictMonoOn]⟩
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [mem_filter, mem_univ, true_and] at hs
  exact ⟨s, hs.1, hs.2.1, hs.2.2, by simp only [incLen]; convert h.symm⟩

private lemma le_incLen (f : Fin N → β) {i : Fin N} {s : Finset (Fin N)} (hi : i ∈ s)
    (hle : ∀ j ∈ s, j ≤ i) (hs : StrictMonoOn f s) : s.card ≤ incLen f i := by
  classical
  unfold incLen
  exact Finset.le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, hi, hle, hs⟩)

private lemma incLen_lt (f : Fin N → β) {i j : Fin N} (hij : i < j) (hf : f i < f j) :
    incLen f i < incLen f j := by
  obtain ⟨s, hi, hle, hs, hc⟩ := exists_incLen f i
  classical
  have hj : j ∉ s := fun h => absurd (hle j h) (not_le.2 hij)
  have hle' : ∀ x ∈ insert j s, x ≤ j := by
    intro x hx
    rcases mem_insert.1 hx with hxj | hx
    · exact hxj.le
    · exact (hle x hx).trans hij.le
  have hmono : StrictMonoOn f (insert j s : Finset (Fin N)) := by
    intro x hx0 y hy0 hxy
    rw [mem_coe] at hx0 hy0
    rcases mem_insert.1 hx0 with hxj | hxs
    · rcases mem_insert.1 hy0 with hyj | hys
      · exact absurd (hxj.trans hyj.symm) hxy.ne
      · exact absurd ((hle y hys).trans_lt (hij.trans_eq hxj.symm)) (not_lt.2 hxy.le)
    · rcases mem_insert.1 hy0 with hyj | hys
      · rw [hyj]
        rcases (hle x hxs).eq_or_lt with h | h
        · rw [h]; exact hf
        · exact (hs (mem_coe.2 hxs) (mem_coe.2 hi) h).trans hf
      · exact hs (mem_coe.2 hxs) (mem_coe.2 hys) hxy
  have := le_incLen f (i := j) (s := insert j s) (mem_insert_self _ _) hle' hmono
  rw [card_insert_of_notMem hj] at this
  omega

end Aux

/-- CO-073. Erdős–Szekeres: among `m*n+1` distinct real numbers (in a sequence) there is an
increasing subsequence with `m+1` terms or a decreasing one with `n+1` terms. -/
@[kb "kellertrotter2017" "Theorem 4.2, p. 83"]
theorem erdos_szekeres (m n : ℕ) (f : Fin (m * n + 1) → ℝ) (hf : Function.Injective f) :
    (∃ s : Finset (Fin (m * n + 1)), s.card = m + 1 ∧ StrictMonoOn f s) ∨
    (∃ s : Finset (Fin (m * n + 1)), s.card = n + 1 ∧ StrictAntiOn f s) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  let d : Fin (m * n + 1) → ℝᵒᵈ := fun k => OrderDual.toDual (f k)
  let g : Fin (m * n + 1) → ℕ × ℕ := fun i => (incLen f i - 1, incLen d i - 1)
  have hbound : ∀ (β : Type) [LinearOrder β] (e : Fin (m * n + 1) → β) (k : ℕ),
      (∀ s : Finset (Fin (m * n + 1)), s.card = k + 1 → ¬ StrictMonoOn e s) →
      ∀ i, incLen e i ≤ k := by
    intro β _ e k h i
    by_contra hk
    obtain ⟨s, -, -, hs, hc⟩ := exists_incLen e i
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := s) (n := k + 1) (by omega)
    exact h t htc (hs.mono hts)
  have hA := hbound ℝ f m h1
  have hB := hbound ℝᵒᵈ d n (fun s hs hm => h2 s hs (fun x hx y hy hxy => hm hx hy hxy))
  have hpos : ∀ (β : Type) [LinearOrder β] (e : Fin (m * n + 1) → β) (i : Fin (m * n + 1)),
      1 ≤ incLen e i := by
    intro β _ e i
    obtain ⟨s, hi, -, -, hc⟩ := exists_incLen e i
    have := Finset.card_pos.2 ⟨i, hi⟩
    omega
  have hmaps : ∀ i ∈ (univ : Finset (Fin (m * n + 1))), g i ∈ (range m) ×ˢ (range n) := by
    intro i _
    have a := hA i
    have b := hB i
    have a' := hpos ℝ f i
    have b' := hpos ℝᵒᵈ d i
    simp only [g, mem_product, mem_range]
    omega
  have hcard : ((range m) ×ˢ (range n)).card < (univ : Finset (Fin (m * n + 1))).card := by
    simp
  obtain ⟨i, -, j, -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [g, Prod.mk.injEq] at heq
  have ha' := hpos ℝ f i
  have hb' := hpos ℝᵒᵈ d i
  have ha'' := hpos ℝ f j
  have hb'' := hpos ℝᵒᵈ d j
  have key : ∀ i j : Fin (m * n + 1), i < j →
      ¬ (incLen f i = incLen f j ∧ incLen d i = incLen d j) := by
    intro i j hij ⟨e1, e2⟩
    rcases lt_or_gt_of_ne (hf.ne hij.ne) with h | h
    · have := incLen_lt f hij h; omega
    · have := incLen_lt d hij (show d i < d j from h); omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h ⟨by omega, by omega⟩
  · exact key j i h ⟨by omega, by omega⟩

/-- The sharpness example for CO-074: index `a*n+b` (with `a < m`, `b < n`) gets the value
`a*n + (n-1-b)`: increasing from block to block, decreasing inside each block. -/
def esExample (m n : ℕ) (i : Fin (m * n)) : ℝ :=
  (((i : ℕ) / n * n + (n - 1 - (i : ℕ) % n) : ℕ) : ℝ)

private lemma esExample_lt {m n : ℕ} {i j : Fin (m * n)} (hij : i < j) :
    ((i : ℕ) / n < (j : ℕ) / n ∧ esExample m n i < esExample m n j) ∨
    ((i : ℕ) / n = (j : ℕ) / n ∧ esExample m n j < esExample m n i) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd i.2 (by simp)
    · exact h
  have hij' : (i : ℕ) < j := hij
  have hi := Nat.div_add_mod (i : ℕ) n
  have hj := Nat.div_add_mod (j : ℕ) n
  have hmi := Nat.mod_lt (i : ℕ) hn
  have hmj := Nat.mod_lt (j : ℕ) hn
  have hle : (i : ℕ) / n ≤ (j : ℕ) / n := Nat.div_le_div_right hij'.le
  unfold esExample
  rcases hle.lt_or_eq with h | h
  · left
    refine ⟨h, ?_⟩
    rw [Nat.cast_lt]
    have : ((i : ℕ) / n + 1) * n ≤ (j : ℕ) / n * n := Nat.mul_le_mul_right _ h
    have h3 : ((i : ℕ) / n + 1) * n = (i : ℕ) / n * n + n := by ring
    omega
  · right
    refine ⟨h, ?_⟩
    rw [Nat.cast_lt, ← h]
    have : (i : ℕ) % n < (j : ℕ) % n := by
      rw [← h] at hj
      omega
    omega

/-- CO-074. Sharpness of Erdős–Szekeres: for all `m n` there are `m*n` distinct reals with no
increasing subsequence of length `m+1` and no decreasing subsequence of length `n+1`. -/
@[kb "kellertrotter2017" "text, p. 88"]
theorem erdos_szekeres_sharp (m n : ℕ) :
    ∃ f : Fin (m * n) → ℝ, Function.Injective f ∧
      (∀ s : Finset (Fin (m * n)), StrictMonoOn f s → s.card ≤ m) ∧
      (∀ s : Finset (Fin (m * n)), StrictAntiOn f s → s.card ≤ n) := by
  refine ⟨esExample m n, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · rcases esExample_lt h with ⟨-, h'⟩ | ⟨-, h'⟩ <;> linarith
    · rcases esExample_lt h with ⟨-, h'⟩ | ⟨-, h'⟩ <;> linarith
  · intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : IsEmpty (Fin (m * 0)) := by simp
      simp [Finset.eq_empty_of_isEmpty s]
    have := Finset.card_le_card_of_injOn (s := s) (t := range m) (fun i : Fin (m * n) => (i : ℕ) / n)
      (by
        intro i _
        simp only [coe_range, Set.mem_Iio]
        exact (Nat.div_lt_iff_lt_mul hn).2 i.2)
      (by
        intro i hi j hj hij
        by_contra hne
        simp only at hij
        rcases lt_or_gt_of_ne hne with h | h
        · rcases esExample_lt h with ⟨h', -⟩ | ⟨-, h'⟩
          · omega
          · exact absurd (hs hi hj h) (not_lt.2 h'.le)
        · rcases esExample_lt h with ⟨h', -⟩ | ⟨-, h'⟩
          · omega
          · exact absurd (hs hj hi h) (not_lt.2 h'.le))
    simpa using this
  · intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : IsEmpty (Fin (m * 0)) := by simp
      simp [Finset.eq_empty_of_isEmpty s]
    have := Finset.card_le_card_of_injOn (s := s) (t := range n) (fun i : Fin (m * n) => (i : ℕ) % n)
      (by
        intro i _
        simp only [coe_range, Set.mem_Iio]
        exact Nat.mod_lt _ hn)
      (by
        intro i hi j hj hij
        by_contra hne
        simp only at hij
        have key : ∀ i j : Fin (m * n), i < j → i ∈ s → j ∈ s → (i : ℕ) % n = (j : ℕ) % n → False := by
          intro i j h hi hj hij
          rcases esExample_lt h with ⟨-, h'⟩ | ⟨h', -⟩
          · exact absurd (hs hi hj h) (not_lt.2 h'.le)
          · have h1 := Nat.div_add_mod (i : ℕ) n
            have h2 := Nat.div_add_mod (j : ℕ) n
            have : (i : ℕ) = j := by rw [← h1, ← h2, h', hij]
            exact absurd h (by simp [Fin.lt_def, this])
        rcases lt_or_gt_of_ne hne with h | h
        · exact key i j h hi hj hij
        · exact key j i h hj hi hij.symm)
    simpa using this

end UndergradKB.Combinatorics
