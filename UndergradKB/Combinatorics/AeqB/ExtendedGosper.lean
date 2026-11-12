import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm

/-!
# Optimality of the extended Gosper algorithm (Petkovsek–Wilf–Zeilberger, "A = B", Section 5.6)

If a sum of pairwise dissimilar hypergeometric terms `u_j` is the difference `a(n+1) - a(n)` of a
closed form `a`, then each `u_j` is Gosper-summable.  The key step is a uniqueness statement for
decompositions into pairwise dissimilar hypergeometric terms.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

theorem eg_sim_of_eq {s t : ℕ → K} (h : ∀ᶠ n : ℕ in atTop, s n = t n) : IsSimilar s t :=
  ⟨1, 1, one_ne_zero, one_ne_zero, h.mono fun n e => by simp only [eval_one, one_mul]; exact e⟩

/-- If two families of dissimilar hypergeometric terms have equal sums and the second is nonempty,
a term of the first is similar to a term of the second. -/
theorem eg_cross {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (A : Finset ι) (B : Finset κ)
    (p : ι → ℕ → K) (q : κ → ℕ → K) (hp : ∀ i ∈ A, IsHypergeometric (p i))
    (hq : ∀ j ∈ B, IsHypergeometric (q j))
    (hdA : ∀ i ∈ A, ∀ i' ∈ A, i ≠ i' → ¬ IsSimilar (p i) (p i'))
    (hdB : ∀ j ∈ B, ∀ j' ∈ B, j ≠ j' → ¬ IsSimilar (q j) (q j')) (hB : B.Nonempty)
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ A, p i n = ∑ j ∈ B, q j n) :
    ∃ i ∈ A, ∃ j ∈ B, IsSimilar (p i) (q j) := by
  classical
  obtain ⟨j0, hj0⟩ := hB
  let t : ι ⊕ κ → ℕ → K := Sum.elim p (fun j n => -q j n)
  have hne : (A.disjSum B).Nonempty := ⟨Sum.inr j0, by simp [hj0]⟩
  have ht : ∀ x ∈ A.disjSum B, IsHypergeometric (t x) := by
    intro x hx
    rcases x with i | j
    · exact hp i (by simpa using hx)
    · exact (isSimilar_neg (q j)).isHypergeometric (hq j (by simpa using hx))
  obtain ⟨x, hx, y, hy, hxy, hs⟩ := exists_similar_of_sum_eq_zero (A.disjSum B) hne t ht (by
    filter_upwards [hsum] with n h
    rw [Finset.sum_disjSum]
    simp only [t, Sum.elim_inl, Sum.elim_inr, Finset.sum_neg_distrib]
    linear_combination h)
  rcases x with i | j <;> rcases y with i' | j'
  · exact absurd hs (hdA i (by simpa using hx) i' (by simpa using hy)
      fun h => hxy (by rw [h]))
  · exact ⟨i, by simpa using hx, j', by simpa using hy, hs.trans (isSimilar_neg (q j'))⟩
  · exact ⟨i', by simpa using hy, j, by simpa using hx,
      ((isSimilar_neg (q j)).symm.trans hs).symm⟩
  · exact absurd (((isSimilar_neg (q j)).symm.trans hs).trans (isSimilar_neg (q j')))
      (hdB j (by simpa using hx) j' (by simpa using hy) fun h => hxy (by rw [h]))

/-- The uniqueness statement for sizes at most `m`. -/
def EgR (K' : Type*) [Field K'] [CharZero K'] (ι κ : Type*) [DecidableEq ι] [DecidableEq κ]
    (m : ℕ) : Prop :=
  ∀ (A : Finset ι) (B : Finset κ) (p : ι → ℕ → K') (q : κ → ℕ → K'), A.card + B.card ≤ m →
    (∀ i ∈ A, IsHypergeometric (p i)) → (∀ j ∈ B, IsHypergeometric (q j)) →
    (∀ i ∈ A, ∀ i' ∈ A, i ≠ i' → ¬ IsSimilar (p i) (p i')) →
    (∀ j ∈ B, ∀ j' ∈ B, j ≠ j' → ¬ IsSimilar (q j) (q j')) →
    (∀ᶠ n : ℕ in atTop, ∑ i ∈ A, p i n = ∑ j ∈ B, q j n) →
    ∀ j0 ∈ B, ∃ i ∈ A, ∀ᶠ n : ℕ in atTop, q j0 n = p i n

theorem eg_step {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {m : ℕ}
    (hI : EgR K ι κ m) (hS : EgR K κ ι m) : EgR K ι κ (m + 1) := by
  intro A B p q hcard hp hq hdA hdB hsum j0 hj0
  obtain ⟨i, hi, j, hj, hsim⟩ := eg_cross A B p q hp hq hdA hdB ⟨j0, hj0⟩ hsum
  have hA1 : (A.erase i).card + 1 = A.card := Finset.card_erase_add_one hi
  have hB1 : (B.erase j).card + 1 = B.card := Finset.card_erase_add_one hj
  have eA : ∀ n, ∑ x ∈ A, p x n = p i n + ∑ x ∈ A.erase i, p x n :=
    fun n => (Finset.add_sum_erase A (fun x => p x n) hi).symm
  have eB : ∀ n, ∑ x ∈ B, q x n = q j n + ∑ x ∈ B.erase j, q x n :=
    fun n => (Finset.add_sum_erase B (fun x => q x n) hj).symm
  by_cases hr : ∀ᶠ n : ℕ in atTop, p i n + -q j n = 0
  · have hrec : ∀ᶠ n : ℕ in atTop, ∑ x ∈ A.erase i, p x n = ∑ x ∈ B.erase j, q x n := by
      filter_upwards [hsum, hr] with n h1 h2
      rw [eA n, eB n] at h1
      linear_combination h1 - h2
    by_cases hjj : j0 = j
    · rw [hjj]
      exact ⟨i, hi, hr.mono fun n h => by linear_combination -h⟩
    · obtain ⟨i', hi', he⟩ := hI (A.erase i) (B.erase j) p q (by omega)
        (fun x hx => hp x (Finset.mem_of_mem_erase hx))
        (fun x hx => hq x (Finset.mem_of_mem_erase hx))
        (fun x hx y hy => hdA x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
        (fun x hx y hy => hdB x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
        hrec j0 (Finset.mem_erase.2 ⟨hjj, hj0⟩)
      exact ⟨i', Finset.mem_of_mem_erase hi', he⟩
  · have hneg : IsHypergeometric (fun n => -q j n) := (isSimilar_neg (q j)).isHypergeometric (hq j hj)
    have hrh : IsHypergeometric (fun n => p i n + -q j n) :=
      (isHypergeometric_add_iff (hp i hi) hneg hr).2 (hsim.trans (isSimilar_neg (q j)).symm)
    have hrs : IsSimilar (fun n => p i n + -q j n) (p i) :=
      (isSimilar_add_neg hsim hr).trans hsim.symm
    let p' : ι → ℕ → K := fun x => if x = i then (fun n => p i n + -q j n) else p x
    have hp'i : p' i = fun n => p i n + -q j n := by simp [p']
    have hp'ne : ∀ x, x ≠ i → p' x = p x := fun x hx => by simp [p', hx]
    have hps : ∀ x ∈ A, IsSimilar (p' x) (p x) := by
      intro x hx
      by_cases h : x = i
      · rw [h, hp'i]; exact hrs
      · rw [hp'ne x h]; exact IsSimilar.refl _
    have hp'h : ∀ x ∈ A, IsHypergeometric (p' x) := fun x hx => (hps x hx).isHypergeometric (hp x hx)
    have hdA' : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ IsSimilar (p' x) (p' y) :=
      fun x hx y hy hxy hs =>
        hdA x hx y hy hxy (((hps x hx).symm.trans hs).trans (hps y hy))
    have hsum' : ∀ᶠ n : ℕ in atTop, ∑ x ∈ A, p' x n = ∑ x ∈ B.erase j, q x n := by
      have e : ∀ n, ∑ x ∈ A, p' x n = (p i n + -q j n) + ∑ x ∈ A.erase i, p x n := by
        intro n
        rw [← Finset.add_sum_erase A (fun x => p' x n) hi, hp'i]
        congr 1
        exact Finset.sum_congr rfl fun x hx => by rw [hp'ne x (Finset.ne_of_mem_erase hx)]
      filter_upwards [hsum] with n h1
      rw [e n]
      rw [eA n, eB n] at h1
      linear_combination h1
    have hqB : ∀ x ∈ B.erase j, IsHypergeometric (q x) := fun x hx =>
      hq x (Finset.mem_of_mem_erase hx)
    have hdB' : ∀ x ∈ B.erase j, ∀ y ∈ B.erase j, x ≠ y → ¬ IsSimilar (q x) (q y) :=
      fun x hx y hy => hdB x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
    by_cases hjj : j0 = j
    · exfalso
      obtain ⟨j', hj', he⟩ := hS (B.erase j) A q p' (by omega) hqB hp'h hdB' hdA'
        (hsum'.mono fun n h => h.symm) i hi
      have hs1 : IsSimilar (q j') (p' i) := eg_sim_of_eq (he.mono fun n h => h.symm)
      exact hdB j' (Finset.mem_of_mem_erase hj') j hj (Finset.ne_of_mem_erase hj')
        ((hs1.trans (hps i hi)).trans hsim)
    · obtain ⟨i', hi', he⟩ := hI A (B.erase j) p' q (by omega) hp'h hqB hdA' hdB' hsum' j0
        (Finset.mem_erase.2 ⟨hjj, hj0⟩)
      by_cases hii : i' = i
      · exfalso
        rw [hii] at he
        exact hdB j0 hj0 j hj hjj (((eg_sim_of_eq he).trans (hps i hi)).trans hsim)
      · exact ⟨i', hi', he.mono fun n h => by rw [h, hp'ne i' hii]⟩

theorem eg_zero {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] : EgR K ι κ 0 := by
  intro A B p q hc _ _ _ _ _ j0 hj0
  have : B.card = 0 := by omega
  rw [Finset.card_eq_zero] at this
  simp [this] at hj0

theorem eg_all {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (m : ℕ) :
    EgR K ι κ m ∧ EgR K κ ι m := by
  induction m with
  | zero => exact ⟨eg_zero, eg_zero⟩
  | succ m ih => exact ⟨eg_step ih.1 ih.2, eg_step ih.2 ih.1⟩

/-- Uniqueness of decompositions into pairwise dissimilar hypergeometric terms: if two such
families have the same sum (for large `n`), every term of the second family equals (for large `n`)
a term of the first. -/
theorem eg_unique {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (A : Finset ι) (B : Finset κ)
    (p : ι → ℕ → K) (q : κ → ℕ → K) (hp : ∀ i ∈ A, IsHypergeometric (p i))
    (hq : ∀ j ∈ B, IsHypergeometric (q j))
    (hdA : ∀ i ∈ A, ∀ i' ∈ A, i ≠ i' → ¬ IsSimilar (p i) (p i'))
    (hdB : ∀ j ∈ B, ∀ j' ∈ B, j ≠ j' → ¬ IsSimilar (q j) (q j'))
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ i ∈ A, p i n = ∑ j ∈ B, q j n) :
    ∀ j0 ∈ B, ∃ i ∈ A, ∀ᶠ n : ℕ in atTop, q j0 n = p i n :=
  (eg_all (K := K) (A.card + B.card)).1 A B p q le_rfl hp hq hdA hdB hsum

/-- Core of CO-419: pairwise dissimilar hypergeometric terms `u_j` summing to `a(n+1) - a(n)` for
a closed form `a` are each Gosper-summable. -/
theorem eg_summable {ι : Type*} [DecidableEq ι] (J : Finset ι) (u : ι → ℕ → K)
    (hu : ∀ j ∈ J, IsHypergeometric (u j))
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) {a : ℕ → K} (ha : IsClosedForm a)
    (hsum : ∀ᶠ n : ℕ in atTop, ∑ j ∈ J, u j n = a (n + 1) - a n) :
    ∀ j ∈ J, IsGosperSummable (u j) := by
  classical
  obtain ⟨r, c, h, hh, hac⟩ := ha
  set I : Finset (Fin r) := Finset.univ.filter (fun i => c i ≠ 0) with hI
  have hIh : ∀ i ∈ I, IsHypergeometric (fun n => c i * h i n) := by
    intro i hi
    have hai : c i ≠ 0 := (Finset.mem_filter.1 hi).2
    exact IsSimilar.isHypergeometric
      ⟨C (c i), 1, by simpa using hai, one_ne_zero, Eventually.of_forall fun n => by simp⟩ (hh i)
  have hsumI : ∀ n, ∑ i, c i * h i n = ∑ i ∈ I, c i * h i n := fun n =>
    (Finset.sum_filter_of_ne fun x _ hx => left_ne_zero_of_mul hx).symm
  obtain ⟨J', v, -, hvh, hvd, hvsum⟩ := exists_dissimilar_sum I (fun i n => c i * h i n) hIh
  have haJ : ∀ᶠ n : ℕ in atTop, a n = ∑ k ∈ J', v k n := by
    filter_upwards [hac, hvsum] with n h1 h2
    rw [h1, hsumI, h2]
  have haJ1 : ∀ᶠ n : ℕ in atTop, a (n + 1) = ∑ k ∈ J', v k (n + 1) :=
    (tendsto_add_atTop_nat 1).eventually haJ
  set Q : Fin r → Prop := fun k => ∀ᶠ n : ℕ in atTop, v k (n + 1) = v k n with hQ
  set J1 : Finset (Fin r) := J'.filter (fun k => ¬ Q k) with hJ1
  have hconst : ∀ᶠ n : ℕ in atTop, ∀ k ∈ J'.filter Q, v k (n + 1) = v k n :=
    (Filter.eventually_all_finset _).2 fun k hk => (Finset.mem_filter.1 hk).2
  have hT : ∀ᶠ n : ℕ in atTop, ∑ j ∈ J, u j n = ∑ k ∈ J1, (v k (n + 1) - v k n) := by
    filter_upwards [hsum, haJ, haJ1, hconst] with n h1 h2 h3 h4
    have e2 : ∑ k ∈ J', (v k (n + 1) - v k n) = ∑ k ∈ J1, (v k (n + 1) - v k n) := by
      rw [← Finset.sum_filter_add_sum_filter_not J' Q]
      rw [Finset.sum_eq_zero (s := J'.filter Q) (fun k hk => sub_eq_zero.2 (h4 k hk)), zero_add]
    rw [← e2, Finset.sum_sub_distrib, ← h2, ← h3, h1]
  have hd' : ∀ k ∈ J1, IsHypergeometric (fun n => v k (n + 1) - v k n) ∧
      IsSimilar (fun n => v k (n + 1) - v k n) (v k) := fun k hk =>
    isHypergeometric_sub_succ (hvh k (Finset.mem_filter.1 hk).1) (Finset.mem_filter.1 hk).2
  intro j0 hj0
  obtain ⟨k, hk, he⟩ := eg_unique J1 J (fun k n => v k (n + 1) - v k n) u
    (fun k hk => (hd' k hk).1) hu
    (fun i hi j hj hij hs' => hvd i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
      (((hd' i hi).2.symm.trans hs').trans (hd' j hj).2))
    hd (hT.mono fun n e => e.symm) j0 hj0
  exact ⟨hu j0 hj0, v k, hvh k (Finset.mem_filter.1 hk).1, he.mono fun n e => e.symm⟩

/-- CO-419. Optimality of the extended Gosper algorithm (page 105, with Theorem 5.6.3): if the
hypergeometric terms `t_i` (`i ∈ s`) sum to the difference `a(n+1) - a(n)` of a closed form `a`
(a fixed-length linear combination of hypergeometric terms, `IsClosedForm`, which is slightly more
general than a finite sum of hypergeometric terms), then the dissimilar terms `u_j` produced by
Step 1 are all Gosper-summable, so Gosper's algorithm succeeds on each of them, all outputs
`gosperAntidiff (u j)` are hypergeometric terms, and they add up to an antidifference of
`∑ t_i`.  The converse direction (failure of Gosper's algorithm precludes a closed form) is
`not_closed_form_of_not_isGosperSummable` (CO-418). -/
@[kb "petkovsekwilfzeilberger1996" "Extended Gosper's Algorithm, p. 105"]
theorem extended_gosper_optimal {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℕ → K)
    (ht : ∀ i ∈ s, IsHypergeometric (t i)) {a : ℕ → K} (ha : IsClosedForm a)
    (hs : ∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = a (n + 1) - a n) :
    ∃ (J : Finset ι) (u : ι → ℕ → K), J ⊆ s ∧ (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in atTop, ∑ i ∈ s, t i n = ∑ j ∈ J, u j n) ∧
      (∀ j ∈ J, IsGosperSummable (u j) ∧ IsHypergeometric (gosperAntidiff (u j))) ∧
      ∀ᶠ n : ℕ in atTop, ∑ j ∈ J, gosperAntidiff (u j) (n + 1) - ∑ j ∈ J, gosperAntidiff (u j) n
        = ∑ i ∈ s, t i n := by
  obtain ⟨J, u, hJs, hJh, hJd, hJsum, -, hfin⟩ := extended_gosper s t ht
  refine ⟨J, u, hJs, hJh, hJd, hJsum, fun j hj => ?_, hfin⟩
  have hsm := eg_summable J u hJh hJd ha
    (by filter_upwards [hJsum, hs] with n h1 h2; rw [← h1, h2]) j hj
  exact ⟨hsm, gosperAntidiff_isHypergeometric hsm⟩

end UndergradKB.Combinatorics.AeqB
