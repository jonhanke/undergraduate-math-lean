import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.List.Permutation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Bool.Count
import UndergradKB.Common.Attr

/-!
# Miscellaneous Keller–Trotter counting results

CO-013, CO-014 (lattice paths below the diagonal, Catalan numbers, reflection), CO-015
(rearrangements of a word), CO-024 (functions as relations), CO-059, CO-061, CO-062 (division
algorithm and Euclid's algorithm), CO-069 (telescoping), CO-070 (merge sort recurrence),
CO-026 (derangements and `n!/e`).
-/

namespace UndergradKB.Combinatorics

open Finset

/-! ### CO-015: rearrangements of a word -/

section Arrangements

variable {α : Type*} [DecidableEq α]

/-- The set of distinct rearrangements (as lists) of the multiset `m` of letters. -/
noncomputable def arrangements (m : Multiset α) : Finset (List α) := m.toList.permutations.toFinset

theorem mem_arrangements {m : Multiset α} {l : List α} :
    l ∈ arrangements m ↔ (l : Multiset α) = m := by
  rw [arrangements, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact (Multiset.coe_eq_coe.mpr h).trans (Multiset.coe_toList m)
  · intro h
    have := Multiset.coe_eq_coe.mp (h.trans (Multiset.coe_toList m).symm)
    exact this

theorem arrangements_zero : arrangements (0 : Multiset α) = {[]} := by
  ext l
  simp [mem_arrangements]

theorem arrangements_eq_biUnion {m : Multiset α} (hm : m ≠ 0) :
    arrangements m = m.toFinset.biUnion
      (fun a => (arrangements (m.erase a)).image (a :: ·)) := by
  ext l
  simp only [mem_arrangements, Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_image]
  constructor
  · intro h
    cases l with
    | nil =>
      exfalso
      apply hm
      rw [← h]; rfl
    | cons b t =>
      refine ⟨b, ?_, t, ?_, rfl⟩
      · rw [← h]; simp
      · rw [← h]; simp
  · rintro ⟨a, ha, t, ht, rfl⟩
    rw [← Multiset.cons_erase ha, ← ht]
    rfl

/-- CO-015 (product form). If the word has `n` letters, letter `a` occurring `k_a` times, the
number of distinct rearrangements times `∏ k_a !` is `n !` (the product may be taken over any
finite set `s` of letters containing those that occur). -/
theorem card_arrangements_mul_prod_factorial (n : ℕ) :
    ∀ (m : Multiset α) (s : Finset α), Multiset.card m = n → m.toFinset ⊆ s →
      (arrangements m).card * ∏ a ∈ s, (m.count a).factorial = n.factorial := by
  induction n with
  | zero =>
    intro m s hn _
    rw [Multiset.card_eq_zero.mp hn, arrangements_zero]
    simp
  | succ n ih =>
    intro m s hn hs
    have hm : m ≠ 0 := by
      rintro rfl; simp at hn
    rw [arrangements_eq_biUnion hm, Finset.card_biUnion]
    · have key : ∀ a ∈ m.toFinset,
          (((arrangements (m.erase a)).image (a :: ·)).card) * ∏ b ∈ s, (m.count b).factorial =
            n.factorial * m.count a := by
        intro a ha
        have ha' : a ∈ m := Multiset.mem_toFinset.mp ha
        rw [Finset.card_image_of_injective _ (List.cons_injective)]
        have hcard : Multiset.card (m.erase a) = n := by
          rw [Multiset.card_erase_of_mem ha', hn]; rfl
        have hsub : (m.erase a).toFinset ⊆ s := by
          intro b hb
          exact hs (Multiset.mem_toFinset.mpr (Multiset.mem_of_mem_erase (Multiset.mem_toFinset.mp hb)))
        have ih' := ih (m.erase a) s hcard hsub
        have has : a ∈ s := hs ha
        have hprod : ∏ b ∈ s, (m.count b).factorial =
            m.count a * ∏ b ∈ s, ((m.erase a).count b).factorial := by
          rw [← Finset.mul_prod_erase s _ has, ← Finset.mul_prod_erase s
            (fun b => ((m.erase a).count b).factorial) has]
          have h1 : ∏ b ∈ s.erase a, (m.count b).factorial =
              ∏ b ∈ s.erase a, ((m.erase a).count b).factorial := by
            refine Finset.prod_congr rfl fun b hb => ?_
            rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hb)]
          rw [h1, Multiset.count_erase_self]
          have hpos : 0 < m.count a := Multiset.count_pos.mpr ha'
          obtain ⟨c, hc⟩ : ∃ c, m.count a = c + 1 := ⟨m.count a - 1, by omega⟩
          rw [hc, Nat.add_sub_cancel, Nat.factorial_succ]
          ring
        rw [hprod, ← mul_assoc, mul_comm _ (m.count a), mul_assoc, ih']
        ring
      rw [Finset.sum_mul, Finset.sum_congr rfl key, ← Finset.mul_sum]
      have := Multiset.toFinset_sum_count_eq m
      rw [this, hn, Nat.factorial_succ]
      ring
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro l hl hl'
      simp only [Finset.mem_image] at hl hl'
      obtain ⟨t, _, rfl⟩ := hl
      obtain ⟨t', _, h⟩ := hl'
      exact hab (List.cons.inj h).1.symm

/-- CO-015. The number of rearrangements of a word with `n` letters in which letter `a` occurs
`k_a` times is `n! / ∏ k_a !`. -/
@[kb "kellertrotter2017" "Example 2.32, p. 54"]
theorem card_arrangements (m : Multiset α) :
    (arrangements m).card = (Multiset.card m).factorial / ∏ a ∈ m.toFinset, (m.count a).factorial := by
  have h := card_arrangements_mul_prod_factorial _ m m.toFinset rfl subset_rfl
  have hpos : 0 < ∏ a ∈ m.toFinset, (m.count a).factorial :=
    Finset.prod_pos fun a _ => Nat.factorial_pos _
  rw [← h, Nat.mul_div_cancel _ hpos]

/-- CO-015, book shape. For `k : Fin r → ℕ`, the number of words in the alphabet `Fin r` in which
letter `i` occurs exactly `k i` times is the multinomial coefficient `(Σ k)! / ∏ (k i)!`. -/
@[kb "kellertrotter2017" "Example 2.32, p. 54"]
theorem card_words_with_multiplicities {r : ℕ} (k : Fin r → ℕ) :
    ((arrangements (∑ i, Multiset.replicate (k i) i)).card) =
      Nat.multinomial Finset.univ k := by
  have h := card_arrangements_mul_prod_factorial _ (∑ i, Multiset.replicate (k i) i)
    Finset.univ rfl (Finset.subset_univ _)
  have hc : ∀ a, (∑ i, Multiset.replicate (k i) i).count a = k a := by
    intro a
    rw [Multiset.count_sum']
    simp [Multiset.count_replicate]
  have hcard : Multiset.card (∑ i, Multiset.replicate (k i) i) = ∑ i, k i := by
    simp
  simp only [hc] at h
  rw [hcard] at h
  have h2 := Nat.multinomial_spec Finset.univ k
  have hpos : 0 < ∏ a, (k a).factorial := Finset.prod_pos fun a _ => Nat.factorial_pos _
  have := h.trans h2.symm
  rw [mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

end Arrangements

/-! ### CO-013, CO-014: lattice paths below the diagonal -/

section LatticePaths

/-- Lattice paths from `(0,0)` to `(a,b)` as words in `{H,V}` (`true` = horizontal step,
`false` = vertical step) with `a` letters `H` and `b` letters `V`. -/
noncomputable def stepWords (a b : ℕ) : Finset (List Bool) :=
  arrangements (Multiset.replicate a true + Multiset.replicate b false)

theorem mem_stepWords {a b : ℕ} {w : List Bool} :
    w ∈ stepWords a b ↔ w.count true = a ∧ w.count false = b := by
  rw [stepWords, mem_arrangements, Multiset.ext]
  constructor
  · intro h
    have h1 := h true
    have h2 := h false
    simp [Multiset.coe_count, Multiset.count_replicate] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ x
    cases x <;> simp [Multiset.count_replicate, h1, h2]

/-- Example 2.27: the number of lattice paths to `(a,b)` is `C(a+b, a)`. -/
theorem card_stepWords (a b : ℕ) : (stepWords a b).card = (a + b).choose a := by
  have h := card_arrangements_mul_prod_factorial (a + b)
    (Multiset.replicate a true + Multiset.replicate b false) Finset.univ (by simp)
    (Finset.subset_univ _)
  have hc : (Multiset.replicate a true + Multiset.replicate b false).card = a + b := by simp
  have e : ∏ x : Bool, ((Multiset.replicate a true + Multiset.replicate b false).count x).factorial
      = a.factorial * b.factorial := by
    simp [Fintype.prod_bool, Multiset.count_replicate]
  rw [e] at h
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h2
  have hpos : 0 < a.factorial * b.factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  rw [stepWords]
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← h2]; ring

/-- A lattice path is *good* if in every initial segment the number of `V` steps never exceeds the
number of `H` steps (never goes above the diagonal). -/
def IsGoodPath (w : List Bool) : Prop :=
  ∀ k, (w.take k).count false ≤ (w.take k).count true

noncomputable instance : DecidablePred IsGoodPath := Classical.decPred _

/-- The good lattice paths from `(0,0)` to `(n,n)`. -/
noncomputable def goodPaths (n : ℕ) : Finset (List Bool) :=
  (stepWords n n).filter IsGoodPath

/-- The bad lattice paths from `(0,0)` to `(n,n)` (those crossing above the diagonal). -/
noncomputable def badPaths (n : ℕ) : Finset (List Bool) :=
  (stepWords n n).filter (fun w => ¬ IsGoodPath w)

theorem mem_goodPaths {n : ℕ} {w : List Bool} :
    w ∈ goodPaths n ↔ w.count true = n ∧ w.count false = n ∧ IsGoodPath w := by
  rw [goodPaths, Finset.mem_filter, mem_stepWords, and_assoc]

/-! Bridge to Mathlib's Dyck words: `H ↦ U`, `V ↦ D`. -/

/-- The letter correspondence `H ↦ U`, `V ↦ D`. -/
def stepOf : Bool → DyckStep
  | true => DyckStep.U
  | false => DyckStep.D

/-- Inverse letter correspondence. -/
def boolOf : DyckStep → Bool
  | DyckStep.U => true
  | DyckStep.D => false

theorem boolOf_stepOf (b : Bool) : boolOf (stepOf b) = b := by cases b <;> rfl
theorem stepOf_boolOf (s : DyckStep) : stepOf (boolOf s) = s := by cases s <;> rfl

theorem stepOf_injective : Function.Injective stepOf :=
  Function.LeftInverse.injective boolOf_stepOf
theorem boolOf_injective : Function.Injective boolOf :=
  Function.LeftInverse.injective stepOf_boolOf

theorem count_U_map_stepOf (w : List Bool) : (w.map stepOf).count DyckStep.U = w.count true :=
  List.count_map_of_injective w stepOf stepOf_injective true
theorem count_D_map_stepOf (w : List Bool) : (w.map stepOf).count DyckStep.D = w.count false :=
  List.count_map_of_injective w stepOf stepOf_injective false
theorem count_true_map_boolOf (l : List DyckStep) :
    (l.map boolOf).count true = l.count DyckStep.U :=
  List.count_map_of_injective l boolOf boolOf_injective DyckStep.U
theorem count_false_map_boolOf (l : List DyckStep) :
    (l.map boolOf).count false = l.count DyckStep.D :=
  List.count_map_of_injective l boolOf boolOf_injective DyckStep.D

/-- Good lattice paths to `(n,n)` correspond to Dyck words of semilength `n`. -/
noncomputable def goodPathsEquivDyck (n : ℕ) :
    {w // w ∈ goodPaths n} ≃ {p : DyckWord // p.semilength = n} where
  toFun w :=
    ⟨⟨w.1.map stepOf, by
        obtain ⟨h1, h2, _⟩ := mem_goodPaths.mp w.2
        rw [count_U_map_stepOf, count_D_map_stepOf, h1, h2], by
        intro i
        obtain ⟨_, _, h3⟩ := mem_goodPaths.mp w.2
        rw [← List.map_take, count_U_map_stepOf, count_D_map_stepOf]
        exact h3 i⟩, by
      obtain ⟨h1, _, _⟩ := mem_goodPaths.mp w.2
      show (w.1.map stepOf).count DyckStep.U = n
      rw [count_U_map_stepOf, h1]⟩
  invFun p :=
    ⟨p.1.toList.map boolOf, by
      have h1 : p.1.toList.count DyckStep.U = n := p.2
      have h2 := p.1.count_U_eq_count_D
      rw [mem_goodPaths, count_true_map_boolOf, count_false_map_boolOf]
      refine ⟨h1, by omega, fun i => ?_⟩
      rw [← List.map_take, count_true_map_boolOf, count_false_map_boolOf]
      exact p.1.count_D_le_count_U i⟩
  left_inv w := by
    apply Subtype.ext
    simp [List.map_map, Function.comp_def, boolOf_stepOf]
  right_inv p := by
    apply Subtype.ext
    apply DyckWord.ext
    simp [List.map_map, Function.comp_def, stepOf_boolOf]

/-- CO-013. The number of lattice paths from `(0,0)` to `(n,n)` that never go above the diagonal
is the Catalan number `C(2n,n)/(n+1)`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem card_goodPaths_eq_catalan (n : ℕ) :
    (goodPaths n).card = catalan n := by
  rw [← DyckWord.card_dyckWord_semilength_eq_catalan,
    ← Fintype.card_congr (goodPathsEquivDyck n), Fintype.card_coe]

/-- CO-013, closed form: `|G| = C(2n,n)/(n+1)`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem card_goodPaths_eq_centralBinom_div (n : ℕ) :
    (goodPaths n).card = n.centralBinom / (n + 1) := by
  rw [card_goodPaths_eq_catalan, catalan_eq_centralBinom_div]

/-! The reflection principle. -/

/-- Balance of a path started from height `d`: horizontal steps minus vertical steps. -/
def PathBal (d : ℤ) (l : List Bool) : ℤ := d + l.count true - l.count false

/-- The path started from height `d` reaches height `-1` (touches the line above the diagonal). -/
def Hit (d : ℤ) (l : List Bool) : Prop := ∃ k, PathBal d (l.take k) = -1

/-- The height after one step. -/
def stepH (d : ℤ) (b : Bool) : ℤ := if b then d + 1 else d - 1

theorem bal_cons (d : ℤ) (b : Bool) (l : List Bool) :
    PathBal d (b :: l) = PathBal (stepH d b) l := by
  cases b <;> simp [PathBal, stepH, List.count_cons] <;> ring

theorem hit_nil (d : ℤ) : Hit d [] ↔ d = -1 := by simp [Hit, PathBal]

theorem hit_cons (d : ℤ) (b : Bool) (l : List Bool) :
    Hit d (b :: l) ↔ d = -1 ∨ Hit (stepH d b) l := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => left; simpa [PathBal] using hk
    | succ k =>
      right
      rw [List.take_succ_cons, bal_cons] at hk
      exact ⟨k, hk⟩
  · rintro (h | ⟨k, hk⟩)
    · exact ⟨0, by simp [PathBal, h]⟩
    · exact ⟨k + 1, by rw [List.take_succ_cons, bal_cons]; exact hk⟩

theorem hit_of_le : ∀ (l : List Bool) (d : ℤ), -1 ≤ d →
    (∃ k, PathBal d (l.take k) ≤ -1) → Hit d l
  | [], d, hd, ⟨k, hk⟩ => by
    rw [hit_nil]
    simp [PathBal] at hk
    omega
  | b :: l, d, hd, ⟨k, hk⟩ => by
    rw [hit_cons]
    by_cases h : d = -1
    · exact Or.inl h
    · right
      cases k with
      | zero => simp [PathBal] at hk; omega
      | succ k =>
        rw [List.take_succ_cons, bal_cons] at hk
        refine hit_of_le l _ ?_ ⟨k, hk⟩
        cases b <;> simp [stepH] <;> omega

theorem not_isGoodPath_iff_hit (w : List Bool) : ¬ IsGoodPath w ↔ Hit 0 w := by
  constructor
  · intro h
    unfold IsGoodPath at h
    push Not at h
    obtain ⟨k, hk⟩ := h
    refine hit_of_le w 0 (by norm_num) ⟨k, ?_⟩
    simp only [PathBal]
    omega
  · rintro ⟨k, hk⟩ hg
    have := hg k
    simp only [PathBal] at hk
    omega

/-- Reflection: flip all steps after the first time the path reaches height `-1`
(`d` is the current height). -/
def reflectPath : ℤ → List Bool → List Bool
  | _, [] => []
  | d, b :: l => if d = -1 then (b :: l).map not else b :: reflectPath (stepH d b) l

theorem reflectPath_cons_of_ne {d : ℤ} (hd : d ≠ -1) (b : Bool) (l : List Bool) :
    reflectPath d (b :: l) = b :: reflectPath (stepH d b) l := by
  simp [reflectPath, hd]

theorem reflectPath_cons_of_eq {d : ℤ} (hd : d = -1) (b : Bool) (l : List Bool) :
    reflectPath d (b :: l) = (b :: l).map not := by
  simp [reflectPath, hd]

theorem reflectPath_length : ∀ (l : List Bool) (d : ℤ), (reflectPath d l).length = l.length
  | [], d => rfl
  | b :: l, d => by
    by_cases hd : d = -1
    · rw [reflectPath_cons_of_eq hd]; simp
    · rw [reflectPath_cons_of_ne hd]; simp [reflectPath_length l]

theorem count_true_map_not (l : List Bool) : (l.map not).count true = l.count false := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [List.count_cons, ih]

theorem count_false_map_not (l : List Bool) : (l.map not).count false = l.count true := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [List.count_cons, ih]

theorem reflectPath_bal : ∀ (l : List Bool) (d : ℤ), Hit d l →
    PathBal d (reflectPath d l) = -2 - PathBal d l
  | [], d, h => by
    rw [hit_nil] at h
    simp [reflectPath, PathBal, h]
  | b :: l, d, h => by
    by_cases hd : d = -1
    · rw [reflectPath_cons_of_eq hd]
      unfold PathBal
      rw [count_true_map_not, count_false_map_not, hd]
      ring
    · rw [reflectPath_cons_of_ne hd, bal_cons, bal_cons]
      exact reflectPath_bal l _ (((hit_cons _ _ _).mp h).resolve_left hd)

theorem reflectPath_involutive : ∀ (l : List Bool) (d : ℤ), Hit d l →
    reflectPath d (reflectPath d l) = l
  | [], d, _ => rfl
  | b :: l, d, h => by
    by_cases hd : d = -1
    · rw [reflectPath_cons_of_eq hd]
      simp only [List.map_cons]
      rw [reflectPath_cons_of_eq hd]
      simp [List.map_map, Function.comp_def]
    · rw [reflectPath_cons_of_ne hd, reflectPath_cons_of_ne hd,
        reflectPath_involutive l _ (((hit_cons _ _ _).mp h).resolve_left hd)]

theorem hit_reflectPath : ∀ (l : List Bool) (d : ℤ), Hit d l → Hit d (reflectPath d l)
  | [], d, h => h
  | b :: l, d, h => by
    by_cases hd : d = -1
    · rw [reflectPath_cons_of_eq hd]
      simp only [List.map_cons]
      exact (hit_cons _ _ _).mpr (Or.inl hd)
    · rw [reflectPath_cons_of_ne hd, hit_cons]
      exact Or.inr (hit_reflectPath l _ (((hit_cons _ _ _).mp h).resolve_left hd))

/-- CO-014. Reflection principle: the bad lattice paths from `(0,0)` to `(m+1,m+1)` are in
bijection (flip `H`/`V` after the first step above the diagonal) with all lattice paths from
`(0,0)` to `(m, m+2)`, i.e. `(n-1, n+1)` for `n = m+1`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem card_badPaths_succ (m : ℕ) :
    (badPaths (m + 1)).card = (stepWords m (m + 2)).card := by
  have hbad : ∀ w, w ∈ badPaths (m + 1) ↔
      w.count true = m + 1 ∧ w.count false = m + 1 ∧ Hit 0 w := by
    intro w
    rw [badPaths, Finset.mem_filter, mem_stepWords, not_isGoodPath_iff_hit, and_assoc]
  apply Finset.card_nbij' (reflectPath 0) (reflectPath 0)
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := (hbad w).mp (Finset.mem_coe.mp hw)
    rw [Finset.mem_coe, mem_stepWords]
    have hb := reflectPath_bal w 0 h3
    have hl := reflectPath_length w 0
    have e1 := List.count_true_add_count_false (reflectPath 0 w)
    have e2 := List.count_true_add_count_false w
    simp only [PathBal] at hb
    omega
  · intro w hw
    obtain ⟨h1, h2⟩ := mem_stepWords.mp (Finset.mem_coe.mp hw)
    have hh : Hit 0 w := by
      refine hit_of_le w 0 (by norm_num) ⟨w.length, ?_⟩
      rw [List.take_length]
      simp only [PathBal]
      omega
    have hb := reflectPath_bal w 0 hh
    have hl := reflectPath_length w 0
    have e1 := List.count_true_add_count_false (reflectPath 0 w)
    have e2 := List.count_true_add_count_false w
    rw [Finset.mem_coe, hbad]
    refine ⟨?_, ?_, hit_reflectPath w 0 hh⟩
    · simp only [PathBal] at hb; omega
    · simp only [PathBal] at hb; omega
  · intro w hw
    exact reflectPath_involutive w 0 (((hbad w).mp (Finset.mem_coe.mp hw)).2.2)
  · intro w hw
    obtain ⟨h1, h2⟩ := mem_stepWords.mp (Finset.mem_coe.mp hw)
    have hh : Hit 0 w := by
      refine hit_of_le w 0 (by norm_num) ⟨w.length, ?_⟩
      rw [List.take_length]
      simp only [PathBal]
      omega
    exact reflectPath_involutive w 0 hh

/-- CO-014 (consequence). `|G| = C(2n,n) - C(2n,n+1)`, in the form `|G(m+1)| + C(2m+2, m) =
C(2m+2, m+1)`. -/
@[kb "kellertrotter2017" "Example 2.28, p. 51"]
theorem card_goodPaths_succ_add_choose (m : ℕ) :
    (goodPaths (m + 1)).card + (2 * m + 2).choose m = (2 * m + 2).choose (m + 1) := by
  have hsum : (goodPaths (m + 1)).card + (badPaths (m + 1)).card =
      (stepWords (m + 1) (m + 1)).card := by
    rw [goodPaths, badPaths]
    exact Finset.card_filter_add_card_filter_not (s := stepWords (m + 1) (m + 1))
      IsGoodPath
  rw [card_badPaths_succ m, card_stepWords, card_stepWords] at hsum
  have e1 : m + (m + 2) = 2 * m + 2 := by ring
  have e2 : m + 1 + (m + 1) = 2 * m + 2 := by ring
  rw [e1, e2] at hsum
  exact hsum

end LatticePaths

/-! ### CO-024: functions as relations -/

/-- CO-024. A binary relation `S ⊆ X × Y` is the graph of a function `X → Y` iff every `x` is
related to exactly one `y`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) binary relation, function, p. 361"]
theorem relation_is_function_iff {X Y : Type*} (S : Set (X × Y)) :
    (∃ f : X → Y, S = {p | p.2 = f p.1}) ↔ ∀ x, ∃! y, (x, y) ∈ S := by
  constructor
  · rintro ⟨f, rfl⟩ x
    exact ⟨f x, rfl, fun y hy => hy⟩
  · intro h
    choose f hf using fun x => (h x).exists
    refine ⟨f, ?_⟩
    ext ⟨x, y⟩
    constructor
    · intro hxy
      exact ((h x).unique hxy (hf x))
    · intro hy
      have : y = f x := hy
      rw [this]; exact hf x

/-! ### CO-059, CO-061, CO-062: division algorithm and Euclid's algorithm -/

/-- CO-059. Division algorithm: for positive `m, n` there are unique `q, r` with `m = q n + r`
and `0 ≤ r < n`. -/
@[kb "kellertrotter2017" "Theorem 3.7, p. 69"]
theorem division_algorithm {m n : ℕ} (_hm : 0 < m) (hn : 0 < n) :
    ∃! p : ℕ × ℕ, m = p.1 * n + p.2 ∧ p.2 < n := by
  refine ⟨(m / n, m % n), ⟨?_, Nat.mod_lt _ hn⟩, ?_⟩
  · simpa [mul_comm] using (Nat.div_add_mod m n).symm
  · rintro ⟨q, r⟩ ⟨h1, h2⟩
    have h3 : r + n * q = m := by rw [h1]; ring
    have := (Nat.div_mod_unique hn).mpr ⟨h3, h2⟩
    exact Prod.ext this.1.symm this.2.symm

/-- CO-061. If `m = q n + r` with `0 < r < n` then `gcd(m,n) = gcd(n,r)`. -/
@[kb "kellertrotter2017" "Theorem 3.8, p. 69"]
theorem gcd_eq_gcd_of_div {m n q r : ℕ} (h : m = q * n + r) (_hr : 0 < r) (_hrn : r < n) :
    Nat.gcd m n = Nat.gcd n r := by
  have hm : m % n = r := by
    rw [h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt _hrn]
  rw [Nat.gcd_comm m n, Nat.gcd_rec n m, hm, Nat.gcd_comm]

/-- CO-061. If `m = q n` (remainder `0`) then `gcd(m,n) = n`. -/
@[kb "kellertrotter2017" "Theorem 3.8, p. 69"]
theorem gcd_eq_of_remainder_zero {m n q : ℕ} (h : m = q * n + 0) : Nat.gcd m n = n := by
  subst h
  simp

/-- Euclid's algorithm: replace `(m, n)` by `(n, m mod n)` until the second entry is `0`. -/
def euclidGcd (m n : ℕ) : ℕ :=
  if h : n = 0 then m else euclidGcd n (m % n)
termination_by n
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- CO-062. Euclid's algorithm (which terminates, being defined by well-founded recursion on the
second argument, since `m mod n < n`) returns the gcd. -/
@[kb "kellertrotter2017" "text, p. 70"]
theorem euclidGcd_eq_gcd (m n : ℕ) : euclidGcd m n = Nat.gcd m n := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    rw [euclidGcd]
    by_cases h : n = 0
    · simp [h]
    · rw [dif_neg h, ih (m % n) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)), Nat.gcd_comm m n,
        Nat.gcd_rec n m, Nat.gcd_comm n (m % n)]

/-! ### CO-069: telescoping -/

/-- CO-069. `Σ_{i=1}^n q(i) = p(n)` for all `n ≥ 0` iff `p(0) = 0` and `p(n) - p(n-1) = q(n)`
for all `n ≥ 1`. -/
@[kb "kellertrotter2017" "text, p. 21"]
theorem sum_eq_iff_telescoping {G : Type*} [AddCommGroup G] (p q : ℕ → G) :
    (∀ n, ∑ i ∈ Icc 1 n, q i = p n) ↔ (p 0 = 0 ∧ ∀ n, 1 ≤ n → p n - p (n - 1) = q n) := by
  constructor
  · intro h
    refine ⟨by simpa using (h 0).symm, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [← h, ← h, Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
    abel
  · rintro ⟨h0, hs⟩ n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, ← hs (k + 1) (by omega)]
      simp

/-! ### CO-070: merge sort -/

/-- CO-070. If `S(2n) ≤ 2 S(n) + 2n` for `n ≥ 1`, then `S(2^k) ≤ 2^k (S(1) + k)` for all `k`. -/
@[kb "kellertrotter2017" "text, p. 72"]
theorem mergeSort_bound (S : ℕ → ℕ) (h : ∀ n, 1 ≤ n → S (2 * n) ≤ 2 * S n + 2 * n) (k : ℕ) :
    S (2 ^ k) ≤ 2 ^ k * (S 1 + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := h (2 ^ k) (Nat.one_le_two_pow)
    rw [pow_succ, mul_comm (2 ^ k) 2]
    nlinarith [ih]

/-- CO-070. Consequently `S(n) ≤ C n log₂ n` for `n = 2^k`, `k ≥ 1`, with `C = S(1) + 1`. -/
@[kb "kellertrotter2017" "text, p. 72"]
theorem mergeSort_bound_nlogn (S : ℕ → ℕ) (h : ∀ n, 1 ≤ n → S (2 * n) ≤ 2 * S n + 2 * n)
    (k : ℕ) (hk : 1 ≤ k) : S (2 ^ k) ≤ (S 1 + 1) * (2 ^ k * k) := by
  have := mergeSort_bound S h k
  calc S (2 ^ k) ≤ 2 ^ k * (S 1 + k) := this
    _ ≤ (S 1 + 1) * (2 ^ k * k) := by
        generalize 2 ^ k = A
        have : A * S 1 ≤ A * S 1 * k := Nat.le_mul_of_pos_right _ hk
        nlinarith [this]

/-! ### CO-026: derangements and `n!/e` -/

/-- Derangement numbers as truncated alternating series. -/
theorem numDerangements_eq_factorial_mul_sum (n : ℕ) :
    (numDerangements n : ℝ) =
      n.factorial * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k / k.factorial := by
  rw [← Int.cast_natCast, numDerangements_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h_le : k ≤ n := Finset.mem_range_succ_iff.mp hk
  rw [Nat.ascFactorial_eq_div, add_tsub_cancel_of_le h_le]
  have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Nat.cast_div (Nat.factorial_dvd_factorial h_le) hk0]
  field_simp

/-- CO-026. For `n ≥ 1` the derangement number `d_n` is within `1/2` of `n!/e`, i.e. it is the
nearest integer to `n!/e`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 169"]
theorem abs_numDerangements_sub_factorial_div_e_lt (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - n.factorial / Real.exp 1| < 1 / 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have : numDerangements 1 = 0 := rfl
    rw [this]
    have he : 2 < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
    rw [abs_lt]; simp only [Nat.factorial_one, Nat.cast_one, Nat.cast_zero, zero_sub]
    have h1 : (Real.exp 1)⁻¹ < 2⁻¹ := inv_strictAnti₀ (by norm_num) he
    have h2 : 0 < (Real.exp 1)⁻¹ := by positivity
    constructor <;> norm_num <;> linarith
  · have hb := Real.exp_bound (x := -1) (by simp) (n := n + 1) (by omega)
    rw [numDerangements_eq_factorial_mul_sum]
    have e1 : (n.factorial : ℝ) / Real.exp 1 = n.factorial * Real.exp (-1) := by
      rw [Real.exp_neg]; ring
    rw [e1, ← mul_sub, abs_mul, Nat.abs_cast, ← abs_neg (∑ _ ∈ _, _ - _), neg_sub]
    simp only [abs_neg, abs_one, one_pow, one_mul] at hb
    have hf : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hnf : (0 : ℝ) < n.factorial := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    calc (n.factorial : ℝ) * |Real.exp (-1) - ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k / k.factorial|
        ≤ n.factorial * ((((n + 1).succ : ℕ) : ℝ) / (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hb hnf.le
      _ = (n + 2) / ((n + 1) * (n + 1)) := by
          rw [hf]; push_cast; field_simp; ring
      _ < 1 / 2 := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith

end UndergradKB.Combinatorics
