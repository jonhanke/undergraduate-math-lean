import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.ExamplesLead
import UndergradKB.Probability.RandomWalk

/-! # Probability: the first-lead recursion derived from the walk (Grinstead–Snell Example 10.7)

`ExamplesLead` proves everything about sequences satisfying the book's recursion for `r_n`.  Here the recursion
is derived from the walk itself: `r_n` is the total weight of the `±1` paths of length `n` which are first in the
lead at time `n`, and decomposing such a path at its first return to `0` gives the recursion. -/

open Finset

namespace UndergradKB.Probability

/-- Weight of a path under independent steps: `p` for each up-step and `q` for each down-step. -/
def pathWeight (p q : ℝ) {n : ℕ} (ω : Fin n → Bool) : ℝ := ∏ i, if ω i then p else q

/-- Peter is first in the lead at time `n`: the walk is at `1` at time `n` and `≤ 0` before. -/
def FirstLead {n : ℕ} (ω : Fin n → Bool) : Prop := walkPos ω n = 1 ∧ ∀ k < n, walkPos ω k ≤ 0

open scoped Classical in
/-- The probability `r_n` that Peter is first in the lead at time `n`. -/
noncomputable def leadProb (p q : ℝ) (n : ℕ) : ℝ :=
  ∑ ω : Fin n → Bool, if FirstLead ω then pathWeight p q ω else 0

/-! ### Elementary facts on paths -/

lemma pathWeight_append (p q : ℝ) {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    pathWeight p q (Fin.append x y) = pathWeight p q x * pathWeight p q y := by
  unfold pathWeight; rw [Fin.prod_univ_add]; simp

lemma pathWeight_cons (p q : ℝ) {n : ℕ} (c : Bool) (x : Fin n → Bool) :
    pathWeight p q (Fin.cons c x : Fin (n + 1) → Bool) = (if c then p else q) * pathWeight p q x := by
  unfold pathWeight; rw [Fin.prod_univ_succ]; simp

lemma walkPos_cons_succ {n : ℕ} (c : Bool) (x : Fin n → Bool) (k : ℕ) :
    walkPos (Fin.cons c x : Fin (n + 1) → Bool) (k + 1) = step c + walkPos x k := by
  unfold walkPos
  rw [Fin.sum_univ_succ]
  simp

lemma step_cases (b : Bool) : step b = 1 ∨ step b = -1 := by
  unfold step; split_ifs <;> simp

lemma lead_walkPos_succ {N : ℕ} (ω : Fin N → Bool) (k : ℕ) (hk : k < N) :
    walkPos ω (k + 1) = walkPos ω k + step (ω ⟨k, hk⟩) := by
  unfold walkPos
  have : ∀ i : Fin N, (if (i : ℕ) < k + 1 then step (ω i) else 0) =
      (if (i : ℕ) < k then step (ω i) else 0) + (if i = ⟨k, hk⟩ then step (ω ⟨k, hk⟩) else 0) := by
    intro i
    by_cases h1 : (i : ℕ) < k
    · have : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at h1; simp at h1
      rw [if_pos h1, if_pos (by omega), if_neg this, add_zero]
    · by_cases h2 : i = ⟨k, hk⟩
      · subst h2; simp
      · have : ¬ (i : ℕ) < k + 1 := by
          intro h; apply h2; ext; simp only; omega
        simp [h1, h2, this]
  rw [sum_congr rfl fun i _ => this i, sum_add_distrib]
  simp

lemma walkPos_parity {n : ℕ} (ω : Fin n → Bool) : ∀ k, k ≤ n → (2 : ℤ) ∣ walkPos ω k - k
  | 0, _ => by simp [walkPos_zero]
  | k + 1, hk => by
    have ih := walkPos_parity ω k (by omega)
    rw [lead_walkPos_succ ω k (by omega)]
    rcases step_cases (ω ⟨k, by omega⟩) with h | h <;> rw [h] <;> push_cast <;> omega

/-! ### Reindexing sums over paths -/

/-- Concatenation of paths as an equivalence. -/
def appEq (a b : ℕ) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin (a + b) → Bool) where
  toFun pr := Fin.append pr.1 pr.2
  invFun ω := (fun i => ω (Fin.castAdd b i), fun j => ω (Fin.natAdd a j))
  left_inv pr := by ext i <;> simp
  right_inv ω := by
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

lemma sum_fin_append {a b : ℕ} (F : (Fin (a + b) → Bool) → ℝ) :
    ∑ ω, F ω = ∑ z : Fin a → Bool, ∑ y : Fin b → Bool, F (Fin.append z y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (appEq a b) _ _ fun _ => rfl).symm

lemma sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ z, F z = ∑ c : Bool, ∑ x : Fin n → Bool, F (Fin.cons c x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) (fun pr => F (Fin.cons pr.1 pr.2)) F
    fun _ => rfl).symm

/-! ### Decomposition at the first return to `0` -/

/-- The first return of the walk to `0` is at time `m + 1`, strictly below `0` before. -/
def LeadSplit {n : ℕ} (m : ℕ) (ω : Fin n → Bool) : Prop :=
  walkPos ω (m + 1) = 0 ∧ ∀ k, 1 ≤ k → k < m + 1 → walkPos ω k < 0

lemma split_iff_aux {m b : ℕ} (hm : 1 ≤ m) (c : Bool) (x : Fin m → Bool) (y : Fin b → Bool)
    (z : Fin (m + 1) → Bool) (hz : ∀ j, walkPos z (j + 1) = step c + walkPos x j) :
    (FirstLead (Fin.append z y) ∧ LeadSplit m (Fin.append z y)) ↔
      (c = false ∧ FirstLead x ∧ FirstLead y) := by
  have h1 : ∀ k, k ≤ m + 1 → walkPos (Fin.append z y) k = walkPos z k := fun k hk => by
    rw [walkPos_append, Nat.sub_eq_zero_of_le hk, walkPos_zero, add_zero]
  have h2 : ∀ k, m + 1 ≤ k →
      walkPos (Fin.append z y) k = walkPos z (m + 1) + walkPos y (k - (m + 1)) := fun k hk => by
    rw [walkPos_append, walkPos_of_le z hk, walkPos_of_le z le_rfl]
  have hz0 : walkPos z 0 = 0 := walkPos_zero z
  have hsf : step false = -1 := by simp [step]
  have hz1 : walkPos z 1 = step c := by simpa [walkPos_zero] using hz 0
  unfold FirstLead LeadSplit
  constructor
  · rintro ⟨⟨hn, hall⟩, hP0, hPk⟩
    have hs : walkPos z (m + 1) = 0 := by rw [← h1 _ le_rfl]; exact hP0
    have e : m + 1 + b - (m + 1) = b := by omega
    rw [h2 _ (by omega), hs, e] at hn
    have hc : c = false := by
      have := hPk 1 le_rfl (by omega)
      rw [h1 1 (by omega), hz1] at this
      rcases step_cases c with h | h
      · omega
      · cases c
        · rfl
        · simp [step] at h
    subst hc
    have hx := hz m
    rw [hs, hsf] at hx
    refine ⟨rfl, ⟨by omega, fun j hj => ?_⟩, ⟨by omega, fun j hj => ?_⟩⟩
    · have := hPk (j + 1) (by omega) (by omega)
      rw [h1 _ (by omega), hz j, hsf] at this
      omega
    · have := hall (m + 1 + j) (by omega)
      rw [h2 _ (by omega), hs] at this
      have e' : m + 1 + j - (m + 1) = j := by omega
      rw [e'] at this
      omega
  · rintro ⟨hc, hx, hy⟩
    subst hc
    have hs : walkPos z (m + 1) = 0 := by rw [hz m, hx.1, hsf]; norm_num
    have e : m + 1 + b - (m + 1) = b := by omega
    refine ⟨⟨?_, fun k hk => ?_⟩, ?_, fun k hk1 hk2 => ?_⟩
    · rw [h2 _ (by omega), hs, e, hy.1]; norm_num
    · by_cases hkm : k ≤ m + 1
      · rw [h1 k hkm]
        rcases k with _ | j
        · rw [hz0]
        · rw [hz j, hsf]
          by_cases hjm : j < m
          · have := hx.2 j hjm; omega
          · have : j = m := by omega
            subst this; have := hx.1; omega
      · rw [h2 k (by omega), hs]
        have := hy.2 (k - (m + 1)) (by omega)
        omega
    · rw [h1 _ le_rfl]; exact hs
    · rw [h1 k (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hz j, hsf]
      have := hx.2 j (by omega)
      omega

lemma split_iff {m b : ℕ} (hm : 1 ≤ m) (c : Bool) (x : Fin m → Bool) (y : Fin b → Bool) :
    (FirstLead (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y) ∧
      LeadSplit m (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y)) ↔
      (c = false ∧ FirstLead x ∧ FirstLead y) :=
  split_iff_aux hm c x y _ fun j => walkPos_cons_succ c x j

open scoped Classical in
lemma fiber_sum (p q : ℝ) {m b n : ℕ} (hm : 1 ≤ m) (h : n = m + 1 + b) :
    ∑ ω : Fin n → Bool, (if FirstLead ω ∧ LeadSplit m ω then pathWeight p q ω else 0) =
      q * leadProb p q m * leadProb p q b := by
  subst h
  have key : ∀ (c : Bool) (x : Fin m → Bool) (y : Fin b → Bool),
      (if FirstLead (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y) ∧
        LeadSplit m (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y) then
        pathWeight p q (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y) else 0) =
      if c = false then (if FirstLead x ∧ FirstLead y then
        q * pathWeight p q x * pathWeight p q y else 0) else 0 := by
    intro c x y
    rw [pathWeight_append, pathWeight_cons]
    by_cases h : FirstLead (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y) ∧
        LeadSplit m (Fin.append (Fin.cons c x : Fin (m + 1) → Bool) y)
    · obtain ⟨rfl, hx, hy⟩ := (split_iff hm c x y).1 h
      simp [h, hx, hy]
    · rw [if_neg h]
      by_cases hc : c = false
      · subst hc
        rw [if_pos rfl, if_neg]
        exact fun h' => h ((split_iff hm false x y).2 ⟨rfl, h'⟩)
      · rw [if_neg hc]
  rw [sum_fin_append, sum_cons]
  simp_rw [key]
  simp only [Fintype.sum_bool, if_true, Bool.true_eq_false, if_false, zero_add, sum_const_zero, add_zero]
  unfold leadProb
  rw [mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  by_cases hx : FirstLead x <;> by_cases hy : FirstLead y <;> simp [hx, hy, mul_assoc]

/-! ### Existence and uniqueness of the first return -/

lemma exists_split {n K : ℕ} (hn : n = 2 * K + 3) (ω : Fin n → Bool) (hF : FirstLead ω) :
    ∃ a, a < K + 1 ∧ LeadSplit (2 * a + 1) ω := by
  obtain ⟨h1, hle⟩ := hF
  have hpen : walkPos ω (n - 1) = 0 := by
    have h := lead_walkPos_succ ω (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e, h1] at h
    have := hle (n - 1) (by omega)
    have hs := step_cases (ω ⟨n - 1, by omega⟩)
    omega
  have hex : ∃ k, 1 ≤ k ∧ walkPos ω k = 0 := ⟨n - 1, by omega, hpen⟩
  have hm0 := Nat.find_spec hex
  have hmle : Nat.find hex ≤ n - 1 := Nat.find_min' hex ⟨by omega, hpen⟩
  have hmin : ∀ k, k < Nat.find hex → ¬ (1 ≤ k ∧ walkPos ω k = 0) :=
    fun k hk => Nat.find_min hex hk
  have hpar := walkPos_parity ω (Nat.find hex) (by omega)
  generalize Nat.find hex = m0 at *
  rw [hm0.2] at hpar
  refine ⟨(m0 - 2) / 2, by omega, ?_⟩
  have e : 2 * ((m0 - 2) / 2) + 1 + 1 = m0 := by omega
  unfold LeadSplit
  rw [e]
  refine ⟨hm0.2, fun k hk1 hk2 => ?_⟩
  have h3 := hmin k (by omega)
  have h4 := hle k (by omega)
  omega

lemma split_unique {n : ℕ} {ω : Fin n → Bool} {m m' : ℕ} (hm : LeadSplit m ω)
    (hm' : LeadSplit m' ω) : m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hm'.2 (m + 1) (by omega) (by omega); have := hm.1; omega
  · have := hm.2 (m' + 1) (by omega) (by omega); have := hm'.1; omega

/-! ### The recursion -/

open scoped Classical in
lemma leadProb_even (p q : ℝ) {n : ℕ} (hn : Even n) : leadProb p q n = 0 := by
  unfold leadProb
  refine sum_eq_zero fun ω _ => ?_
  rw [if_neg]
  rintro ⟨h1, -⟩
  have := walkPos_parity ω n le_rfl
  obtain ⟨j, hj⟩ := hn
  rw [h1] at this
  omega

open scoped Classical in
lemma leadProb_one (p q : ℝ) : leadProb p q 1 = p := by
  unfold leadProb
  rw [sum_cons]
  simp [Fintype.sum_bool, FirstLead, walkPos, pathWeight, step]

open scoped Classical in
lemma leadProb_odd (p q : ℝ) (K : ℕ) :
    leadProb p q (2 * (K + 1) + 1) =
      q * ∑ a ∈ range (K + 1), leadProb p q (2 * a + 1) * leadProb p q (2 * (K + 1) + 1 - 2 - 2 * a) := by
  have hn : 2 * (K + 1) + 1 = 2 * K + 3 := by ring
  have pt : ∀ ω : Fin (2 * (K + 1) + 1) → Bool,
      (if FirstLead ω then pathWeight p q ω else 0) =
        ∑ a ∈ range (K + 1), (if FirstLead ω ∧ LeadSplit (2 * a + 1) ω then pathWeight p q ω else 0) := by
    intro ω
    by_cases hF : FirstLead ω
    · obtain ⟨a0, ha0, hL0⟩ := exists_split hn ω hF
      rw [sum_eq_single a0]
      · simp [hF, hL0]
      · intro a _ hne
        rw [if_neg]
        rintro ⟨-, hL⟩
        exact hne (by have := split_unique hL hL0; omega)
      · intro h; exact absurd (mem_range.2 ha0) h
    · simp [hF]
  unfold leadProb
  rw [sum_congr rfl fun ω _ => pt ω, sum_comm, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_range.1 ha
  rw [fiber_sum p q (m := 2 * a + 1) (b := 2 * (K + 1) + 1 - 2 - 2 * a) (by omega) (by omega)]
  unfold leadProb
  ring

/-- Grinstead–Snell Example 10.7 (PR-179), the walk: under independent `±1` steps with `P(+1) = p`,
`P(-1) = q`, the probability `r_n` that Peter is first in the lead at time `n` (the walk is at `1` at time
`n` and `≤ 0` before) satisfies the book's recursion (`r_n = 0` for even `n`, `r_1 = p`,
`r_n = q (r_1 r_{n-2} + r_3 r_{n-4} + ⋯ + r_{n-2} r_1)` for odd `n > 1`), hence has the closed form
`r_{2k+1} = C_k p^{k+1} q^k`; and with `p + q = 1`, `0 < p < 1`, the walk is ever in the lead with
probability `min (1, p / q)`. -/
@[kb "grinsteadsnell2006" "Example 10.7, p. 380"]
theorem leadProb_isLeadSeq (p q : ℝ) :
    IsLeadSeq p q (leadProb p q) ∧ (∀ k, leadProb p q (2 * k + 1) = (catalan k : ℝ) * p ^ (k + 1) * q ^ k) ∧
      (∀ k, leadProb p q (2 * k) = 0) ∧
      (0 < p → 0 < q → p + q = 1 →
        HasSum (leadProb p q) (if p < q then p / q else 1)) := by
  have hseq : IsLeadSeq p q (leadProb p q) := by
    refine ⟨fun n hn => leadProb_even p q hn, leadProb_one p q, ?_⟩
    rintro n ⟨K', hK'⟩ hn
    obtain ⟨K, rfl⟩ : ∃ K, K' = K + 1 := ⟨K' - 1, by omega⟩
    subst hK'
    have e : (2 * (K + 1) + 1 - 1) / 2 = K + 1 := by omega
    rw [e]
    exact leadProb_odd p q K
  have heq : leadProb p q = leadR p q := funext (isLeadSeq_unique hseq)
  refine ⟨hseq, fun k => ?_, fun k => ?_, fun hp hq hpq => ?_⟩
  · rw [heq, leadR_odd]
  · exact leadProb_even p q (even_two_mul k)
  · have := (lead_total_probability hp hq hpq hseq)
    rw [← this.2]
    exact this.1

end UndergradKB.Probability
