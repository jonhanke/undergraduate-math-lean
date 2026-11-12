import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk

/-! # Probability: arc sine laws for the simple symmetric walk (Grinstead–Snell, §12.3)

Paths are the functions `ω : Fin N → Bool` of `RandomWalk.lean`.  We prove the discrete laws

* the last equalization of a walk of length `2n` is at time `2k` with probability `u_{2k} u_{2n-2k}`
  (Exercise 12.1.6, the quantity `α_{2k,2n}` of §12.3);
* Theorem 12.5: the smallest `j` with `S_j = S_{2n}` equals `2k` with the same probability `α_{2k,2n}`.

The key lemma is that the number of paths of length `2m` which never return to `0` is `C(2m,m)`. -/

open Finset

namespace UndergradKB.Probability

/-! ## Splitting paths -/

/-- Counting paths through a concatenation: if membership of `Fin.append x y` in `R` is the conjunction of a
condition on `x` and one on `y`, the counts multiply. -/
theorem card_filter_append (a b : ℕ) (P : (Fin a → Bool) → Prop) (Q : (Fin b → Bool) → Prop)
    (R : (Fin (a + b) → Bool) → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (h : ∀ x y, R (Fin.append x y) ↔ P x ∧ Q y) :
    (univ.filter R).card = (univ.filter P).card * (univ.filter Q).card := by
  rw [← card_product]
  refine Finset.card_bij' (fun ω _ => (fun i => ω (Fin.castAdd b i), fun j => ω (Fin.natAdd a j)))
    (fun p _ => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro ω hω
    have hω' : ω = Fin.append (fun i => ω (Fin.castAdd b i)) (fun j => ω (Fin.natAdd a j)) := by
      funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hω ⊢
    rw [hω'] at hω
    exact (h _ _).1 hω
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    exact (h _ _).2 hp
  · intro ω _
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  · intro p _
    ext i <;> simp

theorem walkPos_append_le {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) {k : ℕ} (hk : k ≤ a) :
    walkPos (Fin.append x y) k = walkPos x k := by
  rw [walkPos_append, Nat.sub_eq_zero_of_le hk, walkPos_zero, add_zero]

theorem walkPos_append_ge {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) {k : ℕ} (hk : a ≤ k) :
    walkPos (Fin.append x y) k = walkPos x a + walkPos y (k - a) := by
  rw [walkPos_append, walkPos_of_le x hk, walkPos_of_le x (le_refl a)]

theorem FR_append_iff {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    FR (Fin.append x y) a ↔ FR x a := by
  unfold FR
  constructor
  · rintro ⟨h, h0, hj⟩
    refine ⟨h, by rwa [walkPos_append_le x y le_rfl] at h0, fun j hj0 hja => ?_⟩
    rw [← walkPos_append_le x y hja.le]; exact hj j hj0 hja
  · rintro ⟨h, h0, hj⟩
    refine ⟨h, by rwa [walkPos_append_le x y le_rfl], fun j hj0 hja => ?_⟩
    rw [walkPos_append_le x y hja.le]; exact hj j hj0 hja

theorem card_FR_append (a b : ℕ) :
    (univ.filter fun ω : Fin (a + b) → Bool => FR ω a).card = firstCount a * 2 ^ b := by
  have := card_filter_append a b (fun x => FR x a) (fun _ => True) (fun ω => FR ω a)
    (fun x y => by simp [FR_append_iff])
  rw [this]
  simp [firstCount]

theorem card_FR (a N : ℕ) (h : a ≤ N) :
    (univ.filter fun ω : Fin N → Bool => FR ω a).card = firstCount a * 2 ^ (N - a) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact card_FR_append a b

/-! ## Paths with no return to the origin -/

/-- `NR ω`: the path never returns to `0` at a positive time up to its length. -/
def NR {N : ℕ} (ω : Fin N → Bool) : Prop := ∀ j, 0 < j → j ≤ N → walkPos ω j ≠ 0

noncomputable instance {N : ℕ} (ω : Fin N → Bool) : Decidable (NR ω) := Classical.propDecidable _

/-- Number of paths of length `N` with no return to `0`. -/
noncomputable def noRetCount (N : ℕ) : ℕ := (univ.filter fun ω : Fin N → Bool => NR ω).card

theorem noRet_partition (N : ℕ) :
    2 ^ N = noRetCount N + ∑ a ∈ Icc 1 N, (univ.filter fun ω : Fin N → Bool => FR ω a).card := by
  have h1 : (univ.filter fun ω : Fin N → Bool => ¬ NR ω) =
      (Icc 1 N).biUnion (fun a => univ.filter fun ω : Fin N → Bool => FR ω a) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc]
    constructor
    · intro h
      have hex : ∃ k, 0 < k ∧ k ≤ N ∧ walkPos ω k = 0 := by
        unfold NR at h; push Not at h; exact h
      classical
      have hk := Nat.find_spec hex
      have hmin : ∀ j, j < Nat.find hex → ¬ (0 < j ∧ j ≤ N ∧ walkPos ω j = 0) :=
        fun j hj => Nat.find_min hex hj
      generalize Nat.find hex = k at hk hmin
      exact ⟨k, ⟨hk.1, hk.2.1⟩, hk.1, hk.2.2, fun j hj0 hjk hz => hmin j hjk ⟨hj0, by omega, hz⟩⟩
    · rintro ⟨a, ⟨ha1, haN⟩, _, h0, _⟩ hnr
      exact hnr a ha1 haN h0
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin N → Bool))) (fun ω => NR ω)
  rw [h1, card_biUnion] at h2
  · simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h2
    unfold noRetCount
    omega
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω h1 h2
    rw [mem_filter] at h1 h2
    simp only [mem_univ, true_and, FR] at h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h2.2.2 a h1.1 hlt h1.2.1
    · exact h1.2.2 a' h2.1 hlt h2.2.1

theorem noRet_prob (N : ℕ) : (noRetCount N : ℚ) / 2 ^ N = 1 - ∑ a ∈ Icc 1 N, f a := by
  have h' : 2 ^ N = noRetCount N + ∑ a ∈ Icc 1 N, firstCount a * 2 ^ (N - a) := by
    refine (noRet_partition N).trans ?_
    congr 1
    exact sum_congr rfl fun a ha => card_FR a N (mem_Icc.1 ha).2
  have hq : (noRetCount N : ℚ) = 2 ^ N - ∑ a ∈ Icc 1 N, (firstCount a : ℚ) * 2 ^ (N - a) := by
    have := congrArg (Nat.cast : ℕ → ℚ) h'
    push_cast at this
    linarith
  have hp : (2 : ℚ) ^ N ≠ 0 := by positivity
  rw [hq, sub_div, div_self hp, sum_div]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  have : (2 : ℚ) ^ N = 2 ^ a * 2 ^ (N - a) := by rw [← pow_add]; congr 1; omega
  unfold f
  rw [this]
  field_simp

private theorem f_zero' : f 0 = 0 := by
  simp [f, firstCount, FR]

private theorem f_two_mul' (m : ℕ) : f (2 * m) = c (m - 1) - c m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f_zero']
  · exact f_eq m hm

theorem sum_f_Icc_two_mul (m : ℕ) : ∑ k ∈ Icc 1 m, f (2 * k) = 1 - c m := by
  induction m with
  | zero => simp [c_zero]
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega), ih, f_two_mul']
    simp only [Nat.add_sub_cancel]
    ring

/-- The number of paths of length `2m` which never return to `0` is `C(2m,m)`, the number of paths ending at
`0`. -/
theorem noRetCount_even (m : ℕ) : noRetCount (2 * m) = (2 * m).choose m := by
  have h := noRet_prob (2 * m)
  rw [sum_Icc_even f f_odd m, sum_f_Icc_two_mul] at h
  have h2 : (noRetCount (2 * m) : ℚ) / 2 ^ (2 * m) = c m := by rw [h]; ring
  have h3 : ((2 * m).choose m : ℚ) / 2 ^ (2 * m) = c m := by
    unfold c; rw [pow_mul]; norm_num
  have hp : (2 : ℚ) ^ (2 * m) ≠ 0 := by positivity
  have := (div_left_inj' hp).1 (h2.trans h3.symm)
  exact_mod_cast this


/-! ## The last equalization -/

/-- `LastZero ω a`: the last visit of the path `ω` to `0` is at time `a` (the last equalization). -/
def LastZero {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Prop :=
  walkPos ω a = 0 ∧ ∀ j, a < j → j ≤ N → walkPos ω j ≠ 0

noncomputable instance {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Decidable (LastZero ω a) :=
  Classical.propDecidable _

theorem lastZero_append_iff {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    LastZero (Fin.append x y) a ↔ walkPos x a = 0 ∧ NR y := by
  unfold LastZero NR
  constructor
  · rintro ⟨h0, hj⟩
    rw [walkPos_append_le x y le_rfl] at h0
    refine ⟨h0, fun j hj0 hjb => ?_⟩
    have := hj (a + j) (by omega) (by omega)
    rwa [walkPos_append_ge x y (by omega), Nat.add_sub_cancel_left, h0, zero_add] at this
  · rintro ⟨h0, hy⟩
    refine ⟨by rwa [walkPos_append_le x y le_rfl], fun j haj hjN => ?_⟩
    rw [walkPos_append_ge x y haj.le, h0, zero_add]
    exact hy (j - a) (by omega) (by omega)

theorem card_lastZero (a b N : ℕ) (h : a + b = N) :
    (univ.filter fun ω : Fin N → Bool => LastZero ω a).card = zeroCount a * noRetCount b := by
  subst h
  exact card_filter_append a b (fun x => walkPos x a = 0) (fun y => NR y) (fun ω => LastZero ω a)
    (fun x y => lastZero_append_iff x y)

/-- Exercise 12.1.6 (counting form): among the `2^{2n}` paths of length `2n`, exactly `C(2k,k) C(2n-2k,n-k)` have
their last equalization at time `2k`. -/
theorem lastZero_count (n k : ℕ) (hk : k ≤ n) :
    (univ.filter fun ω : Fin (2 * n) → Bool => LastZero ω (2 * k)).card =
      (2 * k).choose k * (2 * (n - k)).choose (n - k) := by
  rw [card_lastZero (2 * k) (2 * (n - k)) (2 * n) (by omega), zeroCount_even, noRetCount_even]

theorem prob_pow_two_mul (n k : ℕ) (hk : k ≤ n) : (2 : ℚ) ^ (2 * n) = 4 ^ k * 4 ^ (n - k) := by
  rw [← pow_add, Nat.add_sub_cancel' hk, pow_mul]; norm_num

/-- Exercise 12.1.6 (probability form, `α_{2k,2n}` of §12.3): the walk of length `2n` has its last equalization at
time `2k` with probability `u_{2k} u_{2n-2k}`. -/
theorem lastZero_prob (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter fun ω : Fin (2 * n) → Bool => LastZero ω (2 * k)).card : ℚ) / 2 ^ (2 * n) =
      u (2 * k) * u (2 * (n - k)) := by
  rw [lastZero_count n k hk, u_two_mul, u_two_mul, prob_pow_two_mul n k hk]
  unfold c
  push_cast
  rw [div_mul_div_comm]

/-! ## Theorem 12.5: the first time the walk reaches its final value -/

/-- `FirstAtEnd ω a`: `a` is the smallest `j` with `S_j = S_N` (the variable `J` of Theorem 12.5). -/
def FirstAtEnd {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Prop :=
  walkPos ω a = walkPos ω N ∧ ∀ j, j < a → walkPos ω j ≠ walkPos ω N

noncomputable instance {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Decidable (FirstAtEnd ω a) :=
  Classical.propDecidable _

/-- Reversing a path: `S_t` of the reversed path is `S_a - S_{a-t}`. -/
theorem walkPos_rev {a : ℕ} (x : Fin a → Bool) {t : ℕ} (ht : t ≤ a) :
    walkPos (fun i => x (Fin.rev i)) t = walkPos x a - walkPos x (a - t) := by
  unfold walkPos
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin a => if (i : ℕ) < t then step (x (Fin.rev i)) else 0)]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have := i.isLt
  split_ifs <;> first | (exfalso; omega) | simp

/-- A path whose walk never returns to its final value before the end (`S_j ≠ S_a` for `j < a`). -/
def Back {a : ℕ} (x : Fin a → Bool) : Prop := ∀ j, j < a → walkPos x j ≠ walkPos x a

noncomputable instance {a : ℕ} (x : Fin a → Bool) : Decidable (Back x) := Classical.propDecidable _

theorem card_back (a : ℕ) : (univ.filter fun x : Fin a → Bool => Back x).card = noRetCount a := by
  unfold noRetCount
  refine Finset.card_bij (fun x _ => fun i => x (Fin.rev i)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    intro t ht0 hta
    rw [walkPos_rev x hta]
    have := hx (a - t) (by omega)
    intro h; apply this; linarith
  · intro x _ y _ h
    funext i
    have := congrFun h (Fin.rev i)
    simpa using this
  · intro y hy
    refine ⟨fun i => y (Fin.rev i), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hy ⊢
      intro j hj
      rw [walkPos_rev y hj.le, walkPos_rev y le_rfl, Nat.sub_self, walkPos_zero]
      have := hy (a - j) (by omega) (by omega)
      intro h; apply this; linarith
    · funext i; simp

theorem firstAtEnd_append_iff {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    FirstAtEnd (Fin.append x y) a ↔ Back x ∧ walkPos y b = 0 := by
  have hN : walkPos (Fin.append x y) (a + b) = walkPos x a + walkPos y b := by
    rw [walkPos_append_ge x y (by omega), Nat.add_sub_cancel_left]
  unfold FirstAtEnd Back
  rw [hN, walkPos_append_le x y le_rfl]
  constructor
  · rintro ⟨h0, hj⟩
    have hy : walkPos y b = 0 := by linarith
    refine ⟨fun j hja => ?_, hy⟩
    have := hj j hja
    rwa [walkPos_append_le x y hja.le, hy, add_zero] at this
  · rintro ⟨hj, hy⟩
    refine ⟨by rw [hy, add_zero], fun j hja => ?_⟩
    rw [walkPos_append_le x y hja.le, hy, add_zero]
    exact hj j hja

theorem card_firstAtEnd (a b N : ℕ) (h : a + b = N) :
    (univ.filter fun ω : Fin N → Bool => FirstAtEnd ω a).card = noRetCount a * zeroCount b := by
  subst h
  rw [← card_back]
  exact card_filter_append a b (fun x => Back x) (fun y => walkPos y b = 0) (fun ω => FirstAtEnd ω a)
    (fun x y => firstAtEnd_append_iff x y)

/-- Grinstead–Snell Theorem 12.5 (PR-129), counting form: among the paths of length `2n`, exactly
`C(2k,k) C(2n-2k,n-k)` have `J = 2k`, where `J` is the smallest `j` with `S_j = S_{2n}`. -/
theorem firstAtEnd_count (n k : ℕ) (hk : k ≤ n) :
    (univ.filter fun ω : Fin (2 * n) → Bool => FirstAtEnd ω (2 * k)).card =
      (2 * k).choose k * (2 * (n - k)).choose (n - k) := by
  rw [card_firstAtEnd (2 * k) (2 * (n - k)) (2 * n) (by omega), zeroCount_even, noRetCount_even]

/-- Grinstead–Snell Theorem 12.5 (PR-129). For a random walk of length `2n`, the probability `γ_{2k,2n}` that the
smallest subscript `j` with `S_j = S_{2n}` equals `2k` is `α_{2k,2n} = u_{2k} u_{2n-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.5, p. 503"]
theorem firstAtEnd_prob (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter fun ω : Fin (2 * n) → Bool => FirstAtEnd ω (2 * k)).card : ℚ) / 2 ^ (2 * n) =
      u (2 * k) * u (2 * (n - k)) := by
  rw [firstAtEnd_count n k hk, u_two_mul, u_two_mul, prob_pow_two_mul n k hk]
  unfold c
  push_cast
  rw [div_mul_div_comm]


/-! ## Theorem 12.4: time in the lead -/

theorem walkPos_succ {N : ℕ} (ω : Fin N → Bool) {k : ℕ} (hk : k < N) :
    walkPos ω (k + 1) = walkPos ω k + step (ω ⟨k, hk⟩) := by
  have h : (∑ i : Fin N, if (i : ℕ) = k then step (ω i) else 0) = step (ω ⟨k, hk⟩) := by
    rw [sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
      simp [this]
    · intro h; exact absurd (mem_univ _) h
  rw [← h]
  unfold walkPos
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> first | (exfalso; omega) | simp

theorem walkPos_succ_cases {N : ℕ} (ω : Fin N → Bool) {k : ℕ} (hk : k < N) :
    walkPos ω (k + 1) = walkPos ω k + 1 ∨ walkPos ω (k + 1) = walkPos ω k - 1 := by
  rw [walkPos_succ ω hk]
  by_cases h : ω ⟨k, hk⟩ = true
  · left; simp [step, h]
  · right; simp [step, h]; ring

/-- The path with every step reversed (reflection in the time axis). -/
def flipPath {N : ℕ} (ω : Fin N → Bool) : Fin N → Bool := fun i => !ω i

theorem step_not (b : Bool) : step (!b) = - step b := by cases b <;> simp [step]

theorem walkPos_flip {N : ℕ} (ω : Fin N → Bool) (k : ℕ) :
    walkPos (flipPath ω) k = - walkPos ω k := by
  unfold walkPos flipPath
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [step_not]

theorem posAll {N : ℕ} (ω : Fin N → Bool) (t0 : ℕ) (ht0 : t0 ≤ N + 1)
    (hnz : ∀ j, 0 < j → j < t0 → walkPos ω j ≠ 0) (h1 : 0 < walkPos ω 1) :
    ∀ j, 0 < j → j < t0 → 0 < walkPos ω j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hjt
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using h1
    · have h0 := ih hj (by omega)
      have hz := hnz (j + 1) (by omega) hjt
      rcases walkPos_succ_cases ω (show j < N by omega) with h | h <;> omega

theorem negAll {N : ℕ} (ω : Fin N → Bool) (t0 : ℕ) (ht0 : t0 ≤ N + 1)
    (hnz : ∀ j, 0 < j → j < t0 → walkPos ω j ≠ 0) (h1 : walkPos ω 1 < 0) :
    ∀ j, 0 < j → j < t0 → walkPos ω j < 0 := by
  have := posAll (flipPath ω) t0 ht0
    (fun j hj hjt => by rw [walkPos_flip]; simpa using hnz j hj hjt) (by rw [walkPos_flip]; linarith)
  intro j hj hjt
  have := this j hj hjt
  rw [walkPos_flip] at this
  linarith

/-- Player A is in the lead during step `k` of the path: the walk is above the axis at time `k`, or is on the
axis at time `k` after having been above it at time `k - 1` (the book's `ε_k = 1`). -/
def inLead {N : ℕ} (ω : Fin N → Bool) (k : ℕ) : Prop :=
  0 < walkPos ω k ∨ (walkPos ω k = 0 ∧ 0 < walkPos ω (k - 1))

instance {N : ℕ} (ω : Fin N → Bool) (k : ℕ) : Decidable (inLead ω k) := by
  unfold inLead; infer_instance

/-- The number of the `N` polygonal segments of the path which lie above the time axis. -/
def leadCount {N : ℕ} (ω : Fin N → Bool) : ℕ := ∑ k ∈ range N, if inLead ω (k + 1) then 1 else 0

theorem leadCount_of_all {N : ℕ} (ω : Fin N → Bool) (h : ∀ k, 1 ≤ k → k ≤ N → inLead ω k) :
    leadCount ω = N := by
  unfold leadCount
  have : ∀ k ∈ range N, (if inLead ω (k + 1) then 1 else 0) = 1 := fun k hk => by
    have := h (k + 1) (by omega) (by have := mem_range.1 hk; omega)
    simp [*]
  rw [sum_congr rfl this]
  simp

theorem leadCount_of_none {N : ℕ} (ω : Fin N → Bool) (h : ∀ k, 1 ≤ k → k ≤ N → ¬ inLead ω k) :
    leadCount ω = 0 := by
  unfold leadCount
  refine sum_eq_zero fun k hk => ?_
  have := h (k + 1) (by omega) (by have := mem_range.1 hk; omega)
  simp [*]

theorem leadCount_FR_pos {a : ℕ} (x : Fin a → Bool) (hx : FR x a) (h1 : 0 < walkPos x 1) :
    leadCount x = a := by
  obtain ⟨ha, h0, hj⟩ := hx
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 1 := by omega
    subst this
    omega
  have hp := posAll x a (by omega) hj h1
  apply leadCount_of_all
  intro k hk1 hka
  by_cases hk : k < a
  · exact Or.inl (hp k (by omega) hk)
  · have hka' : k = a := by omega
    rw [hka']
    exact Or.inr ⟨h0, hp (a - 1) (by omega) (by omega)⟩

theorem leadCount_FR_neg {a : ℕ} (x : Fin a → Bool) (hx : FR x a) (h1 : walkPos x 1 < 0) :
    leadCount x = 0 := by
  obtain ⟨ha, h0, hj⟩ := hx
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 1 := by omega
    subst this
    omega
  have hp := negAll x a (by omega) hj h1
  apply leadCount_of_none
  intro k hk1 hka
  by_cases hk : k < a
  · have := hp k (by omega) hk
    rintro (h | ⟨h, _⟩) <;> omega
  · have hka' : k = a := by omega
    rw [hka']
    have := hp (a - 1) (by omega) (by omega)
    rintro (h | ⟨_, h⟩) <;> omega

theorem leadCount_NR_pos {N : ℕ} (x : Fin N → Bool) (hx : NR x) (h1 : 0 < walkPos x 1) :
    leadCount x = N := by
  have hp := posAll x (N + 1) le_rfl (fun j hj hjt => hx j hj (by omega)) h1
  exact leadCount_of_all x fun k hk1 hkN => Or.inl (hp k (by omega) (by omega))

theorem leadCount_NR_neg {N : ℕ} (x : Fin N → Bool) (hx : NR x) (h1 : walkPos x 1 < 0) :
    leadCount x = 0 := by
  have hp := negAll x (N + 1) le_rfl (fun j hj hjt => hx j hj (by omega)) h1
  refine leadCount_of_none x fun k hk1 hkN => ?_
  have := hp k (by omega) (by omega)
  rintro (h | ⟨h, _⟩) <;> omega

theorem leadCount_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (hx : walkPos x a = 0) :
    leadCount (Fin.append x y) = leadCount x + leadCount y := by
  unfold leadCount
  rw [sum_range_add]
  congr 1
  · refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.1 hk
    have e : inLead (Fin.append x y) (k + 1) ↔ inLead x (k + 1) := by
      unfold inLead
      rw [walkPos_append_le x y (by omega : k + 1 ≤ a), walkPos_append_le x y (by omega : k + 1 - 1 ≤ a)]
    exact if_congr e rfl rfl
  · refine sum_congr rfl fun k hk => ?_
    have e : inLead (Fin.append x y) (a + k + 1) ↔ inLead y (k + 1) := by
      unfold inLead
      have e1 : a + k + 1 - a = k + 1 := by omega
      have e2 : a + k + 1 - 1 - a = k := by omega
      have e3 : k + 1 - 1 = k := by omega
      rw [walkPos_append_ge x y (by omega : a ≤ a + k + 1),
        walkPos_append_ge x y (by omega : a ≤ a + k + 1 - 1)]
      simp only [hx, zero_add, e1, e2, e3]
    exact if_congr e rfl rfl


/-! ### Counting by the first return -/

theorem card_flip {a : ℕ} (P Q : (Fin a → Bool) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q (flipPath x)) (h' : ∀ x, Q x → P (flipPath x)) :
    (univ.filter P).card = (univ.filter Q).card := by
  have hff : ∀ x : Fin a → Bool, flipPath (flipPath x) = x := fun x => by
    funext i; simp [flipPath]
  refine Finset.card_bij' (fun x _ => flipPath x) (fun x _ => flipPath x) ?_ ?_
    (fun x _ => hff x) (fun x _ => hff x)
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact h x hx
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact h' x hx

theorem FR_flip {a : ℕ} (x : Fin a → Bool) : FR (flipPath x) a ↔ FR x a := by
  simp [FR, walkPos_flip]

theorem NR_flip {N : ℕ} (x : Fin N → Bool) : NR (flipPath x) ↔ NR x := by
  simp [NR, walkPos_flip]

/-- First-return paths of length `a` whose first step is up. -/
noncomputable def posRet (a : ℕ) : ℕ :=
  (univ.filter fun x : Fin a → Bool => FR x a ∧ 0 < walkPos x 1).card

/-- First-return paths of length `a` whose first step is down (for `a ≥ 2`). -/
noncomputable def negRet (a : ℕ) : ℕ :=
  (univ.filter fun x : Fin a → Bool => FR x a ∧ ¬ 0 < walkPos x 1).card

theorem posRet_eq_negRet (a : ℕ) (ha : 2 ≤ a) : posRet a = negRet a := by
  unfold posRet negRet
  apply card_flip
  · rintro x ⟨hx, hp⟩
    refine ⟨(FR_flip x).2 hx, ?_⟩
    rw [walkPos_flip]; omega
  · rintro x ⟨hx, hp⟩
    refine ⟨(FR_flip x).2 hx, ?_⟩
    have hne := hx.2.2 1 (by omega) (by omega)
    rw [walkPos_flip]; omega

theorem posRet_add_negRet (a : ℕ) : posRet a + negRet a = firstCount a := by
  unfold posRet negRet firstCount
  have := card_filter_add_card_filter_not
    (s := univ.filter fun x : Fin a → Bool => FR x a) (fun x => 0 < walkPos x 1)
  simp only [filter_filter] at this
  exact this

/-- No-return paths of length `N` whose first step is up. -/
noncomputable def nrPos (N : ℕ) : ℕ :=
  (univ.filter fun x : Fin N → Bool => NR x ∧ 0 < walkPos x 1).card

/-- No-return paths of length `N` whose first step is down (for `N ≥ 1`). -/
noncomputable def nrNeg (N : ℕ) : ℕ :=
  (univ.filter fun x : Fin N → Bool => NR x ∧ ¬ 0 < walkPos x 1).card

theorem nrPos_eq_nrNeg (N : ℕ) (hN : 1 ≤ N) : nrPos N = nrNeg N := by
  unfold nrPos nrNeg
  apply card_flip
  · rintro x ⟨hx, hp⟩
    refine ⟨(NR_flip x).2 hx, ?_⟩
    rw [walkPos_flip]; omega
  · rintro x ⟨hx, hp⟩
    refine ⟨(NR_flip x).2 hx, ?_⟩
    have hne := hx 1 (by omega) hN
    rw [walkPos_flip]; omega

theorem nrPos_add_nrNeg (N : ℕ) : nrPos N + nrNeg N = noRetCount N := by
  unfold nrPos nrNeg noRetCount
  have := card_filter_add_card_filter_not
    (s := univ.filter fun x : Fin N → Bool => NR x) (fun x => 0 < walkPos x 1)
  simp only [filter_filter] at this
  exact this

theorem partition_T (N : ℕ) (T : (Fin N → Bool) → Prop) [DecidablePred T] :
    (univ.filter T).card = (univ.filter fun ω => T ω ∧ NR ω).card +
      ∑ a ∈ Icc 1 N, (univ.filter fun ω => T ω ∧ FR ω a).card := by
  have h1 : (univ.filter fun ω : Fin N → Bool => T ω ∧ ¬ NR ω) =
      (Icc 1 N).biUnion (fun a => univ.filter fun ω : Fin N → Bool => T ω ∧ FR ω a) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc]
    constructor
    · rintro ⟨hT, h⟩
      have hex : ∃ k, 0 < k ∧ k ≤ N ∧ walkPos ω k = 0 := by
        unfold NR at h; push Not at h; exact h
      classical
      have hk := Nat.find_spec hex
      have hmin : ∀ j, j < Nat.find hex → ¬ (0 < j ∧ j ≤ N ∧ walkPos ω j = 0) :=
        fun j hj => Nat.find_min hex hj
      generalize Nat.find hex = k at hk hmin
      exact ⟨k, ⟨hk.1, hk.2.1⟩, hT, hk.1, hk.2.2, fun j hj0 hjk hz => hmin j hjk ⟨hj0, by omega, hz⟩⟩
    · rintro ⟨a, ⟨ha1, haN⟩, hT, _, h0, _⟩
      exact ⟨hT, fun hnr => hnr a ha1 haN h0⟩
  have h2 := card_filter_add_card_filter_not (s := univ.filter T) (fun ω => NR ω)
  simp only [filter_filter] at h2
  rw [h1, card_biUnion] at h2
  · exact h2.symm
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω h1 h2
    rw [mem_filter] at h1 h2
    simp only [mem_univ, true_and, FR] at h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h2.2.2.2 a h1.2.1 hlt h1.2.2.1
    · exact h1.2.2.2 a' h2.2.1 hlt h2.2.2.1

/-- Number of paths of length `N` with exactly `ℓ` segments above the time axis. -/
noncomputable def Lc (N ℓ : ℕ) : ℕ := (univ.filter fun ω : Fin N → Bool => leadCount ω = ℓ).card

theorem card_FRlead (a b N : ℕ) (h : a + b = N) (ha : 2 ≤ a) (ℓ : ℕ) :
    (univ.filter fun ω : Fin N → Bool => leadCount ω = ℓ ∧ FR ω a).card =
      posRet a * (univ.filter fun y : Fin b → Bool => leadCount y + a = ℓ).card +
        negRet a * Lc b ℓ := by
  subst h
  have hs := card_filter_add_card_filter_not
    (s := univ.filter fun ω : Fin (a + b) → Bool => leadCount ω = ℓ ∧ FR ω a) (fun ω => 0 < walkPos ω 1)
  simp only [filter_filter] at hs
  rw [← hs]
  congr 1
  · refine Eq.trans (card_filter_append a b (fun x => FR x a ∧ 0 < walkPos x 1)
      (fun y => leadCount y + a = ℓ) (fun ω => (leadCount ω = ℓ ∧ FR ω a) ∧ 0 < walkPos ω 1) ?_) rfl
    intro x y
    rw [FR_append_iff, walkPos_append_le x y (by omega : 1 ≤ a)]
    constructor
    · rintro ⟨⟨hl, hfr⟩, hp⟩
      rw [leadCount_append x y hfr.2.1, leadCount_FR_pos x hfr hp] at hl
      exact ⟨⟨hfr, hp⟩, by omega⟩
    · rintro ⟨⟨hfr, hp⟩, hl⟩
      refine ⟨⟨?_, hfr⟩, hp⟩
      rw [leadCount_append x y hfr.2.1, leadCount_FR_pos x hfr hp]; omega
  · refine Eq.trans (card_filter_append a b (fun x => FR x a ∧ ¬ 0 < walkPos x 1)
      (fun y => leadCount y = ℓ) (fun ω => (leadCount ω = ℓ ∧ FR ω a) ∧ ¬ 0 < walkPos ω 1) ?_) rfl
    intro x y
    rw [FR_append_iff, walkPos_append_le x y (by omega : 1 ≤ a)]
    constructor
    · rintro ⟨⟨hl, hfr⟩, hp⟩
      have hne := hfr.2.2 1 (by omega) (by omega)
      rw [leadCount_append x y hfr.2.1, leadCount_FR_neg x hfr (by omega)] at hl
      exact ⟨⟨hfr, hp⟩, by omega⟩
    · rintro ⟨⟨hfr, hp⟩, hl⟩
      have hne := hfr.2.2 1 (by omega) (by omega)
      refine ⟨⟨?_, hfr⟩, hp⟩
      rw [leadCount_append x y hfr.2.1, leadCount_FR_neg x hfr (by omega)]; omega

theorem card_NRlead (N : ℕ) (hN : 1 ≤ N) (ℓ : ℕ) :
    (univ.filter fun ω : Fin N → Bool => leadCount ω = ℓ ∧ NR ω).card =
      (if ℓ = N then nrPos N else 0) + (if ℓ = 0 then nrNeg N else 0) := by
  have hs := card_filter_add_card_filter_not
    (s := univ.filter fun ω : Fin N → Bool => leadCount ω = ℓ ∧ NR ω) (fun ω => 0 < walkPos ω 1)
  simp only [filter_filter] at hs
  rw [← hs]
  congr 1
  · by_cases hℓ : ℓ = N
    · subst hℓ
      simp only [↓reduceIte]
      unfold nrPos
      congr 1
      apply filter_congr
      intro ω _
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨leadCount_NR_pos ω h.1 h.2, h.1⟩, h.2⟩⟩
    · simp only [hℓ, ↓reduceIte]
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro ω _ ⟨⟨hl, hnr⟩, hp⟩
      exact hℓ (hl.symm.trans (leadCount_NR_pos ω hnr hp))
  · by_cases hℓ : ℓ = 0
    · subst hℓ
      simp only [↓reduceIte]
      unfold nrNeg
      congr 1
      apply filter_congr
      intro ω _
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · intro h
        have hne := h.1 1 (by omega) hN
        exact ⟨⟨leadCount_NR_neg ω h.1 (by omega), h.1⟩, h.2⟩
    · simp only [hℓ, ↓reduceIte]
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro ω _ ⟨⟨hl, hnr⟩, hp⟩
      have hne := hnr 1 (by omega) hN
      exact hℓ (hl.symm.trans (leadCount_NR_neg ω hnr (by omega)))


theorem card_shift (b a ℓ : ℕ) :
    (univ.filter fun y : Fin b → Bool => leadCount y + a = ℓ).card =
      if a ≤ ℓ then Lc b (ℓ - a) else 0 := by
  by_cases h : a ≤ ℓ
  · simp only [h, ↓reduceIte]
    unfold Lc
    congr 1
    apply filter_congr
    intro y _
    omega
  · simp only [h, ↓reduceIte]
    rw [card_eq_zero, filter_eq_empty_iff]
    intro y _
    omega

theorem FR_false_of_lt {N a : ℕ} (hN : 1 ≤ N) (h : N < a) (ω : Fin N → Bool) : ¬ FR ω a := by
  rintro ⟨ha, h0, hj⟩
  have h1 := hj (a - 1) (by omega) (by omega)
  rw [walkPos_of_le ω (by omega : N ≤ a - 1)] at h1
  rw [walkPos_of_le ω (by omega : N ≤ a)] at h0
  exact h1 h0

theorem FR_false_odd {N a : ℕ} (hN : 1 ≤ N) (ha : a % 2 = 1) (ω : Fin N → Bool) : ¬ FR ω a := by
  by_cases hle : a ≤ N
  · have hc := card_FR a N hle
    obtain ⟨n, rfl⟩ : ∃ n, a = 2 * n + 1 := ⟨a / 2, by omega⟩
    rw [firstCount_odd, zero_mul, card_eq_zero, filter_eq_empty_iff] at hc
    exact hc (mem_univ ω)
  · exact FR_false_of_lt hN (by omega) ω

theorem lead_rec (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    2 * (Lc (2 * m) (2 * k) : ℚ) =
      (if k = m ∨ k = 0 then (noRetCount (2 * m) : ℚ) else 0) +
        ∑ j ∈ Icc 1 m, (firstCount (2 * j) : ℚ) *
          ((if j ≤ k then (Lc (2 * m - 2 * j) (2 * k - 2 * j) : ℚ) else 0) +
            Lc (2 * m - 2 * j) (2 * k)) := by
  have hL : Lc (2 * m) (2 * k) = _ := partition_T (2 * m) (fun ω => leadCount ω = 2 * k)
  rw [card_NRlead (2 * m) (by omega) (2 * k)] at hL
  have hnr := nrPos_add_nrNeg (2 * m)
  have hnr2 := nrPos_eq_nrNeg (2 * m) (by omega)
  have hA : 2 * ((if 2 * k = 2 * m then nrPos (2 * m) else 0) +
      (if 2 * k = 0 then nrNeg (2 * m) else 0)) =
      if k = m ∨ k = 0 then noRetCount (2 * m) else 0 := by
    split_ifs <;> omega
  have hA' := congrArg (Nat.cast : ℕ → ℚ) hA
  push_cast at hA'
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℚ, g = fun a =>
      ((univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k ∧ FR ω a).card : ℚ) := ⟨_, rfl⟩
  have hodd : ∀ n, g (2 * n + 1) = 0 := by
    intro n
    rw [hg]
    simp only [Nat.cast_eq_zero]
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro ω _ ⟨_, h⟩
    exact FR_false_odd (by omega) (by omega) ω h
  have hsum := sum_Icc_even g hodd m
  have hLq : (Lc (2 * m) (2 * k) : ℚ) =
      ((if 2 * k = 2 * m then (nrPos (2 * m) : ℚ) else 0) +
        (if 2 * k = 0 then (nrNeg (2 * m) : ℚ) else 0)) + ∑ a ∈ Icc 1 (2 * m), g a := by
    rw [hL, hg]
    push_cast
    rfl
  have hterm : ∀ j ∈ Icc 1 m, 2 * g (2 * j) = (firstCount (2 * j) : ℚ) *
      ((if j ≤ k then (Lc (2 * m - 2 * j) (2 * k - 2 * j) : ℚ) else 0) +
        Lc (2 * m - 2 * j) (2 * k)) := by
    intro j hj
    rw [mem_Icc] at hj
    rw [hg]
    simp only
    rw [card_FRlead (2 * j) (2 * m - 2 * j) (2 * m) (by omega) (by omega) (2 * k), card_shift]
    have h1 := posRet_add_negRet (2 * j)
    have h2 := posRet_eq_negRet (2 * j) (by omega)
    have hF : (firstCount (2 * j) : ℚ) = 2 * posRet (2 * j) := by
      rw [← h1, h2]; push_cast; ring
    have hN : (negRet (2 * j) : ℚ) = posRet (2 * j) := by rw [h2]
    have hjk : 2 * j ≤ 2 * k ↔ j ≤ k := by omega
    have hjk' : 2 * k - 2 * j = 2 * (k - j) := (Nat.mul_sub 2 k j).symm
    simp only [hjk, hjk']
    by_cases hjk2 : j ≤ k
    · simp only [hjk2, ↓reduceIte]
      push_cast
      rw [hF, hN]; ring
    · simp only [hjk2, ↓reduceIte]
      push_cast
      rw [hF, hN]; ring
  rw [hLq, mul_add, hsum, mul_sum]
  congr 1
  exact sum_congr rfl hterm


/-! ### The recursion solved by the arc sine weights -/

theorem c_renewal (n : ℕ) (hn : 1 ≤ n) : c n = ∑ k ∈ Icc 1 n, f (2 * k) * c (n - k) := by
  have h1 := u_renewal n hn
  rw [u_two_mul] at h1
  have e : ∀ k, u (2 * n - 2 * k) = c (n - k) := fun k => by
    rw [← Nat.mul_sub, u_two_mul]
  simp only [e] at h1
  exact h1

/-- The weights `c_k c_{m-k}` (zero for `k > m`). -/
noncomputable def vee (m k : ℕ) : ℚ := if k ≤ m then c k * c (m - k) else 0

theorem sum_ite_Icc (m k : ℕ) (hk : k ≤ m) (g : ℕ → ℚ) :
    ∑ j ∈ Icc 1 m, (if j ≤ k then g j else 0) = ∑ j ∈ Icc 1 k, g j := by
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_Icc]
  omega

theorem lead_identity (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    2 * vee m k = (if k = m ∨ k = 0 then c m else 0) +
      ∑ j ∈ Icc 1 m, f (2 * j) *
        ((if j ≤ k then vee (m - j) (k - j) else 0) + vee (m - j) k) := by
  by_cases hkm : k ≤ m
  · have hSA : ∑ j ∈ Icc 1 m, f (2 * j) * (if j ≤ k then vee (m - j) (k - j) else 0) =
        if 1 ≤ k then c k * c (m - k) else 0 := by
      have e : ∀ j ∈ Icc 1 m, f (2 * j) * (if j ≤ k then vee (m - j) (k - j) else 0) =
          if j ≤ k then c (m - k) * (f (2 * j) * c (k - j)) else 0 := by
        intro j hj
        rw [mem_Icc] at hj
        by_cases hjk : j ≤ k
        · have h1 : k - j ≤ m - j := by omega
          have h2 : m - j - (k - j) = m - k := by omega
          simp only [hjk, ↓reduceIte, vee, h1, h2]
          ring
        · simp [hjk]
      rw [sum_congr rfl e, sum_ite_Icc m k hkm (fun j => c (m - k) * (f (2 * j) * c (k - j))), ← mul_sum]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [← c_renewal k hk]
        simp only [show 1 ≤ k from hk, ↓reduceIte]
        ring
    have hSB : ∑ j ∈ Icc 1 m, f (2 * j) * vee (m - j) k =
        if 1 ≤ m - k then c k * c (m - k) else 0 := by
      have e : ∀ j ∈ Icc 1 m, f (2 * j) * vee (m - j) k =
          if j ≤ m - k then c k * (f (2 * j) * c (m - k - j)) else 0 := by
        intro j hj
        rw [mem_Icc] at hj
        by_cases hjk : j ≤ m - k
        · have h1 : k ≤ m - j := by omega
          have h2 : m - j - k = m - k - j := by omega
          simp only [hjk, ↓reduceIte, vee, h1, h2]
          ring
        · have h1 : ¬ k ≤ m - j := by omega
          simp [hjk, vee, h1]
      rw [sum_congr rfl e, sum_ite_Icc m (m - k) (by omega) (fun j => c k * (f (2 * j) * c (m - k - j))),
        ← mul_sum]
      rcases Nat.eq_zero_or_pos (m - k) with h0 | hk
      · rw [h0]; simp
      · rw [← c_renewal (m - k) hk]
        simp only [show 1 ≤ m - k from hk, ↓reduceIte]
    simp only [mul_add, sum_add_distrib, hSA, hSB]
    unfold vee
    simp only [hkm, ↓reduceIte]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [c_zero, hm]
      ring
    · have hk1 : 1 ≤ k := hk
      by_cases hkm2 : k = m
      · subst hkm2
        simp [c_zero, hk.ne', hk1]
        ring
      · have h1 : 1 ≤ m - k := by omega
        simp [hk.ne', hkm2, hk1, h1]
        ring
  · have h0 : ∀ j ∈ Icc 1 m, f (2 * j) *
        ((if j ≤ k then vee (m - j) (k - j) else 0) + vee (m - j) k) = 0 := by
      intro j hj
      rw [mem_Icc] at hj
      have h1 : ¬ (k - j ≤ m - j) := by omega
      have h2 : ¬ k ≤ m - j := by omega
      simp [vee, h1, h2]
    rw [sum_eq_zero h0]
    have h3 : ¬ k = m := by omega
    have h4 : ¬ k = 0 := by omega
    simp [vee, hkm, h3, h4]

/-- Counting form of the arc sine law for the time in the lead (weights `4^m c_k c_{m-k}`). -/
theorem Lc_eq (m : ℕ) : ∀ k, (Lc (2 * m) (2 * k) : ℚ) = 4 ^ m * vee m k := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · by_cases hk : k = 0
      · subst hk
        simp [Lc, leadCount, vee, c_zero]
      · simp [Lc, leadCount, vee, hk]
    · have h := lead_rec m hm k
      have hi := lead_identity m hm k
      have hNR : (noRetCount (2 * m) : ℚ) = 4 ^ m * c m := by
        rw [noRetCount_even]
        unfold c
        field_simp
      have hsum : ∑ j ∈ Icc 1 m, (firstCount (2 * j) : ℚ) *
          ((if j ≤ k then (Lc (2 * m - 2 * j) (2 * k - 2 * j) : ℚ) else 0) +
            Lc (2 * m - 2 * j) (2 * k)) =
          4 ^ m * ∑ j ∈ Icc 1 m, f (2 * j) *
            ((if j ≤ k then vee (m - j) (k - j) else 0) + vee (m - j) k) := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        rw [mem_Icc] at hj
        have hF : (firstCount (2 * j) : ℚ) = f (2 * j) * 4 ^ j := by
          unfold f
          rw [pow_mul]
          norm_num
        have e4 : (4 : ℚ) ^ m = 4 ^ j * 4 ^ (m - j) := by
          rw [← pow_add]; congr 1; omega
        have hm1 : 2 * m - 2 * j = 2 * (m - j) := (Nat.mul_sub 2 m j).symm
        have hk1 : 2 * k - 2 * j = 2 * (k - j) := (Nat.mul_sub 2 k j).symm
        rw [hm1, hk1, hF, ih (m - j) (by omega) k, e4]
        by_cases hjk : j ≤ k
        · simp only [hjk, ↓reduceIte]
          rw [ih (m - j) (by omega) (k - j)]
          ring
        · simp only [hjk, ↓reduceIte]
          ring
      have h2 : 2 * (Lc (2 * m) (2 * k) : ℚ) = 4 ^ m * (2 * vee m k) := by
        rw [h, hi, hsum, mul_add]
        by_cases hc : k = m ∨ k = 0
        · simp only [hc, ↓reduceIte]; rw [hNR]
        · simp only [hc, ↓reduceIte]; ring
      linarith

/-- Grinstead–Snell Theorem 12.4 (PR-129), counting form: among the `2^{2m}` paths of length `2m`, exactly
`C(2k,k) C(2m-2k,m-k)` have exactly `2k` of their segments above the time axis. -/
theorem leadCount_count (m k : ℕ) (hk : k ≤ m) :
    Lc (2 * m) (2 * k) = (2 * k).choose k * (2 * (m - k)).choose (m - k) := by
  have h := Lc_eq m k
  unfold vee c at h
  simp only [hk, ↓reduceIte] at h
  have h4 : (4 : ℚ) ^ m = 4 ^ k * 4 ^ (m - k) := by
    rw [← pow_add]; congr 1; omega
  rw [h4] at h
  field_simp at h
  exact_mod_cast h

/-- Grinstead–Snell Theorem 12.4 (PR-129). If Peter and Paul play Heads or Tails with `2m` tosses, the probability
`b_{2k,2m}` that Peter is in the lead exactly `2k` times (the walk has exactly `2k` segments above the axis) is
`α_{2k,2m} = u_{2k} u_{2m-2k}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.4, p. 502"]
theorem leadCount_prob (m k : ℕ) (hk : k ≤ m) :
    ((univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card : ℚ) / 2 ^ (2 * m) =
      u (2 * k) * u (2 * (m - k)) := by
  have h : (univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card =
      (2 * k).choose k * (2 * (m - k)).choose (m - k) := leadCount_count m k hk
  rw [h, u_two_mul, u_two_mul, prob_pow_two_mul m k hk]
  unfold c
  push_cast
  rw [div_mul_div_comm]


/-! ## The continuous limit (arc sine law)

The weights `u_{2k} u_{2m-2k}` have the Riemann-sum limit `(2/π) arcsin √α`: Stirling gives
`u_{2k} √k → 1/√π`, the step function `m u_{2⌊xm⌋} u_{2m-2⌊xm⌋}` is dominated by `C / √x` (from the bound
`(2k+1) u_{2k}² ≤ 1`), and dominated convergence gives the integral of `1/(π √(x(1-x)))`. -/

section ArcSineLimit

open Filter Topology Real MeasureTheory Set


theorem c_eq_stirling (k : ℕ) (hk : 1 ≤ k) :
    (c k : ℝ) = Stirling.stirlingSeq (2 * k) / (Stirling.stirlingSeq k ^ 2 * √(k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : ∀ n : ℕ, 1 ≤ n → (n.factorial : ℝ) = Stirling.stirlingSeq n * (√(2 * n) * (n / exp 1) ^ n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold Stirling.stirlingSeq
    have : √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n ≠ 0 := by positivity
    field_simp
  have hch : ((2 * k).choose k : ℝ) = ((2 * k).factorial : ℝ) / ((k.factorial : ℝ) * (k.factorial : ℝ)) := by
    have e : 2 * k - k = k := by omega
    rw [Nat.cast_choose ℝ (by omega : k ≤ 2 * k), e]
  unfold c
  push_cast
  rw [hch, hs (2 * k) (by omega), hs k hk]
  push_cast
  have hsk : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le (Real.sqrt_pos.2 pi_pos) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hr : √(2 * (2 * (k : ℝ))) = 2 * √(k : ℝ) := by
    rw [show 2 * (2 * (k : ℝ)) = 2 ^ 2 * k by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have ht : √(2 * (k : ℝ)) * √(2 * (k : ℝ)) = 2 * k := Real.mul_self_sqrt (by positivity)
  have hk2 : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hkpos.le
  have hX : ∀ x : ℝ, x ^ (2 * k) = x ^ k * x ^ k := fun x => by rw [two_mul, pow_add]
  have hpow : (2 * (k : ℝ) / exp 1) ^ (2 * k) = 4 ^ k * ((k : ℝ) / exp 1) ^ k * ((k : ℝ) / exp 1) ^ k := by
    rw [mul_div_assoc, mul_pow, hX 2, hX ((k : ℝ) / exp 1)]
    have : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
    rw [← this]; ring
  rw [hr, hpow]
  have hXp : 0 < ((k : ℝ) / exp 1) ^ k := by positivity
  have hqp : 0 < √(2 * (k : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hrp : 0 < √(k : ℝ) := Real.sqrt_pos.2 hkpos
  generalize ((k : ℝ) / exp 1) ^ k = X at *
  generalize √(2 * (k : ℝ)) = q at *
  generalize √(k : ℝ) = r at *
  field_simp
  have hq2 : q ^ 2 = 2 * r ^ 2 := by rw [sq, sq, ht]; linarith
  rw [hq2]; ring


theorem c_sqrt_tendsto : Tendsto (fun k : ℕ => ((c k : ℚ) : ℝ) * √(k : ℝ)) atTop (𝓝 (1 / √π)) := by
  have hmul : Tendsto (fun k : ℕ => 2 * k) atTop atTop := tendsto_atTop_mono (fun n => by simp only [id]; omega) tendsto_id
  have h1 : Tendsto (fun k : ℕ => Stirling.stirlingSeq (2 * k)) atTop (𝓝 (√π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp hmul
  have h2 : Tendsto (fun k : ℕ => Stirling.stirlingSeq k ^ 2) atTop (𝓝 (√π ^ 2)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.pow 2
  have hpi : 0 < √π := Real.sqrt_pos.2 pi_pos
  have h3 := h1.div h2 (by positivity)
  have hval : √π / √π ^ 2 = 1 / √π := by field_simp
  rw [hval] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [c_eq_stirling k hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le (Real.sqrt_pos.2 pi_pos) (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hkpos).ne'
  simp only [Pi.div_apply]
  field_simp


/-- `v m k = m c_k c_{m-k}`: `m` times the arc sine weight. -/
noncomputable def vw (m k : ℕ) : ℝ := (m : ℝ) * (((c k : ℚ) : ℝ) * ((c (m - k) : ℚ) : ℝ))

theorem vw_tendsto (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun m : ℕ => vw m ⌊x * m⌋₊) atTop (𝓝 (1 / (π * √(x * (1 - x))))) := by
  set k : ℕ → ℕ := fun m => ⌊x * m⌋₊ with hkdef
  have hrat : Tendsto (fun m : ℕ => (k m : ℝ) / m) atTop (𝓝 x) :=
    (tendsto_nat_floor_mul_div_atTop hx0.le).comp tendsto_natCast_atTop_atTop
  have hk : Tendsto k atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hx0)
  have hkle : ∀ m, k m ≤ m := fun m => by
    have : (k m : ℝ) ≤ x * m := Nat.floor_le (by positivity)
    have h2 : x * (m : ℝ) ≤ m := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact_mod_cast this.trans h2
  have hk' : Tendsto (fun m => m - k m) atTop atTop := by
    have h1 : Tendsto (fun m : ℕ => (1 - x) * (m : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
    have h2 : Tendsto (fun m : ℕ => ⌊(1 - x) * (m : ℝ)⌋₊) atTop atTop := tendsto_nat_floor_atTop.comp h1
    refine tendsto_atTop_mono (fun m => ?_) h2
    have : (k m : ℝ) ≤ x * m := Nat.floor_le (by positivity)
    apply Nat.floor_le_of_le
    rw [Nat.cast_sub (hkle m)]
    linarith
  have hA := c_sqrt_tendsto.comp hk
  have hB := c_sqrt_tendsto.comp hk'
  have hW : Tendsto (fun m : ℕ => ((k m : ℝ) / m) * (1 - (k m : ℝ) / m)) atTop (𝓝 (x * (1 - x))) :=
    hrat.mul (tendsto_const_nhds.sub hrat)
  have hWp : 0 < x * (1 - x) := by nlinarith
  have hS := (hW.sqrt)
  have hlim := (hA.mul hB).div hS (Real.sqrt_pos.2 hWp).ne'
  have hval : 1 / √π * (1 / √π) / √(x * (1 - x)) = 1 / (π * √(x * (1 - x))) := by
    have hpi : 0 < √π := Real.sqrt_pos.2 pi_pos
    have : √π * √π = π := Real.mul_self_sqrt pi_pos.le
    have hs : 0 < √(x * (1 - x)) := Real.sqrt_pos.2 hWp
    field_simp
    rw [sq, this]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hk.eventually_ge_atTop 1, hk'.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with m h1 h2 h3
  simp only [Function.comp, Pi.div_apply]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast h3
  have hkpos : (0 : ℝ) < k m := by exact_mod_cast h1
  have hmk : ((m - k m : ℕ) : ℝ) = m - k m := Nat.cast_sub (hkle m)
  have hmk' : (0 : ℝ) < m - k m := by rw [← hmk]; exact_mod_cast h2
  set W : ℝ := ((k m : ℝ) / m) * (1 - (k m : ℝ) / m) with hWdef
  have hWpos : 0 < W := by
    have : (k m : ℝ) / m < 1 := by rw [div_lt_one hmpos]; linarith
    have : 0 < (k m : ℝ) / m := by positivity
    rw [hWdef]; nlinarith
  have hsq : √(k m : ℝ) * √((m : ℝ) - k m) = m * √W := by
    rw [← Real.sqrt_mul hkpos.le]
    have : (k m : ℝ) * ((m : ℝ) - k m) = (m : ℝ) ^ 2 * W := by
      rw [hWdef]; field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hmpos.le]
  unfold vw
  rw [hmk]
  have hs1 : 0 < √(k m : ℝ) := Real.sqrt_pos.2 hkpos
  have hs2 : 0 < √((m : ℝ) - k m) := Real.sqrt_pos.2 hmk'
  have hsW : 0 < √W := Real.sqrt_pos.2 hWpos
  have e : ((c (k m) : ℚ) : ℝ) * √(k m : ℝ) * (((c (m - k m) : ℚ) : ℝ) * √((m : ℝ) - k m)) / √W =
      ((c (k m) : ℚ) : ℝ) * ((c (m - k m) : ℚ) : ℝ) * (√(k m : ℝ) * √((m : ℝ) - k m)) / √W := by ring
  rw [e, hsq]
  show _ = (m : ℝ) * (((c (k m) : ℚ) : ℝ) * ((c (m - k m) : ℚ) : ℝ))
  field_simp


theorem c_sq_bound' (k : ℕ) : (2 * (k : ℚ) + 1) * c k ^ 2 ≤ 1 := by
  induction k with
  | zero => simp [c_zero]
  | succ k ih =>
    have h := c_succ k
    have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hc : 0 ≤ c k ^ 2 := sq_nonneg _
    have hd : (2 * ((k : ℚ) + 1)) ^ 2 * c (k + 1) ^ 2 = (2 * k + 1) ^ 2 * c k ^ 2 := by
      rw [← mul_pow, h, mul_pow]
    push_cast
    have hpos : 0 < (2 * ((k : ℚ) + 1)) ^ 2 := by positivity
    have : (2 * ((k : ℚ) + 1)) ^ 2 * ((2 * ((k : ℚ) + 1) + 1) * c (k + 1) ^ 2) ≤
        (2 * ((k : ℚ) + 1)) ^ 2 * 1 := by
      have e : (2 * ((k : ℚ) + 1)) ^ 2 * ((2 * ((k : ℚ) + 1) + 1) * c (k + 1) ^ 2) =
          (2 * ((k : ℚ) + 1) + 1) * ((2 * k + 1) ^ 2 * c k ^ 2) := by
        rw [← hd]; ring
      rw [e]
      nlinarith [mul_nonneg (mul_nonneg hk hk) hc, mul_nonneg hk hc, hc]
    exact le_of_mul_le_mul_left this hpos

theorem cR_nonneg (k : ℕ) : 0 ≤ ((c k : ℚ) : ℝ) := by
  have : (0 : ℚ) ≤ c k := by unfold c; positivity
  exact_mod_cast this

theorem cR_sq_bound (k : ℕ) : (2 * (k : ℝ) + 1) * ((c k : ℚ) : ℝ) ^ 2 ≤ 1 := by
  have := c_sq_bound' k
  exact_mod_cast this

theorem vw_nonneg (m k : ℕ) : 0 ≤ vw m k := by
  unfold vw
  exact mul_nonneg (Nat.cast_nonneg m) (mul_nonneg (cR_nonneg k) (cR_nonneg _))

theorem vw_sq_le (m k : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (hk1 : x * m < k + 1)
    (hk2 : (k : ℝ) ≤ x * m) (hkm : k ≤ m) : vw m k ^ 2 ≤ 1 / (x * (1 - x)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [vw]; positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : ((m - k : ℕ) : ℝ) = m - k := Nat.cast_sub hkm
  have h1 : ((c k : ℚ) : ℝ) ^ 2 ≤ 1 / (x * m) := by
    rw [le_div_iff₀ (by positivity)]
    have := cR_sq_bound k
    nlinarith [sq_nonneg (((c k : ℚ) : ℝ)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2 : ((c (m - k) : ℚ) : ℝ) ^ 2 ≤ 1 / ((1 - x) * m) := by
    rw [le_div_iff₀ (by have : 0 < 1 - x := by linarith
                        positivity)]
    have := cR_sq_bound (m - k)
    rw [hmk] at this
    nlinarith [sq_nonneg (((c (m - k) : ℚ) : ℝ))]
  unfold vw
  have e : ((m : ℝ) * (((c k : ℚ) : ℝ) * ((c (m - k) : ℚ) : ℝ))) ^ 2 =
      (m : ℝ) ^ 2 * (((c k : ℚ) : ℝ) ^ 2 * ((c (m - k) : ℚ) : ℝ) ^ 2) := by ring
  rw [e]
  have hx2 : 0 < 1 - x := by linarith
  calc (m : ℝ) ^ 2 * (((c k : ℚ) : ℝ) ^ 2 * ((c (m - k) : ℚ) : ℝ) ^ 2)
      ≤ (m : ℝ) ^ 2 * (1 / (x * m) * (1 / ((1 - x) * m))) := by
        gcongr
    _ = 1 / (x * (1 - x)) := by field_simp


/-- The step function whose integral is the arc sine sum. -/
noncomputable def Gm (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (⌊α * m⌋₊ + 1),
    Set.indicator (Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m)) (fun _ => vw m k) x

theorem mem_Ico_iff_floor (m k : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 ≤ x) :
    x ∈ Set.Ico ((k : ℝ) / m) (((k : ℝ) + 1) / m) ↔ ⌊x * m⌋₊ = k := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity), Set.mem_Ico, div_le_iff₀ hmpos, lt_div_iff₀ hmpos]

theorem Gm_apply (α : ℝ) (m : ℕ) (hm : 0 < m) (x : ℝ) (hx : 0 < x) :
    Gm α m x = if ⌊x * m⌋₊ ≤ ⌊α * m⌋₊ then vw m ⌊x * m⌋₊ else 0 := by
  unfold Gm
  by_cases h : ⌊x * m⌋₊ ≤ ⌊α * m⌋₊
  · rw [if_pos h, Finset.sum_eq_single ⌊x * m⌋₊]
    · exact Set.indicator_of_mem ((mem_Ico_iff_floor m _ hm x hx.le).2 rfl) _
    · intro k _ hk
      exact Set.indicator_of_notMem (fun hmem => hk ((mem_Ico_iff_floor m k hm x hx.le).1 hmem).symm) _
    · intro hn
      exact absurd (mem_range.2 (Nat.lt_succ_of_le h)) hn
  · rw [if_neg h]
    refine sum_eq_zero fun k hk => Set.indicator_of_notMem (fun hmem => h ?_) _
    rw [(mem_Ico_iff_floor m k hm x hx.le).1 hmem]
    exact Nat.lt_succ_iff.1 (mem_range.1 hk)

theorem Gm_of_neg (α : ℝ) (m : ℕ) (x : ℝ) (hx : x < 0) : Gm α m x = 0 := by
  unfold Gm
  refine sum_eq_zero fun k _ => Set.indicator_of_notMem (fun hmem => ?_) _
  have : (0 : ℝ) ≤ (k : ℝ) / m := by positivity
  exact absurd hmem.1 (by linarith)

theorem Gm_nonneg (α : ℝ) (m : ℕ) (x : ℝ) : 0 ≤ Gm α m x :=
  sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => vw_nonneg m k) x

theorem Gm_integrable (α : ℝ) (m : ℕ) : Integrable (Gm α m) := by
  unfold Gm
  refine integrable_finsetSum _ fun k _ => ?_
  refine IntegrableOn.integrable_indicator (integrableOn_const ?_) measurableSet_Ico
  rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top

theorem Gm_integral (α : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, Gm α m x = ∑ k ∈ range (⌊α * m⌋₊ + 1), ((c k : ℚ) : ℝ) * ((c (m - k) : ℚ) : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  unfold Gm
  rw [integral_finsetSum _ (fun k _ => ?_)]
  · refine sum_congr rfl fun k _ => ?_
    rw [integral_indicator measurableSet_Ico, setIntegral_const]
    have : ((k : ℝ) + 1) / m - (k : ℝ) / m = 1 / m := by field_simp; ring
    simp only [Measure.real, Real.volume_Ico, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by rw [this]; positivity), this]
    unfold vw
    field_simp
  · refine IntegrableOn.integrable_indicator (integrableOn_const ?_) measurableSet_Ico
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top


theorem integrableOn_div_sqrt (C a : ℝ) (_ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ => C / √x) (Set.Ioc 0 a) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := -(1 / 2 : ℝ))
    (by norm_num)).1
  have h2 : IntegrableOn (fun x : ℝ => C * x ^ (-(1 / 2 : ℝ))) (Set.Ioc 0 a) := Integrable.const_mul h C
  refine IntegrableOn.congr_fun h2 (fun x hx => ?_) measurableSet_Ioc
  have hx0 : 0 ≤ x := hx.1.le
  rw [Real.rpow_neg hx0, Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

theorem arcsin_integral (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    ∫ x in Set.Ioo 0 α, 1 / (π * √(x * (1 - x))) = (2 / π) * Real.arcsin (√α) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h0.le]
  have hcont : ContinuousOn (fun x : ℝ => (2 / π) * Real.arcsin (√x)) (Set.Icc 0 α) :=
    (continuous_const.mul (Real.continuous_arcsin.comp Real.continuous_sqrt)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo 0 α, HasDerivAt (fun x : ℝ => (2 / π) * Real.arcsin (√x))
      (1 / (π * √(x * (1 - x)))) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2.trans h1
    have hs : HasDerivAt (fun x : ℝ => √x) (1 / (2 * √x)) x := (hasDerivAt_id x).sqrt hx0.ne'
    have hsx : √x < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hx1
    have hsx0 : 0 < √x := Real.sqrt_pos.2 hx0
    have ha := (((hasDerivAt_arcsin (by linarith : √x ≠ -1) hsx.ne).comp x hs)).const_mul (2 / π)
    refine ha.congr_deriv ?_
    have h2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
    rw [h2, Real.sqrt_mul hx0.le]
    have h3 : 0 < √(1 - x) := Real.sqrt_pos.2 (by linarith)
    field_simp
  have hbd : IntegrableOn (fun x : ℝ => (1 / √(1 - α)) / √x) (Set.Ioc 0 α) :=
    integrableOn_div_sqrt _ _ h0.le
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (π * √(x * (1 - x)))) MeasureTheory.volume 0 α := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0.le]
    refine Integrable.mono' hbd ?_ ?_
    · exact (by fun_prop : Measurable (fun x : ℝ => 1 / (π * √(x * (1 - x))))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
      have hx1 : x ≤ α := hx.2
      have hx0 : 0 < x := hx.1
      have hpos : 0 < √(x * (1 - x)) := Real.sqrt_pos.2 (by nlinarith)
      have hs : 0 < √x := Real.sqrt_pos.2 hx0
      have hsa : 0 < √(1 - α) := Real.sqrt_pos.2 (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (π * √(x * (1 - x)))), Real.sqrt_mul hx0.le]
      have hle : √(1 - α) ≤ √(1 - x) := Real.sqrt_le_sqrt (by linarith)
      have hpi : 1 ≤ π := by linarith [pi_gt_three]
      have h3 : 0 < √(1 - x) := lt_of_lt_of_le hsa hle
      calc 1 / (π * (√x * √(1 - x))) ≤ 1 / (1 * (√x * √(1 - α))) := by
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith [mul_pos hs hsa, mul_le_mul_of_nonneg_left hle hs.le]
        _ = 1 / √(1 - α) / √x := by field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0.le hcont hderiv hint]
  simp


/-- The arc sine sums converge to the arc sine distribution function:
`∑_{k ≤ αm} u_{2k} u_{2m-2k} → (2/π) arcsin √α`. -/
theorem arcsine_sum_tendsto (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1), ((c k : ℚ) : ℝ) * ((c (m - k) : ℚ) : ℝ))
      atTop (𝓝 ((2 / π) * Real.arcsin (√α))) := by
  set α' : ℝ := (1 + α) / 2 with hα'
  have hαα' : α < α' := by rw [hα']; linarith
  have hα'1 : α' < 1 := by rw [hα']; linarith
  set C : ℝ := 1 / √(1 - α') with hC
  have hCpos : 0 < C := by
    have : 0 < √(1 - α') := Real.sqrt_pos.2 (by linarith)
    positivity
  set b : ℝ → ℝ := Set.indicator (Set.Ioo 0 α') (fun x => C / √x) with hb
  set f : ℝ → ℝ := Set.indicator (Set.Ioo 0 α) (fun x => 1 / (π * √(x * (1 - x)))) with hf
  have hbint : Integrable b := by
    rw [hb, integrable_indicator_iff measurableSet_Ioo]
    exact (integrableOn_div_sqrt C α' (by linarith)).mono_set Set.Ioo_subset_Ioc_self
  have hbnn : ∀ x, 0 ≤ b x := fun x => Set.indicator_nonneg (fun y _ => by positivity) x
  have hev : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧ 1 ≤ (α' - α) * m := by
    filter_upwards [eventually_ge_atTop 1,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / (α' - α))] with m h1m h2m
    refine ⟨h1m, ?_⟩
    have hd : 0 < α' - α := by linarith
    rw [div_le_iff₀ hd] at h2m
    linarith
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun m : ℕ => Gm α m x) atTop (𝓝 (f x)) := by
    have hne : ∀ᵐ x : ℝ, x ≠ α ∧ x ≠ 0 := by
      have h1 := (Set.countable_singleton α).ae_notMem (volume : Measure ℝ)
      have h2 := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      filter_upwards [h1, h2] with x hx1 hx2
      exact ⟨hx1, hx2⟩
    filter_upwards [hne] with x hx
    obtain ⟨hxα, hx0⟩ := hx
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have : f x = 0 := Set.indicator_of_notMem (fun h : x ∈ Set.Ioo 0 α => by linarith [h.1]) _
      rw [this]
      exact tendsto_const_nhds.congr (fun m => (Gm_of_neg α m x hneg).symm)
    rcases lt_or_gt_of_ne hxα with hlt | hgt
    · have hfx : f x = 1 / (π * √(x * (1 - x))) := Set.indicator_of_mem (show x ∈ Set.Ioo 0 α from ⟨hpos, hlt⟩) _
      rw [hfx]
      refine (vw_tendsto x hpos (by linarith)).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with m hm
      rw [Gm_apply α m hm x hpos, if_pos]
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hlt.le (Nat.cast_nonneg m))
    · have hfx : f x = 0 := Set.indicator_of_notMem (fun h : x ∈ Set.Ioo 0 α => by linarith [h.2]) _
      rw [hfx]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1,
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / (x - α))] with m hm h2m
      have hcond : ¬ ⌊x * m⌋₊ ≤ ⌊α * m⌋₊ := by
        push Not
        apply Nat.lt_of_succ_le
        apply Nat.le_floor
        have hd : 0 < x - α := by linarith
        rw [div_le_iff₀ hd] at h2m
        have := Nat.floor_le (show 0 ≤ α * (m : ℝ) by positivity)
        push_cast
        nlinarith
      rw [Gm_apply α m hm x hpos, if_neg hcond]
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ᵐ x : ℝ, ‖Gm α m x‖ ≤ b x := by
    filter_upwards [hev] with m hmM
    obtain ⟨hm, hM⟩ := hmM
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have h0ae : ∀ᵐ x : ℝ, x ≠ 0 := by
      have h2 := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
      filter_upwards [h2] with x hx using hx
    filter_upwards [h0ae] with x hx0
    rw [Real.norm_eq_abs, abs_of_nonneg (Gm_nonneg α m x)]
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · rw [Gm_of_neg α m x hneg]; exact hbnn x
    rw [Gm_apply α m hm x hpos]
    by_cases hxa : x < α'
    · have hbx : b x = C / √x := Set.indicator_of_mem (show x ∈ Set.Ioo 0 α' from ⟨hpos, hxa⟩) _
      rw [hbx]
      split_ifs with hfl
      · have hkx : ((⌊x * m⌋₊ : ℕ) : ℝ) ≤ x * m := Nat.floor_le (by positivity)
        have hkx' : x * m < ⌊x * m⌋₊ + 1 := Nat.lt_floor_add_one _
        have hkm : ⌊x * m⌋₊ ≤ m := by
          have : (⌊x * m⌋₊ : ℝ) ≤ m := by nlinarith
          exact_mod_cast this
        have hsq := vw_sq_le m ⌊x * m⌋₊ x hpos (by linarith) hkx' hkx hkm
        have hsx : 0 < √x := Real.sqrt_pos.2 hpos
        have h1x : 1 / (x * (1 - x)) ≤ (C / √x) ^ 2 := by
          rw [div_pow, hC, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hpos.le, one_pow, div_div,
            div_le_div_iff₀ (by nlinarith) (by nlinarith)]
          nlinarith
        have := hsq.trans h1x
        exact (pow_le_pow_iff_left₀ (vw_nonneg _ _) (by positivity) two_ne_zero).1 this
      · positivity
    · have hbx : b x = 0 := Set.indicator_of_notMem (fun h : x ∈ Set.Ioo 0 α' => hxa h.2) _
      rw [hbx]
      split_ifs with hfl
      · exfalso
        have h1 := Nat.floor_le (show 0 ≤ α * (m : ℝ) by positivity)
        have h2 : ((⌊x * m⌋₊ : ℕ) : ℝ) ≤ α * m := (Nat.cast_le.2 hfl).trans h1
        have h3 : α' * m ≤ x * m := mul_le_mul_of_nonneg_right (not_lt.1 hxa) hmpos.le
        have h4 := Nat.lt_floor_add_one (x * (m : ℝ))
        nlinarith
      · exact le_rfl
  have key := tendsto_integral_filter_of_dominated_convergence b
    (Eventually.of_forall fun m => (Gm_integrable α m).aestronglyMeasurable) hbound hbint hlim
  have hfint : ∫ x, f x = (2 / π) * Real.arcsin (√α) := by
    rw [hf, integral_indicator measurableSet_Ioo]
    exact arcsin_integral α h0 h1
  rw [hfint] at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact Gm_integral α m hm


end ArcSineLimit

/-- Passage to the limit for any family of counts equal to the arc sine weights. -/
theorem arcsine_prob_tendsto (cnt : ℕ → ℕ → ℕ)
    (hcnt : ∀ m k, k ≤ m → ((cnt m k : ℕ) : ℚ) / 2 ^ (2 * m) = u (2 * k) * u (2 * (m - k)))
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1), ((cnt m k : ℕ) : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) := by
  refine (arcsine_sum_tendsto α h0 h1).congr fun m => ?_
  refine (sum_congr rfl fun k hk => ?_).symm
  have hk' : k ≤ m := by
    have h2 := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have h3 : (⌊α * m⌋₊ : ℝ) ≤ α * m := Nat.floor_le (by positivity)
    have h4 : α * (m : ℝ) ≤ m := by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have : (k : ℝ) ≤ m := (Nat.cast_le.2 h2).trans (h3.trans h4)
    exact_mod_cast this
  have h := hcnt m k hk'
  rw [u_two_mul, u_two_mul] at h
  have := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at this
  exact this

/-- Grinstead–Snell Theorem 12.4 (PR-129), limit form (arc sine law for the time in the lead): for
`0 < α < 1`, the probability that a walk of length `2m` spends at most `2αm` segments above the time axis (the
sum of the probabilities `b_{2k,2m}` over `k ≤ αm`) tends to `(2/π) arcsin √α` as `m → ∞`. -/
@[kb "grinsteadsnell2006" "Theorem 12.4, p. 502"]
theorem leadCount_cdf_tendsto (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1),
        ((univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) :=
  arcsine_prob_tendsto (fun m k => (univ.filter fun ω : Fin (2 * m) → Bool => leadCount ω = 2 * k).card)
    (fun m k hk => leadCount_prob m k hk) α h0 h1

/-- Grinstead–Snell Theorem 12.5 (PR-129), limit form: the same arc sine limit for the smallest `j` with
`S_j = S_{2m}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.5, p. 503"]
theorem firstAtEnd_cdf_tendsto (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1),
        ((univ.filter fun ω : Fin (2 * m) → Bool => FirstAtEnd ω (2 * k)).card : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) :=
  arcsine_prob_tendsto (fun m k => (univ.filter fun ω : Fin (2 * m) → Bool => FirstAtEnd ω (2 * k)).card)
    (fun m k hk => firstAtEnd_prob m k hk) α h0 h1

/-- Arc sine law for the last equalization (Exercise 12.1.6): the same limit. -/
theorem lastZero_cdf_tendsto (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ k ∈ range (⌊α * m⌋₊ + 1),
        ((univ.filter fun ω : Fin (2 * m) → Bool => LastZero ω (2 * k)).card : ℝ) / 2 ^ (2 * m))
      Filter.atTop (nhds ((2 / Real.pi) * Real.arcsin (Real.sqrt α))) :=
  arcsine_prob_tendsto (fun m k => (univ.filter fun ω : Fin (2 * m) → Bool => LastZero ω (2 * k)).card)
    (fun m k hk => lastZero_prob m k hk) α h0 h1

end UndergradKB.Probability
