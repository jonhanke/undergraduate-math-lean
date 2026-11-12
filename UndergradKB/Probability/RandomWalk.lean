import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import UndergradKB.Common.Attr

/-! # Probability: random walks (Grinstead–Snell, Chapter 12)

The simple symmetric random walk of length `N` is modelled combinatorially: a path is a function
`ω : Fin N → Bool` (`true` is an up-step `+1`, `false` a down-step `-1`), all `2 ^ N` paths are equally likely, and
the position at time `k` is the partial sum `walkPos ω k`.  Probabilities are counts divided by `2 ^ N`, in `ℚ`.

* PR-124: the random walk as partial sums of a sequence (`randomWalk`).
* PR-125: `u_{2m} = C(2m,m) 2^{-2m}` (Theorem 12.1).
* PR-126: the first-return decomposition and `f_{2m} = u_{2m}/(2m-1)` (Theorems 12.2, 12.3), proved
  combinatorially (decomposition at the first return) plus a convolution identity for `u`.
* PR-128: gambler's ruin (fair and unfair) as a harmonic-function statement. -/

open Finset

namespace UndergradKB.Probability

/-! ## PR-124: random walks as partial sums -/

/-- The random walk `S_n = X_0 + ... + X_{n-1}` attached to a sequence `X` of steps (Definition 12.1 takes the
steps iid; the partial-sum construction itself needs no hypothesis). -/
def randomWalk {Ω E : Type*} [AddCommMonoid E] (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : E :=
  ∑ i ∈ range n, X i ω

/-- Grinstead–Snell Definition 12.1 (PR-124). The walk moves from `S_n` to `S_{n+1} = S_n + X_n`. -/
@[kb "grinsteadsnell2006" "Definition 12.1, p. 479"]
theorem randomWalk_succ {Ω E : Type*} [AddCommMonoid E] (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    randomWalk X (n + 1) ω = randomWalk X n ω + X n ω := by
  simp [randomWalk, sum_range_succ]

theorem randomWalk_zero {Ω E : Type*} [AddCommMonoid E] (X : ℕ → Ω → E) (ω : Ω) :
    randomWalk X 0 ω = 0 := by simp [randomWalk]

/-! ## The combinatorial model -/

/-- The step `+1` for `true` and `-1` for `false`. -/
def step (b : Bool) : ℤ := if b then 1 else -1

/-- Position at time `k` of the path `ω` (steps beyond the length of the path are absent). -/
def walkPos {N : ℕ} (ω : Fin N → Bool) (k : ℕ) : ℤ :=
  ∑ i : Fin N, if (i : ℕ) < k then step (ω i) else 0

theorem walkPos_of_le {N : ℕ} (ω : Fin N → Bool) {k : ℕ} (h : N ≤ k) :
    walkPos ω k = ∑ i : Fin N, step (ω i) := by
  unfold walkPos
  exact sum_congr rfl fun i _ => by simp [i.isLt.trans_le h]

theorem walkPos_zero {N : ℕ} (ω : Fin N → Bool) : walkPos ω 0 = 0 := by simp [walkPos]

/-- Number of up-steps. -/
def ups {N : ℕ} (ω : Fin N → Bool) : ℕ := (univ.filter fun i => ω i = true).card

theorem total_eq {N : ℕ} (ω : Fin N → Bool) : (∑ i : Fin N, step (ω i)) = 2 * (ups ω : ℤ) - N := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun i => ω i = true)
  simp only [card_univ, Fintype.card_fin] at h
  unfold step ups
  rw [sum_ite]
  simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg]
  have h' : (univ.filter fun i => ¬ ω i = true).card = N - (univ.filter fun i => ω i = true).card := by omega
  rw [h']
  have : (univ.filter fun i => ω i = true).card ≤ N := by omega
  rw [Nat.cast_sub this]
  ring

/-- The number of paths of length `N` with exactly `m` up-steps is `C(N,m)`. -/
theorem card_ups (N m : ℕ) :
    (univ.filter fun ω : Fin N → Bool => ups ω = m).card = N.choose m := by
  have hc : N.choose m = (powersetCard m (univ : Finset (Fin N))).card := by
    rw [card_powersetCard]; simp
  rw [hc]
  refine Finset.card_bij' (fun ω _ => univ.filter fun i => ω i = true)
    (fun s _ => fun i => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro ω hω
    have h := (mem_filter.1 hω).2
    exact mem_powersetCard.2 ⟨subset_univ _, h⟩
  · intro s hs
    simp only [mem_powersetCard, subset_univ, true_and] at hs
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    unfold ups
    simp only [decide_eq_true_eq]
    rw [filter_mem_eq_inter, univ_inter]; exact hs
  · intro ω _
    funext i; simp
  · intro s _
    ext i; simp

/-! ## PR-125 -/

/-- Number of paths of length `N` which are at `0` at time `N`. -/
def zeroCount (N : ℕ) : ℕ := (univ.filter fun ω : Fin N → Bool => walkPos ω N = 0).card

/-- `u_N`, the probability that the walk is at the origin at time `N`. -/
def u (N : ℕ) : ℚ := (zeroCount N : ℚ) / 2 ^ N

theorem zeroCount_even (m : ℕ) : zeroCount (2 * m) = (2 * m).choose m := by
  rw [← card_ups (2 * m) m]
  unfold zeroCount
  congr 1
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  rw [walkPos_of_le ω le_rfl, total_eq]
  push_cast
  omega

theorem zeroCount_odd (m : ℕ) : zeroCount (2 * m + 1) = 0 := by
  unfold zeroCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro ω _
  rw [walkPos_of_le ω le_rfl, total_eq]
  push_cast
  omega

/-- Grinstead–Snell Theorem 12.1 (PR-125). The simple symmetric walk is at the origin at time `2m` with
probability `C(2m,m) 2^{-2m}`. -/
@[kb "grinsteadsnell2006" "Theorem 12.1, p. 481"]
theorem u_even (m : ℕ) : u (2 * m) = ((2 * m).choose m : ℚ) / 2 ^ (2 * m) := by
  simp [u, zeroCount_even]

/-- Grinstead–Snell Theorem 12.1 (PR-125), odd times: the walk cannot be at the origin at odd times. -/
@[kb "grinsteadsnell2006" "Theorem 12.1, p. 481"]
theorem u_odd (m : ℕ) : u (2 * m + 1) = 0 := by
  simp [u, zeroCount_odd]

/-! ## PR-126: first returns -/

/-- `FR ω a`: the path `ω` is at `0` at time `a > 0` and at no earlier positive time. -/
def FR {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Prop :=
  0 < a ∧ walkPos ω a = 0 ∧ ∀ j, 0 < j → j < a → walkPos ω j ≠ 0

noncomputable instance {N : ℕ} (ω : Fin N → Bool) (a : ℕ) : Decidable (FR ω a) :=
  Classical.propDecidable _

/-- Number of paths of length `a` whose first return to `0` is at time `a`. -/
noncomputable def firstCount (a : ℕ) : ℕ := (univ.filter fun ω : Fin a → Bool => FR ω a).card

/-- `f_N`, the probability that the first return to the origin is at time `N`. -/
noncomputable def f (N : ℕ) : ℚ := (firstCount N : ℚ) / 2 ^ N

theorem walkPos_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) (k : ℕ) :
    walkPos (Fin.append x y) k = walkPos x k + walkPos y (k - a) := by
  unfold walkPos
  rw [Fin.sum_univ_add]
  congr 1
  · refine sum_congr rfl fun i _ => by simp
  · refine sum_congr rfl fun j _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    by_cases h : a + (j : ℕ) < k
    · simp [h]; omega
    · simp [h]; omega

theorem FR_append {a b : ℕ} (x : Fin a → Bool) (y : Fin b → Bool) :
    (walkPos (Fin.append x y) (a + b) = 0 ∧ FR (Fin.append x y) a) ↔
      (FR x a ∧ walkPos y b = 0) := by
  have h1 : ∀ k, k ≤ a → walkPos (Fin.append x y) k = walkPos x k := by
    intro k hk
    rw [walkPos_append, Nat.sub_eq_zero_of_le hk, walkPos_zero, add_zero]
  have h2 : walkPos (Fin.append x y) (a + b) = walkPos x a + walkPos y b := by
    rw [walkPos_append, walkPos_of_le x (by omega : a ≤ a + b)]
    rw [← walkPos_of_le x (le_refl a)]
    simp
  unfold FR
  rw [h2, h1 a le_rfl]
  constructor
  · rintro ⟨h, ha, h0, hj⟩
    refine ⟨⟨ha, h0, fun j hj0 hja => ?_⟩, ?_⟩
    · rw [← h1 j hja.le]; exact hj j hj0 hja
    · rw [h0] at h; simpa using h
  · rintro ⟨⟨ha, h0, hj⟩, hy⟩
    refine ⟨by rw [h0, hy]; simp, ha, h0, fun j hj0 hja => ?_⟩
    rw [h1 j hja.le]; exact hj j hj0 hja

/-- Paths of length `N` which are at `0` at time `N` and have first return at time `a`. -/
noncomputable def returnSet (N a : ℕ) : Finset (Fin N → Bool) :=
  univ.filter fun ω => walkPos ω N = 0 ∧ FR ω a

theorem card_returnSet (a b N : ℕ) (h : a + b = N) :
    (returnSet N a).card = firstCount a * zeroCount b := by
  subst h
  unfold firstCount zeroCount
  rw [← card_product]
  refine Finset.card_bij' (fun ω _ => (fun i => ω (Fin.castAdd b i), fun j => ω (Fin.natAdd a j)))
    (fun p _ => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro ω hω
    have hω' : ω = Fin.append (fun i => ω (Fin.castAdd b i)) (fun j => ω (Fin.natAdd a j)) := by
      funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
    simp only [returnSet, mem_filter, mem_univ, true_and, mem_product] at hω ⊢
    rw [hω'] at hω
    exact (FR_append _ _).1 hω
  · intro p hp
    simp only [returnSet, mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    exact (FR_append _ _).2 hp
  · intro ω _
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  · intro p _
    ext i <;> simp

/-- Every path at `0` at time `N ≥ 1` has exactly one first-return time `a ∈ [1, N]`. -/
theorem zeroCount_eq_sum (N : ℕ) (hN : 0 < N) :
    zeroCount N = ∑ a ∈ Icc 1 N, (returnSet N a).card := by
  unfold zeroCount
  rw [← card_biUnion]
  · congr 1
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc, returnSet]
    constructor
    · intro h0
      have hex : ∃ k, 0 < k ∧ walkPos ω k = 0 := ⟨N, hN, h0⟩
      classical
      let k := Nat.find hex
      have hk := Nat.find_spec hex
      have hmin : ∀ j, j < k → ¬ (0 < j ∧ walkPos ω j = 0) := fun j hj => Nat.find_min hex hj
      refine ⟨k, ⟨hk.1, Nat.find_min' hex ⟨hN, h0⟩⟩, h0, hk.1, hk.2, fun j hj0 hjk hz => ?_⟩
      exact hmin j hjk ⟨hj0, hz⟩
    · rintro ⟨a, _, h0, _⟩; exact h0
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω h1 h2
    unfold returnSet at h1 h2
    rw [mem_filter] at h1 h2
    simp only [mem_univ, true_and, FR] at h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h2.2.2.2 a h1.2.1 hlt h1.2.2.1
    · exact h1.2.2.2 a' h2.2.1 hlt h2.2.2.1

/-- Counting form of the first-return decomposition: `Z_N = Σ_{a=1}^N F_a Z_{N-a}`. -/
theorem zeroCount_renewal (N : ℕ) (hN : 0 < N) :
    zeroCount N = ∑ a ∈ Icc 1 N, firstCount a * zeroCount (N - a) := by
  rw [zeroCount_eq_sum N hN]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  exact card_returnSet a (N - a) N (by omega)

theorem firstCount_odd (m : ℕ) : firstCount (2 * m + 1) = 0 := by
  unfold firstCount
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ω _ ⟨_, h0, _⟩
  rw [walkPos_of_le ω le_rfl, total_eq] at h0
  push_cast at h0
  omega

theorem u_zero : u 0 = 1 := by
  simp [u, zeroCount, walkPos_zero]

/-- Renewal identity on all indices: `u_N = Σ_{a=1}^N f_a u_{N-a}`. -/
theorem u_renewal_all (N : ℕ) (hN : 0 < N) : u N = ∑ a ∈ Icc 1 N, f a * u (N - a) := by
  unfold u f
  rw [zeroCount_renewal N hN]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  have : (2 : ℚ) ^ N = 2 ^ a * 2 ^ (N - a) := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

theorem f_odd (m : ℕ) : f (2 * m + 1) = 0 := by simp [f, firstCount_odd]

/-- Sums over `Icc 1 (2n)` of a function vanishing at odd arguments reduce to even arguments. -/
theorem sum_Icc_even (g : ℕ → ℚ) (hg : ∀ m, g (2 * m + 1) = 0) (n : ℕ) :
    ∑ a ∈ Icc 1 (2 * n), g a = ∑ k ∈ Icc 1 n, g (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ← e, ih,
      sum_Icc_succ_top (by omega), hg]
    simp

/-- Grinstead–Snell Theorem 12.2 (PR-126). The probability `u_{2n}` of being at the origin at time `2n` is
`Σ_{k=1}^n f_{2k} u_{2n-2k}`, splitting at the first return. -/
@[kb "grinsteadsnell2006" "Theorem 12.2, p. 481"]
theorem u_renewal (n : ℕ) (hn : 1 ≤ n) :
    u (2 * n) = ∑ k ∈ Icc 1 n, f (2 * k) * u (2 * n - 2 * k) := by
  rw [u_renewal_all (2 * n) (by omega)]
  refine sum_Icc_even (fun a => f a * u (2 * n - a)) (fun m => ?_) n
  simp [f_odd]

/-! ### The convolution identity and `f_{2m} = u_{2m}/(2m-1)` -/

/-- `c k = C(2k,k)/4^k`, the value `u_{2k}`. -/
noncomputable def c (k : ℕ) : ℚ := ((2 * k).choose k : ℚ) / 4 ^ k

theorem u_two_mul (k : ℕ) : u (2 * k) = c k := by
  rw [u_even]; simp [c, pow_mul]; norm_num

theorem c_zero : c 0 = 1 := by simp [c]

theorem c_succ (k : ℕ) : (2 * ((k : ℚ) + 1)) * c (k + 1) = (2 * k + 1) * c k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((k : ℚ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℚ) = 2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by
    exact_mod_cast h
  unfold c
  rw [pow_succ]
  field_simp
  linarith

/-- `Σ_{k=0}^n c_k c_{n-k} = 1`. -/
theorem c_conv (n : ℕ) : ∑ k ∈ range (n + 1), c k * c (n - k) = 1 := by
  induction n with
  | zero => simp [c_zero]
  | succ n ih =>
    set A : ℕ → ℚ := fun n => ∑ k ∈ range (n + 1), c k * c (n - k) with hA
    have hA' : ∀ n, A n = ∑ k ∈ range (n + 1), c k * c (n - k) := fun n => rfl
    -- (n+1) A_{n+1} = 2 Σ k c_k c_{n+1-k}
    have h1 : ((n : ℚ) + 1) * A (n + 1) = 2 * ∑ k ∈ range (n + 2), (k : ℚ) * (c k * c (n + 1 - k)) := by
      have hsym : ∑ k ∈ range (n + 2), ((n : ℚ) + 1 - k) * (c k * c (n + 1 - k)) =
          ∑ k ∈ range (n + 2), (k : ℚ) * (c k * c (n + 1 - k)) := by
        rw [← sum_range_reflect]
        refine sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk
        have e : n + 1 + 1 - 1 - k = n + 1 - k := by omega
        rw [e, Nat.sub_sub_self (by omega : k ≤ n + 1)]
        push_cast [Nat.cast_sub (by omega : k ≤ n + 1)]
        ring
      have : ((n : ℚ) + 1) * A (n + 1) = ∑ k ∈ range (n + 2), ((n : ℚ) + 1 - k) * (c k * c (n + 1 - k)) +
          ∑ k ∈ range (n + 2), (k : ℚ) * (c k * c (n + 1 - k)) := by
        rw [hA', mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => by ring
      rw [this, hsym]; ring
    -- 2 Σ k c_k c_{n+1-k} = Σ_{j ≤ n} (2j+1) c_j c_{n-j}
    have h2 : 2 * ∑ k ∈ range (n + 2), (k : ℚ) * (c k * c (n + 1 - k)) =
        ∑ j ∈ range (n + 1), (2 * (j : ℚ) + 1) * (c j * c (n - j)) := by
      rw [sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero]
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      have := c_succ j
      have e : n + 1 - (j + 1) = n - j := by omega
      rw [e]
      push_cast
      linear_combination (c (n - j)) * this
    -- n+1 times A_n via symmetrisation
    have h3 : ∑ j ∈ range (n + 1), (2 * (j : ℚ) + 1) * (c j * c (n - j)) = ((n : ℚ) + 1) * A n := by
      have hsym : ∑ j ∈ range (n + 1), (2 * ((n : ℚ) - j) + 1) * (c j * c (n - j)) =
          ∑ j ∈ range (n + 1), (2 * (j : ℚ) + 1) * (c j * c (n - j)) := by
        rw [← sum_range_reflect]
        refine sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk
        have e : n + 1 - 1 - k = n - k := by omega
        rw [e, Nat.sub_sub_self (by omega : k ≤ n)]
        push_cast [Nat.cast_sub (by omega : k ≤ n)]
        ring
      have : (2 : ℚ) * ∑ j ∈ range (n + 1), (2 * (j : ℚ) + 1) * (c j * c (n - j)) =
          ((n : ℚ) + 1) * 2 * A n := by
        have : ∑ j ∈ range (n + 1), (2 * (j : ℚ) + 1) * (c j * c (n - j)) +
            ∑ j ∈ range (n + 1), (2 * ((n : ℚ) - j) + 1) * (c j * c (n - j)) =
            ∑ j ∈ range (n + 1), (2 * (n : ℚ) + 2) * (c j * c (n - j)) := by
          rw [← sum_add_distrib]; exact sum_congr rfl fun k _ => by ring
        rw [hsym, ← mul_sum] at this
        rw [hA']
        linarith
      linarith
    have hAn : A n = 1 := ih
    have hn1 : ((n : ℚ) + 1) * A (n + 1) = ((n : ℚ) + 1) * 1 := by
      rw [h1, h2, h3, hAn]
    have : A (n + 1) = 1 := by
      have hp : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact mul_left_cancel₀ hp hn1
    exact this

theorem sum_Icc_shift (g : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, g k = ∑ k ∈ range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), sum_range_succ, ih]

/-- `g_m = c_{m-1} - c_m` also satisfies the renewal identity. -/
theorem g_renewal (n : ℕ) (hn : 1 ≤ n) :
    c n = ∑ k ∈ Icc 1 n, (c (k - 1) - c k) * c (n - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [sub_mul, sum_sub_distrib]
  have e1 : ∑ k ∈ Icc 1 (m + 1), c (k - 1) * c (m + 1 - k) = 1 := by
    rw [sum_Icc_shift (fun k => c (k - 1) * c (m + 1 - k)), ← c_conv m]
    refine sum_congr rfl fun k _ => ?_
    simp
  have e2 : ∑ k ∈ Icc 1 (m + 1), c k * c (m + 1 - k) = 1 - c (m + 1) := by
    rw [sum_Icc_shift (fun k => c k * c (m + 1 - k))]
    have := c_conv (m + 1)
    rw [sum_range_succ', c_zero, one_mul] at this
    simp only [Nat.sub_zero] at this
    linarith
  rw [e1, e2]; ring

/-- The first-return probabilities satisfy `f_{2m} = u_{2m-2} - u_{2m}` (uniqueness from the renewal). -/
theorem f_eq (m : ℕ) (hm : 1 ≤ m) : f (2 * m) = c (m - 1) - c m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := u_renewal m hm
    have h2 := g_renewal m hm
    rw [u_two_mul] at h1
    have e : ∀ k, u (2 * m - 2 * k) = c (m - k) := fun k => by
      rw [← Nat.mul_sub, u_two_mul]
    simp only [e] at h1
    rw [h1] at h2
    rw [← Finset.add_sum_erase _ _ (mem_Icc.2 ⟨hm, le_rfl⟩),
      ← Finset.add_sum_erase _ _ (mem_Icc.2 ⟨hm, le_rfl⟩)] at h2
    have h3 : ∑ k ∈ (Icc 1 m).erase m, f (2 * k) * c (m - k) =
        ∑ k ∈ (Icc 1 m).erase m, (c (k - 1) - c k) * c (m - k) := by
      refine sum_congr rfl fun k hk => ?_
      rw [mem_erase, mem_Icc] at hk
      rw [ih k (by omega) hk.2.1]
    rw [h3] at h2
    simp [c_zero] at h2
    linarith

/-- Grinstead–Snell Theorem 12.3 (PR-126). The probability that the first return to the origin is at time `2m`
is `u_{2m}/(2m-1)`. -/
@[kb "grinsteadsnell2006" "Theorem 12.3, p. 482"]
theorem f_even (m : ℕ) (hm : 1 ≤ m) : f (2 * m) = u (2 * m) / (2 * m - 1) := by
  rw [f_eq m hm, u_two_mul]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := c_succ k
  have hp : (2 * ((k + 1 : ℕ) : ℚ) - 1) ≠ 0 := by
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    push_cast; intro h; linarith
  simp only [Nat.add_sub_cancel]
  push_cast at hp ⊢
  field_simp
  linear_combination (-1) * h

/-! ## PR-128: gambler's ruin -/

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), fair game, existence: `h(k) = k/M` is the harmonic
function on `0..M` with `h(0) = 0`, `h(M) = 1`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gamblersRuin_fair_exists (M : ℕ) (hM : 0 < M) :
    (fun k : ℕ => (k : ℝ) / M) 0 = 0 ∧ (fun k : ℕ => (k : ℝ) / M) M = 1 ∧
      ∀ k, 0 < k → k < M →
        (fun k : ℕ => (k : ℝ) / M) k =
          ((fun k : ℕ => (k : ℝ) / M) (k - 1) + (fun k : ℕ => (k : ℝ) / M) (k + 1)) / 2 := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  refine ⟨by simp, by simp [hM'], fun k hk _ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), fair game, uniqueness: a function on `0..M` with `h(0) = 0`,
`h(M) = 1` and `h(k) = (h(k-1) + h(k+1))/2` for `0 < k < M` equals `k/M`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gamblersRuin_fair_unique (M : ℕ) (hM : 0 < M) (h : ℕ → ℝ) (h0 : h 0 = 0) (hM1 : h M = 1)
    (hh : ∀ k, 0 < k → k < M → h k = (h (k - 1) + h (k + 1)) / 2) :
    ∀ k ≤ M, h k = (k : ℝ) / M := by
  have key : ∀ k, k + 1 ≤ M → h k = k * h 1 ∧ h (k + 1) = (k + 1) * h 1 := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨by push_cast; exact b, ?_⟩
      have := hh (k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      push_cast
      rw [a, b] at this
      linarith
  have hM' : (M : ℝ) ≠ 0 := by positivity
  have hd : h 1 = 1 / M := by
    have := (key (M - 1) (by omega)).2
    rw [Nat.sub_add_cancel (by omega), hM1] at this
    have e : ((M - 1 : ℕ) : ℝ) + 1 = M := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e] at this
    field_simp
    linarith
  intro k hk
  rcases Nat.eq_zero_or_pos M with h' | h'
  · omega
  by_cases hkM : k = M
  · subst hkM; rw [hM1]; field_simp
  · have := (key k (by omega)).1
    rw [this, hd]; field_simp

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), unfair game with win probability `p`, loss probability
`q = 1 - p` and `r = q/p ≠ 1`, existence: `h(k) = (r^k - 1)/(r^M - 1)` is the probability of reaching `M` before
`0` from `k`; it satisfies `h(k) = p h(k+1) + q h(k-1)` with `h(0) = 0`, `h(M) = 1`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gamblersRuin_unfair_exists (M : ℕ) (hM : 0 < M) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) (hr : q / p ≠ 1) :
    (fun k : ℕ => ((q / p) ^ k - 1) / ((q / p) ^ M - 1)) 0 = 0 ∧
      (fun k : ℕ => ((q / p) ^ k - 1) / ((q / p) ^ M - 1)) M = 1 ∧
      ∀ k, 0 < k → k < M →
        (fun k : ℕ => ((q / p) ^ k - 1) / ((q / p) ^ M - 1)) k =
          p * (fun k : ℕ => ((q / p) ^ k - 1) / ((q / p) ^ M - 1)) (k + 1) +
            q * (fun k : ℕ => ((q / p) ^ k - 1) / ((q / p) ^ M - 1)) (k - 1) := by
  have hr0 : 0 ≤ q / p := by positivity
  have hrM : (q / p) ^ M - 1 ≠ 0 := by
    intro h
    exact hr ((pow_eq_one_iff_of_nonneg hr0 hM.ne').1 (sub_eq_zero.1 h))
  refine ⟨by simp, by simp [hrM], fun k hk _ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hqp : q = p * (q / p) := by field_simp
  generalize q / p = r at *
  have hp1 : p * (1 + r) = 1 := by
    have := hpq
    rw [hqp] at this
    linarith
  have key : r ^ (j + 1) - 1 = p * (r ^ (j + 1 + 1) - 1) + q * (r ^ j - 1) := by
    rw [hqp]
    linear_combination (1 - r ^ (j + 1)) * hp1
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, ← key]

/-- Grinstead–Snell §12.2 gambler's ruin (PR-128), unfair game, uniqueness: any `h` on `0..M` with `h(0) = 0`,
`h(M) = 1` and `h(k) = p h(k+1) + q h(k-1)` for `0 < k < M` equals `(r^k - 1)/(r^M - 1)`. -/
@[kb "grinsteadsnell2006" "§12.2 gambler's ruin, p. 494"]
theorem gamblersRuin_unfair_unique (M : ℕ) (hM : 0 < M) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) (hr : q / p ≠ 1) (h : ℕ → ℝ) (h0 : h 0 = 0) (hM1 : h M = 1)
    (hh : ∀ k, 0 < k → k < M → h k = p * h (k + 1) + q * h (k - 1)) :
    ∀ k ≤ M, h k = ((q / p) ^ k - 1) / ((q / p) ^ M - 1) := by
  set r := q / p with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hrM : r ^ M - 1 ≠ 0 := by
    intro h
    exact hr ((pow_eq_one_iff_of_nonneg hr0 hM.ne').1 (sub_eq_zero.1 h))
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.2 hr
  have hqp : q = p * r := by rw [hrdef]; field_simp
  have key : ∀ k, k + 1 ≤ M →
      h k = h 1 * (r ^ k - 1) / (r - 1) ∧ h (k + 1) = h 1 * (r ^ (k + 1) - 1) / (r - 1) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]; field_simp
    | succ k ih =>
      intro hk
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨b, ?_⟩
      have := hh (k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at this
      have hp0 : p ≠ 0 := hp.ne'
      have h2 : h (k + 1 + 1) = h (k + 1) + r * (h (k + 1) - h k) := by
        have : p * (h (k + 1 + 1) - h (k + 1) - r * (h (k + 1) - h k)) = 0 := by
          linear_combination (-1) * this + (-(h (k + 1))) * hpq + (h (k + 1) - h k) * hqp
        have := (mul_eq_zero.1 this).resolve_left hp0
        linarith
      rw [h2, a, b]
      field_simp
      ring
  have hd : h 1 = (r - 1) / (r ^ M - 1) := by
    have := (key (M - 1) (by omega)).2
    rw [Nat.sub_add_cancel (by omega), hM1] at this
    field_simp
    field_simp at this
    linarith
  intro k hk
  by_cases hkM : k = M
  · subst hkM; rw [hM1]; field_simp
  · have := (key k (by omega)).1
    rw [this, hd]; field_simp

end UndergradKB.Probability
