import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk

/-!
# Polya's theorem: first returns and the renewal relation for a walk with finitely many steps

A walk on an additive group `G` whose steps are chosen uniformly from a finite step type `S` (with step
map `st : S → G`) is modelled by its paths `Fin N → S`.  This file proves, in this generality, the first
return decomposition `u_N = Σ_{a=1}^N f_a u_{N-a}` (Grinstead–Snell, equation (12.2)) together with the
trichotomy of Example 12.2: the probability of an eventual return is `1 - 1/Σ u` when `Σ u` converges and
`1` when it diverges.
-/

set_option linter.unusedSectionVars false

open Finset Filter
open scoped Topology Classical

namespace UndergradKB.Probability.Polya

section General

variable {S G : Type*} [Fintype S] [AddCommGroup G] (st : S → G)

/-- Position at time `k` of the path `ω` (steps beyond the length of the path are absent). -/
def pos {N : ℕ} (ω : Fin N → S) (k : ℕ) : G :=
  ∑ i : Fin N, if (i : ℕ) < k then st (ω i) else 0

theorem pos_of_le {N : ℕ} (ω : Fin N → S) {k : ℕ} (h : N ≤ k) :
    pos st ω k = ∑ i : Fin N, st (ω i) := by
  unfold pos
  exact sum_congr rfl fun i _ => by simp [i.isLt.trans_le h]

theorem pos_zero {N : ℕ} (ω : Fin N → S) : pos st ω 0 = 0 := by simp [pos]

theorem pos_append {a b : ℕ} (x : Fin a → S) (y : Fin b → S) (k : ℕ) :
    pos st (Fin.append x y) k = pos st x k + pos st y (k - a) := by
  unfold pos
  rw [Fin.sum_univ_add]
  congr 1
  · refine sum_congr rfl fun i _ => by simp
  · refine sum_congr rfl fun j _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    by_cases h : a + (j : ℕ) < k
    · simp [h]; omega
    · simp [h]; omega

/-- Number of paths of length `N` which are at `0` at time `N`. -/
noncomputable def zeroCount (N : ℕ) : ℕ := (univ.filter fun ω : Fin N → S => pos st ω N = 0).card

/-- `u_N`, the probability that the walk is at the origin at time `N`. -/
noncomputable def u (N : ℕ) : ℝ := (zeroCount st N : ℝ) / (Fintype.card S : ℝ) ^ N

/-- `FR ω a`: the path `ω` is at `0` at time `a > 0` and at no earlier positive time. -/
def FR {N : ℕ} (ω : Fin N → S) (a : ℕ) : Prop :=
  0 < a ∧ pos st ω a = 0 ∧ ∀ j, 0 < j → j < a → pos st ω j ≠ 0

/-- Number of paths of length `a` whose first return to `0` is at time `a`. -/
noncomputable def firstCount (a : ℕ) : ℕ := (univ.filter fun ω : Fin a → S => FR st ω a).card

/-- `f_N`, the probability that the first return to the origin is at time `N`. -/
noncomputable def f (N : ℕ) : ℝ := (firstCount st N : ℝ) / (Fintype.card S : ℝ) ^ N

theorem FR_append {a b : ℕ} (x : Fin a → S) (y : Fin b → S) :
    (pos st (Fin.append x y) (a + b) = 0 ∧ FR st (Fin.append x y) a) ↔
      (FR st x a ∧ pos st y b = 0) := by
  have h1 : ∀ k, k ≤ a → pos st (Fin.append x y) k = pos st x k := by
    intro k hk
    rw [pos_append, Nat.sub_eq_zero_of_le hk, pos_zero, add_zero]
  have h2 : pos st (Fin.append x y) (a + b) = pos st x a + pos st y b := by
    rw [pos_append, pos_of_le st x (by omega : a ≤ a + b)]
    rw [← pos_of_le st x (le_refl a)]
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
noncomputable def returnSet (N a : ℕ) : Finset (Fin N → S) :=
  univ.filter fun ω => pos st ω N = 0 ∧ FR st ω a

theorem card_returnSet (a b N : ℕ) (h : a + b = N) :
    (returnSet st N a).card = firstCount st a * zeroCount st b := by
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
    exact (FR_append st _ _).1 hω
  · intro p hp
    simp only [returnSet, mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    exact (FR_append st _ _).2 hp
  · intro ω _
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  · intro p _
    ext i <;> simp

/-- Every path at `0` at time `N ≥ 1` has exactly one first-return time `a ∈ [1, N]`. -/
theorem zeroCount_eq_sum (N : ℕ) (hN : 0 < N) :
    zeroCount st N = ∑ a ∈ Icc 1 N, (returnSet st N a).card := by
  unfold zeroCount
  rw [← card_biUnion]
  · congr 1
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc, returnSet]
    constructor
    · intro h0
      have hex : ∃ k, 0 < k ∧ pos st ω k = 0 := ⟨N, hN, h0⟩
      let k := Nat.find hex
      have hk := Nat.find_spec hex
      have hmin : ∀ j, j < k → ¬ (0 < j ∧ pos st ω j = 0) := fun j hj => Nat.find_min hex hj
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
    zeroCount st N = ∑ a ∈ Icc 1 N, firstCount st a * zeroCount st (N - a) := by
  rw [zeroCount_eq_sum st N hN]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  exact card_returnSet st a (N - a) N (by omega)

theorem u_zero : u st 0 = 1 := by
  simp [u, zeroCount, pos_zero]

variable [Nonempty S]

/-- Grinstead–Snell Example 12.2 (PR-127). Renewal identity (equation (12.2) of the book) for a walk with
finitely many equally likely steps: `u_N = Σ_{a=1}^N f_a u_{N-a}` for `N ≥ 1`, splitting at the first
return. -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem u_renewal (N : ℕ) (hN : 0 < N) : u st N = ∑ a ∈ Icc 1 N, f st a * u st (N - a) := by
  unfold u f
  rw [zeroCount_renewal st N hN]
  push_cast
  rw [sum_div]
  have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  have : (Fintype.card S : ℝ) ^ N = (Fintype.card S : ℝ) ^ a * (Fintype.card S : ℝ) ^ (N - a) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

theorem u_nonneg (N : ℕ) : 0 ≤ u st N := by unfold u; positivity

theorem f_nonneg (N : ℕ) : 0 ≤ f st N := by unfold f; positivity

theorem firstCount_zero : firstCount st 0 = 0 := by
  unfold firstCount
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ω _ ⟨h, _⟩
  omega

theorem f_zero : f st 0 = 0 := by simp [f, firstCount_zero]

theorem FR_append_left {a b : ℕ} (x : Fin a → S) (y : Fin b → S) :
    FR st (Fin.append x y) a ↔ FR st x a := by
  have h1 : ∀ k, k ≤ a → pos st (Fin.append x y) k = pos st x k := by
    intro k hk
    rw [pos_append, Nat.sub_eq_zero_of_le hk, pos_zero, add_zero]
  unfold FR
  rw [h1 a le_rfl]
  constructor
  · rintro ⟨ha, h0, hj⟩
    exact ⟨ha, h0, fun j hj0 hja => by rw [← h1 j hja.le]; exact hj j hj0 hja⟩
  · rintro ⟨ha, h0, hj⟩
    exact ⟨ha, h0, fun j hj0 hja => by rw [h1 j hja.le]; exact hj j hj0 hja⟩

theorem card_firstSet (a N : ℕ) (h : a ≤ N) :
    (univ.filter fun ω : Fin N → S => FR st ω a).card =
      firstCount st a * Fintype.card S ^ (N - a) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  unfold firstCount
  have : Fintype.card S ^ b = (univ : Finset (Fin b → S)).card := by simp
  rw [this, ← card_product]
  refine Finset.card_bij' (fun ω _ => (fun i => ω (Fin.castAdd b i), fun j => ω (Fin.natAdd a j)))
    (fun p _ => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro ω hω
    have hω' : ω = Fin.append (fun i => ω (Fin.castAdd b i)) (fun j => ω (Fin.natAdd a j)) := by
      funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
    simp only [mem_filter, mem_univ, true_and, mem_product, and_true] at hω ⊢
    rw [hω'] at hω
    exact (FR_append_left st _ _).1 hω
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_product, and_true] at hp ⊢
    exact (FR_append_left st _ _).2 hp
  · intro ω _
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  · intro p _
    ext i <;> simp

/-- Partial sums `F_N = Σ_{a=1}^N f_a`: the probability of a return to `0` by time `N`. -/
noncomputable def Fsum (N : ℕ) : ℝ := ∑ a ∈ Icc 1 N, f st a

/-- Partial sums `U_N = Σ_{n=0}^N u_n`: the expected number of visits to `0` up to time `N`. -/
noncomputable def Usum (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), u st n

theorem Fsum_le_one (N : ℕ) : Fsum st N ≤ 1 := by
  have hc : (0 : ℝ) < (Fintype.card S : ℝ) ^ N := by
    have : 0 < Fintype.card S := Fintype.card_pos
    positivity
  have hcard : ∑ a ∈ Icc 1 N, firstCount st a * Fintype.card S ^ (N - a) ≤
      Fintype.card S ^ N := by
    calc ∑ a ∈ Icc 1 N, firstCount st a * Fintype.card S ^ (N - a)
        = ∑ a ∈ Icc 1 N, (univ.filter fun ω : Fin N → S => FR st ω a).card := by
          refine sum_congr rfl fun a ha => ?_
          rw [card_firstSet st a N (mem_Icc.1 ha).2]
      _ = (Finset.biUnion (Icc 1 N) fun a => univ.filter fun ω : Fin N → S => FR st ω a).card := by
          rw [card_biUnion]
          intro a _ a' _ hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro ω h1 h2
          rw [mem_filter] at h1 h2
          simp only [mem_univ, true_and, FR] at h1 h2
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact h2.2.2 a h1.1 hlt h1.2.1
          · exact h1.2.2 a' h2.1 hlt h2.2.1
      _ ≤ (univ : Finset (Fin N → S)).card := card_le_card (subset_univ _)
      _ = Fintype.card S ^ N := by simp
  have hcast : ∑ a ∈ Icc 1 N, (firstCount st a : ℝ) * (Fintype.card S : ℝ) ^ (N - a) ≤
      (Fintype.card S : ℝ) ^ N := by exact_mod_cast hcard
  have hc' : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have key : Fsum st N = (∑ a ∈ Icc 1 N, (firstCount st a : ℝ) * (Fintype.card S : ℝ) ^ (N - a)) /
        (Fintype.card S : ℝ) ^ N := by
    unfold Fsum f
    rw [sum_div]
    refine sum_congr rfl fun a ha => ?_
    have ha' := (mem_Icc.1 ha).2
    have : (Fintype.card S : ℝ) ^ N =
        (Fintype.card S : ℝ) ^ a * (Fintype.card S : ℝ) ^ (N - a) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp
  rw [key, div_le_one hc]
  exact hcast

theorem Usum_succ (N : ℕ) : Usum st (N + 1) = Usum st N + u st (N + 1) := by
  simp [Usum, sum_range_succ]

theorem Usum_zero : Usum st 0 = 1 := by simp [Usum, u_zero]

theorem Usum_mono : Monotone (Usum st) := by
  refine monotone_nat_of_le_succ fun N => ?_
  rw [Usum_succ]
  linarith [u_nonneg st (N + 1)]

theorem Usum_ge_one (N : ℕ) : 1 ≤ Usum st N := by
  have := Usum_mono st (Nat.zero_le N)
  rwa [Usum_zero] at this

theorem Usum_eq (N : ℕ) : Usum st N = 1 + ∑ a ∈ Icc 1 N, f st a * Usum st (N - a) := by
  induction N with
  | zero => simp [Usum_zero]
  | succ N ih =>
    rw [Usum_succ, ih, u_renewal st (N + 1) (by omega), sum_Icc_succ_top (by omega),
      sum_Icc_succ_top (by omega)]
    have : ∀ a ∈ Icc 1 N, f st a * Usum st (N + 1 - a) =
        f st a * Usum st (N - a) + f st a * u st (N + 1 - a) := by
      intro a ha
      have : N + 1 - a = (N - a) + 1 := by have := (mem_Icc.1 ha).2; omega
      rw [this, Usum_succ, ← mul_add]
    rw [sum_congr rfl this, sum_add_distrib]
    simp [Usum_zero, u_zero]
    ring

theorem Usum_sub_one_le (N : ℕ) : Usum st N - 1 ≤ Fsum st N * Usum st N := by
  have h := Usum_eq st N
  unfold Fsum
  rw [sum_mul]
  have : ∑ a ∈ Icc 1 N, f st a * Usum st (N - a) ≤ ∑ a ∈ Icc 1 N, f st a * Usum st N :=
    sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Usum_mono st (Nat.sub_le N a)) (f_nonneg st a)
  linarith

theorem one_sub_inv_le_Fsum (N : ℕ) : 1 - (Usum st N)⁻¹ ≤ Fsum st N := by
  have hp : 0 < Usum st N := by linarith [Usum_ge_one st N]
  have : 1 - (Usum st N)⁻¹ = (Usum st N - 1) / Usum st N := by field_simp
  rw [this, div_le_iff₀ hp]
  exact Usum_sub_one_le st N

theorem one_add_Fsum_mul_le {M N : ℕ} (h : M ≤ N) :
    1 + Fsum st M * Usum st (N - M) ≤ Usum st N := by
  rw [Usum_eq st N]
  have h1 : Fsum st M * Usum st (N - M) ≤ ∑ a ∈ Icc 1 M, f st a * Usum st (N - a) := by
    unfold Fsum
    rw [sum_mul]
    exact sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
      (Usum_mono st (by have := (mem_Icc.1 ha).2; omega)) (f_nonneg st a)
  have h2 : ∑ a ∈ Icc 1 M, f st a * Usum st (N - a) ≤
      ∑ a ∈ Icc 1 N, f st a * Usum st (N - a) := by
    refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h) fun a _ _ => ?_
    exact mul_nonneg (f_nonneg st a) (by linarith [Usum_ge_one st (N - a)])
  linarith

theorem sum_range_f (N : ℕ) : ∑ a ∈ range (N + 1), f st a = Fsum st N := by
  induction N with
  | zero => simp [f_zero, Fsum]
  | succ N ih => rw [sum_range_succ, ih]; unfold Fsum; rw [sum_Icc_succ_top (by omega)]

theorem summable_f : Summable (f st) :=
  summable_of_sum_range_le (c := 1) (f_nonneg st) fun n => by
    cases n with
    | zero => simp
    | succ n => rw [sum_range_f]; exact Fsum_le_one st n

theorem tsum_f_le_one : ∑' a, f st a ≤ 1 :=
  (summable_f st).tsum_le_of_sum_range_le fun n => by
    cases n with
    | zero => simp
    | succ n => rw [sum_range_f]; exact Fsum_le_one st n

theorem tendsto_Fsum : Tendsto (Fsum st) atTop (𝓝 (∑' a, f st a)) := by
  have := (summable_f st).hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat 1] at this
  simpa [sum_range_f] using this

/-- Grinstead–Snell Example 12.2 (PR-127), convergent case. If `Σ u_n = U < ∞` then the probability of an
eventual return, `Σ f_a`, equals `(U - 1)/U = 1 - 1/U`. -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem hasSum_f_of_hasSum_u {U : ℝ} (hU : HasSum (u st) U) : HasSum (f st) (1 - U⁻¹) := by
  have hUt : Tendsto (Usum st) atTop (𝓝 U) := by
    have := hU.tendsto_sum_nat
    rw [← tendsto_add_atTop_iff_nat 1] at this
    exact this
  have hU1 : 1 ≤ U := ge_of_tendsto' hUt (Usum_ge_one st)
  have hUpos : 0 < U := by linarith
  have hlow : 1 - U⁻¹ ≤ ∑' a, f st a := by
    have h1 : Tendsto (fun N => 1 - (Usum st N)⁻¹) atTop (𝓝 (1 - U⁻¹)) :=
      tendsto_const_nhds.sub (hUt.inv₀ hUpos.ne')
    exact le_of_tendsto_of_tendsto h1 (tendsto_Fsum st)
      (Eventually.of_forall fun N => one_sub_inv_le_Fsum st N)
  have hup : ∑' a, f st a ≤ 1 - U⁻¹ := by
    refine (summable_f st).tsum_le_of_sum_range_le fun n => ?_
    cases n with
    | zero => simp; exact inv_le_one_of_one_le₀ hU1
    | succ M =>
      rw [sum_range_f]
      have h1 : Tendsto (fun N => 1 + Fsum st M * Usum st (N - M)) atTop
          (𝓝 (1 + Fsum st M * U)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul
          (hUt.comp (tendsto_sub_atTop_nat M)))
      have h2 : 1 + Fsum st M * U ≤ U :=
        le_of_tendsto_of_tendsto h1 hUt
          ((eventually_ge_atTop M).mono fun N hN => one_add_Fsum_mul_le st hN)
      rw [le_sub_comm, inv_eq_one_div, div_le_iff₀ hUpos]
      nlinarith
  have heq : ∑' a, f st a = 1 - U⁻¹ := le_antisymm hup hlow
  rw [← heq]
  exact (summable_f st).hasSum

/-- Grinstead–Snell Example 12.2 (PR-127), divergent case. If `Σ u_n` diverges then a return to the
origin is certain. -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem hasSum_f_of_not_summable_u (hU : ¬ Summable (u st)) : HasSum (f st) 1 := by
  have hUt : Tendsto (Usum st) atTop atTop := by
    have := (not_summable_iff_tendsto_nat_atTop_of_nonneg (u_nonneg st)).1 hU
    rw [← tendsto_add_atTop_iff_nat 1] at this
    exact this
  have hlow : 1 ≤ ∑' a, f st a := by
    have h1 : Tendsto (fun N => 1 - (Usum st N)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hUt)
    exact le_of_tendsto_of_tendsto h1 (tendsto_Fsum st)
      (Eventually.of_forall fun N => one_sub_inv_le_Fsum st N)
  have heq : ∑' a, f st a = 1 := le_antisymm (tsum_f_le_one st) hlow
  rw [← heq]
  exact (summable_f st).hasSum

/-- Grinstead–Snell Example 12.2 (PR-127). The walk returns to the origin with probability one if and
only if `Σ u_n` diverges. -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem tsum_f_eq_one_iff : ∑' a, f st a = 1 ↔ ¬ Summable (u st) := by
  constructor
  · intro h hs
    have h1 := (hasSum_f_of_hasSum_u st hs.hasSum).tsum_eq
    have hU1 : 1 ≤ ∑' n, u st n := by
      have := hs.le_tsum 0 (fun j _ => u_nonneg st j)
      rwa [u_zero] at this
    have : 0 < (∑' n, u st n)⁻¹ := inv_pos.2 (by linarith)
    linarith
  · intro h
    exact (hasSum_f_of_not_summable_u st h).tsum_eq

end General

/-! ### Invariance of the return counts under a change of coordinates -/

section Invariance

variable {S S' G H : Type*} [Fintype S] [Fintype S'] [AddCommGroup G] [AddCommGroup H]

theorem pos_map (e : S ≃ S') (φ : G →+ H) (st : S → G) (st' : S' → H)
    (h : ∀ s, st' (e s) = φ (st s)) {N : ℕ} (ω : Fin N → S) (k : ℕ) :
    pos st' (fun i => e (ω i)) k = φ (pos st ω k) := by
  unfold pos
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs
  · exact h _
  · simp

theorem zeroCount_congr (e : S ≃ S') (φ : G →+ H) (hφ : Function.Injective φ) (st : S → G)
    (st' : S' → H) (h : ∀ s, st' (e s) = φ (st s)) (N : ℕ) :
    zeroCount st N = zeroCount st' N := by
  unfold zeroCount
  refine Finset.card_bij' (fun ω _ => fun i => e (ω i)) (fun ω _ => fun i => e.symm (ω i))
    ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    rw [pos_map e φ st st' h, hω, map_zero]
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    apply hφ
    rw [← pos_map e φ st st' h]
    simpa using hω
  · intro ω _; funext i; simp
  · intro ω _; funext i; simp

end Invariance

/-! ### The simple symmetric walk on `ℤ^d` -/

/-- The step of the simple symmetric walk on `ℤ^d`: `±e_i`, indexed by `(i, sign)`. -/
def simpleStep (d : ℕ) : Fin d × Bool → (Fin d → ℤ) :=
  fun p => Pi.single p.1 (if p.2 then 1 else -1)

/-- Rotation by `45°` and scaling: `(x, y) ↦ (x + y, x - y)`. -/
def rot : (Fin 2 → ℤ) →+ ℤ × ℤ :=
  AddMonoidHom.mk' (fun x => (x 0 + x 1, x 0 - x 1)) (by
    intro x y; ext <;> simp <;> ring)

theorem rot_injective : Function.Injective rot := by
  intro x y h
  simp only [rot, AddMonoidHom.mk'_apply, Prod.mk.injEq] at h
  funext i
  fin_cases i <;> simp <;> omega

/-- The two-dimensional steps matched with pairs of one-dimensional steps. -/
def stepEquiv : Fin 2 × Bool ≃ Bool × Bool where
  toFun p := (p.2, if p.1 = 0 then p.2 else !p.2)
  invFun q := (if q.1 = q.2 then 0 else 1, q.1)
  left_inv := by decide
  right_inv := by decide

/-- Pairs of independent one-dimensional steps. -/
def pairStep : Bool × Bool → ℤ × ℤ := fun q => (UndergradKB.Probability.step q.1, UndergradKB.Probability.step q.2)

theorem pairStep_stepEquiv (s : Fin 2 × Bool) : pairStep (stepEquiv s) = rot (simpleStep 2 s) := by
  rcases s with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp [pairStep, stepEquiv, rot, simpleStep, UndergradKB.Probability.step]

theorem zeroCount_pair (N : ℕ) :
    zeroCount pairStep N = UndergradKB.Probability.zeroCount N ^ 2 := by
  unfold zeroCount UndergradKB.Probability.zeroCount
  rw [sq, ← card_product]
  refine Finset.card_bij' (fun ω _ => (fun i => (ω i).1, fun i => (ω i).2))
    (fun p _ i => (p.1 i, p.2 i)) ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and, mem_product] at hω ⊢
    have h1 := congrArg Prod.fst hω
    have h2 := congrArg Prod.snd hω
    simp only [pos, pairStep, Prod.fst_sum, Prod.snd_sum, apply_ite Prod.fst, apply_ite Prod.snd,
      Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact ⟨h1, h2⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, mem_product] at hp ⊢
    ext
    · simp only [pos, pairStep, Prod.fst_sum, apply_ite Prod.fst, Prod.fst_zero]
      exact hp.1
    · simp only [pos, pairStep, Prod.snd_sum, apply_ite Prod.snd, Prod.snd_zero]
      exact hp.2
  · intro ω _; rfl
  · intro p _; rfl

theorem zeroCount_simple_two (N : ℕ) :
    zeroCount (simpleStep 2) N = UndergradKB.Probability.zeroCount N ^ 2 := by
  rw [zeroCount_congr stepEquiv rot rot_injective (simpleStep 2) pairStep pairStep_stepEquiv N,
    zeroCount_pair]

/-- The probability that the planar walk is at the origin at time `N` is the square of the
corresponding one-dimensional probability. -/
theorem u_simple_two (N : ℕ) :
    u (simpleStep 2) N = ((UndergradKB.Probability.u N : ℚ) : ℝ) ^ 2 := by
  unfold u UndergradKB.Probability.u
  rw [zeroCount_simple_two]
  have hc : Fintype.card (Fin 2 × Bool) = 4 := by simp
  rw [hc]
  push_cast
  have : (4 : ℝ) ^ N = (2 ^ N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this, div_pow]

/-- Grinstead–Snell Example 12.2 (PR-127), `m = 2`, counting step. The probability that the planar
simple symmetric walk is at the origin at time `2n` is `(C(2n,n)/4^n)^2` (Exercise 12 of the book). -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem u_simple_two_even (n : ℕ) :
    u (simpleStep 2) (2 * n) = (((2 * n).choose n : ℝ) / 4 ^ n) ^ 2 := by
  rw [u_simple_two, UndergradKB.Probability.u_even]
  push_cast
  rw [pow_mul]
  norm_num

theorem u_simple_two_odd (n : ℕ) : u (simpleStep 2) (2 * n + 1) = 0 := by
  rw [u_simple_two, UndergradKB.Probability.u_odd]
  simp

/-- The lower bound `c_k^2 ≥ 1/(4k)` for the central binomial probabilities. -/
theorem c_sq_ge (k : ℕ) (hk : 1 ≤ k) :
    1 / (4 * (k : ℝ)) ≤ ((UndergradKB.Probability.c k : ℚ) : ℝ) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base =>
    have : UndergradKB.Probability.c 1 = 1 / 2 := by
      unfold UndergradKB.Probability.c; norm_num [Nat.choose]
    rw [this]; norm_num
  | succ k hk ih =>
    have h := UndergradKB.Probability.c_succ k
    have h' : (2 * ((k : ℝ) + 1)) * ((UndergradKB.Probability.c (k + 1) : ℚ) : ℝ) =
        (2 * k + 1) * ((UndergradKB.Probability.c k : ℚ) : ℝ) := by exact_mod_cast h
    have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpos : 0 < 2 * ((k : ℝ) + 1) := by positivity
    have hsq : ((UndergradKB.Probability.c (k + 1) : ℚ) : ℝ) ^ 2 =
        ((2 * k + 1) * ((UndergradKB.Probability.c k : ℚ) : ℝ)) ^ 2 / (2 * ((k : ℝ) + 1)) ^ 2 := by
      rw [← h', mul_pow, mul_div_cancel_left₀ _ (by positivity)]
    rw [hsq]
    push_cast
    have hk' : (0 : ℝ) < k := by linarith
    have A : (2 * (k : ℝ) + 1) ^ 2 * (1 / (4 * (k : ℝ))) ≤
        ((2 * (k : ℝ) + 1) * ((UndergradKB.Probability.c k : ℚ) : ℝ)) ^ 2 := by
      rw [mul_pow]; gcongr
    have hdiff : ((2 * (k : ℝ) + 1) ^ 2 * (1 / (4 * (k : ℝ)))) / (2 * ((k : ℝ) + 1)) ^ 2 -
        1 / (4 * ((k : ℝ) + 1)) = 1 / (16 * (k : ℝ) * ((k : ℝ) + 1) ^ 2) := by
      field_simp; ring
    have hpos : 0 < 1 / (16 * (k : ℝ) * ((k : ℝ) + 1) ^ 2) := by positivity
    have hA' := div_le_div_of_nonneg_right A (by positivity : (0 : ℝ) ≤ (2 * ((k : ℝ) + 1)) ^ 2)
    linarith

theorem not_summable_u_simple_two : ¬ Summable (u (simpleStep 2)) := by
  intro h
  have h2 : Summable fun n : ℕ => u (simpleStep 2) (2 * n) :=
    h.comp_injective fun a b hab => by simpa using hab
  simp_rw [u_simple_two, UndergradKB.Probability.u_two_mul] at h2
  have h3 : Summable fun n : ℕ => 1 / (4 * (n : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using sq_nonneg _
        · exact c_sq_ge n hn) h2
  have h4 : Summable fun n : ℕ => ((n : ℝ))⁻¹ := by
    have := h3.mul_left 4
    refine this.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by positivity
      field_simp
  exact Real.not_summable_natCast_inv h4

/-- Grinstead–Snell Example 12.2 (PR-127), `m = 2`. In the plane the simple symmetric walk returns to
the origin with probability one: the first-return probabilities sum to `1`. -/
@[kb "grinsteadsnell2006" "Example 12.2, p. 484"]
theorem hasSum_firstReturn_two : HasSum (f (simpleStep 2)) 1 :=
  hasSum_f_of_not_summable_u _ not_summable_u_simple_two

end UndergradKB.Probability.Polya
