import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.Matrix.Basis
import UndergradKB.Common.Attr

/-! # Magic squares (Hefferon, Topic: Magic Squares)

An `n × n` real matrix is *magic* if all row sums, all column sums and both diagonal sums are equal; the
common value is its magic number.  The magic squares form a subspace of the `n × n` matrices, and so do
those with magic number `0`.  For `n ≥ 3` the subspace of magic squares with magic number `0` has dimension
`n² - 2n - 1` and all magic squares form a subspace of dimension `n² - 2n`.  (Hefferon's text has
`n² - n` for the latter at one place; its own computation gives `n² - 2n`.) -/

open Module Matrix

namespace UndergradKB.LinearAlgebra
namespace MagicSquares

/-- The `2n + 2` places where a sum is constrained: `n` rows, `n` columns, and the two diagonals
(`true` is the main diagonal, `false` the anti-diagonal). -/
abbrev Slot (n : ℕ) := Fin n ⊕ Fin n ⊕ Bool

/-- All the row, column and diagonal sums of a matrix, as a vector indexed by `Slot n`. -/
def sums (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Slot n → ℝ) where
  toFun M := Sum.elim (fun i => ∑ j, M i j) (Sum.elim (fun j => ∑ i, M i j)
      (fun b => if b then ∑ i, M i i else ∑ i, M i (Fin.rev i)))
  map_add' M N := by
    ext (i | j | b)
    · simp [Finset.sum_add_distrib]
    · simp [Finset.sum_add_distrib]
    · cases b <;> simp [Finset.sum_add_distrib]
  map_smul' c M := by
    ext (i | j | b)
    · simp [Finset.mul_sum]
    · simp [Finset.mul_sum]
    · cases b <;> simp [Finset.mul_sum]

/-- The magic squares: matrices all of whose row, column and diagonal sums are one common number. -/
def magicSquares (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | ∃ s : ℝ, sums n M = fun _ => s}
  zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
  add_mem' := by
    rintro M N ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, by rw [map_add, hs, ht]; rfl⟩
  smul_mem' := by
    rintro c M ⟨s, hs⟩
    exact ⟨c * s, by rw [map_smul, hs]; rfl⟩

/-- The magic squares with magic number `0`. -/
def zeroMagicSquares (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := LinearMap.ker (sums n)

/-- A matrix is magic with magic number `s` iff all its row sums, column sums and the two diagonal sums
equal `s`; and the magic squares form a subspace (`magicSquares n` is a `Submodule`). -/
@[kb "hefferon2020" "Topic-MagicSquares.1, p. 319"]
theorem mem_magicSquares_iff (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ magicSquares n ↔ ∃ s : ℝ, (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) ∧
      ∑ i, M i i = s ∧ ∑ i, M i (Fin.rev i) = s := by
  change (∃ s : ℝ, sums n M = fun _ => s) ↔ _
  refine exists_congr fun s => ?_
  simp only [funext_iff, Sum.forall, Bool.forall_bool, sums, LinearMap.coe_mk, AddHom.coe_mk,
    Sum.elim_inl, Sum.elim_inr]
  simp
  tauto

/-- A matrix lies in `zeroMagicSquares` iff all the row, column and diagonal sums are `0`; the magic
squares with magic number `0` form a subspace of the magic squares. -/
@[kb "hefferon2020" "Topic-MagicSquares.1, p. 319"]
theorem mem_zeroMagicSquares_iff (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ zeroMagicSquares n ↔ (∀ i, ∑ j, M i j = 0) ∧ (∀ j, ∑ i, M i j = 0) ∧
      ∑ i, M i i = 0 ∧ ∑ i, M i (Fin.rev i) = 0 := by
  change sums n M = 0 ↔ _
  simp only [funext_iff, Sum.forall, Bool.forall_bool, sums, LinearMap.coe_mk, AddHom.coe_mk,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
  simp
  tauto

theorem zeroMagicSquares_le (n : ℕ) : zeroMagicSquares n ≤ magicSquares n :=
  fun _ hM => ⟨0, (LinearMap.mem_ker.1 hM).trans rfl⟩

section Rank

/-- The functional "sum of the row sums minus sum of the column sums" on `Slot n → ℝ`; it vanishes on
the range of `sums n`. -/
def balance (n : ℕ) : Module.Dual ℝ (Slot n → ℝ) :=
  (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Slot n => ℝ) (Sum.inl i)) -
    ∑ j, LinearMap.proj (R := ℝ) (φ := fun _ : Slot n => ℝ) (Sum.inr (Sum.inl j))

theorem balance_apply (n : ℕ) (x : Slot n → ℝ) :
    balance n x = ∑ i, x (Sum.inl i) - ∑ j, x (Sum.inr (Sum.inl j)) := by
  simp [balance]

theorem balance_sums (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : balance n (sums n M) = 0 := by
  rw [balance_apply]
  simp only [sums, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_comm, sub_self]

theorem balance_ne_zero (n : ℕ) [NeZero n] : balance n ≠ 0 := by
  intro h
  have := congrArg (fun f => f (Sum.elim (fun _ => 1) (fun _ => 0))) h
  simp [balance_apply] at this
  exact NeZero.ne n this

/-- The linear constraints `a i + b j + [i = j] g + [j = rev i] d = 0` for all `i j`, with `n ≥ 3`, force
`a` constant `t`, `b` constant `-t`, and `g = d = 0`. -/
theorem key (n : ℕ) (hn : 3 ≤ n) (a b : Fin n → ℝ) (g d : ℝ)
    (h : ∀ i j : Fin n, a i + b j + (if i = j then g else 0) + (if j = Fin.rev i then d else 0) = 0) :
    ∃ t : ℝ, (∀ i, a i = t) ∧ (∀ j, b j = -t) ∧ g = 0 ∧ d = 0 := by
  have hz0 : 0 < n := by omega
  set z : Fin n := ⟨0, hz0⟩ with hzdef
  have hmain : (∀ i, a i = a z) ∧ (∀ j, b j = - a z) := by
    rcases (by omega : n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | h5
    · have hz : z = 0 := rfl
      rw [hz]
      have e00 := h 0 0
      rw [ite_eq_left (by decide : (0 : Fin 3) = 0), ite_eq_right (by decide : ¬ ((0 : Fin 3) = Fin.rev 0))] at e00
      have e01 := h 0 1
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 3) = 1)), ite_eq_right (by decide : ¬ ((1 : Fin 3) = Fin.rev 0))] at e01
      have e02 := h 0 2
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 3) = 2)), ite_eq_left (by decide : (2 : Fin 3) = Fin.rev 0)] at e02
      have e10 := h 1 0
      rw [ite_eq_right (by decide : ¬ ((1 : Fin 3) = 0)), ite_eq_right (by decide : ¬ ((0 : Fin 3) = Fin.rev 1))] at e10
      have e11 := h 1 1
      rw [ite_eq_left (by decide : (1 : Fin 3) = 1), ite_eq_left (by decide : (1 : Fin 3) = Fin.rev 1)] at e11
      have e12 := h 1 2
      rw [ite_eq_right (by decide : ¬ ((1 : Fin 3) = 2)), ite_eq_right (by decide : ¬ ((2 : Fin 3) = Fin.rev 1))] at e12
      have e20 := h 2 0
      rw [ite_eq_right (by decide : ¬ ((2 : Fin 3) = 0)), ite_eq_left (by decide : (0 : Fin 3) = Fin.rev 2)] at e20
      have e21 := h 2 1
      rw [ite_eq_right (by decide : ¬ ((2 : Fin 3) = 1)), ite_eq_right (by decide : ¬ ((1 : Fin 3) = Fin.rev 2))] at e21
      have e22 := h 2 2
      rw [ite_eq_left (by decide : (2 : Fin 3) = 2), ite_eq_right (by decide : ¬ ((2 : Fin 3) = Fin.rev 2))] at e22
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · have hz : z = 0 := rfl
      rw [hz]
      have e00 := h 0 0
      rw [ite_eq_left (by decide : (0 : Fin 4) = 0), ite_eq_right (by decide : ¬ ((0 : Fin 4) = Fin.rev 0))] at e00
      have e01 := h 0 1
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 4) = 1)), ite_eq_right (by decide : ¬ ((1 : Fin 4) = Fin.rev 0))] at e01
      have e02 := h 0 2
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 4) = 2)), ite_eq_right (by decide : ¬ ((2 : Fin 4) = Fin.rev 0))] at e02
      have e03 := h 0 3
      rw [ite_eq_right (by decide : ¬ ((0 : Fin 4) = 3)), ite_eq_left (by decide : (3 : Fin 4) = Fin.rev 0)] at e03
      have e10 := h 1 0
      rw [ite_eq_right (by decide : ¬ ((1 : Fin 4) = 0)), ite_eq_right (by decide : ¬ ((0 : Fin 4) = Fin.rev 1))] at e10
      have e11 := h 1 1
      rw [ite_eq_left (by decide : (1 : Fin 4) = 1), ite_eq_right (by decide : ¬ ((1 : Fin 4) = Fin.rev 1))] at e11
      have e12 := h 1 2
      rw [ite_eq_right (by decide : ¬ ((1 : Fin 4) = 2)), ite_eq_left (by decide : (2 : Fin 4) = Fin.rev 1)] at e12
      have e13 := h 1 3
      rw [ite_eq_right (by decide : ¬ ((1 : Fin 4) = 3)), ite_eq_right (by decide : ¬ ((3 : Fin 4) = Fin.rev 1))] at e13
      have e20 := h 2 0
      rw [ite_eq_right (by decide : ¬ ((2 : Fin 4) = 0)), ite_eq_right (by decide : ¬ ((0 : Fin 4) = Fin.rev 2))] at e20
      have e21 := h 2 1
      rw [ite_eq_right (by decide : ¬ ((2 : Fin 4) = 1)), ite_eq_left (by decide : (1 : Fin 4) = Fin.rev 2)] at e21
      have e22 := h 2 2
      rw [ite_eq_left (by decide : (2 : Fin 4) = 2), ite_eq_right (by decide : ¬ ((2 : Fin 4) = Fin.rev 2))] at e22
      have e23 := h 2 3
      rw [ite_eq_right (by decide : ¬ ((2 : Fin 4) = 3)), ite_eq_right (by decide : ¬ ((3 : Fin 4) = Fin.rev 2))] at e23
      have e30 := h 3 0
      rw [ite_eq_right (by decide : ¬ ((3 : Fin 4) = 0)), ite_eq_left (by decide : (0 : Fin 4) = Fin.rev 3)] at e30
      have e31 := h 3 1
      rw [ite_eq_right (by decide : ¬ ((3 : Fin 4) = 1)), ite_eq_right (by decide : ¬ ((1 : Fin 4) = Fin.rev 3))] at e31
      have e32 := h 3 2
      rw [ite_eq_right (by decide : ¬ ((3 : Fin 4) = 2)), ite_eq_right (by decide : ¬ ((2 : Fin 4) = Fin.rev 3))] at e32
      have e33 := h 3 3
      rw [ite_eq_left (by decide : (3 : Fin 4) = 3), ite_eq_right (by decide : ¬ ((3 : Fin 4) = Fin.rev 3))] at e33
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp <;> linarith
    · have gen : ∀ i j : Fin n, j ≠ i → j ≠ Fin.rev i → a i + b j = 0 := by
        intro i j h1 h2
        have := h i j
        rw [ite_eq_right (Ne.symm h1), ite_eq_right h2] at this
        linarith
      have hex : ∀ s : Finset (Fin n), s.card < n → ∃ j, j ∉ s := fun s hs => by
        by_contra hcon
        push Not at hcon
        have : s = Finset.univ := Finset.eq_univ_of_forall hcon
        rw [this, Finset.card_univ, Fintype.card_fin] at hs
        omega
      have haeq : ∀ i, a i = a z := by
        intro i
        obtain ⟨j, hj⟩ := hex ({i, Fin.rev i, z, Fin.rev z} : Finset (Fin n))
          (lt_of_le_of_lt Finset.card_le_four (by omega))
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        obtain ⟨h1, h2, h3, h4⟩ := hj
        have := gen i j h1 h2
        have := gen z j h3 h4
        linarith
      refine ⟨haeq, fun j => ?_⟩
      obtain ⟨i, hi⟩ := hex ({j, Fin.rev j} : Finset (Fin n))
        (lt_of_le_of_lt Finset.card_le_two (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      have h1 : j ≠ i := fun e => hi.1 e.symm
      have h2 : j ≠ Fin.rev i := fun e => hi.2 (by rw [e, Fin.rev_rev])
      have := gen i j h1 h2
      have := haeq i
      linarith
  obtain ⟨ha, hb⟩ := hmain
  have hzr : z ≠ Fin.rev z := by
    intro e
    have := congrArg Fin.val e
    simp [Fin.val_rev, hzdef] at this
    omega
  have hg : g = 0 := by
    have := h z z
    rw [ite_eq_left rfl, ite_eq_right hzr] at this
    have := hb z
    linarith
  have hd : d = 0 := by
    have := h z (Fin.rev z)
    rw [ite_eq_right hzr, ite_eq_left rfl] at this
    have := hb (Fin.rev z)
    linarith
  exact ⟨a z, ha, hb, hg, hd⟩

theorem sums_single (n : ℕ) (i j : Fin n) :
    sums n (Matrix.single i j (1 : ℝ)) = Sum.elim (fun i' => if i = i' then 1 else 0)
      (Sum.elim (fun j' => if j = j' then 1 else 0)
        (fun b => if b then (if i = j then 1 else 0) else (if j = Fin.rev i then 1 else 0))) := by
  ext (i' | j' | b)
  · simp [sums, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  · simp [sums, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  · cases b
    · simp only [sums, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Matrix.single_apply]
      simp only [Bool.false_eq_true, ite_false, Finset.sum_boole]
      split_ifs with h
      · rw [Nat.cast_eq_one, Finset.card_eq_one]
        refine ⟨i, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, -⟩; exact h1.symm
        · rintro rfl; exact ⟨rfl, h⟩
      · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro x - ⟨h1, h2⟩
        exact h (by rw [h2, ← h1])
    · simp only [sums, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, Matrix.single_apply]
      simp only [ite_true, Finset.sum_boole]
      split_ifs with h
      · rw [Nat.cast_eq_one, Finset.card_eq_one]
        refine ⟨i, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, -⟩; exact h1.symm
        · rintro rfl; exact ⟨rfl, h.symm⟩
      · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro x - ⟨h1, h2⟩
        exact h (h1.trans h2.symm)

theorem dualAnn_eq (n : ℕ) (hn : 3 ≤ n) :
    (LinearMap.range (sums n)).dualAnnihilator = Submodule.span ℝ {balance n} := by
  apply le_antisymm
  · intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have hexp : ∀ x, φ x = ∑ k, x k * φ (fun j => if k = j then 1 else 0) := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have heq : ∀ i j : Fin n, φ (fun k => if Sum.inl i = k then 1 else 0) +
        φ (fun k => if Sum.inr (Sum.inl j) = k then 1 else 0) +
        (if i = j then φ (fun k => if Sum.inr (Sum.inr true) = k then 1 else 0) else 0) +
        (if j = Fin.rev i then φ (fun k => if Sum.inr (Sum.inr false) = k then 1 else 0)
          else 0) = 0 := by
      intro i j
      have := hφ (sums n (Matrix.single i j 1)) ⟨_, rfl⟩
      rw [hexp, sums_single] at this
      simp [Fintype.sum_sum_type] at this
      linarith
    obtain ⟨t, ha, hb, hg, hd⟩ := key n hn
      (fun i => φ (fun k => if Sum.inl i = k then 1 else 0))
      (fun j => φ (fun k => if Sum.inr (Sum.inl j) = k then 1 else 0))
      (φ (fun k => if Sum.inr (Sum.inr true) = k then 1 else 0))
      (φ (fun k => if Sum.inr (Sum.inr false) = k then 1 else 0)) heq
    have ha' : ∀ i, φ (fun k => if Sum.inl i = k then 1 else 0) = t := ha
    have hb' : ∀ j, φ (fun k => if Sum.inr (Sum.inl j) = k then 1 else 0) = -t := hb
    rw [Submodule.mem_span_singleton]
    refine ⟨t, ?_⟩
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.smul_apply, balance_apply, hexp x]
    simp only [Fintype.sum_sum_type, Fintype.sum_bool, ha', hb', hg, hd]
    simp [← Finset.sum_mul, smul_eq_mul]
    ring
  · rw [Submodule.span_le]
    rintro _ rfl
    exact Submodule.mem_dualAnnihilator _ |>.2 (fun w ⟨M, hM⟩ => by rw [← hM]; exact balance_sums n M)

theorem finrank_range_sums (n : ℕ) (hn : 3 ≤ n) :
    finrank ℝ (LinearMap.range (sums n)) = 2 * n + 1 := by
  have : NeZero n := ⟨by omega⟩
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range (sums n))
  rw [dualAnn_eq n hn, finrank_span_singleton (balance_ne_zero n)] at h1
  have h2 : finrank ℝ (Slot n → ℝ) = 2 * n + 2 := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  omega

theorem finrank_zeroMagic_add (n : ℕ) (hn : 3 ≤ n) :
    finrank ℝ (zeroMagicSquares n) + (2 * n + 1) = n * n := by
  have h := (sums n).finrank_range_add_finrank_ker
  rw [finrank_range_sums n hn, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  change finrank ℝ (LinearMap.ker (sums n)) + _ = _
  omega

/-- For `n ≥ 3` the `n × n` magic squares with magic number `0` form a space of dimension
`n² - 2n - 1`: the `2n + 2` linear constraints have rank `2n + 1`. -/
@[kb "hefferon2020" "Topic-MagicSquares.2, p. 320"]
theorem hefferon_MagicSquares_2 (n : ℕ) (hn : 3 ≤ n) :
    finrank ℝ (zeroMagicSquares n) = n ^ 2 - 2 * n - 1 := by
  have := finrank_zeroMagic_add n hn
  rw [sq]
  omega

end Rank

section Total

/-- The all-ones matrix, a magic square with magic number `n`. -/
def ones (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

theorem sums_ones (n : ℕ) : sums n (ones n) = fun _ => (n : ℝ) := by
  ext (i | j | b)
  · simp [sums, ones]
  · simp [sums, ones]
  · cases b <;> simp [sums, ones]

theorem magic_eq_sup (n : ℕ) (hn : 3 ≤ n) :
    magicSquares n = zeroMagicSquares n ⊔ Submodule.span ℝ {ones n} := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  apply le_antisymm
  · rintro M ⟨s, hs⟩
    have hM : M - (s / n) • ones n ∈ zeroMagicSquares n := by
      change sums n (M - (s / n) • ones n) = 0
      rw [map_sub, map_smul, hs, sums_ones]
      ext k
      simp [hn0]
    have := Submodule.add_mem_sup hM (Submodule.smul_mem (Submodule.span ℝ {ones n}) (s / n)
      (Submodule.mem_span_singleton_self (ones n)))
    simpa using this
  · refine sup_le (zeroMagicSquares_le n) ?_
    rw [Submodule.span_le]
    rintro _ rfl
    exact ⟨n, sums_ones n⟩

/-- The space of `n × n` magic squares has dimension one more than the subspace with magic number `0`
(the magic number is onto `ℝ`), hence `n² - 2n` for `n ≥ 3`. -/
@[kb "hefferon2020" "Topic-MagicSquares.3, p. 319"]
theorem hefferon_MagicSquares_3 (n : ℕ) (hn : 3 ≤ n) :
    finrank ℝ (magicSquares n) = finrank ℝ (zeroMagicSquares n) + 1 ∧
      finrank ℝ (magicSquares n) = n ^ 2 - 2 * n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hones : ones n ≠ 0 := by
    intro h
    have := congrArg (fun M => sums n M) h
    simp only [sums_ones, map_zero] at this
    exact hn0 (congrFun this (Sum.inl ⟨0, by omega⟩))
  have hdisj : Disjoint (zeroMagicSquares n) (Submodule.span ℝ {ones n}) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx'
    have h0 : sums n (c • ones n) = 0 := hx
    rw [map_smul, sums_ones] at h0
    have := congrFun h0 (Sum.inl ⟨0, by omega⟩)
    simp [hn0] at this
    simp [this]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (zeroMagicSquares n)
    (Submodule.span ℝ {ones n})
  rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hones, ← magic_eq_sup n hn] at h1
  have h2 := finrank_zeroMagic_add n hn
  refine ⟨by omega, ?_⟩
  rw [sq]
  omega

end Total

end MagicSquares
end UndergradKB.LinearAlgebra
