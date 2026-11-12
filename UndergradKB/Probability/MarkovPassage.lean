import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovRegular

/-! # Mean first passage and mean recurrence times

Grinstead–Snell §11.5. For an ergodic chain and a target state `j`, the book computes the mean first passage times
`m i j` by making `j` absorbing. Here `stopAt P j` is that modified chain, `notYetHit P j n i` is the probability,
starting from `i`, that the chain has not reached `j` within `n` steps, and the mean first passage time is the sum of
these tail probabilities (the expected value of the first passage time `T`, written `∑_n P(T > n)`). The mean
recurrence time is `r i = 1 + ∑_k p_ik m k i` (one step, then the passage back to `i`).

Main results: the first-step equations `m i j = 1 + ∑_k p_ik m k j` for `i ≠ j` (Theorem 11.15 setting, the matrix
equation `(I - P) M = C - D`), and `r i = 1 / w i` (Theorem 11.15 / Corollary 11.1), with `w` the fixed probability
vector. -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The chain `P` with the state `j` made absorbing (Grinstead–Snell §11.5). -/
def stopAt (P : Matrix S S ℝ) (j : S) : Matrix S S ℝ :=
  fun i k => if i = j then (if k = j then 1 else 0) else P i k

/-- The probability, starting from `i`, that the chain `P` has not reached `j` within the first `n` steps. -/
noncomputable def notYetHit (P : Matrix S S ℝ) (j : S) (n : ℕ) (i : S) : ℝ :=
  ∑ l ∈ univ.erase j, (stopAt P j ^ n) i l

/-- Grinstead–Snell Definition 11.7 (PR-120): the mean first passage time `m i j` from `i` to `j`, the expected
number of steps to reach `j` starting from `i`, written as the sum of the tail probabilities `P(T > n)`
(`m j j = 0`). -/
@[kb "grinsteadsnell2006" "Definition 11.7, p. 461"]
noncomputable def meanFirstPassage (P : Matrix S S ℝ) (i j : S) : ℝ := ∑' n, notYetHit P j n i

/-- Grinstead–Snell Definition 11.8 (PR-120): the mean recurrence time `r i`, the expected number of steps to return
to `i` starting from `i`: one step, then the mean first passage time back to `i`. -/
@[kb "grinsteadsnell2006" "Definition 11.8, p. 462"]
noncomputable def meanRecurrence (P : Matrix S S ℝ) (i : S) : ℝ := 1 + ∑ k, P i k * meanFirstPassage P k i

variable {P : Matrix S S ℝ}

theorem stopAt_of_ne {i j : S} (hi : i ≠ j) (k : S) : stopAt P j i k = P i k := by
  simp [stopAt, hi]

theorem stopAt_mem (hP : P ∈ rowStochastic ℝ S) (j : S) : stopAt P j ∈ rowStochastic ℝ S := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i k => ?_, fun i => ?_⟩
  · unfold stopAt
    split_ifs
    · exact zero_le_one
    · exact le_rfl
    · exact nonneg_of_mem_rowStochastic hP
  · by_cases hi : i = j
    · simp [stopAt, hi]
    · simp only [stopAt, hi, ite_false]
      exact sum_row_of_mem_rowStochastic hP i

theorem stopAt_absorbing (j : S) : IsAbsorbingState (stopAt P j) j := by
  simp [IsAbsorbingState, stopAt]

theorem stopAt_pow_self (j : S) (n : ℕ) (l : S) : (stopAt P j ^ n) j l = if l = j then 1 else 0 := by
  induction n generalizing l with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
    simp [stopAt]

theorem notYetHit_self (j : S) (n : ℕ) : notYetHit P j n j = 0 := by
  unfold notYetHit
  refine sum_eq_zero fun l hl => ?_
  rw [stopAt_pow_self, if_neg (ne_of_mem_erase hl)]

theorem notYetHit_zero {i j : S} (hi : i ≠ j) : notYetHit P j 0 i = 1 := by
  unfold notYetHit
  simp only [pow_zero, Matrix.one_apply]
  rw [sum_ite_eq]
  simp [hi]

theorem notYetHit_succ {i j : S} (hi : i ≠ j) (n : ℕ) :
    notYetHit P j (n + 1) i = ∑ k, P i k * notYetHit P j n k := by
  unfold notYetHit
  simp only [pow_succ', Matrix.mul_apply, stopAt_of_ne hi, mul_sum]
  exact sum_comm

/-- If `j` can be reached from `i` in `P`, it can be reached in the stopped chain. -/
theorem exists_stopAt_pow_pos (hP : P ∈ rowStochastic ℝ S) (j : S) :
    ∀ n i, 0 < (P ^ n) i j → ∃ m, 0 < (stopAt P j ^ m) i j := by
  intro n
  induction n with
  | zero =>
    intro i h
    have : i = j := by
      by_contra hij
      simp [Matrix.one_apply, hij] at h
    subst this
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro i h
    by_cases hij : i = j
    · subst hij; exact ⟨0, by simp⟩
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ : ∃ l ∈ univ, 0 < P i l * (P ^ n) l j := by
      by_contra hcon
      push Not at hcon
      exact absurd (sum_nonpos hcon) (not_le.2 h)
    have hPil : 0 < P i l := by
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hl with h' | h'
      · exact h'.1
      · exact absurd h'.1 (not_lt.2 (nonneg_of_mem_rowStochastic hP))
    have hPn : 0 < (P ^ n) l j := by
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hl with h' | h'
      · exact h'.2
      · exact absurd h'.2 (not_lt.2 (nonneg_of_mem_rowStochastic (pow_mem hP n)))
    obtain ⟨m, hm⟩ := ih l hPn
    refine ⟨m + 1, ?_⟩
    have hQ := stopAt_mem hP j
    rw [pow_succ', Matrix.mul_apply]
    calc (0 : ℝ) < stopAt P j i l * (stopAt P j ^ m) l j := by
          rw [stopAt_of_ne hij]; exact mul_pos hPil hm
      _ ≤ ∑ k, stopAt P j i k * (stopAt P j ^ m) k j :=
          single_le_sum (f := fun k => stopAt P j i k * (stopAt P j ^ m) k j)
            (fun k _ => mul_nonneg (nonneg_of_mem_rowStochastic hQ)
              (nonneg_of_mem_rowStochastic (pow_mem hQ m))) (mem_univ l)

/-- For an ergodic chain, making `j` absorbing gives an absorbing chain. -/
theorem stopAt_isAbsorbingChain (h : IsErgodicChain P) (j : S) : IsAbsorbingChain (stopAt P j) := by
  refine ⟨⟨j, stopAt_absorbing j⟩, fun i => ?_⟩
  obtain ⟨hP, hirr⟩ := isErgodicChain_iff.1 h
  obtain ⟨k, -, hk⟩ := hirr i j
  obtain ⟨m, hm⟩ := exists_stopAt_pow_pos hP j k i hk
  exact ⟨m, j, stopAt_absorbing j, hm⟩

/-- For an ergodic chain, `j` is the only absorbing state of the stopped chain. -/
theorem stopAt_not_absorbing (h : IsErgodicChain P) {l j : S} (hl : l ≠ j) :
    ¬ IsAbsorbingState (stopAt P j) l := by
  intro habs
  obtain ⟨hP, hirr⟩ := isErgodicChain_iff.1 h
  have hQ := stopAt_mem hP j
  have hzero : ∀ m, (stopAt P j ^ m) l j = 0 := by
    intro m
    induction m with
    | zero => simp [Matrix.one_apply, hl]
    | succ m ih =>
      rw [pow_succ', Matrix.mul_apply, sum_eq_single l]
      · rw [ih, mul_zero]
      · intro k _ hk
        rw [absorbing_row_eq_zero hQ habs hk, zero_mul]
      · intro hl'; exact absurd (mem_univ l) hl'
  obtain ⟨k, -, hk⟩ := hirr l j
  obtain ⟨m, hm⟩ := exists_stopAt_pow_pos hP j k l hk
  rw [hzero m] at hm
  exact lt_irrefl 0 hm

theorem sum_transient_stopAt (h : IsErgodicChain P) (j : S) (f : S → ℝ) :
    ∑ l : Transient (stopAt P j), f l = ∑ l ∈ univ.erase j, f l := by
  refine (Finset.sum_subtype (univ.erase j) (fun l => ?_) f).symm
  simp only [mem_erase, mem_univ, and_true]
  exact ⟨fun hl => stopAt_not_absorbing h hl, fun hna hl => hna (by subst hl; exact stopAt_absorbing _)⟩

theorem meanFirstPassage_self (j : S) : meanFirstPassage P j j = 0 := by
  simp [meanFirstPassage, notYetHit_self]

/-- Grinstead–Snell Definition 11.7 (PR-120): for an ergodic chain the tail probabilities `P(T > n)` of the first
passage time from `i` to `j` are summable, with sum the mean first passage time `m i j` (it is finite). -/
@[kb "grinsteadsnell2006" "Definition 11.7, p. 461"]
theorem hasSum_notYetHit (h : IsErgodicChain P) (i j : S) :
    HasSum (fun n => notYetHit P j n i) (meanFirstPassage P i j) := by
  by_cases hij : i = j
  · subst hij
    simp only [notYetHit_self, meanFirstPassage_self]
    exact hasSum_zero
  have hP := h.1
  have hA := hasSum_absorption_time (stopAt_mem hP j) (stopAt_isAbsorbingChain h j)
    ⟨i, stopAt_not_absorbing h hij⟩
  have hs : Summable fun n => notYetHit P j n i :=
    hA.summable.congr fun k => sum_transient_stopAt h j (fun l => (stopAt P j ^ k) i l)
  exact hs.hasSum

/-- Grinstead–Snell §11.5 (PR-120), first-step equations: for an ergodic chain and `i ≠ j`,
`m i j = 1 + ∑_k p_ik m k j` (with `m j j = 0`); in matrix form `(I - P) M = C - D`. -/
@[kb "grinsteadsnell2006" "Theorem 11.15, p. 463"]
theorem meanFirstPassage_eq (h : IsErgodicChain P) {i j : S} (hij : i ≠ j) :
    meanFirstPassage P i j = 1 + ∑ k, P i k * meanFirstPassage P k j := by
  have h1 := hasSum_notYetHit h i j
  rw [← hasSum_nat_add_iff' 1] at h1
  simp only [range_one, sum_singleton, notYetHit_zero hij, notYetHit_succ hij] at h1
  have h2 : HasSum (fun n => ∑ k, P i k * notYetHit P j n k) (∑ k, P i k * meanFirstPassage P k j) :=
    hasSum_sum fun k _ => (hasSum_notYetHit h k j).mul_left (P i k)
  have := h1.unique h2
  linarith

/-- The first-step equations in matrix form `(I - P) M = C - D` (Grinstead–Snell §11.5): entry `(i, j)` of
`(I - P) M` is `1 - δ_ij r_j`. -/
theorem firstStep_matrix (h : IsErgodicChain P) (i j : S) :
    meanFirstPassage P i j - ∑ l, P i l * meanFirstPassage P l j =
      1 - (if i = j then meanRecurrence P j else 0) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, meanRecurrence, meanFirstPassage_self]
    ring
  · rw [if_neg hij, meanFirstPassage_eq h hij]
    ring

/-- For an ergodic chain and any fixed probability vector `w`, `w j r j = 1`. -/
theorem mul_meanRecurrence_eq_one (h : IsErgodicChain P) {w : S → ℝ} (hsum : ∑ j, w j = 1)
    (hfix : IsFixedRow P w) (j : S) : w j * meanRecurrence P j = 1 := by
  set m : S → ℝ := fun i => meanFirstPassage P i j with hm
  have hfixsum : ∑ i, w i * (∑ l, P i l * m l) = ∑ l, w l * m l := by
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    have hl := congrFun hfix l
    simp only [vecMul, dotProduct] at hl
    rw [← hl, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  have htot : ∑ i, w i * (m i - ∑ l, P i l * m l) = 0 := by
    simp only [mul_sub, sum_sub_distrib, hfixsum, sub_self]
  simp only [hm, firstStep_matrix h, mul_sub, mul_one, sum_sub_distrib, hsum, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, if_true] at htot
  linarith

variable [Nonempty S]

/-- Grinstead–Snell Theorem 11.15 and Corollary 11.1 (PR-120): for an ergodic chain with fixed probability vector `w`,
the mean recurrence time of every state is `r i = 1 / w i`. -/
@[kb "grinsteadsnell2006" "Theorem 11.15, p. 463"]
theorem meanRecurrence_eq_inv (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ j, meanRecurrence P j = 1 / w j := by
  obtain ⟨w, hpos, hsum, hfix, -⟩ := ergodic_fixed_vector h
  refine ⟨w, hpos, hsum, hfix, fun j => ?_⟩
  rw [eq_div_iff (hpos j).ne', mul_comm]
  exact mul_meanRecurrence_eq_one h hsum hfix j

/-- The matrix `W` all of whose rows equal `w`. -/
def rowsMatrix (w : S → ℝ) : Matrix S S ℝ := Matrix.of fun _ k => w k

/-- For an ergodic chain a column vector fixed by `P` is constant (equal to its `w`-average). -/
theorem fixedColumn_const {w : S → ℝ}
    (hw : ∀ i j, Tendsto (fun n => cesaroAvg P n i j) atTop (𝓝 (w j))) {x : S → ℝ} (hx : P *ᵥ x = x)
    (i : S) : x i = ∑ k, w k * x k := by
  have hpow : ∀ k, P ^ k *ᵥ x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hx, ih]
  have hlim : Tendsto (fun n => ∑ l, cesaroAvg P n i l * x l) atTop (𝓝 (∑ l, w l * x l)) :=
    tendsto_finsetSum _ fun l _ => (hw i l).mul_const (x l)
  have hev : ∀ n ≥ 1, ∑ l, cesaroAvg P n i l * x l = x i := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    simp only [cesaroAvg, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
    have : ∀ k ∈ range n, ∑ l, (P ^ k) i l * x l = x i := fun k _ => congrFun (hpow k) i
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hlim' : Tendsto (fun n => ∑ l, cesaroAvg P n i l * x l) atTop (𝓝 (x i)) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hev n hn).symm⟩)
  exact tendsto_nhds_unique hlim' hlim

/-- Grinstead–Snell Theorem 11.16 (PR-120): for an ergodic chain with fixed probability vector `w` and limiting
matrix `W` (rows `w`), the fundamental matrix `Z = (I - P + W)⁻¹` exists and the mean first passage times are
`m i j = (z j j - z i j) / w j`. -/
@[kb "grinsteadsnell2006" "Theorem 11.16, p. 467"]
theorem meanFirstPassage_eq_fundamental (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      IsUnit (1 - P + rowsMatrix w) ∧
      ∀ i j, meanFirstPassage P i j =
        ((1 - P + rowsMatrix w)⁻¹ j j - (1 - P + rowsMatrix w)⁻¹ i j) / w j := by
  obtain ⟨w, hpos, hsum, hfix, hw⟩ := ergodic_cesaro_tendsto h
  have hP := h.1
  set W := rowsMatrix w with hWdef
  set A : Matrix S S ℝ := 1 - P + W with hAdef
  -- `w x = ∑ w_k x_k` is preserved by `P`
  have hwP : ∀ x : S → ℝ, ∑ i, w i * (P *ᵥ x) i = ∑ k, w k * x k := by
    intro x
    simp only [mulVec, dotProduct, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    have hk := congrFun hfix k
    simp only [vecMul, dotProduct] at hk
    rw [← hk, sum_mul]
    exact sum_congr rfl fun i _ => by ring
  have hWx : ∀ x : S → ℝ, W *ᵥ x = fun _ => ∑ k, w k * x k := by
    intro x; funext i; simp [hWdef, rowsMatrix, mulVec, dotProduct]
  have hinj : Function.Injective (A *ᵥ ·) := by
    intro x y hxy
    set z := x - y
    have hz : A *ᵥ z = 0 := by simp only [z, mulVec_sub, hxy, sub_self]
    have hz' : ∀ i, z i - (P *ᵥ z) i + ∑ k, w k * z k = 0 := by
      intro i
      have := congrFun hz i
      simpa [hAdef, add_mulVec, sub_mulVec, one_mulVec, hWx] using this
    have hs : ∑ k, w k * z k = 0 := by
      have : ∑ i, w i * (z i - (P *ᵥ z) i + ∑ k, w k * z k) = 0 := by simp [hz']
      simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, hwP, ← sum_mul, hsum, one_mul] at this
      linarith
    have hPz : P *ᵥ z = z := by
      funext i; have := hz' i; rw [hs] at this; linarith
    have hz0 : z = 0 := by
      funext i
      rw [fixedColumn_const hw hPz i, hs]; rfl
    exact sub_eq_zero.1 hz0
  have hA : IsUnit A := mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA
  set Z := A⁻¹ with hZdef
  have hZA : Z * A = 1 := nonsing_inv_mul _ hdet
  -- `W` is fixed by `A` on the left: `A W = W`
  have hAW : A * W = W := by
    rw [hAdef, add_mul, sub_mul, Matrix.one_mul]
    ext i k
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, hWdef, rowsMatrix, Matrix.of_apply]
    rw [← sum_mul, ← sum_mul, sum_row_of_mem_rowStochastic hP i, hsum]
    ring
  have hZW : Z * W = W := by rw [← hAW, ← Matrix.mul_assoc, hZA, Matrix.one_mul, hAW]
  have hZP : Z * (1 - P) = 1 - W := by
    have : (1 - P : Matrix S S ℝ) = A - W := by simp [hAdef]
    rw [this, Matrix.mul_sub, hZA, hZW]
  have hZrow : ∀ i, ∑ k, Z i k = 1 := by
    have h1 : A *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
      funext i
      simp only [hAdef, add_mulVec, sub_mulVec, one_mulVec, hWx, Pi.add_apply, Pi.sub_apply, mul_one, hsum]
      have := congrFun (one_vecMul_of_mem_rowStochastic hP) i
      simp only [Pi.one_apply] at this
      rw [show (fun _ : S => (1 : ℝ)) = 1 from rfl, this]
      ring
    intro i
    have h2 : Z *ᵥ (A *ᵥ fun _ => (1 : ℝ)) = fun _ => 1 := by rw [mulVec_mulVec, hZA, one_mulVec]
    rw [h1] at h2
    simpa [mulVec, dotProduct] using congrFun h2 i
  have hr : ∀ j, meanRecurrence P j = 1 / w j := fun j => by
    rw [eq_div_iff (hpos j).ne', mul_comm]; exact mul_meanRecurrence_eq_one h hsum hfix j
  -- the matrix identity `Z (I - P) M = (I - W) M`, entrywise
  set M : Matrix S S ℝ := Matrix.of fun i j => meanFirstPassage P i j with hMdef
  have hE : (1 - P) * M = Matrix.of fun i j => 1 - (if i = j then meanRecurrence P j else 0) := by
    rw [sub_mul, Matrix.one_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, hMdef, Matrix.of_apply]
    exact firstStep_matrix h i j
  have key : ∀ i j, meanFirstPassage P i j - ∑ k, w k * meanFirstPassage P k j =
      1 - Z i j * meanRecurrence P j := by
    intro i j
    have h1 : (Z * (1 - P) * M) i j = (Z * ((1 - P) * M)) i j := by rw [Matrix.mul_assoc]
    rw [hZP, hE, sub_mul, Matrix.one_mul] at h1
    simp only [Matrix.sub_apply, Matrix.mul_apply, hMdef, Matrix.of_apply, hWdef,
      rowsMatrix, mul_sub, mul_one, sum_sub_distrib, hZrow, mul_ite, mul_zero, sum_ite_eq', mem_univ,
      if_true] at h1
    linarith
  refine ⟨w, hpos, hsum, hfix, hA, fun i j => ?_⟩
  have hi := key i j
  have hj := key j j
  rw [meanFirstPassage_self] at hj
  rw [hr j] at hi hj
  rw [eq_div_iff (hpos j).ne']
  have hwj := (hpos j).ne'
  field_simp at hi hj
  linarith

end UndergradKB.Probability
