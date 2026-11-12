import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

/-! # Ergodic and regular Markov chains

Grinstead–Snell §11.3 and Lemma 11.1. A chain is ergodic when every state can be reached from every state
(Mathlib's `Matrix.IsIrreducible`) and regular when some power of the transition matrix has only positive entries.
For a regular chain the powers `P^n` converge to a matrix all of whose rows equal a positive probability vector `w`,
the unique fixed row vector. The proof follows the book: for a matrix with all entries at least `ε` the oscillation
(maximum minus minimum) of `P y` is at most `(1 - 2ε)` times that of `y` (Lemma 11.1). -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Grinstead–Snell Definition 11.4 (PR-115): an ergodic chain is a chain with transition matrix `P` in which it is
possible to go from every state to every state (in a positive number of steps), i.e. `P` is irreducible. -/
@[kb "grinsteadsnell2006" "Definition 11.4, p. 441"]
def IsErgodicChain (P : Matrix S S ℝ) : Prop := P ∈ rowStochastic ℝ S ∧ P.IsIrreducible

/-- Grinstead–Snell Definition 11.5 (PR-115): a regular chain is a chain with transition matrix `P` some positive
power of which has only positive entries. -/
@[kb "grinsteadsnell2006" "Definition 11.5, p. 441"]
def IsRegularChain (P : Matrix S S ℝ) : Prop :=
  P ∈ rowStochastic ℝ S ∧ ∃ N > 0, ∀ i j, 0 < (P ^ N) i j

/-- Grinstead–Snell Definition 11.4 (PR-115): ergodicity is "every state reachable from every state". -/
@[kb "grinsteadsnell2006" "Definition 11.4, p. 441"]
theorem isErgodicChain_iff {P : Matrix S S ℝ} :
    IsErgodicChain P ↔ P ∈ rowStochastic ℝ S ∧ ∀ i j, ∃ k > 0, 0 < (P ^ k) i j := by
  refine and_congr_right fun hP => ?_
  exact isIrreducible_iff_exists_pow_pos (fun i j => nonneg_of_mem_rowStochastic hP)

/-- Grinstead–Snell §11.3 (PR-115): a regular chain is ergodic. -/
@[kb "grinsteadsnell2006" "Definition 11.5, p. 441"]
theorem IsRegularChain.isErgodicChain {P : Matrix S S ℝ} (h : IsRegularChain P) : IsErgodicChain P := by
  obtain ⟨hP, N, hN, hpos⟩ := h
  refine ⟨hP, ?_⟩
  rw [isIrreducible_iff_exists_pow_pos (fun i j => nonneg_of_mem_rowStochastic hP)]
  exact fun i j => ⟨N, hN, hpos i j⟩

/-- Grinstead–Snell Definition 11.5 (PR-115): a regular chain is the same as a primitive stochastic matrix (Mathlib's
`Matrix.IsPrimitive`). -/
@[kb "grinsteadsnell2006" "Definition 11.5, p. 441"]
theorem isRegularChain_iff_isPrimitive {P : Matrix S S ℝ} :
    IsRegularChain P ↔ P ∈ rowStochastic ℝ S ∧ P.IsPrimitive := by
  constructor
  · rintro ⟨hP, N, hN, hpos⟩
    exact ⟨hP, ⟨fun i j => nonneg_of_mem_rowStochastic hP, N, hN, hpos⟩⟩
  · rintro ⟨hP, _, N, hN, hpos⟩
    exact ⟨hP, N, hN, hpos⟩

/-- Grinstead–Snell Definition 11.6 (PR-116): `w` is a fixed row vector of `P` when `w P = w`. -/
@[kb "grinsteadsnell2006" "Definition 11.6, p. 443"]
def IsFixedRow (P : Matrix S S ℝ) (w : S → ℝ) : Prop := w ᵥ* P = w

/-- Grinstead–Snell Definition 11.6 (PR-116): `x` is a fixed column vector of `P` when `P x = x`. -/
@[kb "grinsteadsnell2006" "Definition 11.6, p. 443"]
def IsFixedColumn (P : Matrix S S ℝ) (x : S → ℝ) : Prop := P *ᵥ x = x

section Osc

variable [Nonempty S]

/-- The largest entry of a vector. -/
noncomputable def vmax (y : S → ℝ) : ℝ := univ.sup' univ_nonempty y

/-- The smallest entry of a vector. -/
noncomputable def vmin (y : S → ℝ) : ℝ := univ.inf' univ_nonempty y

theorem le_vmax (y : S → ℝ) (i : S) : y i ≤ vmax y := le_sup' y (mem_univ i)

theorem vmin_le (y : S → ℝ) (i : S) : vmin y ≤ y i := inf'_le y (mem_univ i)

theorem exists_eq_vmax (y : S → ℝ) : ∃ i, y i = vmax y := by
  obtain ⟨i, _, h⟩ := exists_mem_eq_sup' (univ_nonempty (α := S)) y
  exact ⟨i, h.symm⟩

theorem exists_eq_vmin (y : S → ℝ) : ∃ i, y i = vmin y := by
  obtain ⟨i, _, h⟩ := exists_mem_eq_inf' (univ_nonempty (α := S)) y
  exact ⟨i, h.symm⟩

theorem vmin_le_vmax (y : S → ℝ) : vmin y ≤ vmax y :=
  (vmin_le y (Classical.arbitrary S)).trans (le_vmax y _)

theorem mulVec_apply_eq (P : Matrix S S ℝ) (y : S → ℝ) (i : S) :
    (P *ᵥ y) i = ∑ j, P i j * y j := rfl

theorem mulVec_le_vmax {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (y : S → ℝ) (i : S) :
    (P *ᵥ y) i ≤ vmax y := by
  rw [mulVec_apply_eq]
  calc ∑ j, P i j * y j ≤ ∑ j, P i j * vmax y :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_vmax y j) (nonneg_of_mem_rowStochastic hP)
    _ = vmax y := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul]

theorem vmin_le_mulVec {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (y : S → ℝ) (i : S) :
    vmin y ≤ (P *ᵥ y) i := by
  rw [mulVec_apply_eq]
  calc vmin y = ∑ j, P i j * vmin y := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul]
    _ ≤ ∑ j, P i j * y j :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (vmin_le y j) (nonneg_of_mem_rowStochastic hP)

/-- The oscillation (maximum minus minimum) of a vector. -/
noncomputable def osc (y : S → ℝ) : ℝ := vmax y - vmin y

theorem osc_nonneg (y : S → ℝ) : 0 ≤ osc y := sub_nonneg.2 (vmin_le_vmax y)

theorem osc_mulVec_le {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (y : S → ℝ) :
    osc (P *ᵥ y) ≤ osc y := by
  unfold osc
  have h1 : vmax (P *ᵥ y) ≤ vmax y := sup'_le _ _ fun i _ => mulVec_le_vmax hP y i
  have h2 : vmin y ≤ vmin (P *ᵥ y) := le_inf' _ _ fun i _ => vmin_le_mulVec hP y i
  linarith

/-- Grinstead–Snell Lemma 11.1 (PR-117): if every entry of the transition matrix `P` is at least `ε`, the
oscillation of `P y` is at most `1 - 2ε` times the oscillation of `y`. -/
@[kb "grinsteadsnell2006" "Lemma 11.1, p. 456"]
theorem osc_mulVec_le_of_entries_ge {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {ε : ℝ}
    (hε : ∀ i j, ε ≤ P i j) (y : S → ℝ) : osc (P *ᵥ y) ≤ (1 - 2 * ε) * osc y := by
  obtain ⟨j0, hj0⟩ := exists_eq_vmin y
  obtain ⟨j1, hj1⟩ := exists_eq_vmax y
  have hosc := osc_nonneg y
  have hup : ∀ i, (P *ᵥ y) i ≤ vmax y - ε * osc y := by
    intro i
    have h1 : ∑ j, P i j * (vmax y - y j) = vmax y - (P *ᵥ y) i := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul,
        mulVec_apply_eq]
    have h2 : P i j0 * (vmax y - y j0) ≤ ∑ j, P i j * (vmax y - y j) :=
      single_le_sum (f := fun j => P i j * (vmax y - y j))
        (fun j _ => mul_nonneg (nonneg_of_mem_rowStochastic hP) (sub_nonneg.2 (le_vmax y j))) (mem_univ j0)
    have h3 : ε * osc y ≤ P i j0 * (vmax y - y j0) := by
      rw [hj0]; exact mul_le_mul_of_nonneg_right (hε i j0) hosc
    linarith
  have hlo : ∀ i, vmin y + ε * osc y ≤ (P *ᵥ y) i := by
    intro i
    have h1 : ∑ j, P i j * (y j - vmin y) = (P *ᵥ y) i - vmin y := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul,
        mulVec_apply_eq]
    have h2 : P i j1 * (y j1 - vmin y) ≤ ∑ j, P i j * (y j - vmin y) :=
      single_le_sum (f := fun j => P i j * (y j - vmin y))
        (fun j _ => mul_nonneg (nonneg_of_mem_rowStochastic hP) (sub_nonneg.2 (vmin_le y j))) (mem_univ j1)
    have h3 : ε * osc y ≤ P i j1 * (y j1 - vmin y) := by
      rw [hj1]; exact mul_le_mul_of_nonneg_right (hε i j1) hosc
    linarith
  have h1 : vmax (P *ᵥ y) ≤ vmax y - ε * osc y := sup'_le _ _ fun i _ => hup i
  have h2 : vmin y + ε * osc y ≤ vmin (P *ᵥ y) := le_inf' _ _ fun i _ => hlo i
  unfold osc at *
  nlinarith

/-- `k` steps of the contraction: if `P^N` has all entries at least `ε`, with `0 < ε ≤ 1/2`, then
`osc ((P^N)^k y) ≤ (1 - 2ε)^k osc y`. -/
theorem osc_pow_le {Q : Matrix S S ℝ} (hQ : Q ∈ rowStochastic ℝ S) {ε : ℝ} (hε0 : ε ≤ 1 / 2)
    (hε : ∀ i j, ε ≤ Q i j) (y : S → ℝ) (k : ℕ) : osc (Q ^ k *ᵥ y) ≤ (1 - 2 * ε) ^ k * osc y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    calc osc (Q *ᵥ (Q ^ k *ᵥ y)) ≤ (1 - 2 * ε) * osc (Q ^ k *ᵥ y) :=
          osc_mulVec_le_of_entries_ge hQ hε _
      _ ≤ (1 - 2 * ε) * ((1 - 2 * ε) ^ k * osc y) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - 2 * ε) ^ (k + 1) * osc y := by ring

/-- For a stochastic `P` with `P^N` entrywise at least `ε` (`0 < ε ≤ 1/2`, `N > 0`), the oscillation of `P^n y`
tends to `0`. -/
theorem tendsto_osc_pow {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hε : ∀ i j, ε ≤ (P ^ N) i j) (y : S → ℝ) :
    Tendsto (fun n => osc (P ^ n *ᵥ y)) atTop (𝓝 0) := by
  have hc0 : 0 ≤ 1 - 2 * ε := by linarith
  have hc1 : 1 - 2 * ε < 1 := by linarith
  have hlim : Tendsto (fun n : ℕ => (1 - 2 * ε) ^ (n / N) * osc y) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp
      (Nat.tendsto_div_const_atTop hN.ne')).mul_const (osc y)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => osc_nonneg _) (fun n => ?_)
  have hn : P ^ n = (P ^ N) ^ (n / N) * P ^ (n % N) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  simp only
  rw [hn, ← mulVec_mulVec]
  calc osc ((P ^ N) ^ (n / N) *ᵥ (P ^ (n % N) *ᵥ y))
      ≤ (1 - 2 * ε) ^ (n / N) * osc (P ^ (n % N) *ᵥ y) :=
        osc_pow_le (pow_mem hP N) hε1 hε _ _
    _ ≤ (1 - 2 * ε) ^ (n / N) * osc y :=
        mul_le_mul_of_nonneg_left (osc_mulVec_le (pow_mem hP _) y) (pow_nonneg hc0 _)

/-- The columns `P^n y` of a power sequence converge to a constant vector, when `P^N` has entries bounded below by
`ε` (the second half of the proof of Theorem 11.13). -/
theorem exists_tendsto_mulVec_pow {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hε : ∀ i j, ε ≤ (P ^ N) i j) (y : S → ℝ) :
    ∃ L : ℝ, ∀ i, Tendsto (fun n => (P ^ n *ᵥ y) i) atTop (𝓝 L) := by
  set Mx : ℕ → ℝ := fun n => vmax (P ^ n *ᵥ y) with hMx
  set mn : ℕ → ℝ := fun n => vmin (P ^ n *ᵥ y) with hmn
  have hstep : ∀ n, P ^ (n + 1) *ᵥ y = P *ᵥ (P ^ n *ᵥ y) := by
    intro n; rw [pow_succ', mulVec_mulVec]
  have hMa : Antitone Mx := by
    refine antitone_nat_of_succ_le fun n => ?_
    simp only [hMx, hstep]
    exact sup'_le _ _ fun i _ => mulVec_le_vmax hP _ i
  have hma : Monotone mn := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [hmn, hstep]
    exact le_inf' _ _ fun i _ => vmin_le_mulVec hP _ i
  have hmM : ∀ n, mn n ≤ Mx n := fun n => vmin_le_vmax _
  have hbdd : BddBelow (Set.range Mx) := ⟨mn 0, by
    rintro _ ⟨n, rfl⟩; exact (hma (Nat.zero_le n)).trans (hmM n)⟩
  have hT := tendsto_atTop_ciInf hMa hbdd
  have hmT : Tendsto mn atTop (𝓝 (⨅ n, Mx n)) := by
    have := hT.sub (tendsto_osc_pow hP hN hε0 hε1 hε y)
    simpa [osc, hMx, hmn] using this
  refine ⟨⨅ n, Mx n, fun i => ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hmT hT (fun n => vmin_le _ i) (fun n => le_vmax _ i)

/-- Entry `(i, j)` of `P^(n+N)` is at least the smallest entry of column `j` of `P^N` (row `i` of `P^n` is a
probability vector). -/
theorem le_pow_add_apply {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {N : ℕ} {m : ℝ}
    (hm : ∀ k j, m ≤ (P ^ N) k j) (n : ℕ) (i j : S) : m ≤ (P ^ (n + N)) i j := by
  rw [pow_add, Matrix.mul_apply]
  have hn := pow_mem hP n
  calc m = ∑ k, (P ^ n) i k * m := by rw [← sum_mul, sum_row_of_mem_rowStochastic hn i, one_mul]
    _ ≤ ∑ k, (P ^ n) i k * (P ^ N) k j :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hm k j) (nonneg_of_mem_rowStochastic hn)

/-- Grinstead–Snell Theorem 11.7 (PR-117): for a regular chain the powers `P^n` converge to a matrix `W` all of whose
rows equal one strictly positive probability vector `w`: `(P^n)_{ij} → w_j` for every starting state `i`. -/
@[kb "grinsteadsnell2006" "Theorem 11.7, p. 442"]
theorem regular_pow_tendsto {P : Matrix S S ℝ} (h : IsRegularChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧
      ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j)) := by
  obtain ⟨hP, N, hN, hpos⟩ := h
  set m : ℝ := (univ : Finset (S × S)).inf' univ_nonempty (fun ij => (P ^ N) ij.1 ij.2) with hmdef
  have hm0 : 0 < m := (lt_inf'_iff _).2 fun ij _ => hpos ij.1 ij.2
  have hm : ∀ k j, m ≤ (P ^ N) k j := fun k j => inf'_le (fun ij : S × S => (P ^ N) ij.1 ij.2) (mem_univ (k, j))
  have hcol : ∀ j, ∃ L : ℝ, ∀ i, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 L) := by
    intro j
    obtain ⟨L, hL⟩ := exists_tendsto_mulVec_pow hP hN (ε := min m (1 / 2)) (lt_min hm0 (by norm_num))
      (min_le_right _ _) (fun i k => (min_le_left _ _).trans (hm i k)) (Pi.single j 1)
    refine ⟨L, fun i => ?_⟩
    convert hL i using 2 with n
    simp [mulVec, dotProduct, Pi.single_apply]
  choose w hw using hcol
  obtain ⟨i0⟩ := ‹Nonempty S›
  refine ⟨w, fun j => ?_, ?_, fun i j => hw j i⟩
  · have hlim : Tendsto (fun n => (P ^ (n + N)) i0 j) atTop (𝓝 (w j)) :=
      (hw j i0).comp (tendsto_add_atTop_nat N)
    exact hm0.trans_le (ge_of_tendsto' hlim fun n => le_pow_add_apply hP hm n i0 j)
  · have hlim : Tendsto (fun n => ∑ j, (P ^ n) i0 j) atTop (𝓝 (∑ j, w j)) :=
      tendsto_finsetSum _ fun j _ => hw j i0
    have hone : (fun n => ∑ j, (P ^ n) i0 j) = fun _ => (1 : ℝ) := by
      funext n; exact sum_row_of_mem_rowStochastic (pow_mem hP n) i0
    rw [hone] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- A probability vector `u` pushed through `P^n`: `(u P^n)_j → w_j` when every row of `P^n` tends to `w`. -/
theorem vecMul_pow_tendsto_of {P : Matrix S S ℝ} {w u : S → ℝ} (hu : ∑ i, u i = 1)
    (hw : ∀ i j, Tendsto (fun n => (P ^ n) i j) atTop (𝓝 (w j))) (j : S) :
    Tendsto (fun n => (u ᵥ* P ^ n) j) atTop (𝓝 (w j)) := by
  have h : Tendsto (fun n => ∑ i, u i * (P ^ n) i j) atTop (𝓝 (∑ i, u i * w j)) :=
    tendsto_finsetSum _ fun i _ => (hw i j).const_mul (u i)
  rw [← sum_mul, hu, one_mul] at h
  simpa [vecMul, dotProduct] using h

/-- If row `i0` of `P^n` tends to `w`, then `w` is a fixed row vector of `P`. -/
theorem isFixedRow_of_pow_tendsto {P : Matrix S S ℝ} {w : S → ℝ} {i0 : S}
    (hw : ∀ j, Tendsto (fun n => (P ^ n) i0 j) atTop (𝓝 (w j))) : IsFixedRow P w := by
  funext j
  have h1 : Tendsto (fun n => (P ^ (n + 1)) i0 j) atTop (𝓝 (w j)) :=
    (hw j).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => (P ^ (n + 1)) i0 j) atTop (𝓝 (∑ k, w k * P k j)) := by
    have : Tendsto (fun n => ∑ k, (P ^ n) i0 k * P k j) atTop (𝓝 (∑ k, w k * P k j)) :=
      tendsto_finsetSum _ fun k _ => (hw k).mul_const (P k j)
    refine this.congr fun n => ?_
    rw [pow_succ, Matrix.mul_apply]
  have := tendsto_nhds_unique h2 h1
  simpa [vecMul, dotProduct] using this

/-- Grinstead–Snell Theorem 11.8 (PR-117): for a regular chain the limiting row vector `w` is a fixed probability
vector (`w P = w`), and every fixed probability vector of `P` equals `w`. -/
@[kb "grinsteadsnell2006" "Theorem 11.8, p. 443"]
theorem regular_fixed_vector {P : Matrix S S ℝ} (h : IsRegularChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ v : S → ℝ, ∑ i, v i = 1 → IsFixedRow P v → v = w := by
  obtain ⟨w, hpos, hsum, hw⟩ := regular_pow_tendsto h
  refine ⟨w, hpos, hsum, ?_, fun v hv hfix => ?_⟩
  · obtain ⟨i0⟩ := ‹Nonempty S›
    exact isFixedRow_of_pow_tendsto (hw i0)
  · have hpow : ∀ n, v ᵥ* P ^ n = v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← vecMul_vecMul, ih]; exact hfix
    funext j
    have := vecMul_pow_tendsto_of hv hw j
    simp only [hpow] at this
    exact tendsto_nhds_unique tendsto_const_nhds this

/-- Grinstead–Snell Theorem 11.9 (PR-117): for a regular chain and any starting probability vector `u`, the
distribution `u P^n` after `n` steps tends to the fixed probability vector `w`. -/
@[kb "grinsteadsnell2006" "Theorem 11.9, p. 444"]
theorem regular_distribution_tendsto {P : Matrix S S ℝ} (h : IsRegularChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ u : S → ℝ, ∑ i, u i = 1 → ∀ j, Tendsto (fun n => (u ᵥ* P ^ n) j) atTop (𝓝 (w j)) := by
  obtain ⟨w, hpos, hsum, hw⟩ := regular_pow_tendsto h
  obtain ⟨i0⟩ := ‹Nonempty S›
  exact ⟨w, hpos, hsum, isFixedRow_of_pow_tendsto (hw i0), fun u hu j => vecMul_pow_tendsto_of hu hw j⟩

/-! ### Ergodic chains -/

/-- The lazy chain `(P + I) / 2` used in the book's proof of Theorem 11.10. -/
noncomputable def lazyChain (P : Matrix S S ℝ) : Matrix S S ℝ := (1 / 2 : ℝ) • (P + 1)

theorem lazyChain_mem {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) : lazyChain P ∈ rowStochastic ℝ S := by
  have h := convex_rowStochastic (R := ℝ) (n := S) hP (one_mem (rowStochastic ℝ S))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [lazyChain, smul_add] using h

/-- Entry `(i, j)` of `(P + I)^n` is at least `(P^k)_{ij}` for `k ≤ n` (binomial expansion). -/
theorem pow_apply_le_add_one_pow {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {k n : ℕ} (hk : k ≤ n)
    (i j : S) : (P ^ k) i j ≤ ((P + 1) ^ n) i j := by
  rw [(Commute.one_right P).add_pow, Matrix.sum_apply]
  have hterm : ∀ m ∈ range (n + 1), (P ^ m * 1 ^ (n - m) * (n.choose m : Matrix S S ℝ)) i j =
      (P ^ m) i j * n.choose m := by
    intro m _
    rw [one_pow, mul_one]
    simp [Matrix.mul_apply, Matrix.natCast_apply]
  rw [sum_congr rfl hterm]
  have hnn : ∀ m ∈ range (n + 1), 0 ≤ (P ^ m) i j * n.choose m := fun m _ =>
    mul_nonneg (nonneg_of_mem_rowStochastic (pow_mem hP m)) (Nat.cast_nonneg _)
  calc (P ^ k) i j ≤ (P ^ k) i j * n.choose k := by
        have : (1 : ℝ) ≤ n.choose k := by exact_mod_cast Nat.choose_pos hk
        nlinarith [nonneg_of_mem_rowStochastic (pow_mem hP k) (i := i) (j := j)]
    _ ≤ _ := single_le_sum hnn (mem_range.2 (Nat.lt_succ_of_le hk))

/-- The lazy chain of an ergodic chain is regular (Grinstead–Snell, proof of Theorem 11.10). -/
theorem IsErgodicChain.lazyChain_regular {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    IsRegularChain (lazyChain P) := by
  obtain ⟨hP, hirr⟩ := isErgodicChain_iff.1 h
  choose k hk0 hkpos using hirr
  set n := (univ : Finset (S × S)).sup fun ij => k ij.1 ij.2
  have hkn : ∀ i j, k i j ≤ n := fun i j => le_sup (f := fun ij : S × S => k ij.1 ij.2) (mem_univ (i, j))
  obtain ⟨i0⟩ := ‹Nonempty S›
  refine ⟨lazyChain_mem hP, n, (hk0 i0 i0).trans_le (hkn i0 i0), fun i j => ?_⟩
  rw [lazyChain, smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_pos (by positivity) ((hkpos i j).trans_le (pow_apply_le_add_one_pow hP (hkn i j) i j))

theorem isFixedRow_lazyChain_iff {P : Matrix S S ℝ} {v : S → ℝ} :
    IsFixedRow (lazyChain P) v ↔ IsFixedRow P v := by
  simp only [IsFixedRow, lazyChain, vecMul_smul, vecMul_add, vecMul_one, funext_iff, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  refine forall_congr' fun j => ?_
  constructor <;> intro h <;> linarith

/-- Grinstead–Snell Theorem 11.10 (PR-118): an ergodic chain has a unique fixed probability vector `w`
(`w P = w`, entries summing to `1`), and all its entries are strictly positive. -/
@[kb "grinsteadsnell2006" "Theorem 11.10, p. 446"]
theorem ergodic_fixed_vector {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ v : S → ℝ, ∑ i, v i = 1 → IsFixedRow P v → v = w := by
  obtain ⟨w, hpos, hsum, hfix, huniq⟩ := regular_fixed_vector h.lazyChain_regular
  exact ⟨w, hpos, hsum, isFixedRow_lazyChain_iff.1 hfix,
    fun v hv hvf => huniq v hv (isFixedRow_lazyChain_iff.2 hvf)⟩

/-- The Cesàro average `(1/n) ∑_{k<n} (P^k)_{ij}`. -/
noncomputable def cesaroAvg (P : Matrix S S ℝ) (n : ℕ) (i j : S) : ℝ := (∑ k ∈ range n, (P ^ k) i j) / n

theorem cesaroAvg_vecMul (P : Matrix S S ℝ) (n : ℕ) (i : S) :
    cesaroAvg P n i ᵥ* P = fun j => (∑ k ∈ range n, (P ^ (k + 1)) i j) / n := by
  funext j
  simp only [vecMul, dotProduct, cesaroAvg, div_mul_eq_mul_div, ← sum_div, sum_mul]
  rw [sum_comm]
  congr 1

/-- Grinstead–Snell Theorem 11.11 (PR-118): for an ergodic chain the averages `(I + P + ⋯ + P^{n-1}) / n`
converge to the matrix `W` whose rows all equal the fixed probability vector `w`. -/
@[kb "grinsteadsnell2006" "Theorem 11.11, p. 446"]
theorem ergodic_cesaro_tendsto {P : Matrix S S ℝ} (h : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧
      ∀ i j, Tendsto (fun n => cesaroAvg P n i j) atTop (𝓝 (w j)) := by
  obtain ⟨w, hpos, hsum, hfix, huniq⟩ := ergodic_fixed_vector h
  have hP := h.1
  refine ⟨w, hpos, hsum, hfix, fun i => ?_⟩
  rw [← tendsto_pi_nhds]
  set a : ℕ → S → ℝ := fun n => cesaroAvg P n i with ha
  set s : Set (S → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  have hs : IsCompact s := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, a n ∈ s := by
    intro n j _
    simp only [ha, cesaroAvg]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hnn : ∀ k, 0 ≤ (P ^ k) i j := fun k => nonneg_of_mem_rowStochastic (pow_mem hP k)
    have hle : ∀ k, (P ^ k) i j ≤ 1 := fun k => le_one_of_mem_rowStochastic (pow_mem hP k)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    constructor
    · exact div_nonneg (sum_nonneg fun k _ => hnn k) hnpos.le
    · rw [div_le_one hnpos]
      calc ∑ k ∈ range n, (P ^ k) i j ≤ ∑ k ∈ range n, (1 : ℝ) := sum_le_sum fun k _ => hle k
        _ = n := by simp
  refine hs.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem) fun x _ hx => ?_
  -- the cluster point has entries summing to one
  have hsum1 : x ∈ {y : S → ℝ | ∑ j, y j = 1} := by
    refine (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
      |>.mem_of_mapClusterPt hx ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [ha, cesaroAvg, ← sum_div]
    rw [sum_comm]
    have : ∀ k ∈ range n, ∑ j, (P ^ k) i j = 1 := fun k _ => sum_row_of_mem_rowStochastic (pow_mem hP k) i
    rw [sum_congr rfl this]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn))
  -- the cluster point is fixed: `a n - a n P → 0`
  set g : (S → ℝ) → (S → ℝ) := fun y => y - y ᵥ* P
  have hg : Continuous g := continuous_id.sub (continuous_id.matrix_vecMul continuous_const)
  have hglim : Tendsto (g ∘ a) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro j
    have hform : ∀ n, (g ∘ a) n j = ((P ^ 0) i j - (P ^ n) i j) / n := by
      intro n
      simp only [Function.comp_apply, g, Pi.sub_apply, ha, cesaroAvg_vecMul]
      rw [cesaroAvg, ← sub_div, ← sum_sub_distrib]
      congr 1
      have := sum_range_sub (fun k => (P ^ k) i j) n
      rw [sum_sub_distrib] at this ⊢
      linarith
    simp only [hform]
    have h0 : Tendsto (fun n : ℕ => (P ^ 0) i j / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Tendsto (fun n : ℕ => (P ^ n) i j / n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat 1) (fun n => ?_) (fun n => ?_)
      · exact div_nonneg (nonneg_of_mem_rowStochastic (pow_mem hP n)) (Nat.cast_nonneg _)
      · exact div_le_div_of_nonneg_right (le_one_of_mem_rowStochastic (pow_mem hP n)) (Nat.cast_nonneg _)
    simpa [sub_div] using h0.sub h1
  have hgx : g x = 0 := by
    have hc := hx.continuousAt_comp hg.continuousAt
    exact eq_of_nhds_neBot (ClusterPt.mono hc hglim)
  have hxfix : IsFixedRow P x := by
    have := sub_eq_zero.1 hgx
    exact this.symm
  exact huniq x hsum1 hxfix

end Osc

end UndergradKB.Probability
