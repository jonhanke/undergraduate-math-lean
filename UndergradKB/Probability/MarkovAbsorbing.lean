import UndergradKB.Probability.MarkovBasic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Absorbing Markov chains

Grinstead–Snell §11.2. A state `a` is absorbing when `P a a = 1`; a chain is absorbing when it has an absorbing state
and from every state some absorbing state can be reached. The non-absorbing states are transient. In the canonical form
of the book, `Q` is the transition matrix between transient states and `R` the matrix from transient to absorbing
states; here they are matrices indexed by the subtypes `Transient P` and `Absorbing P` of the state space.

Main results: `Q^n → 0` and absorption is certain (Theorem 11.3); the fundamental matrix `N = (I - Q)⁻¹ = I + Q + Q² + ⋯`
whose entries are expected numbers of visits (Theorem 11.4); expected absorption times `t = N c` (Theorem 11.5);
absorption probabilities `B = N R` (Theorem 11.6); harmonic functions are determined by their values on the absorbing
states (§11.2). -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Grinstead–Snell Definition 11.1 (PR-112): the state `i` is absorbing when the chain never leaves it, `P i i = 1`. -/
@[kb "grinsteadsnell2006" "Definition 11.1, p. 424"]
def IsAbsorbingState (P : Matrix S S ℝ) (i : S) : Prop := P i i = 1

noncomputable instance (P : Matrix S S ℝ) : DecidablePred (IsAbsorbingState P) :=
  fun i => inferInstanceAs (Decidable (P i i = 1))

/-- Grinstead–Snell Definition 11.1 (PR-112): a Markov chain is absorbing if it has at least one absorbing state and from every
state it is possible to reach an absorbing state (in some number of steps). -/
@[kb "grinsteadsnell2006" "Definition 11.1, p. 424"]
def IsAbsorbingChain (P : Matrix S S ℝ) : Prop :=
  (∃ a, IsAbsorbingState P a) ∧ ∀ i, ∃ n a, IsAbsorbingState P a ∧ 0 < (P ^ n) i a

/-- Grinstead–Snell Definition 11.2 (PR-112): the transient (non-absorbing) states of the chain. -/
@[kb "grinsteadsnell2006" "Definition 11.2, p. 424"]
abbrev Transient (P : Matrix S S ℝ) := {i : S // ¬ IsAbsorbingState P i}

/-- The absorbing states of the chain. -/
abbrev Absorbing (P : Matrix S S ℝ) := {i : S // IsAbsorbingState P i}

/-- The matrix `Q` of the canonical form: transition probabilities between transient states. -/
def absorbQ (P : Matrix S S ℝ) : Matrix (Transient P) (Transient P) ℝ := fun i j => P i j

/-- The matrix `R` of the canonical form: transition probabilities from transient to absorbing states. -/
def absorbR (P : Matrix S S ℝ) : Matrix (Transient P) (Absorbing P) ℝ := fun i a => P i a

/-- Grinstead–Snell Definition 11.3: the fundamental matrix `N = (I - Q)⁻¹` of an absorbing chain. -/
noncomputable def fundamentalMatrix (P : Matrix S S ℝ) : Matrix (Transient P) (Transient P) ℝ :=
  (1 - absorbQ P)⁻¹

variable {P : Matrix S S ℝ}

/-- From an absorbing state the chain moves to no other state. -/
theorem absorbing_row_eq_zero (hP : P ∈ rowStochastic ℝ S) {a j : S} (ha : IsAbsorbingState P a) (hj : j ≠ a) :
    P a j = 0 := by
  have hsum := sum_row_of_mem_rowStochastic hP a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hsum
  have h0 : ∑ x ∈ univ.erase a, P a x = 0 := by
    have : P a a = 1 := ha
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nonneg_of_mem_rowStochastic hP)] at h0
  exact h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)

omit [DecidableEq S] in
/-- Splitting a sum over the states into the absorbing and the transient states. -/
theorem sum_absorbing_add_transient (P : Matrix S S ℝ) (f : S → ℝ) :
    ∑ a : Absorbing P, f a + ∑ i : Transient P, f i = ∑ k, f k :=
  Fintype.sum_subtype_add_sum_subtype (IsAbsorbingState P) f

/-- Between transient states, the `n`-step transition probabilities are the entries of `Q^n`. -/
theorem pow_transient_eq (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i j : Transient P) :
    (P ^ n) i j = (absorbQ P ^ n) i j := by
  induction n generalizing j with
  | zero =>
    simp [Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, ← sum_absorbing_add_transient P]
    have h0 : ∑ a : Absorbing P, (P ^ n) i a * P a j = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [absorbing_row_eq_zero hP a.2 (fun h => j.2 (by rw [h]; exact a.2)), mul_zero]
    rw [h0, zero_add]
    exact Finset.sum_congr rfl fun k _ => by rw [ih k]; rfl

/-- From a transient state `i`, the probability of being in the absorbing state `a` after `n + 1` steps is the
probability of being there after `n` steps plus that of entering `a` at step `n + 1`. -/
theorem pow_succ_absorbing (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : Transient P) (a : Absorbing P) :
    (P ^ (n + 1)) i a = (absorbQ P ^ n * absorbR P) i a + (P ^ n) i a := by
  rw [pow_succ, Matrix.mul_apply, ← sum_absorbing_add_transient P, add_comm, Matrix.mul_apply]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by rw [pow_transient_eq hP]; rfl
  · rw [Finset.sum_eq_single a]
    · have : P a a = 1 := a.2
      rw [this, mul_one]
    · intro b _ hb
      rw [absorbing_row_eq_zero hP b.2 (fun h => hb (Subtype.ext h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

/-- From a transient state, the probability of being absorbed in `a` within `n` steps is `∑_{m < n} (Q^m R) i a`. -/
theorem pow_absorbing_eq_sum (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : Transient P) (a : Absorbing P) :
    (P ^ n) i a = ((∑ m ∈ range n, absorbQ P ^ m) * absorbR P) i a := by
  induction n with
  | zero =>
    have hia : (i : S) ≠ a := fun h => i.2 (by rw [h]; exact a.2)
    simp [Matrix.one_apply_ne hia]
  | succ n ih =>
    rw [pow_succ_absorbing hP, ih, sum_range_succ, Matrix.add_mul, Matrix.add_apply, add_comm]

theorem absorbQ_pow_nonneg (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i j : Transient P) :
    0 ≤ (absorbQ P ^ n) i j := by
  rw [← pow_transient_eq hP]
  exact nonneg_of_mem_rowStochastic (pow_mem hP n)

theorem absorbR_nonneg (hP : P ∈ rowStochastic ℝ S) (i : Transient P) (a : Absorbing P) :
    0 ≤ absorbR P i a :=
  nonneg_of_mem_rowStochastic hP

/-- From a transient state, the probability of being in a transient state plus the probability of being in an
absorbing state after `n` steps is one. -/
theorem sum_transient_add_absorbing (hP : P ∈ rowStochastic ℝ S) (n : ℕ) (i : Transient P) :
    ∑ j, (absorbQ P ^ n) i j + ∑ a : Absorbing P, (P ^ n) i a = 1 := by
  rw [← sum_row_of_mem_rowStochastic (pow_mem hP n) (i : S), ← sum_absorbing_add_transient P, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (pow_transient_eq hP n i j).symm

/-- Grinstead–Snell Theorem 11.3 (PR-113), the key estimate: in an absorbing chain the probability of still being in a
transient state after `n` steps, starting from a transient state, tends to `0`. -/
theorem transient_rowsum_tendsto_zero (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i₀ : Transient P) :
    Tendsto (fun n => ∑ j, (absorbQ P ^ n) i₀ j) atTop (𝓝 0) := by
  set r : ℕ → Transient P → ℝ := fun n i => ∑ j, (absorbQ P ^ n) i j with hr
  have hr0 : ∀ n i, 0 ≤ r n i := fun n i => Finset.sum_nonneg fun j _ => absorbQ_pow_nonneg hP n i j
  have hadd : ∀ m n i, r (m + n) i = ∑ k, (absorbQ P ^ m) i k * r n k := by
    intro m n i
    simp only [hr, pow_add, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have habs0 : ∀ n i, 0 ≤ ∑ a : Absorbing P, (P ^ n) i a :=
    fun n i => Finset.sum_nonneg fun a _ => nonneg_of_mem_rowStochastic (pow_mem hP n)
  have hle1 : ∀ n i, r n i ≤ 1 := by
    intro n i
    have := sum_transient_add_absorbing hP n i
    have := habs0 n i
    simp only [hr]; linarith
  have hanti : ∀ i, Antitone fun n => r n i := by
    intro i
    refine antitone_nat_of_succ_le fun n => ?_
    rw [hadd n 1 i]
    calc ∑ k, (absorbQ P ^ n) i k * r 1 k ≤ ∑ k, (absorbQ P ^ n) i k * 1 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hle1 1 k) (absorbQ_pow_nonneg hP n i k)
      _ = r n i := by simp [hr]
  have hex : ∀ i : Transient P, ∃ m, r m i < 1 := by
    intro i
    obtain ⟨n, a, ha, hpos⟩ := hA.2 i
    refine ⟨n, ?_⟩
    have h1 := sum_transient_add_absorbing hP n i
    have h2 : (P ^ n) i a ≤ ∑ b : Absorbing P, (P ^ n) i b :=
      Finset.single_le_sum (f := fun b : Absorbing P => (P ^ n) i b)
        (fun b _ => nonneg_of_mem_rowStochastic (pow_mem hP n)) (Finset.mem_univ ⟨a, ha⟩)
    simp only [hr]; linarith
  choose m hm using hex
  set M := univ.sup m + 1 with hM
  have hMpos : M ≠ 0 := by omega
  have hMlt : ∀ i, r M i < 1 := fun i =>
    lt_of_le_of_lt (hanti i (by have := Finset.le_sup (f := m) (Finset.mem_univ i); omega)) (hm i)
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image univ (fun i => r M i) ⟨i₀, Finset.mem_univ _⟩
  set c := r M i₁
  have hc0 : 0 ≤ c := hr0 M i₁
  have hc1 : c < 1 := hMlt i₁
  have hgeom : ∀ k i, r (k * M) i ≤ c ^ k := by
    intro k
    induction k with
    | zero => intro i; simpa using hle1 0 i
    | succ k ih =>
      intro i
      rw [show (k + 1) * M = M + k * M by ring, hadd]
      calc ∑ l, (absorbQ P ^ M) i l * r (k * M) l ≤ ∑ l, (absorbQ P ^ M) i l * c ^ k :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (ih l) (absorbQ_pow_nonneg hP M i l)
        _ = r M i * c ^ k := by simp [hr, Finset.sum_mul]
        _ ≤ c * c ^ k := mul_le_mul_of_nonneg_right (hi₁ i (Finset.mem_univ i)) (pow_nonneg hc0 k)
        _ = c ^ (k + 1) := by ring
  have hlim : Tendsto (fun n => c ^ (n / M)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp (Nat.tendsto_div_const_atTop hMpos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => hr0 n i₀) fun n => ?_
  exact le_trans (hanti i₀ (Nat.div_mul_le_self n M)) (hgeom (n / M) i₀)

/-- Grinstead–Snell Theorem 11.3 (PR-113): in an absorbing Markov chain, `Q^n → 0` as `n → ∞`. -/
@[kb "grinsteadsnell2006" "Theorem 11.3, p. 425"]
theorem absorbQ_pow_tendsto_zero (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) :
    Tendsto (fun n => absorbQ P ^ n) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (transient_rowsum_tendsto_zero hP hA i) (fun n => absorbQ_pow_nonneg hP n i j) fun n => ?_
  exact Finset.single_le_sum (f := fun j => (absorbQ P ^ n) i j)
    (fun k _ => absorbQ_pow_nonneg hP n i k) (Finset.mem_univ j)

/-- Grinstead–Snell Theorem 11.3 (PR-113): in an absorbing Markov chain the process is absorbed with probability one:
starting from any state, the probability of being in an absorbing state after `n` steps tends to `1`. -/
@[kb "grinsteadsnell2006" "Theorem 11.3, p. 425"]
theorem absorption_certain (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : S) :
    Tendsto (fun n => ∑ a : Absorbing P, (P ^ n) i a) atTop (𝓝 1) := by
  by_cases hi : IsAbsorbingState P i
  · refine tendsto_const_nhds.congr fun n => ?_
    -- from an absorbing state the chain stays there
    have hstay : ∀ n, (P ^ n) i i = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
        · rw [ih]; exact (one_mul _).trans hi
        · intro b _ hb
          have : (P ^ n) i b = 0 := by
            have h1 := sum_row_of_mem_rowStochastic (pow_mem hP n) i
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ih] at h1
            have h2 : ∑ x ∈ univ.erase i, (P ^ n) i x = 0 := by linarith
            rw [Finset.sum_eq_zero_iff_of_nonneg
              (fun x _ => nonneg_of_mem_rowStochastic (pow_mem hP n))] at h2
            exact h2 b (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩)
          rw [this, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
    have hrow := sum_row_of_mem_rowStochastic (pow_mem hP n) i
    rw [← sum_absorbing_add_transient P] at hrow
    have ht : ∑ j : Transient P, (P ^ n) i j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have h1 := sum_row_of_mem_rowStochastic (pow_mem hP n) i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hstay n] at h1
      have h2 : ∑ x ∈ univ.erase i, (P ^ n) i x = 0 := by linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nonneg_of_mem_rowStochastic (pow_mem hP n))] at h2
      exact h2 j (Finset.mem_erase.2 ⟨fun h => j.2 (h ▸ hi), Finset.mem_univ _⟩)
    linarith
  · have h := transient_rowsum_tendsto_zero hP hA ⟨i, hi⟩
    have : (fun n => ∑ a : Absorbing P, (P ^ n) i a) = fun n => 1 - ∑ j, (absorbQ P ^ n) ⟨i, hi⟩ j := by
      funext n
      have := sum_transient_add_absorbing hP n ⟨i, hi⟩
      linarith
    rw [this]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- In an absorbing chain the matrix `I - Q` is invertible. -/
theorem isUnit_one_sub_absorbQ (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) :
    IsUnit (1 - absorbQ P) := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  set z := x - y
  have hz : (1 - absorbQ P) *ᵥ z = 0 := by
    simp only [z, mulVec_sub, hxy, sub_self]
  have hQz : absorbQ P *ᵥ z = z := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hz
    exact hz.symm
  have hpow : ∀ n, absorbQ P ^ n *ᵥ z = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, hQz]
  have hlim : Tendsto (fun n => absorbQ P ^ n *ᵥ z) atTop (𝓝 ((0 : Matrix (Transient P) (Transient P) ℝ) *ᵥ z)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto _).comp (absorbQ_pow_tendsto_zero hP hA)
  simp only [hpow, zero_mulVec] at hlim
  have : z = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  exact sub_eq_zero.1 this

/-- The partial sums `I + Q + ⋯ + Q^(n-1)` tend to the fundamental matrix. -/
theorem tendsto_sum_absorbQ_pow (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) :
    Tendsto (fun n => ∑ k ∈ range n, absorbQ P ^ k) atTop (𝓝 (fundamentalMatrix P)) := by
  have hdet : IsUnit (1 - absorbQ P).det := (isUnit_iff_isUnit_det _).1 (isUnit_one_sub_absorbQ hP hA)
  have heq : ∀ n, ∑ k ∈ range n, absorbQ P ^ k = (1 - absorbQ P ^ n) * fundamentalMatrix P := by
    intro n
    rw [← geom_sum_mul_neg, mul_assoc, fundamentalMatrix, mul_nonsing_inv _ hdet, mul_one]
  simp only [heq]
  have h1 : Tendsto (fun n => 1 - absorbQ P ^ n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (absorbQ_pow_tendsto_zero hP hA)
  simpa using h1.mul_const (fundamentalMatrix P)

/-- Grinstead–Snell Theorem 11.4 and Definition 11.3 (PR-114): for an absorbing chain the matrix `I - Q` has an
inverse `N = (I - Q)⁻¹`, and `N = I + Q + Q² + ⋯` (the partial sums converge to `N`). -/
@[kb "grinsteadsnell2006" "Theorem 11.4, p. 426"]
theorem fundamentalMatrix_spec (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) :
    (1 - absorbQ P) * fundamentalMatrix P = 1 ∧ fundamentalMatrix P * (1 - absorbQ P) = 1 ∧
      Tendsto (fun n => ∑ k ∈ range n, absorbQ P ^ k) atTop (𝓝 (fundamentalMatrix P)) := by
  have hdet : IsUnit (1 - absorbQ P).det := (isUnit_iff_isUnit_det _).1 (isUnit_one_sub_absorbQ hP hA)
  exact ⟨mul_nonsing_inv _ hdet, nonsing_inv_mul _ hdet, tendsto_sum_absorbQ_pow hP hA⟩

/-- Grinstead–Snell Theorem 11.4 (PR-114): the entry `N i j` of the fundamental matrix is the expected number of times
the chain started in the transient state `i` is in the transient state `j`: the series of the probabilities
`P(X_k = j)` (by linearity of expectation, the expected number of visits) sums to `N i j`. -/
@[kb "grinsteadsnell2006" "Theorem 11.4, p. 426"]
theorem hasSum_visits (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i j : Transient P) :
    HasSum (fun k => (P ^ k) i j) (fundamentalMatrix P i j) := by
  simp only [pow_transient_eq hP]
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => absorbQ_pow_nonneg hP k i j)]
  have h := tendsto_sum_absorbQ_pow hP hA
  have h' := (continuous_apply j).tendsto _ |>.comp ((continuous_apply i).tendsto _ |>.comp h)
  refine h'.congr fun n => ?_
  simp [Function.comp, Matrix.sum_apply]

/-- Grinstead–Snell Theorem 11.5 (PR-114): starting in the transient state `i`, the expected number of steps before
absorption, `∑_k P(the chain is still in a transient state at step k)`, is `t i = ∑_j N i j`, i.e. `t = N c` with
`c` the column of ones. -/
@[kb "grinsteadsnell2006" "Theorem 11.5, p. 427"]
theorem hasSum_absorption_time (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : Transient P) :
    HasSum (fun k => ∑ j : Transient P, (P ^ k) i j) ((fundamentalMatrix P *ᵥ fun _ => 1) i) := by
  have : (fundamentalMatrix P *ᵥ fun _ => 1) i = ∑ j, fundamentalMatrix P i j := by
    simp [mulVec, dotProduct]
  rw [this]
  exact hasSum_sum fun j _ => hasSum_visits hP hA i j

/-- Grinstead–Snell Theorem 11.6 (PR-114): starting in the transient state `i`, the probability of being absorbed in
the absorbing state `a` (the limit of the probabilities of being in `a` after `n` steps) is the entry `B i a` of
`B = N R`. -/
@[kb "grinsteadsnell2006" "Theorem 11.6, p. 428"]
theorem absorption_prob_tendsto (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : Transient P)
    (a : Absorbing P) :
    Tendsto (fun n => (P ^ n) i a) atTop (𝓝 ((fundamentalMatrix P * absorbR P) i a)) := by
  simp only [pow_absorbing_eq_sum hP]
  have h2 : Tendsto (fun n => (∑ k ∈ range n, absorbQ P ^ k) * absorbR P) atTop
      (𝓝 (fundamentalMatrix P * absorbR P)) :=
    ((continuous_id.matrix_mul (continuous_const (y := absorbR P))).tendsto _).comp
      (tendsto_sum_absorbQ_pow hP hA)
  exact (continuous_apply a).tendsto _ |>.comp ((continuous_apply i).tendsto _ |>.comp h2)

/-- Grinstead–Snell Theorem 11.6 (PR-114): the absorption probabilities from a transient state sum to one. -/
@[kb "grinsteadsnell2006" "Theorem 11.6, p. 428"]
theorem sum_absorption_prob (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (i : Transient P) :
    ∑ a, (fundamentalMatrix P * absorbR P) i a = 1 :=
  tendsto_nhds_unique (tendsto_finsetSum _ fun a _ => absorption_prob_tendsto hP hA i a)
    (absorption_certain hP hA i)

/-- Grinstead–Snell §11.2 harmonic function (PR-123): in an absorbing chain a function `f` on the states with
`P f = f` (a harmonic function) is determined by its values on the absorbing states: `f i = ∑_a B i a f a` for every
transient state `i`, with `B = N R` the absorption probabilities. -/
@[kb "grinsteadsnell2006" "§11.2 harmonic function, p. 436"]
theorem harmonic_eq_absorption (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) {f : S → ℝ}
    (hf : P *ᵥ f = f) (i : Transient P) :
    f i = ∑ a : Absorbing P, (fundamentalMatrix P * absorbR P) i a * f a := by
  set fT : Transient P → ℝ := fun j => f j
  set fA : Absorbing P → ℝ := fun a => f a
  have hT : fT = absorbQ P *ᵥ fT + absorbR P *ᵥ fA := by
    funext j
    have := congrFun hf j
    simp only [mulVec, dotProduct] at this
    rw [← sum_absorbing_add_transient P] at this
    simp only [fT, fA, Pi.add_apply, mulVec, dotProduct, absorbQ, absorbR]
    linarith
  have h1 : (1 - absorbQ P) *ᵥ fT = absorbR P *ᵥ fA := by
    rw [sub_mulVec, one_mulVec]
    nth_rewrite 1 [hT]
    abel
  have hdet : IsUnit (1 - absorbQ P).det := (isUnit_iff_isUnit_det _).1 (isUnit_one_sub_absorbQ hP hA)
  have h2 : fT = (fundamentalMatrix P * absorbR P) *ᵥ fA := by
    rw [← mulVec_mulVec, ← h1, mulVec_mulVec, fundamentalMatrix, nonsing_inv_mul _ hdet, one_mulVec]
  have := congrFun h2 i
  simpa [fT, fA, mulVec, dotProduct] using this

end UndergradKB.Probability
