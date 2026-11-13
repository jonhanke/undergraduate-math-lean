import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Choose.Sum
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovPassage

/-! # Worked examples on Markov chains (drunkard's walk, ergodic chains that are not regular)

Grinstead–Snell chapter 11: the drunkard's walk (Examples 11.13–11.15), the two-state flip chain (Example 11.16)
and the Ehrenfest urn (Examples 11.8, 11.17, 11.23). -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

/-! ## Drunkard's walk -/

/-- Grinstead–Snell Example 11.13 (PR-144): the drunkard's walk on the states `0, …, 4`; the states `0` and `4`
are absorbing and otherwise the walker steps left or right with probability `1/2`. -/
@[kb "grinsteadsnell2006" "Example 11.13, p. 424"]
noncomputable def drunkP : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 1/2, 0, 1/2, 0, 0; 0, 1/2, 0, 1/2, 0; 0, 0, 1/2, 0, 1/2; 0, 0, 0, 0, 1]

theorem drunkP_mem : drunkP ∈ rowStochastic ℝ (Fin 5) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [drunkP]
  · fin_cases i <;> simp [drunkP, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.13 (PR-144): the drunkard's walk is an absorbing chain (the states `0` and `4`
are absorbing and every state can reach one of them). -/
@[kb "grinsteadsnell2006" "Example 11.13, p. 424"]
theorem drunkP_isAbsorbingChain : IsAbsorbingChain drunkP := by
  have h0 : IsAbsorbingState drunkP 0 := by simp [IsAbsorbingState, drunkP]
  have h4 : IsAbsorbingState drunkP 4 := by simp [IsAbsorbingState, drunkP]
  refine ⟨⟨0, h0⟩, fun i => ?_⟩
  fin_cases i
  · exact ⟨0, 0, h0, by simp⟩
  · exact ⟨1, 0, h0, by simp [drunkP]⟩
  · exact ⟨2, 0, h0, by simp [pow_two, drunkP, Matrix.mul_apply, Fin.sum_univ_succ]⟩
  · exact ⟨1, 4, h4, by simp [drunkP]⟩
  · exact ⟨0, 4, h4, by simp⟩

/-- The state `i + 1` of the drunkard's walk, `i = 0, 1, 2`. -/
def drunkS (i : Fin 3) : Fin 5 := ⟨i.1 + 1, by omega⟩

/-- The transient state `i + 1` of the drunkard's walk, `i = 0, 1, 2`. -/
def drunkT (i : Fin 3) : Transient drunkP :=
  ⟨drunkS i, by fin_cases i <;> simp [drunkS, IsAbsorbingState, drunkP]⟩

/-- The transient states of the drunkard's walk are `1, 2, 3`: an equivalence with `Fin 3`. -/
noncomputable def drunkEquiv : Fin 3 ≃ Transient drunkP :=
  Equiv.ofBijective drunkT
    ⟨fun a b h => by
      have := congrArg (fun x : Transient drunkP => (x.1 : ℕ)) h
      exact Fin.ext (by simpa [drunkT, drunkS] using this), by
      rintro ⟨a, ha⟩
      fin_cases a
      · simp [IsAbsorbingState, drunkP] at ha
      · exact ⟨0, Subtype.ext rfl⟩
      · exact ⟨1, Subtype.ext rfl⟩
      · exact ⟨2, Subtype.ext rfl⟩
      · simp [IsAbsorbingState, drunkP] at ha⟩

theorem drunkEquiv_val (i : Fin 3) : (drunkEquiv i).1 = drunkS i := rfl

/-- The matrix `N` of Example 11.14. -/
noncomputable def drunkN : Matrix (Fin 3) (Fin 3) ℝ := !![3/2, 1, 1/2; 1, 2, 1; 1/2, 1, 3/2]

/-- The matrix `Q` of the canonical form of the drunkard's walk, on the transient states `1, 2, 3`. -/
noncomputable def drunkQ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1/2, 0; 1/2, 0, 1/2; 0, 1/2, 0]

theorem drunkQ_mul : (1 - drunkQ) * drunkN = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [drunkQ, drunkN, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three] <;> norm_num

theorem drunkEquiv_absorbQ (i j : Fin 3) :
    absorbQ drunkP (drunkEquiv i) (drunkEquiv j) = drunkQ i j := by
  show drunkP (drunkS i) (drunkS j) = drunkQ i j
  fin_cases i <;> fin_cases j <;> simp [drunkS, drunkQ, drunkP]

theorem drunk_fundamental_apply (i j : Fin 3) :
    fundamentalMatrix drunkP (drunkEquiv i) (drunkEquiv j) = drunkN i j := by
  have hspec := (fundamentalMatrix_spec drunkP_mem drunkP_isAbsorbingChain).1
  set N' : Matrix (Fin 3) (Fin 3) ℝ := (fundamentalMatrix drunkP).submatrix drunkEquiv drunkEquiv with hN'
  have hQ : (1 - absorbQ drunkP).submatrix drunkEquiv drunkEquiv = 1 - drunkQ := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, drunkEquiv_absorbQ]
  have h1 : (1 - drunkQ) * N' = 1 := by
    rw [← hQ, hN', Matrix.submatrix_mul_equiv, hspec, Matrix.submatrix_one_equiv]
  have e1 : (1 - drunkQ)⁻¹ = N' := Matrix.inv_eq_right_inv h1
  have e2 : (1 - drunkQ)⁻¹ = drunkN := Matrix.inv_eq_right_inv drunkQ_mul
  have : N' = drunkN := e1.symm.trans e2
  simpa [hN'] using congrFun (congrFun this i) j

/-- Grinstead–Snell Example 11.14 (PR-144): the fundamental matrix of the drunkard's walk, on the transient
states `1, 2, 3`, is `N = [[3/2, 1, 1/2], [1, 2, 1], [1/2, 1, 3/2]]`. -/
@[kb "grinsteadsnell2006" "Example 11.14, p. 427"]
theorem drunk_fundamentalMatrix (i j : Fin 3) :
    fundamentalMatrix drunkP (drunkEquiv i) (drunkEquiv j) =
      (!![3/2, 1, 1/2; 1, 2, 1; 1/2, 1, 3/2] : Matrix (Fin 3) (Fin 3) ℝ) i j :=
  drunk_fundamental_apply i j

/-- Grinstead–Snell Example 11.14 (PR-144): the expected number of steps before absorption `t = N 1` from the
states `1, 2, 3` is `(3, 4, 3)`. -/
@[kb "grinsteadsnell2006" "Example 11.14, p. 427"]
theorem drunk_absorption_time (i : Fin 3) :
    HasSum (fun k => ∑ j : Transient drunkP, (drunkP ^ k) (drunkEquiv i) j) (![3, 4, 3] i : ℝ) := by
  have h := hasSum_absorption_time drunkP_mem drunkP_isAbsorbingChain (drunkEquiv i)
  have e : (fundamentalMatrix drunkP *ᵥ fun _ => (1 : ℝ)) (drunkEquiv i) = (![3, 4, 3] i : ℝ) := by
    simp only [mulVec, dotProduct, mul_one]
    rw [← Equiv.sum_comp drunkEquiv]
    simp only [drunk_fundamental_apply]
    fin_cases i <;> simp [drunkN, Fin.sum_univ_three] <;> norm_num
  rwa [e] at h

theorem drunk_absorbing_apply (a : Fin 5) (ha : IsAbsorbingState drunkP a) (i : Fin 3) :
    (fundamentalMatrix drunkP * absorbR drunkP) (drunkEquiv i) ⟨a, ha⟩ =
      ∑ j : Fin 3, drunkN i j * drunkP (drunkS j) a := by
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp drunkEquiv]
  simp only [drunk_fundamental_apply, absorbR, drunkEquiv_val]

/-- Grinstead–Snell Example 11.15 (PR-144): the probabilities of absorption at `0`, starting at `1, 2, 3`,
are `(3/4, 1/2, 1/4)` (the first column of `B = N R`); `P^n` converges to them. -/
@[kb "grinsteadsnell2006" "Example 11.15, p. 428"]
theorem drunk_absorption_zero (i : Fin 3) :
    Tendsto (fun n => (drunkP ^ n) (drunkS i) 0) atTop (𝓝 (![3/4, 1/2, 1/4] i : ℝ)) := by
  have h0 : IsAbsorbingState drunkP 0 := by simp [IsAbsorbingState, drunkP]
  have h := absorption_prob_tendsto drunkP_mem drunkP_isAbsorbingChain (drunkEquiv i) ⟨0, h0⟩
  rw [drunk_absorbing_apply 0 h0 i] at h
  have e : ∑ j : Fin 3, drunkN i j * drunkP (drunkS j) 0 = (![3/4, 1/2, 1/4] i : ℝ) := by
    fin_cases i <;> simp [drunkN, drunkP, drunkS, Fin.sum_univ_three] <;> norm_num
  rw [e] at h
  exact h

/-- Grinstead–Snell Example 11.15 (PR-144): the probabilities of absorption at `4`, starting at `1, 2, 3`,
are `(1/4, 1/2, 3/4)` (the second column of `B = N R`). -/
@[kb "grinsteadsnell2006" "Example 11.15, p. 428"]
theorem drunk_absorption_four (i : Fin 3) :
    Tendsto (fun n => (drunkP ^ n) (drunkS i) 4) atTop (𝓝 (![1/4, 1/2, 3/4] i : ℝ)) := by
  have h4 : IsAbsorbingState drunkP 4 := by simp [IsAbsorbingState, drunkP]
  have h := absorption_prob_tendsto drunkP_mem drunkP_isAbsorbingChain (drunkEquiv i) ⟨4, h4⟩
  rw [drunk_absorbing_apply 4 h4 i] at h
  have e : ∑ j : Fin 3, drunkN i j * drunkP (drunkS j) 4 = (![1/4, 1/2, 3/4] i : ℝ) := by
    fin_cases i <;> simp [drunkN, drunkP, drunkS, Fin.sum_univ_three] <;> norm_num
  rw [e] at h
  exact h

/-! ## The flip chain -/

/-- The two-state flip chain of Example 11.16. -/
noncomputable def flipChain : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem flipChain_mem : flipChain ∈ rowStochastic ℝ (Fin 2) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [flipChain]
  · fin_cases i <;> simp [flipChain, Fin.sum_univ_succ]

theorem flipChain_sq : flipChain ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, flipChain, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Grinstead–Snell Example 11.16 (PR-145): the chain `[[0,1],[1,0]]` is ergodic but not regular. -/
@[kb "grinsteadsnell2006" "Example 11.16, p. 441"]
theorem flipChain_ergodic_not_regular : IsErgodicChain flipChain ∧ ¬ IsRegularChain flipChain := by
  constructor
  · rw [isErgodicChain_iff]
    refine ⟨flipChain_mem, fun i j => ?_⟩
    by_cases h : i = j
    · subst h
      exact ⟨2, by norm_num, by rw [flipChain_sq]; simp⟩
    · refine ⟨1, by norm_num, ?_⟩
      fin_cases i <;> fin_cases j <;> simp [flipChain] at h ⊢
  · rintro ⟨-, N, hN, hpos⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
    · have := hpos 0 1
      rw [pow_mul, flipChain_sq, one_pow] at this
      simp at this
    · have := hpos 0 0
      rw [pow_succ, pow_mul, flipChain_sq, one_pow, one_mul] at this
      simp [flipChain] at this

/-! ## Ehrenfest urn -/

/-- Grinstead–Snell Example 11.8 (PR-145): the Ehrenfest urn chain with `n` balls; the state is the number of balls
in the first urn, `i → i - 1` with probability `i / n` and `i → i + 1` with probability `(n - i) / n`. -/
@[kb "grinsteadsnell2006" "Example 11.8, p. 418"]
noncomputable def ehrenfest (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  if (j : ℕ) + 1 = i then (i : ℝ) / n else if (j : ℕ) = i + 1 then ((n : ℝ) - i) / n else 0

/-- Grinstead–Snell Example 11.8 (PR-145): with four balls the Ehrenfest matrix is the matrix printed in the
book. -/
@[kb "grinsteadsnell2006" "Example 11.8, p. 418"]
theorem ehrenfest_four :
    ehrenfest 4 = !![0, 1, 0, 0, 0; 1/4, 0, 3/4, 0, 0; 0, 1/2, 0, 1/2, 0; 0, 0, 3/4, 0, 1/4; 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ehrenfest] <;> norm_num

variable {n : ℕ}

theorem ehrenfest_nonneg (i j : Fin (n + 1)) : 0 ≤ ehrenfest n i j := by
  have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 i.isLt
  unfold ehrenfest
  split_ifs
  · positivity
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact le_refl _

theorem ehrenfest_rowsum (hn : 1 ≤ n) (i : Fin (n + 1)) : ∑ j, ehrenfest n i j = 1 := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.isLt
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have key : ∑ j : Fin (n + 1), ehrenfest n i j =
      ∑ j ∈ range (n + 1), ((if j + 1 = (i : ℕ) then ((i : ℕ) : ℝ) / n else 0) +
        (if j = (i : ℕ) + 1 then ((n : ℝ) - (i : ℕ)) / n else 0)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ((if j + 1 = (i : ℕ) then ((i : ℕ) : ℝ) / n else 0) +
        (if j = (i : ℕ) + 1 then ((n : ℝ) - (i : ℕ)) / n else 0))) (n + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold ehrenfest
    by_cases h1 : (j : ℕ) + 1 = i
    · have : ¬ (j : ℕ) = i + 1 := by omega
      simp [h1, this]
    · simp [h1]
  rw [key, Finset.sum_add_distrib]
  generalize hm : (i : ℕ) = m at hi
  have s1 : ∑ j ∈ range (n + 1), (if j + 1 = m then (m : ℝ) / n else 0) = (m : ℝ) / n := by
    rcases m with _ | m
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq']
      simp
      omega
  have s2 : ∑ j ∈ range (n + 1), (if j = m + 1 then ((n : ℝ) - m) / n else 0) = ((n : ℝ) - m) / n := by
    rw [Finset.sum_ite_eq']
    by_cases h : m + 1 ∈ range (n + 1)
    · simp [h]
    · have : m = n := by simp at h; omega
      subst this
      simp [h]
  rw [s1, s2]
  field_simp
  ring

/-- Grinstead–Snell Example 11.8 (PR-145): the Ehrenfest chain is a transition matrix. -/
@[kb "grinsteadsnell2006" "Example 11.8, p. 418"]
theorem ehrenfest_mem (hn : 1 ≤ n) : ehrenfest n ∈ rowStochastic ℝ (Fin (n + 1)) := by
  rw [mem_rowStochastic_iff_sum]
  exact ⟨fun i j => ehrenfest_nonneg i j, ehrenfest_rowsum hn⟩

theorem ehrenfest_step_down (hn : 1 ≤ n) {i j : Fin (n + 1)} (h : (j : ℕ) + 1 = i) : 0 < ehrenfest n i j := by
  have h0 : (0 : ℝ) < ((i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (i : ℕ))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ehrenfest
  rw [if_pos h]
  exact div_pos h0 hn'

theorem ehrenfest_step_up (hn : 1 ≤ n) {i j : Fin (n + 1)} (h : (j : ℕ) = i + 1) : 0 < ehrenfest n i j := by
  have h1 : ((i : ℕ) : ℝ) < n := by exact_mod_cast (by have := j.isLt; omega : (i : ℕ) < n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : ¬ (j : ℕ) + 1 = i := by omega
  unfold ehrenfest
  rw [if_neg this, if_pos h]
  exact div_pos (by linarith) hn'

/-- If `0 < (P^k) a b` and `0 < (P^l) b c` then `0 < (P^(k+l)) a c`. -/
theorem pow_add_pos {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S)
    {k l : ℕ} {a b c : S} (h1 : 0 < (P ^ k) a b) (h2 : 0 < (P ^ l) b c) : 0 < (P ^ (k + l)) a c := by
  rw [pow_add, Matrix.mul_apply]
  have hk : ∀ x y, 0 ≤ (P ^ k) x y := fun x y => nonneg_of_mem_rowStochastic (pow_mem hP k)
  have hl : ∀ x y, 0 ≤ (P ^ l) x y := fun x y => nonneg_of_mem_rowStochastic (pow_mem hP l)
  calc 0 < (P ^ k) a b * (P ^ l) b c := mul_pos h1 h2
    _ ≤ ∑ m, (P ^ k) a m * (P ^ l) m c :=
        Finset.single_le_sum (f := fun m => (P ^ k) a m * (P ^ l) m c) (fun m _ => mul_nonneg (hk _ _) (hl _ _))
          (Finset.mem_univ b)

theorem ehrenfest_reach_up (hn : 1 ≤ n) : ∀ d : ℕ, ∀ i j : Fin (n + 1), (j : ℕ) = i + d →
    ∃ k, 0 < (ehrenfest n ^ k) i j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨0, by simp⟩
  | succ d ih =>
    intro i j h
    obtain ⟨k, hk⟩ := ih i ⟨i + d, by have := j.isLt; omega⟩ rfl
    refine ⟨k + 1, ?_⟩
    have hs : 0 < (ehrenfest n ^ 1) ⟨i + d, by have := j.isLt; omega⟩ j := by
      rw [pow_one]
      exact ehrenfest_step_up hn (by simp; omega)
    exact pow_add_pos (ehrenfest_mem hn) hk hs

theorem ehrenfest_reach_down (hn : 1 ≤ n) : ∀ d : ℕ, ∀ i j : Fin (n + 1), (i : ℕ) = j + d →
    ∃ k, 0 < (ehrenfest n ^ k) i j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨0, by simp⟩
  | succ d ih =>
    intro i j h
    obtain ⟨k, hk⟩ := ih ⟨j + d, by have := i.isLt; omega⟩ j rfl
    refine ⟨1 + k, ?_⟩
    have hs : 0 < (ehrenfest n ^ 1) i ⟨j + d, by have := i.isLt; omega⟩ := by
      rw [pow_one]
      exact ehrenfest_step_down hn (by simp; omega)
    exact pow_add_pos (ehrenfest_mem hn) hs hk

theorem ehrenfest_reach (hn : 1 ≤ n) (i j : Fin (n + 1)) : ∃ k, 0 < (ehrenfest n ^ k) i j := by
  rcases le_total (i : ℕ) j with h | h
  · exact ehrenfest_reach_up hn (j - i) i j (by omega)
  · exact ehrenfest_reach_down hn (i - j) i j (by omega)

/-- If `P^k a b ≠ 0` then `a + b + k` is even (the Ehrenfest chain moves one step at a time). -/
theorem ehrenfest_parity : ∀ (k : ℕ) (i j : Fin (n + 1)), (ehrenfest n ^ k) i j ≠ 0 → ((i : ℕ) + j + k) % 2 = 0 := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have : i = j := by
      by_contra hij
      exact h (by simp [hij])
    subst this
    omega
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (ehrenfest n ^ k) i m ≠ 0 := left_ne_zero_of_mul hm
    have h2 : ehrenfest n m j ≠ 0 := right_ne_zero_of_mul hm
    have h3 : (j : ℕ) + 1 = m ∨ (j : ℕ) = m + 1 := by
      by_contra hc
      rw [not_or] at hc
      unfold ehrenfest at h2
      rw [if_neg hc.1, if_neg hc.2] at h2
      exact h2 rfl
    have := ih i m h1
    omega

/-- Grinstead–Snell Example 11.17 (PR-145): the Ehrenfest urn chain with `n ≥ 1` balls is ergodic but not
regular. -/
@[kb "grinsteadsnell2006" "Example 11.17, p. 441"]
theorem ehrenfest_ergodic_not_regular (hn : 1 ≤ n) :
    IsErgodicChain (ehrenfest n) ∧ ¬ IsRegularChain (ehrenfest n) := by
  constructor
  · rw [isErgodicChain_iff]
    refine ⟨ehrenfest_mem hn, fun i j => ?_⟩
    obtain ⟨k1, h1⟩ := ehrenfest_reach hn i ⟨0, by omega⟩
    obtain ⟨k2, h2⟩ := ehrenfest_reach hn ⟨1, by omega⟩ j
    have hs : 0 < (ehrenfest n ^ 1) (⟨0, by omega⟩ : Fin (n + 1)) ⟨1, by omega⟩ := by
      rw [pow_one]
      exact ehrenfest_step_up hn (by simp)
    refine ⟨k1 + 1 + k2, by omega, ?_⟩
    exact pow_add_pos (ehrenfest_mem hn) (pow_add_pos (ehrenfest_mem hn) h1 hs) h2
  · rintro ⟨-, N, hN, hpos⟩
    have a := ehrenfest_parity N ⟨0, by omega⟩ ⟨0, by omega⟩ (hpos _ _).ne'
    have b := ehrenfest_parity N ⟨0, by omega⟩ ⟨1, by omega⟩ (hpos _ _).ne'
    simp at a b
    omega

/-- The binomial vector `w_i = C(n, i) / 2^n`. -/
noncomputable def binomialVec (n : ℕ) : Fin (n + 1) → ℝ := fun i => (n.choose i : ℝ) / 2 ^ n

theorem ehrenfest_balance (hn : 1 ≤ n) (i j : Fin (n + 1)) :
    binomialVec n i * ehrenfest n i j = binomialVec n j * ehrenfest n j i := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  -- key identity: C(n, k+1) (k+1) = C(n, k) (n - k)
  have key : ∀ k : ℕ, k < n → (n.choose (k + 1) : ℝ) * (k + 1) = n.choose k * ((n : ℝ) - k) := by
    intro k hk
    have := Nat.choose_succ_right_eq n k
    have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub hk.le
    rw [← h2]
    exact_mod_cast this
  by_cases h1 : (j : ℕ) + 1 = i
  · have h2 : (i : ℕ) = j + 1 := h1.symm
    have h3 : ¬ (i : ℕ) + 1 = j := by omega
    have hk := key j (by have := i.isLt; omega)
    unfold binomialVec ehrenfest
    rw [if_pos h1, if_neg h3, if_pos h2, h2]
    push_cast
    field_simp
    nlinarith [hk]
  · by_cases h2 : (j : ℕ) = i + 1
    · have h3 : (i : ℕ) + 1 = j := h2.symm
      have hk := key i (by have := j.isLt; omega)
      have h4 : ¬ (i : ℕ) = j + 1 := by omega
      unfold binomialVec ehrenfest
      rw [if_neg h1, if_pos h2, if_pos h3, h2]
      push_cast
      field_simp
      nlinarith [hk]
    · have h3 : ¬ (i : ℕ) + 1 = j := fun h => h2 h.symm
      have h4 : ¬ (i : ℕ) = j + 1 := fun h => h1 h.symm
      unfold ehrenfest
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      simp

theorem binomialVec_sum : ∑ j, binomialVec n j = 1 := by
  unfold binomialVec
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => (n.choose j : ℝ)) (n + 1)]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  exact div_self (by positivity)

/-- Grinstead–Snell Example 11.23 (PR-145): the fixed probability vector of the Ehrenfest urn chain with `n`
balls is binomial, `w_i = C(n, i) / 2^n` (for `n = 4`: `(1/16, 4/16, 6/16, 4/16, 1/16)`), and it is the only
fixed probability vector. -/
@[kb "grinsteadsnell2006" "Example 11.23, p. 449"]
theorem ehrenfest_fixed (hn : 1 ≤ n) :
    IsFixedRow (ehrenfest n) (binomialVec n) ∧ ∑ j, binomialVec n j = 1 ∧
      ∀ v : Fin (n + 1) → ℝ, ∑ i, v i = 1 → IsFixedRow (ehrenfest n) v → v = binomialVec n := by
  have h1 : IsFixedRow (ehrenfest n) (binomialVec n) := by
    unfold IsFixedRow
    funext j
    simp only [Matrix.vecMul, dotProduct]
    simp_rw [ehrenfest_balance hn _ j]
    rw [← Finset.mul_sum, ehrenfest_rowsum hn, mul_one]
  obtain ⟨w, -, -, -, huniq⟩ := ergodic_fixed_vector (ehrenfest_ergodic_not_regular hn).1
  refine ⟨h1, binomialVec_sum, fun v hv hvf => ?_⟩
  rw [huniq v hv hvf, huniq _ binomialVec_sum h1]

/-- Grinstead–Snell Example 11.23 (PR-145), the case of four balls: the fixed vector is
`(1/16, 4/16, 6/16, 4/16, 1/16)`. -/
@[kb "grinsteadsnell2006" "Example 11.23, p. 449"]
theorem ehrenfest_four_fixed :
    binomialVec 4 = ![1/16, 4/16, 6/16, 4/16, 1/16] := by
  funext i
  fin_cases i <;> simp [binomialVec, Nat.choose] <;> norm_num

end UndergradKB.Probability
