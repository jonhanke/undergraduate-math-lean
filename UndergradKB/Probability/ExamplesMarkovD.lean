import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovBasic
import UndergradKB.Probability.MarkovAbsorbing
import UndergradKB.Probability.MarkovRegular
import UndergradKB.Probability.MarkovPassage
import UndergradKB.Probability.ExamplesMarkov
import UndergradKB.Probability.ExamplesMarkovB

/-! # Worked examples on Markov chains, part D (two-state chain, Harvard/Yale/Dartmouth, genetics, Oz `Z`)

Grinstead–Snell chapter 11: the two-state chain (Example 11.4), the horse race (11.5), the
Harvard–Yale–Dartmouth chains (11.6, 11.7), the gene models (11.9, 11.10, 11.11) and the fundamental matrix `Z` of the
Land of Oz (11.26). -/

namespace UndergradKB.Probability

open Matrix Finset Filter Topology

/-! ## Helpers for concrete absorbing chains -/

section Helpers

variable {S : Type*} [Fintype S] [DecidableEq S] {P : Matrix S S ℝ}

/-- If `Nf` restricted to the transient states `T` is a right inverse of `I - Q`, it is the fundamental matrix. -/
theorem fundamentalMatrix_eq_of_mul (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (T : Finset S)
    (hT : ∀ x, ¬ IsAbsorbingState P x ↔ x ∈ T) (Nf : S → S → ℝ)
    (h : ∀ i ∈ T, ∀ j ∈ T, ∑ k ∈ T, ((1 : Matrix S S ℝ) i k - P i k) * Nf k j = (1 : Matrix S S ℝ) i j)
    (i j : Transient P) : fundamentalMatrix P i j = Nf i j := by
  set M : Matrix (Transient P) (Transient P) ℝ := fun i j => Nf i j with hM
  have h1 : (1 - absorbQ P) * M = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have key := h i ((hT _).1 i.2) j ((hT _).1 j.2)
    rw [Finset.sum_subtype T (fun x => (hT x).symm) (fun k => ((1 : Matrix S S ℝ) i k - P i k) * Nf k j)] at key
    simpa [Matrix.one_apply, Subtype.ext_iff, absorbQ, hM] using key
  obtain ⟨-, h2, -⟩ := fundamentalMatrix_spec hP hA
  have : fundamentalMatrix P = M := by
    calc fundamentalMatrix P = fundamentalMatrix P * ((1 - absorbQ P) * M) := by rw [h1, mul_one]
      _ = (fundamentalMatrix P * (1 - absorbQ P)) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [h2, one_mul]
  rw [this]

/-- Expected absorption times from the entries of the fundamental matrix. -/
theorem absorption_time_of_fundamental (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (T : Finset S)
    (hT : ∀ x, ¬ IsAbsorbingState P x ↔ x ∈ T) (Nf : S → S → ℝ)
    (hN : ∀ i j : Transient P, fundamentalMatrix P i j = Nf i j) (tf : S → ℝ)
    (ht : ∀ i ∈ T, ∑ j ∈ T, Nf i j = tf i) (i : Transient P) :
    HasSum (fun k => ∑ j : Transient P, (P ^ k) i j) (tf i) := by
  have := hasSum_absorption_time hP hA i
  convert this using 1
  have e : (fundamentalMatrix P *ᵥ fun _ => (1 : ℝ)) i = ∑ j : Transient P, Nf i j := by
    simp [mulVec, dotProduct, hN]
  rw [e, ← Finset.sum_subtype T (fun x => (hT x).symm) (fun j => Nf i j), ht i ((hT _).1 i.2)]

/-- Absorption probabilities from the entries of the fundamental matrix. -/
theorem absorption_prob_of_fundamental (hP : P ∈ rowStochastic ℝ S) (hA : IsAbsorbingChain P) (T : Finset S)
    (hT : ∀ x, ¬ IsAbsorbingState P x ↔ x ∈ T) (Nf : S → S → ℝ)
    (hN : ∀ i j : Transient P, fundamentalMatrix P i j = Nf i j) (Bf : S → S → ℝ)
    (hB : ∀ i ∈ T, ∀ a, IsAbsorbingState P a → ∑ k ∈ T, Nf i k * P k a = Bf i a)
    (i : Transient P) (a : Absorbing P) :
    Tendsto (fun n => (P ^ n) i a) atTop (𝓝 (Bf i a)) := by
  have := absorption_prob_tendsto hP hA i a
  convert this using 2
  have e : (fundamentalMatrix P * absorbR P) i a = ∑ k : Transient P, Nf i k * P k a := by
    simp [Matrix.mul_apply, absorbR, hN]
  rw [e, ← Finset.sum_subtype T (fun x => (hT x).symm) (fun k => Nf i k * P k a), hB i ((hT _).1 i.2) a a.2]

/-- Uniqueness of the fixed probability vector of a regular chain, in the form used below. -/
theorem regular_fixed_unique [Nonempty S] (h : IsRegularChain P) {w : S → ℝ} (hs : ∑ j, w j = 1) (hf : IsFixedRow P w) :
    ∀ v : S → ℝ, ∑ i, v i = 1 → IsFixedRow P v → v = w := by
  obtain ⟨w', -, -, -, huniq⟩ := regular_fixed_vector h
  intro v hv hvf
  rw [huniq v hv hvf, huniq w hs hf]

end Helpers

/-! ## Example 11.4: the two-state chain -/

/-- The transition matrix `[[1-a, a], [b, 1-b]]` of the two-state chain (the message `yes`/`no` of Example 11.4). -/
def twoStateP (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]

/-- Grinstead–Snell Example 11.4 (PR-181): for `a + b ≠ 0` the powers of the two-state matrix are
`P^n = (1/(a+b)) [[b, a], [b, a]] + ((1-a-b)^n/(a+b)) [[a, -a], [-b, b]]`. -/
@[kb "grinsteadsnell2006" "Example 11.4, p. 417"]
theorem twoStateP_pow {a b : ℝ} (hab : a + b ≠ 0) (n : ℕ) :
    twoStateP a b ^ n = (1 / (a + b)) • !![b, a; b, a] + ((1 - a - b) ^ n / (a + b)) • !![a, -a; -b, b] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [twoStateP] <;> field_simp <;> ring
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [twoStateP, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- The limiting row `(b/(a+b), a/(a+b))` of the two-state chain. -/
noncomputable def twoStateFixed (a b : ℝ) : Fin 2 → ℝ := ![b / (a + b), a / (a + b)]

/-- Grinstead–Snell Example 11.4 (PR-181): for `0 ≤ a, b ≤ 1` and `0 < a + b < 2` the powers `P^n` of the two-state
chain converge to the matrix both of whose rows are `(b, a)/(a+b)`, and this row is a fixed probability vector. -/
@[kb "grinsteadsnell2006" "Example 11.4, p. 417"]
theorem twoStateP_pow_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpos : 0 < a + b) (hlt : a + b < 2) :
    (∀ i j, Tendsto (fun n => (twoStateP a b ^ n) i j) atTop (𝓝 (twoStateFixed a b j))) ∧
      IsFixedRow (twoStateP a b) (twoStateFixed a b) ∧ ∑ j, twoStateFixed a b j = 1 := by
  have hne : a + b ≠ 0 := hpos.ne'
  have hr : Tendsto (fun n : ℕ => (1 - a - b) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> linarith)
  have key : ∀ c d : ℝ, Tendsto (fun n : ℕ => c + (1 - a - b) ^ n / (a + b) * d) atTop (𝓝 c) := by
    intro c d
    have := (tendsto_const_nhds (x := c)).add ((hr.div_const (a + b)).mul_const d)
    simpa using this
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · simp only [twoStateP_pow hne]
    fin_cases i <;> fin_cases j <;> simp [twoStateFixed]
    · exact Tendsto.congr (fun n => by ring) (key (b / (a + b)) a)
    · exact Tendsto.congr (fun n => by ring) (key (a / (a + b)) (-a))
    · exact Tendsto.congr (fun n => by ring) (key (b / (a + b)) (-b))
    · exact Tendsto.congr (fun n => by ring) (key (a / (a + b)) b)
  · unfold IsFixedRow
    funext j
    fin_cases j <;> simp [twoStateFixed, twoStateP, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      field_simp <;> ring
  · simp [twoStateFixed, Fin.sum_univ_succ]
    field_simp
    ring

/-! ## Example 11.5: the horse race -/

/-- The transition matrix of the horse race of Example 11.5 (win, place, show), all three rows `(1/2, 1/4, 1/4)`. -/
noncomputable def horseMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/4, 1/4; 1/2, 1/4, 1/4; 1/2, 1/4, 1/4]

/-- The row `(1/2, 1/4, 1/4)`. -/
noncomputable def horseFixed : Fin 3 → ℝ := ![1/2, 1/4, 1/4]

theorem horseMatrix_mem : horseMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [horseMatrix] <;> norm_num
  · fin_cases i <;> simp [horseMatrix, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.5 (PR-182): for the horse race matrix with three equal rows `(1/2, 1/4, 1/4)` one has
`P^n = P` for every `n ≥ 1`. -/
@[kb "grinsteadsnell2006" "Example 11.5, p. 417"]
theorem horseMatrix_pow {n : ℕ} (hn : 1 ≤ n) : horseMatrix ^ n = horseMatrix := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n _ ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [horseMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.5 (PR-182): the horse race chain is regular (already `P^1` is positive), and its
unique fixed probability vector is `(1/2, 1/4, 1/4)`. -/
@[kb "grinsteadsnell2006" "Example 11.5, p. 417"]
theorem horseMatrix_regular_fixed :
    IsRegularChain horseMatrix ∧ IsFixedRow horseMatrix horseFixed ∧ ∑ j, horseFixed j = 1 ∧
      ∀ v : Fin 3 → ℝ, ∑ i, v i = 1 → IsFixedRow horseMatrix v → v = horseFixed := by
  have hreg : IsRegularChain horseMatrix := by
    refine ⟨horseMatrix_mem, 1, by norm_num, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [horseMatrix] <;> norm_num
  have h1 : IsFixedRow horseMatrix horseFixed := by
    unfold IsFixedRow
    funext j
    fin_cases j <;> simp [horseFixed, horseMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> norm_num
  have h2 : ∑ j, horseFixed j = 1 := by
    simp [horseFixed, Fin.sum_univ_succ]; norm_num
  exact ⟨hreg, h1, h2, regular_fixed_unique hreg h2 h1⟩

/-! ## Examples 11.6 and 11.7: Harvard, Yale, Dartmouth -/

/-- Grinstead–Snell Example 11.6 (PR-183): the Harvard (H), Yale (Y), Dartmouth (D) chain, states `0, 1, 2`. -/
noncomputable def hydMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![4/5, 1/5, 0; 3/10, 2/5, 3/10; 1/5, 1/10, 7/10]

/-- The fixed vector `(5/9, 2/9, 2/9)` of the Harvard–Yale–Dartmouth chain. -/
noncomputable def hydFixed : Fin 3 → ℝ := ![5/9, 2/9, 2/9]

theorem hydMatrix_mem : hydMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hydMatrix] <;> norm_num
  · fin_cases i <;> simp [hydMatrix, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.6 (PR-183): the Harvard–Yale–Dartmouth chain is regular (`P^2` is positive) and its
unique fixed probability vector is `(5/9, 2/9, 2/9)`. -/
@[kb "grinsteadsnell2006" "Example 11.6, p. 418"]
theorem hydMatrix_regular_fixed :
    IsRegularChain hydMatrix ∧ IsFixedRow hydMatrix hydFixed ∧ ∑ j, hydFixed j = 1 ∧
      ∀ v : Fin 3 → ℝ, ∑ i, v i = 1 → IsFixedRow hydMatrix v → v = hydFixed := by
  have hreg : IsRegularChain hydMatrix := by
    refine ⟨hydMatrix_mem, 2, by norm_num, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, hydMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have h1 : IsFixedRow hydMatrix hydFixed := by
    unfold IsFixedRow
    funext j
    fin_cases j <;> simp [hydFixed, hydMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> norm_num
  have h2 : ∑ j, hydFixed j = 1 := by
    simp [hydFixed, Fin.sum_univ_succ]; norm_num
  exact ⟨hreg, h1, h2, regular_fixed_unique hreg h2 h1⟩

/-- Grinstead–Snell Example 11.7 (PR-183): the modified chain in which Harvard sons always go to Harvard. -/
noncomputable def hydAbsMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 3/10, 2/5, 3/10; 1/5, 1/10, 7/10]

theorem hydAbsMatrix_mem : hydAbsMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hydAbsMatrix] <;> norm_num
  · fin_cases i <;> simp [hydAbsMatrix, Fin.sum_univ_succ] <;> norm_num

theorem hydAbs_transient (x : Fin 3) :
    ¬ IsAbsorbingState hydAbsMatrix x ↔ x ∈ ({1, 2} : Finset (Fin 3)) := by
  fin_cases x <;> simp [IsAbsorbingState, hydAbsMatrix] <;> norm_num

/-- Grinstead–Snell Example 11.7 (PR-183): the modified chain is absorbing, with Harvard (state `0`) the only
absorbing state. -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem hydAbsMatrix_absorbing : IsAbsorbingChain hydAbsMatrix := by
  refine ⟨⟨0, by simp [IsAbsorbingState, hydAbsMatrix]⟩, fun i => ⟨1, 0, by simp [IsAbsorbingState, hydAbsMatrix], ?_⟩⟩
  fin_cases i <;> simp [hydAbsMatrix] <;> norm_num

/-- Grinstead–Snell Example 11.7 (PR-183): with the repository's fundamental matrix `N = (I - Q)⁻¹`, where
`Q = [[.4, .3], [.1, .7]]` on the transient states Yale, Dartmouth (`1, 2`), one has `N = [[2, 2], [2/3, 4]]`. -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem hydAbs_fundamental (i j : Transient hydAbsMatrix) :
    fundamentalMatrix hydAbsMatrix i j =
      (!![0, 0, 0; 0, 2, 2; 0, 2/3, 4] : Matrix (Fin 3) (Fin 3) ℝ) i.1 j.1 := by
  refine fundamentalMatrix_eq_of_mul hydAbsMatrix_mem hydAbsMatrix_absorbing {1, 2} hydAbs_transient _ ?_ i j
  intro i hi j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp [hydAbsMatrix, Matrix.one_apply, Finset.sum_pair] <;> norm_num

/-- Grinstead–Snell Example 11.7 (PR-183): the expected number of generations before the family enters Harvard,
`t = N c`, is `4` from Yale and `14/3` from Dartmouth. -/
@[kb "grinsteadsnell2006" "Example 11.7, p. 418"]
theorem hydAbs_time (i : Transient hydAbsMatrix) :
    HasSum (fun k => ∑ j : Transient hydAbsMatrix, (hydAbsMatrix ^ k) i j) ((![0, 4, 14/3] : Fin 3 → ℝ) i.1) := by
  refine absorption_time_of_fundamental hydAbsMatrix_mem hydAbsMatrix_absorbing {1, 2} hydAbs_transient
    (fun i j => (!![0, 0, 0; 0, 2, 2; 0, 2/3, 4] : Matrix (Fin 3) (Fin 3) ℝ) i j) hydAbs_fundamental _ ?_ i
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp [Finset.sum_pair] <;> norm_num

/-! ## Examples 11.9 and 11.10: gene model -/

/-- Grinstead–Snell Example 11.9 (PR-184): the gene model mated with a hybrid, states `GG, Gg, gg`. -/
noncomputable def geneHybridMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/2, 1/2, 0; 1/4, 1/2, 1/4; 0, 1/2, 1/2]

/-- The fixed vector `(1/4, 1/2, 1/4)` of the hybrid-mating gene chain. -/
noncomputable def geneHybridFixed : Fin 3 → ℝ := ![1/4, 1/2, 1/4]

theorem geneHybridMatrix_mem : geneHybridMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [geneHybridMatrix] <;> norm_num
  · fin_cases i <;> simp [geneHybridMatrix, Fin.sum_univ_succ] <;> norm_num

/-- Grinstead–Snell Example 11.9 (PR-184): the gene chain mated with a hybrid is regular (`P^2` is positive); its
unique fixed probability vector is `(1/4, 1/2, 1/4)`. -/
@[kb "grinsteadsnell2006" "Example 11.9, p. 419"]
theorem geneHybrid_regular_fixed :
    IsRegularChain geneHybridMatrix ∧ IsFixedRow geneHybridMatrix geneHybridFixed ∧
      ∑ j, geneHybridFixed j = 1 ∧
      ∀ v : Fin 3 → ℝ, ∑ i, v i = 1 → IsFixedRow geneHybridMatrix v → v = geneHybridFixed := by
  have hreg : IsRegularChain geneHybridMatrix := by
    refine ⟨geneHybridMatrix_mem, 2, by norm_num, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, geneHybridMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have h1 : IsFixedRow geneHybridMatrix geneHybridFixed := by
    unfold IsFixedRow
    funext j
    fin_cases j <;> simp [geneHybridFixed, geneHybridMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      norm_num
  have h2 : ∑ j, geneHybridFixed j = 1 := by
    simp [geneHybridFixed, Fin.sum_univ_succ]; norm_num
  exact ⟨hreg, h1, h2, regular_fixed_unique hreg h2 h1⟩

/-- Grinstead–Snell Example 11.10 (PR-184): the gene model mated with a dominant individual. -/
noncomputable def geneDomMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 1/2, 1/2, 0; 0, 1, 0]

theorem geneDomMatrix_mem : geneDomMatrix ∈ rowStochastic ℝ (Fin 3) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [geneDomMatrix] <;> norm_num
  · fin_cases i <;> simp [geneDomMatrix, Fin.sum_univ_succ] <;> norm_num

theorem geneDom_transient (x : Fin 3) :
    ¬ IsAbsorbingState geneDomMatrix x ↔ x ∈ ({1, 2} : Finset (Fin 3)) := by
  fin_cases x <;> simp [IsAbsorbingState, geneDomMatrix] <;> norm_num

/-- Grinstead–Snell Example 11.10 (PR-184): the gene chain mated with a dominant is absorbing (`GG` is the only
absorbing state; `Gg` reaches it in one step and `gg` in two). -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem geneDomMatrix_absorbing : IsAbsorbingChain geneDomMatrix := by
  refine ⟨⟨0, by simp [IsAbsorbingState, geneDomMatrix]⟩, fun i => ?_⟩
  fin_cases i
  · exact ⟨1, 0, by simp [IsAbsorbingState, geneDomMatrix], by simp [geneDomMatrix]⟩
  · exact ⟨1, 0, by simp [IsAbsorbingState, geneDomMatrix], by simp [geneDomMatrix]⟩
  · refine ⟨2, 0, by simp [IsAbsorbingState, geneDomMatrix], ?_⟩
    simp [pow_two, geneDomMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Grinstead–Snell Example 11.10 (PR-184): the fundamental matrix of the dominant-mating chain, with
`Q = [[1/2, 0], [1, 0]]` on the transient states `Gg, gg`, is `N = [[2, 0], [2, 1]]`. -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem geneDom_fundamental (i j : Transient geneDomMatrix) :
    fundamentalMatrix geneDomMatrix i j =
      (!![0, 0, 0; 0, 2, 0; 0, 2, 1] : Matrix (Fin 3) (Fin 3) ℝ) i.1 j.1 := by
  refine fundamentalMatrix_eq_of_mul geneDomMatrix_mem geneDomMatrix_absorbing {1, 2} geneDom_transient _ ?_ i j
  intro i hi j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp [geneDomMatrix, Matrix.one_apply, Finset.sum_pair] <;> norm_num

/-- Grinstead–Snell Example 11.10 (PR-184): the expected number of generations until a dominant offspring is
reached is `2` from a hybrid `Gg` and `3` from a recessive `gg`. -/
@[kb "grinsteadsnell2006" "Example 11.10, p. 419"]
theorem geneDom_time (i : Transient geneDomMatrix) :
    HasSum (fun k => ∑ j : Transient geneDomMatrix, (geneDomMatrix ^ k) i j)
      ((![0, 2, 3] : Fin 3 → ℝ) i.1) := by
  refine absorption_time_of_fundamental geneDomMatrix_mem geneDomMatrix_absorbing {1, 2} geneDom_transient
    (fun i j => (!![0, 0, 0; 0, 2, 0; 0, 2, 1] : Matrix (Fin 3) (Fin 3) ℝ) i j) geneDom_fundamental _ ?_ i
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp [Finset.sum_pair] <;> norm_num

/-! ## Example 11.11: inbreeding -/

/-- Grinstead–Snell Example 11.11 (PR-185): the inbreeding chain on the pairs `(GG,GG), (GG,Gg), (GG,gg), (Gg,Gg),
(Gg,gg), (gg,gg)` (states `0, …, 5`); the book prints `.062` for `1/16` and `.125` for `1/8`. -/
noncomputable def inbreedMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0;
     1/4, 1/2, 0, 1/4, 0, 0;
     0, 0, 0, 1, 0, 0;
     1/16, 1/4, 1/8, 1/4, 1/4, 1/16;
     0, 0, 0, 1/4, 1/2, 1/4;
     0, 0, 0, 0, 0, 1]

theorem inbreedMatrix_mem : inbreedMatrix ∈ rowStochastic ℝ (Fin 6) := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [inbreedMatrix] <;> norm_num
  · fin_cases i <;> simp [inbreedMatrix, Fin.sum_univ_succ] <;> norm_num

theorem inbreed_transient (x : Fin 6) :
    ¬ IsAbsorbingState inbreedMatrix x ↔ x ∈ ({1, 2, 3, 4} : Finset (Fin 6)) := by
  fin_cases x <;> simp [IsAbsorbingState, inbreedMatrix] <;> norm_num

/-- Grinstead–Snell Example 11.11 (PR-185): the inbreeding chain is absorbing: the states `(GG,GG)` and `(gg,gg)`
(states `0` and `5`) are absorbing and every state reaches one of them. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem inbreedMatrix_absorbing : IsAbsorbingChain inbreedMatrix := by
  have h1 : ∀ {i a : Fin 6}, 0 < inbreedMatrix i a → 0 < (inbreedMatrix ^ 1) i a := by simp
  have h2 : ∀ {i b a : Fin 6}, 0 < inbreedMatrix i b → 0 < inbreedMatrix b a →
      0 < (inbreedMatrix ^ 2) i a := fun p q => by
    simpa using pow_add_pos (P := inbreedMatrix) inbreedMatrix_mem (k := 1) (l := 1) (h1 p) (h1 q)
  have a0 : IsAbsorbingState inbreedMatrix 0 := by simp [IsAbsorbingState, inbreedMatrix]
  have a5 : IsAbsorbingState inbreedMatrix 5 := by simp [IsAbsorbingState, inbreedMatrix]
  refine ⟨⟨0, a0⟩, fun i => ?_⟩
  fin_cases i
  · exact ⟨1, 0, a0, by simp [inbreedMatrix]⟩
  · exact ⟨1, 0, a0, by simp [inbreedMatrix]⟩
  · exact ⟨2, 0, a0, h2 (b := 3) (by simp [inbreedMatrix]) (by simp [inbreedMatrix])⟩
  · exact ⟨1, 0, a0, by simp [inbreedMatrix]⟩
  · exact ⟨1, 5, a5, by simp [inbreedMatrix]⟩
  · exact ⟨1, 5, a5, by simp [inbreedMatrix]⟩

/-- The fundamental matrix of the inbreeding chain on the transient states `s2, s3, s4, s5` (the book's Exercise 5
of §11.2, extended by zeros to all six states). -/
noncomputable def inbreedN : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0;
     0, 8/3, 1/6, 4/3, 2/3, 0;
     0, 4/3, 4/3, 8/3, 4/3, 0;
     0, 4/3, 1/3, 8/3, 4/3, 0;
     0, 2/3, 1/6, 4/3, 8/3, 0;
     0, 0, 0, 0, 0, 0]

theorem inbreed_fundamental_aux (i j : Transient inbreedMatrix) :
    fundamentalMatrix inbreedMatrix i j = inbreedN i.1 j.1 := by
  refine fundamentalMatrix_eq_of_mul inbreedMatrix_mem inbreedMatrix_absorbing {1, 2, 3, 4}
    inbreed_transient _ ?_ i j
  intro i hi j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
    simp [inbreedMatrix, inbreedN, Matrix.one_apply, Finset.sum_insert] <;> norm_num

/-- Grinstead–Snell Example 11.11 (PR-185): the fundamental matrix of the inbreeding chain (transient states
`(GG,Gg), (GG,gg), (Gg,Gg), (Gg,gg)`) is
`N = [[8/3, 1/6, 4/3, 2/3], [4/3, 4/3, 8/3, 4/3], [4/3, 1/3, 8/3, 4/3], [2/3, 1/6, 4/3, 8/3]]`. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem inbreed_fundamental (i j : Transient inbreedMatrix) :
    fundamentalMatrix inbreedMatrix i j = inbreedN i.1 j.1 := inbreed_fundamental_aux i j

/-- Grinstead–Snell Example 11.11 (PR-185): the expected numbers of generations before one of the two absorbing
states is reached are `t = N c = (29/6, 20/3, 17/3, 29/6)` from the four transient states. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem inbreed_time (i : Transient inbreedMatrix) :
    HasSum (fun k => ∑ j : Transient inbreedMatrix, (inbreedMatrix ^ k) i j)
      ((![0, 29/6, 20/3, 17/3, 29/6, 0] : Fin 6 → ℝ) i.1) := by
  refine absorption_time_of_fundamental inbreedMatrix_mem inbreedMatrix_absorbing {1, 2, 3, 4}
    inbreed_transient (fun i j => inbreedN i j) inbreed_fundamental_aux _ ?_ i
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp [inbreedN, Finset.sum_insert] <;> norm_num

/-- The absorption probabilities `B = N R` of the inbreeding chain, extended by zeros: column `0` is absorption in
`(GG,GG)`, column `5` is absorption in `(gg,gg)`. -/
noncomputable def inbreedB : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 0, 0;
     3/4, 0, 0, 0, 0, 1/4;
     1/2, 0, 0, 0, 0, 1/2;
     1/2, 0, 0, 0, 0, 1/2;
     1/4, 0, 0, 0, 0, 3/4;
     0, 0, 0, 0, 0, 0]

/-- Grinstead–Snell Example 11.11 (PR-185): the probabilities of eventual absorption in `(GG,GG)` and `(gg,gg)`
are `B = N R`, namely `(3/4, 1/4), (1/2, 1/2), (1/2, 1/2), (1/4, 3/4)` from the four transient states. -/
@[kb "grinsteadsnell2006" "Example 11.11, p. 420"]
theorem inbreed_absorption_prob (i : Transient inbreedMatrix) (a : Absorbing inbreedMatrix) :
    Tendsto (fun n => (inbreedMatrix ^ n) i a) atTop (𝓝 (inbreedB i.1 a.1)) := by
  refine absorption_prob_of_fundamental inbreedMatrix_mem inbreedMatrix_absorbing {1, 2, 3, 4}
    inbreed_transient (fun i j => inbreedN i j) inbreed_fundamental_aux (fun i a => inbreedB i a) ?_ i a
  intro i hi a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  have : a = 0 ∨ a = 5 := by
    revert ha
    fin_cases a <;> simp [IsAbsorbingState, inbreedMatrix] <;> norm_num
  rcases hi with rfl | rfl | rfl | rfl <;> rcases this with rfl | rfl <;>
    simp [inbreedN, inbreedB, inbreedMatrix, Finset.sum_insert] <;> norm_num

/-! ## Example 11.26: the fundamental matrix `Z` of the Land of Oz -/

/-- Grinstead–Snell Example 11.26 (PR-186): for the Land of Oz chain, `I - P + W` (with `W` the matrix all of whose
rows are the fixed vector `(2/5, 1/5, 2/5)`) equals `[[9/10, -1/20, 3/20], [-1/10, 6/5, -1/10], [3/20, -1/20, 9/10]]`
and is invertible with inverse `Z = [[86/75, 1/25, -14/75], [2/25, 21/25, 2/25], [-14/75, 1/25, 86/75]]`. -/
@[kb "grinsteadsnell2006" "Example 11.26, p. 466"]
theorem ozMatrix_fundamentalZ :
    (1 - ozMatrix + rowsMatrix ozFixed =
        !![9/10, -1/20, 3/20; -1/10, 6/5, -1/10; 3/20, -1/20, 9/10]) ∧
      IsUnit (1 - ozMatrix + rowsMatrix ozFixed) ∧
      (1 - ozMatrix + rowsMatrix ozFixed)⁻¹ = ozZ := by
  have hA : 1 - ozMatrix + rowsMatrix ozFixed =
      !![9/10, -1/20, 3/20; -1/10, 6/5, -1/10; 3/20, -1/20, 9/10] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ozMatrix, ozFixed, rowsMatrix, Matrix.one_apply] <;> norm_num
  have hmul : (1 - ozMatrix + rowsMatrix ozFixed) * ozZ = 1 := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ozZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num
  refine ⟨hA, ?_, Matrix.inv_eq_right_inv hmul⟩
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hmul)

/-- Grinstead–Snell Example 11.26 (PR-186): the repository's `Z` of the ergodic Oz chain, built from the unique
fixed probability vector given by `meanFirstPassage_eq_fundamental`, is the matrix `ozZ`; consequently the mean first
passage times of the Oz chain are `m i j = (z j j - z i j)/w j` with this `Z`. -/
@[kb "grinsteadsnell2006" "Example 11.26, p. 466"]
theorem ozMatrix_meanFirstPassage_Z (i j : Fin 3) :
    meanFirstPassage ozMatrix i j = (ozZ j j - ozZ i j) / ozFixed j := by
  obtain ⟨w, -, hs, hfix, -, hm⟩ := meanFirstPassage_eq_fundamental (P := ozMatrix) ozMatrix_regular.isErgodicChain
  have hw := ozMatrix_fixed.2.2 w hs hfix
  subst hw
  rw [hm, (ozMatrix_fundamentalZ).2.2]

end UndergradKB.Probability
