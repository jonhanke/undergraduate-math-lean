import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Group
import UndergradKB.Combinatorics.Probability.Markov
import UndergradKB.Common.Attr

/-!
# Limiting distribution of a regular Markov chain (Keller–Trotter, Theorem 16.9)

If some power `Q = P^k` of the transition matrix has all entries `≥ δ > 0`, then the spread
`max - min` of every column of `P^m` contracts by the factor `1 - nδ < 1` every `k` steps and never
increases; hence each column of `P^m` converges to a constant vector.
-/

namespace UndergradKB.Combinatorics

open Matrix Filter Topology

namespace Markov

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Maximum of a vector. -/
noncomputable def vmax (v : n → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty v
/-- Minimum of a vector. -/
noncomputable def vmin (v : n → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty v

lemma le_vmax (v : n → ℝ) (i : n) : v i ≤ vmax v := Finset.le_sup' v (Finset.mem_univ i)
lemma vmin_le (v : n → ℝ) (i : n) : vmin v ≤ v i := Finset.inf'_le v (Finset.mem_univ i)

lemma vmax_le {v : n → ℝ} {b : ℝ} (h : ∀ i, v i ≤ b) : vmax v ≤ b :=
  Finset.sup'_le _ _ fun i _ => h i

lemma le_vmin {v : n → ℝ} {b : ℝ} (h : ∀ i, b ≤ v i) : b ≤ vmin v :=
  Finset.le_inf' _ _ fun i _ => h i

lemma vmin_le_vmax (v : n → ℝ) : vmin v ≤ vmax v := by
  obtain ⟨i⟩ := ‹Nonempty n›
  exact (vmin_le v i).trans (le_vmax v i)

/-- A stochastic matrix maps a vector into the interval `[min, max]` of the vector. -/
lemma mulVec_bounds {A : Matrix n n ℝ} (hA : IsTransition A) (v : n → ℝ) (j : n) :
    vmin v ≤ (A *ᵥ v) j ∧ (A *ᵥ v) j ≤ vmax v := by
  have e : (A *ᵥ v) j = ∑ i, A j i * v i := rfl
  constructor
  · calc vmin v = ∑ i, A j i * vmin v := by rw [← Finset.sum_mul, hA.sum_row, one_mul]
      _ ≤ _ := e ▸ Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (vmin_le v i) (hA.nonneg j i)
  · calc (A *ᵥ v) j ≤ ∑ i, A j i * vmax v := e ▸ Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_vmax v i) (hA.nonneg j i)
      _ = vmax v := by rw [← Finset.sum_mul, hA.sum_row, one_mul]

/-- The contraction estimate for a matrix with all entries at least `δ`. -/
lemma spread_contract {Q : Matrix n n ℝ} (hQ : IsTransition Q) {δ : ℝ}
    (hδ : ∀ j k, δ ≤ Q j k) (v : n → ℝ) :
    vmax (Q *ᵥ v) - vmin (Q *ᵥ v) ≤ (1 - Fintype.card n * δ) * (vmax v - vmin v) := by
  have key : ∀ j, δ * ∑ i, v i + (1 - Fintype.card n * δ) * vmin v ≤ (Q *ᵥ v) j ∧
      (Q *ᵥ v) j ≤ δ * ∑ i, v i + (1 - Fintype.card n * δ) * vmax v := by
    intro j
    have e : (Q *ᵥ v) j = δ * ∑ i, v i + ∑ i, (Q j i - δ) * v i := by
      show ∑ i, Q j i * v i = _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h3 : ∀ b : ℝ, ∑ i, (Q j i - δ) * b = (1 - Fintype.card n * δ) * b := by
      intro b
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hQ.sum_row j]
      simp
    rw [e]
    constructor
    · have := Finset.sum_le_sum (s := Finset.univ) (f := fun i => (Q j i - δ) * vmin v)
        (g := fun i => (Q j i - δ) * v i) fun i _ =>
          mul_le_mul_of_nonneg_left (vmin_le v i) (sub_nonneg.2 (hδ j i))
      rw [h3] at this
      linarith
    · have := Finset.sum_le_sum (s := Finset.univ) (f := fun i => (Q j i - δ) * v i)
        (g := fun i => (Q j i - δ) * vmax v) fun i _ =>
          mul_le_mul_of_nonneg_left (le_vmax v i) (sub_nonneg.2 (hδ j i))
      rw [h3] at this
      linarith
  have h1 := vmax_le fun j => (key j).2
  have h2 := le_vmin fun j => (key j).1
  linarith

/-- Column `c` of a matrix as a vector. -/
def colv (M : Matrix n n ℝ) (c : n) : n → ℝ := fun j => M j c

lemma colv_mul (A B : Matrix n n ℝ) (c : n) : colv (A * B) c = A *ᵥ colv B c := by
  funext j
  simp [colv, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- CO-253. Theorem 16.9 (limiting distribution): for a regular transition matrix `P` there is a
vector `W` of positive reals summing to `1` such that every row of `P^m` tends to `W`, and
`W P = W`. (Stated for any finite nonempty state type, e.g. `Fin n` with `n ≥ 1`.) -/
@[kb "kellertrotter2017" "Theorem 16.9, p. 345"]
theorem regular_chain_limit {P : Matrix n n ℝ} (hP : IsRegular P) :
    ∃ W : n → ℝ, (∀ c, 0 < W c) ∧ ∑ c, W c = 1 ∧
      (∀ j, Tendsto (fun m : ℕ => (P ^ m) j) atTop (𝓝 W)) ∧ W ᵥ* P = W := by
  obtain ⟨hT, k, hk⟩ := hP
  have hQ := hT.pow k
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (Finset.univ : Finset (n × n))
    (fun p => (P ^ k) p.1 p.2) Finset.univ_nonempty
  set δ := (P ^ k) p.1 p.2 with hδdef
  have hδpos : 0 < δ := hk _ _
  have hδ : ∀ j c, δ ≤ (P ^ k) j c := fun j c => hp (j, c) (Finset.mem_univ _)
  obtain ⟨j0⟩ := ‹Nonempty n›
  set r : ℝ := 1 - Fintype.card n * δ with hr
  have hr0 : 0 ≤ r := by
    have : 0 ≤ ∑ i, ((P ^ k) j0 i - δ) :=
      Finset.sum_nonneg fun i _ => sub_nonneg.2 (hδ j0 i)
    rw [Finset.sum_sub_distrib, hQ.sum_row j0] at this
    simpa [hr] using this
  have hr1 : r < 1 := by
    have : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [hr]; nlinarith
  -- monotonicity along the powers
  let col : ℕ → n → n → ℝ := fun m c => colv (P ^ m) c
  have step : ∀ m c, col (m + 1) c = P *ᵥ col m c := fun m c => by
    simp only [col]; rw [pow_succ', colv_mul]
  have hmax_anti : ∀ c, Antitone fun m => vmax (col m c) := fun c =>
    antitone_nat_of_succ_le fun m => by
      rw [step]; exact vmax_le fun j => (mulVec_bounds hT _ j).2
  have hmin_mono : ∀ c, Monotone fun m => vmin (col m c) := fun c =>
    monotone_nat_of_le_succ fun m => by
      rw [step]; exact le_vmin fun j => (mulVec_bounds hT _ j).1
  let s : ℕ → n → ℝ := fun m c => vmax (col m c) - vmin (col m c)
  have s_anti : ∀ c, Antitone fun m => s m c := fun c a b hab =>
    sub_le_sub (hmax_anti c hab) (hmin_mono c hab)
  have s_k : ∀ m c, s (k + m) c ≤ r * s m c := fun m c => by
    have : col (k + m) c = (P ^ k) *ᵥ col m c := by
      simp only [col]; rw [pow_add, colv_mul]
    show vmax (col (k + m) c) - vmin (col (k + m) c) ≤ _
    rw [this]; exact spread_contract hQ hδ _
  have s_j : ∀ j c, s (j * k) c ≤ r ^ j * s 0 c := fun j c => by
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (j + 1) * k = k + j * k := by ring
      rw [e, pow_succ]
      calc s (k + j * k) c ≤ r * s (j * k) c := s_k _ c
        _ ≤ r * (r ^ j * s 0 c) := mul_le_mul_of_nonneg_left ih hr0
        _ = _ := by ring
  have s_nonneg : ∀ m c, 0 ≤ s m c := fun m c => sub_nonneg.2 (vmin_le_vmax _)
  have s_small : ∀ c, ∀ ε > 0, ∃ N, ∀ m ≥ N, s m c < ε := by
    intro c ε hε
    have hC : 0 < s 0 c + 1 := by linarith [s_nonneg 0 c]
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hε hC) hr1
    refine ⟨j * k, fun m hm => ?_⟩
    have := (lt_div_iff₀ hC).1 hj
    calc s m c ≤ s (j * k) c := s_anti c hm
      _ ≤ r ^ j * s 0 c := s_j j c
      _ ≤ r ^ j * (s 0 c + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 _)
      _ < ε := this
  have entry_le_one : ∀ m j c, (P ^ m) j c ≤ 1 := fun m j c => by
    have h := hT.pow m
    calc (P ^ m) j c ≤ ∑ c', (P ^ m) j c' :=
          Finset.single_le_sum (f := fun c' => (P ^ m) j c') (fun c' _ => h.nonneg j c')
            (Finset.mem_univ c)
      _ = 1 := h.sum_row j
  have bdd : ∀ c, BddAbove (Set.range fun m => vmin (col m c)) := fun c =>
    ⟨1, by rintro _ ⟨m, rfl⟩; exact (vmin_le _ j0).trans (entry_le_one m j0 c)⟩
  let W : n → ℝ := fun c => ⨆ m, vmin (col m c)
  have W_ge : ∀ c m, vmin (col m c) ≤ W c := fun c m => le_ciSup (bdd c) m
  have W_le : ∀ c m, W c ≤ vmax (col m c) := fun c m => by
    refine ciSup_le fun m' => ?_
    rcases le_total m' m with h | h
    · exact (hmin_mono c h).trans (vmin_le_vmax _)
    · exact (vmin_le_vmax _).trans (hmax_anti c h)
  have dist_le : ∀ j c m, |(P ^ m) j c - W c| ≤ s m c := fun j c m => by
    have h1 : vmin (col m c) ≤ (P ^ m) j c := vmin_le (col m c) j
    have h2 : (P ^ m) j c ≤ vmax (col m c) := le_vmax (col m c) j
    have := W_ge c m
    have := W_le c m
    rw [abs_le]; constructor <;> simp only [s] <;> linarith
  have hconv : ∀ j c, Tendsto (fun m : ℕ => (P ^ m) j c) atTop (𝓝 (W c)) := by
    intro j c
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := s_small c ε hε
    exact ⟨N, fun m hm => by
      rw [Real.dist_eq]; exact (dist_le j c m).trans_lt (hN m hm)⟩
  refine ⟨W, fun c => ?_, ?_, fun j => tendsto_pi_nhds.2 (hconv j), ?_⟩
  · have h1 : δ ≤ vmin (col k c) := le_vmin fun j => hδ j c
    exact lt_of_lt_of_le hδpos (h1.trans (W_ge c k))
  · have h1 : Tendsto (fun m : ℕ => ∑ c, (P ^ m) j0 c) atTop (𝓝 (∑ c, W c)) :=
      tendsto_finsetSum _ fun c _ => hconv j0 c
    have h2 : Tendsto (fun m : ℕ => ∑ c, (P ^ m) j0 c) atTop (𝓝 1) := by
      simp only [(hT.pow _).sum_row]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · funext c
    have h1 : Tendsto (fun m : ℕ => (P ^ (m + 1)) j0 c) atTop (𝓝 (W c)) :=
      (hconv j0 c).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun m : ℕ => (P ^ (m + 1)) j0 c) atTop (𝓝 (∑ i, W i * P i c)) := by
      have : ∀ m : ℕ, (P ^ (m + 1)) j0 c = ∑ i, (P ^ m) j0 i * P i c := fun m => by
        rw [pow_succ, Matrix.mul_apply]
      simp only [this]
      exact tendsto_finsetSum _ fun i _ => (hconv j0 i).mul_const _
    exact (tendsto_nhds_unique h2 h1)

end Markov

end UndergradKB.Combinatorics
