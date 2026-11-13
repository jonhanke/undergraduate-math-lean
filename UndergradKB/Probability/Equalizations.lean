import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Stirling
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk
import UndergradKB.Probability.ArcSine

/-! # Probability: the expected number of equalizations (Grinstead–Snell, Example 12.3)

Paths of the simple symmetric walk of length `N` are the `2 ^ N` equally likely functions `ω : Fin N → Bool`
of `RandomWalk.lean`. An equalization is a time `k ∈ [1, N]` with `S_k = 0` (time `0` is not counted).
`g_N` is the total number of equalizations over all paths, so `g_N / 2^N` is the expected number of
equalizations. Example 12.3 finds, by generating functions,

  `g_{2m} = (1/2) C(2m+2, m+1) (m+1) - 2^{2m}`,   and   `g_{2m} / 2^{2m} ~ √(2/π) √(2m)`.

We prove both, by linearity of expectation instead of the book's generating functions: the expected number of
equalizations is `Σ_{k=1}^m u_{2k}`, and `Σ_{k=1}^m u_{2k} = (2m+1) u_{2m} - 1` by induction (row PR-127). -/

open Finset Filter Topology Real

namespace UndergradKB.Probability

/-- The number of equalizations of the path `ω`: times `k ∈ [1, N]` at which the walk is at `0`. -/
def equalizations {N : ℕ} (ω : Fin N → Bool) : ℕ := ((Icc 1 N).filter fun k => walkPos ω k = 0).card

/-- `g_N`: the number of equalizations summed over all `2 ^ N` paths of length `N`. -/
def equalTotal (N : ℕ) : ℕ := ∑ ω : Fin N → Bool, equalizations ω

/-- The expected number of equalizations of the simple walk of length `N` (all paths equally likely). -/
def expectedEqualizations (N : ℕ) : ℚ := (equalTotal N : ℚ) / 2 ^ N

/-- The number of paths of length `a + b` at `0` at time `a` is `Z_a 2^b`. -/
theorem card_walkPos_eq_zero_append (a b : ℕ) :
    (univ.filter fun ω : Fin (a + b) → Bool => walkPos ω a = 0).card = zeroCount a * 2 ^ b := by
  rw [card_filter_append a b (fun x => walkPos x a = 0) (fun _ => True)]
  · simp [zeroCount]
  · intro x y
    rw [walkPos_append_le x y le_rfl]
    simp

theorem card_walkPos_eq_zero {N k : ℕ} (hk : k ≤ N) :
    (univ.filter fun ω : Fin N → Bool => walkPos ω k = 0).card = zeroCount k * 2 ^ (N - k) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  exact card_walkPos_eq_zero_append k b

/-- Linearity: `g_N = Σ_{k=1}^N Z_k 2^{N-k}`. -/
theorem equalTotal_eq (N : ℕ) : equalTotal N = ∑ k ∈ Icc 1 N, zeroCount k * 2 ^ (N - k) := by
  unfold equalTotal equalizations
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [← card_filter]
  exact card_walkPos_eq_zero (mem_Icc.1 hk).2

/-- The expected number of equalizations is `Σ_{k=1}^N u_k`. -/
theorem expectedEqualizations_eq_sum_u (N : ℕ) :
    expectedEqualizations N = ∑ k ∈ Icc 1 N, u k := by
  unfold expectedEqualizations
  rw [equalTotal_eq, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkN := (mem_Icc.1 hk).2
  unfold u
  have h2 : (2 : ℚ) ^ N = 2 ^ k * 2 ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hkN]
  rw [h2]
  push_cast
  field_simp

/-- `Σ_{k=1}^m u_{2k} = (2m+1) u_{2m} - 1`. -/
theorem sum_c_eq (m : ℕ) : ∑ k ∈ Icc 1 m, c k = (2 * m + 1) * c m - 1 := by
  induction m with
  | zero => simp [c_zero]
  | succ m ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    have h := c_succ m
    push_cast
    linarith

/-- Grinstead–Snell Example 12.3 (PR-127). The expected number of equalizations of the simple symmetric walk
of length `2m` is `Σ_{k=1}^m u_{2k} = (2m+1) u_{2m} - 1`. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem expectedEqualizations_two_mul (m : ℕ) :
    expectedEqualizations (2 * m) = ∑ k ∈ Icc 1 m, u (2 * k) ∧
      expectedEqualizations (2 * m) = (2 * m + 1) * u (2 * m) - 1 := by
  have h1 : expectedEqualizations (2 * m) = ∑ k ∈ Icc 1 m, u (2 * k) := by
    rw [expectedEqualizations_eq_sum_u]
    exact sum_Icc_even u u_odd m
  refine ⟨h1, ?_⟩
  rw [h1]
  simp_rw [u_two_mul]
  exact sum_c_eq m

/-- Grinstead–Snell Example 12.3 (PR-127), the book's closed form: the total number of equalizations over all
`2^{2m}` paths of length `2m` is `g_{2m} = (1/2) C(2m+2, m+1) (m+1) - 2^{2m}`. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem equalTotal_two_mul (m : ℕ) :
    (equalTotal (2 * m) : ℚ) = (1 / 2) * ((2 * m + 2).choose (m + 1) : ℚ) * (m + 1) - 2 ^ (2 * m) := by
  have h := (expectedEqualizations_two_mul m).2
  unfold expectedEqualizations at h
  rw [u_two_mul] at h
  have hc := c_succ m
  have hpos : (0 : ℚ) < 2 ^ (2 * m) := by positivity
  have hg : (equalTotal (2 * m) : ℚ) = ((2 * m + 1) * c m - 1) * 2 ^ (2 * m) := by
    rw [← h]; field_simp
  rw [hg]
  have hc1 : c (m + 1) = ((2 * m + 2).choose (m + 1) : ℚ) / 4 ^ (m + 1) := by
    unfold c; congr 2
  rw [hc1] at hc
  have h4 : (4 : ℚ) ^ (m + 1) = 4 * 2 ^ (2 * m) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h4] at hc
  field_simp at hc
  field_simp
  nlinarith [hc]

/-- Grinstead–Snell Example 12.3 (PR-127), asymptotics: the expected number of equalizations in `2m` steps is
asymptotic to `√(2/π) √(2m)`. -/
@[kb "grinsteadsnell2006" "Example 12.3, p. 487"]
theorem expectedEqualizations_asymptotic :
    Tendsto (fun m : ℕ => (expectedEqualizations (2 * m) : ℝ) / √(2 * (m : ℝ))) atTop (𝓝 (√(2 / π))) := by
  have hc := c_sqrt_tendsto
  -- E / √(2m) = (2m+1)/(√2 m) * (c m √m) - 1/√(2m)
  have hA : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) / (√2 * m)) atTop (𝓝 (2 / √2)) := by
    have : Tendsto (fun m : ℕ => (2 + 1 / (m : ℝ)) / √2) atTop (𝓝 ((2 + 0) / √2)) :=
      ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).div_const _)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    field_simp
  have hB : Tendsto (fun m : ℕ => 1 / √(2 * (m : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m : ℕ => (1 / 2 : ℝ) * (1 / (m : ℝ))) atTop (𝓝 ((1 / 2) * 0)) :=
      tendsto_one_div_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at h0
    have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at h1
    refine h1.congr fun m => ?_
    simp only [Function.comp_apply]
    rw [← Real.sqrt_one, ← Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ 2 * m), Real.sqrt_one]
    congr 1
    ring
  have hlim : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) / (√2 * m) * (((c m : ℚ) : ℝ) * √(m : ℝ))
      - 1 / √(2 * (m : ℝ))) atTop (𝓝 (2 / √2 * (1 / √π) - 0)) := (hA.mul hc).sub hB
  have hval : 2 / √2 * (1 / √π) - 0 = √(2 / π) := by
    rw [sub_zero, Real.sqrt_div' 2 (le_of_lt pi_pos)]
    have h2 : (0 : ℝ) < √2 := by positivity
    have : (2 : ℝ) = √2 * √2 := (Real.mul_self_sqrt (by norm_num)).symm
    field_simp
    nth_rewrite 1 [this]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [(expectedEqualizations_two_mul m).2, u_two_mul]
  push_cast
  have hs : √(2 * (m : ℝ)) = √2 * √(m : ℝ) := Real.sqrt_mul (by norm_num) _
  have hsm : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hm'.le
  have h2 : (0 : ℝ) < √2 := by positivity
  have hsm0 : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.2 hm'
  rw [hs]
  field_simp
  rw [sq, hsm]
  ring

end UndergradKB.Probability
