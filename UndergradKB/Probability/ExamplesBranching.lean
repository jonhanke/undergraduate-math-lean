import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.Branching

/-!
# Probability: a branching process with geometric offspring law (Grinstead–Snell, Example 10.11)
-/

open Finset Filter Set
open scoped Topology

namespace UndergradKB.Probability

/-- The offspring law of Example 10.11: `p_k = b c^(k-1)` for `k ≥ 1`, `p_0 = 1 - b/(1-c)`. -/
noncomputable def geomOffspring (b c : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - b / (1 - c) else b * c ^ (k - 1)

namespace GeomBranching

variable {b c : ℝ}

theorem hasSum_tail (hc0 : 0 ≤ c) (hc1 : c < 1) :
    HasSum (fun k : ℕ => geomOffspring b c (k + 1)) (b / (1 - c)) := by
  have h := (hasSum_geometric_of_lt_one hc0 hc1).mul_left b
  simpa [geomOffspring, div_eq_mul_inv, mul_comm] using h

theorem isOffspring (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1) :
    IsOffspring (geomOffspring b c) where
  nonneg k := by
    have h1c : 0 < 1 - c := by linarith
    have : b / (1 - c) ≤ 1 := (div_le_one h1c).2 hbc
    rcases k with _ | k
    · simp only [geomOffspring, ite_true]; linarith
    · simp only [geomOffspring, Nat.succ_ne_zero, ite_false]
      positivity
  hasSum := by
    have h := hasSum_tail (b := b) hc0.le hc1
    refine (hasSum_nat_add_iff' 1).1 ?_
    simp only [geomOffspring, sum_range_one, ite_true] at h ⊢
    simpa using h

theorem hasSum_gf (hc0 : 0 ≤ c) (hc1 : c < 1) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ => geomOffspring b c k * z ^ k) (1 - b / (1 - c) + b * z / (1 - c * z)) := by
  have hcz0 : 0 ≤ c * z := mul_nonneg hc0 hz.1
  have hcz1 : c * z < 1 := by nlinarith [hz.1, hz.2]
  have h := (hasSum_geometric_of_lt_one hcz0 hcz1).mul_left (b * z)
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [geomOffspring, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, sum_range_one,
    ite_true, pow_zero, mul_one]
  convert h using 1
  · funext n; rw [mul_pow]; ring
  · have : 1 - c * z ≠ 0 := by linarith
    field_simp; ring

theorem gf_eq (hc0 : 0 ≤ c) (hc1 : c < 1) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    offspringGF (geomOffspring b c) z = 1 - b / (1 - c) + b * z / (1 - c * z) :=
  (hasSum_gf hc0 hc1 hz).tsum_eq

theorem hasSum_mean (hc0 : 0 ≤ c) (hc1 : c < 1) :
    HasSum (fun k : ℕ => (k : ℝ) * geomOffspring b c k) (b / (1 - c) ^ 2) := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := c)
    (by rw [Real.norm_of_nonneg hc0]; exact hc1)
  have h2 := hasSum_geometric_of_lt_one hc0 hc1
  have h := (h1.add h2).mul_left b
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [geomOffspring, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, sum_range_one,
    Nat.cast_zero, zero_mul, sub_zero, Nat.cast_add, Nat.cast_one]
  convert h using 1
  · funext n; ring
  · have : 1 - c ≠ 0 := by linarith
    field_simp; ring

/-- The only roots of `h z = z` in `[0,1]` are `1` and `d = (1-b-c)/(c(1-c))`. -/
theorem root_cases (hc0 : 0 < c) (hc1 : c < 1) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hroot : 1 - b / (1 - c) + b * z / (1 - c * z) = z) :
    z = 1 ∨ z = (1 - b - c) / (c * (1 - c)) := by
  have h1c : 1 - c ≠ 0 := by linarith
  have hcz : 1 - c * z ≠ 0 := by nlinarith [hz.1, hz.2]
  have hc : c ≠ 0 := hc0.ne'
  field_simp at hroot
  have : (z - 1) * (c * (1 - c) * z - (1 - b - c)) = 0 := by linear_combination hroot
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; field_simp; linarith

end GeomBranching

open GeomBranching

/-- Grinstead–Snell Example 10.11 (PR-142), generating function and mean. The geometric offspring law
`p_k = b c^(k-1)` (`0 < b ≤ 1-c`, `0 < c < 1`) is a probability law with generating function
`h(z) = 1 - b/(1-c) + bz/(1-cz)` on `[0,1]` and mean `m = h'(1) = b/(1-c)^2`. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem geomOffspring_gf_mean {b c : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1) :
    IsOffspring (geomOffspring b c) ∧
      (∀ z ∈ Icc (0 : ℝ) 1,
        offspringGF (geomOffspring b c) z = 1 - b / (1 - c) + b * z / (1 - c * z)) ∧
      HasSum (fun k : ℕ => (k : ℝ) * geomOffspring b c k) (b / (1 - c) ^ 2) :=
  ⟨isOffspring hb hbc hc0 hc1, fun _ hz => gf_eq hc0.le hc1 hz, hasSum_mean hc0.le hc1⟩

/-- Grinstead–Snell Example 10.11 (PR-142), extinction probability. For the geometric offspring law
with mean `m = b/(1-c)^2`: if `m ≤ 1` the extinction probability is `1`; if `m > 1` it is
`d = (1-b-c)/(c(1-c))`, and then `d < 1`. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem geomOffspring_extinction {b c : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c)
    (hc1 : c < 1) :
    (b / (1 - c) ^ 2 ≤ 1 → extinctionProb (geomOffspring b c) = 1) ∧
    (1 < b / (1 - c) ^ 2 →
      extinctionProb (geomOffspring b c) = (1 - b - c) / (c * (1 - c)) ∧
        (1 - b - c) / (c * (1 - c)) < 1) := by
  have hp := isOffspring hb hbc hc0 hc1
  have hsum := hasSum_mean (b := b) hc0.le hc1
  have h1c : 0 < 1 - c := by linarith
  have hp1 : geomOffspring b c 1 < 1 := by simp [geomOffspring]; linarith
  refine ⟨fun hm => extinction_prob_eq_one hp hp1 hsum.summable (by rw [hsum.tsum_eq]; exact hm), ?_⟩
  intro hm
  have hm' : (1 - c) ^ 2 < b := by
    rw [lt_div_iff₀ (by positivity)] at hm; linarith
  have hd : (1 - b - c) / (c * (1 - c)) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  refine ⟨?_, hd⟩
  have hlt := extinction_prob_lt_one hp (by
    rintro ⟨_, h⟩; rw [hsum.tsum_eq] at h; linarith)
  obtain ⟨_, _, ⟨hmem, hfix⟩, _⟩ := extinction_smallest_root hp
  rw [gf_eq hc0.le hc1 hmem] at hfix
  rcases root_cases hc0 hc1 hmem hfix with h | h
  · exact absurd h hlt.ne
  · exact h

/-- Grinstead–Snell Example 10.11 (PR-142), the book's remark that `d < 1` exactly when `m > 1`. -/
@[kb "grinsteadsnell2006" "Example 10.11, p. 392"]
theorem geomOffspring_d_lt_one_iff {b c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (1 - b - c) / (c * (1 - c)) < 1 ↔ 1 < b / (1 - c) ^ 2 := by
  have h1c : 0 < 1 - c := by linarith
  rw [div_lt_one (by positivity), lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

end UndergradKB.Probability
