import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import UndergradKB.ComplexAnalysis.ExamplesSingularities
import UndergradKB.ComplexAnalysis.ResidueTheorem

/-!
# More worked examples (Beck, Examples 5.3.3, 8.1.7, 8.3.10)

* Example 5.3.3: `2x⁴ + 5x² + 3` has no real root and factors over `ℂ` into four linear factors.
* Example 8.1.7: the power series of `exp` about `π`.
* Example 8.3.10: `∫_{C[2,3]} exp z / sin z dz = 2πi (1 - e^π)`, from the residues at `0` and `π`
  (Examples 9.2.5, 9.2.8) and the residue theorem on the circle.
-/

open Complex Metric Set
open scoped Real Nat

namespace UndergradKB.ComplexAnalysis

/-- Beck Example 5.3.3: `2x⁴ + 5x² + 3` has no real roots, but factors over `ℂ` as
`(x + i)(x - i)(√2 x + √3 i)(√2 x - √3 i)`. -/
@[kb "beck2025" "Example 5.3.3, p. 96"]
theorem example_5_3_3 :
    (∀ x : ℝ, 2 * x ^ 4 + 5 * x ^ 2 + 3 ≠ 0) ∧
    ∀ z : ℂ, 2 * z ^ 4 + 5 * z ^ 2 + 3 =
      (z + I) * (z - I) * ((√2 : ℝ) * z + (√3 : ℝ) * I) * ((√2 : ℝ) * z - (√3 : ℝ) * I) := by
  refine ⟨fun x => by positivity, fun z => ?_⟩
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (-(z ^ 4 + z ^ 2)) * h2 + (-(z ^ 2 + 1)) * h3 +
    (((√2 : ℝ) : ℂ) ^ 2 * z ^ 2 + ((√3 : ℝ) : ℂ) ^ 2 * z ^ 2 -
      ((√3 : ℝ) : ℂ) ^ 2 * (I ^ 2 - 1)) * I_sq

/-- Beck Example 8.1.7: the Taylor series of `exp` centred at `π` is `∑ e^π (z - π)^k / k!`,
converging on all of `ℂ`. -/
@[kb "beck2025" "Example 8.1.7, p. 132"]
theorem example_8_1_7 (z : ℂ) :
    HasSum (fun k : ℕ => Complex.exp π / (k ! : ℂ) * (z - π) ^ k) (Complex.exp z) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (z - π)).mul_left (Complex.exp π)
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_add, add_sub_cancel] at h
  convert h using 2 with k
  ring

/-- Beck Example 8.3.10: `∫_{C[2,3]} exp z / sin z dz = 2πi (1 - e^π)`: the circle encloses the
simple poles `0` and `π` of `exp / sin` (residues `1` and `-e^π`) and no other zero of `sin`. -/
@[kb "beck2025" "Example 8.3.10, p. 142"]
theorem example_8_3_10 :
    (∮ z in C(2, 3), Complex.exp z / Complex.sin z) = 2 * π * I * (1 - Real.exp π) := by
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hS : ∀ s ∈ ({0, (π : ℂ)} : Finset ℂ), s ∈ ball (2 : ℂ) 3 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rw [mem_ball, dist_eq_norm]
    rcases hs with rfl | rfl
    · norm_num
    · rw [show (π : ℂ) - 2 = ((π - 2 : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith [Real.pi_gt_three, Real.pi_lt_four]
  have hf : DifferentiableOn ℂ (fun z => Complex.exp z / Complex.sin z)
      (closedBall (2 : ℂ) 3 \ (({0, (π : ℂ)} : Finset ℂ) : Set ℂ)) := by
    intro z hz
    refine (Complex.differentiable_exp z).div (Complex.differentiable_sin z) ?_
      |>.differentiableWithinAt
    intro hsin
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hsin
    have hz1 := hz.1
    rw [mem_closedBall, dist_eq_norm, hk] at hz1
    have hre := (Complex.abs_re_le_norm _).trans hz1
    simp only [sub_re, mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero,
      re_ofNat] at hre
    rw [abs_le] at hre
    have hk1 : (k : ℝ) * π ≤ 5 := by linarith [hre.2]
    have hk2 : -1 ≤ (k : ℝ) * π := by linarith [hre.1]
    have hkle : k ≤ 1 := by
      by_contra h
      have : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
      nlinarith [Real.pi_gt_three]
    have hkge : 0 ≤ k := by
      by_contra h
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      nlinarith [Real.pi_gt_three]
    have hmem : z ∈ (({0, (π : ℂ)} : Finset ℂ) : Set ℂ) := by
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
      interval_cases k
      · left; simpa using hk
      · right; simpa using hk
    exact hz.2 hmem
  rw [residue_theorem_circle (by norm_num) hS hf, Finset.sum_pair hπ0.symm, example_9_2_5,
    example_9_2_8]
  ring

end UndergradKB.ComplexAnalysis
