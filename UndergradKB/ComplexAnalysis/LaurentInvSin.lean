import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import UndergradKB.Common.Attr
import UndergradKB.ComplexAnalysis.ExamplesWave4b

/-!
# Beck et al., Example 8.3.4: the Laurent series of `1/sin z`

The Laurent expansion of `1 / sin z` at `0` begins `1/z + z/6 + 7 z^3/360 + 31 z^5/15120`.
-/

open Set Metric Complex Filter Topology Asymptotics

namespace UndergradKB.ComplexAnalysis

/-- The Taylor polynomial of `sin` of degree `7`. -/
private noncomputable def sinPoly (z : ℂ) : ℂ := z - z ^ 3 / 6 + z ^ 5 / 120 - z ^ 7 / 5040

private theorem sin_sub_sinPoly_bound :
    ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Complex.sin z - sinPoly z‖ ≤ C * ‖z‖ ^ 9 := by
  refine ⟨((Nat.succ 9 : ℕ) : ℝ) * ((Nat.factorial 9 : ℕ) * (9 : ℕ) : ℝ)⁻¹, fun z hz => ?_⟩
  have h1 := Complex.exp_bound (x := z * I) (by simpa using hz) (n := 9) (by norm_num)
  have h2 := Complex.exp_bound (x := -z * I) (by simpa using hz) (n := 9) (by norm_num)
  have hn1 : ‖z * I‖ = ‖z‖ := by simp
  have hn2 : ‖-z * I‖ = ‖z‖ := by simp
  rw [hn1] at h1
  rw [hn2] at h2
  have key : Complex.sin z - sinPoly z =
      ((Complex.exp (-z * I) - ∑ m ∈ Finset.range 9, (-z * I) ^ m / m.factorial) -
       (Complex.exp (z * I) - ∑ m ∈ Finset.range 9, (z * I) ^ m / m.factorial)) * I / 2 := by
    have hI2 : I ^ 2 = -1 := Complex.I_sq
    have hs : Complex.sin z = (Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2 := by
      rw [Complex.sin]
    rw [hs]
    have hI3 : I ^ 3 = -I := by rw [pow_succ, hI2]; ring
    have hI4 : I ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hI2]; norm_num
    have hI5 : I ^ 5 = I := by rw [pow_succ, hI4]; ring
    have hI6 : I ^ 6 = -1 := by rw [pow_succ, hI5, ← sq, hI2]
    have hI7 : I ^ 7 = -I := by rw [pow_succ, hI6]; ring
    have hI8 : I ^ 8 = 1 := by rw [pow_succ, hI7]; linear_combination (-1 : ℂ) * hI2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, sinPoly, mul_pow]
    simp only [hI2, hI3, hI4, hI5, hI6, hI7, hI8]
    norm_num [Nat.factorial]
    linear_combination (-(z - z ^ 3 / 6 + z ^ 5 / 120 - z ^ 7 / 5040)) * hI2
  rw [key]
  have : ‖((Complex.exp (-z * I) - ∑ m ∈ Finset.range 9, (-z * I) ^ m / m.factorial) -
       (Complex.exp (z * I) - ∑ m ∈ Finset.range 9, (z * I) ^ m / m.factorial)) * I / 2‖ ≤
      (‖Complex.exp (-z * I) - ∑ m ∈ Finset.range 9, (-z * I) ^ m / m.factorial‖ +
       ‖Complex.exp (z * I) - ∑ m ∈ Finset.range 9, (z * I) ^ m / m.factorial‖) / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one]
    have := norm_sub_le (Complex.exp (-z * I) - ∑ m ∈ Finset.range 9, (-z * I) ^ m / m.factorial)
      (Complex.exp (z * I) - ∑ m ∈ Finset.range 9, (z * I) ^ m / m.factorial)
    simp only [Complex.norm_ofNat]
    linarith
  linarith

private theorem sin_sub_sinPoly_isBigO :
    (fun z : ℂ => Complex.sin z - sinPoly z) =O[𝓝 0] fun z => z ^ 9 := by
  obtain ⟨C, hC⟩ := sin_sub_sinPoly_bound
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with z hz
  have : ‖z‖ ≤ 1 := by simpa using hz
  simpa [norm_pow] using hC z this

/-- The Laurent polynomial `1/z + z/6 + 7 z^3/360 + 31 z^5/15120`. -/
private noncomputable def laurentPoly (z : ℂ) : ℂ :=
  1 / z + z / 6 + 7 / 360 * z ^ 3 + 31 / 15120 * z ^ 5

private theorem sin_mul_laurentPoly_isBigO :
    (fun z : ℂ => 1 - Complex.sin z * laurentPoly z) =O[𝓝[≠] 0] fun z => z ^ 8 := by
  have hpoly : (fun z : ℂ => 1 - sinPoly z * laurentPoly z) =O[𝓝[≠] 0] fun z => z ^ 8 := by
    set c8 : ℂ := (-1/6)*(31/15120) + (1/120)*(7/360) + (-1/5040)*(1/6) with hc8
    set c10 : ℂ := (1/120)*(31/15120) + (-1/5040)*(7/360) with hc10
    set c12 : ℂ := (-1/5040)*(31/15120) with hc12
    have heq : ∀ z : ℂ, z ≠ 0 → 1 - sinPoly z * laurentPoly z =
        z ^ 8 * (-(c8 + c10 * z ^ 2 + c12 * z ^ 4)) := by
      intro z hz
      simp only [sinPoly, laurentPoly, hc8, hc10, hc12]
      field_simp
      ring
    have hw : (fun z : ℂ => -(c8 + c10 * z ^ 2 + c12 * z ^ 4)) =O[𝓝[≠] 0] fun _ => (1 : ℂ) := by
      have hc : Continuous fun z : ℂ => -(c8 + c10 * z ^ 2 + c12 * z ^ 4) := by fun_prop
      exact (hc.tendsto 0).isBigO_one ℂ |>.mono nhdsWithin_le_nhds
    have := (isBigO_refl (fun z : ℂ => z ^ 8) (𝓝[≠] 0)).mul hw
    refine this.congr' ?_ ?_
    · exact (eventually_mem_nhdsWithin.mono fun z hz => (heq z hz).symm)
    · exact Eventually.of_forall fun z => by simp
  have hR : (fun z : ℂ => Complex.sin z - sinPoly z) =O[𝓝[≠] 0] fun z => z ^ 9 :=
    sin_sub_sinPoly_isBigO.mono nhdsWithin_le_nhds
  have hW : (fun z : ℂ => 1 + z ^ 2 / 6 + 7 / 360 * z ^ 4 + 31 / 15120 * z ^ 6) =O[𝓝[≠] 0]
      fun _ => (1 : ℂ) := by
    have hc : Continuous fun z : ℂ => 1 + z ^ 2 / 6 + 7 / 360 * z ^ 4 + 31 / 15120 * z ^ 6 := by
      fun_prop
    exact (hc.tendsto 0).isBigO_one ℂ |>.mono nhdsWithin_le_nhds
  have h1 : (fun z : ℂ => (Complex.sin z - sinPoly z) * z⁻¹) =O[𝓝[≠] 0] fun z => z ^ 8 := by
    refine ((hR.mul (isBigO_refl (fun z : ℂ => z⁻¹) _)).congr' ?_ ?_)
    · exact Eventually.of_forall fun z => rfl
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have : z ≠ 0 := hz
      field_simp
  have h2 := h1.mul hW
  have h2' : (fun z : ℂ => (Complex.sin z - sinPoly z) * laurentPoly z) =O[𝓝[≠] 0]
      fun z => z ^ 8 := by
    refine h2.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have : z ≠ 0 := hz
      simp only [laurentPoly]
      field_simp
    · exact Eventually.of_forall fun z => by simp
  refine (hpoly.sub h2').congr' ?_ ?_
  · exact Eventually.of_forall fun z => by ring
  · exact Eventually.of_forall fun z => by simp

private theorem norm_le_two_mul_sin :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have h := hasDerivAt_iff_tendsto_slope.1 (Complex.hasDerivAt_sin 0)
  rw [Complex.cos_zero] at h
  have h2 := h.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h2, self_mem_nhdsWithin] with z hz hz0
  have hz0 : z ≠ 0 := hz0
  rw [slope_def_field] at hz
  simp only [dist_eq_norm, Complex.sin_zero, sub_zero] at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have h3 : ‖Complex.sin z / z‖ > 1 / 2 := by
    have := norm_sub_norm_le 1 (Complex.sin z / z)
    simp only [norm_one] at this
    linarith [norm_sub_rev (Complex.sin z / z) 1]
  rw [norm_div, gt_iff_lt, lt_div_iff₀ hn] at h3
  linarith

/-- Beck Example 8.3.4: the Laurent expansion of `1/sin z` at `0` begins
`1/z + z/6 + 7 z^3/360 + 31 z^5/15120`; precisely, the remainder is `O(z^7)`. -/
@[kb "beck2025" "Example 8.3.4, p. 139"]
theorem inv_sin_sub_laurent_isBigO :
    (fun z : ℂ => 1 / Complex.sin z - (1 / z + z / 6 + 7 / 360 * z ^ 3 + 31 / 15120 * z ^ 5))
      =O[𝓝[≠] 0] (fun z => z ^ 7) := by
  obtain ⟨K, hK⟩ := (sin_mul_laurentPoly_isBigO).bound
  refine IsBigO.of_bound (2 * |K|) ?_
  filter_upwards [hK, norm_le_two_mul_sin, self_mem_nhdsWithin] with z hz hz2 hz0
  have hz0 : z ≠ 0 := hz0
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hsn : 0 < ‖Complex.sin z‖ := by linarith
  have hs0 : Complex.sin z ≠ 0 := norm_pos_iff.1 hsn
  have heq : 1 / Complex.sin z - (1 / z + z / 6 + 7 / 360 * z ^ 3 + 31 / 15120 * z ^ 5) =
      (1 - Complex.sin z * laurentPoly z) / Complex.sin z := by
    simp only [laurentPoly]
    field_simp
  rw [heq, norm_div, div_le_iff₀ hsn]
  rw [norm_pow] at hz ⊢
  have h8 : ‖(1 : ℂ) - Complex.sin z * laurentPoly z‖ ≤ |K| * ‖z‖ ^ 8 :=
    hz.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg (norm_nonneg z) 8))
  have : |K| * ‖z‖ ^ 8 = |K| * ‖z‖ ^ 7 * ‖z‖ := by ring
  have hK0 : 0 ≤ |K| * ‖z‖ ^ 7 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hz2 hK0]

/-- Beck Example 8.3.4: `(1/sin z - 1/z) / z → 1/6` as `z → 0`. -/
@[kb "beck2025" "Example 8.3.4, p. 139"]
theorem tendsto_inv_sin_sub_inv_div :
    Tendsto (fun z : ℂ => (1 / Complex.sin z - 1 / z) / z) (𝓝[≠] 0) (𝓝 (1 / 6)) := by
  set f : ℂ → ℂ := fun z =>
    1 / Complex.sin z - (1 / z + z / 6 + 7 / 360 * z ^ 3 + 31 / 15120 * z ^ 5) with hf
  have h1 : (fun z : ℂ => f z * z⁻¹) =O[𝓝[≠] 0] fun z => z ^ 6 := by
    refine ((inv_sin_sub_laurent_isBigO.mul (isBigO_refl (fun z : ℂ => z⁻¹) _)).congr' ?_ ?_)
    · exact Eventually.of_forall fun z => rfl
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have : z ≠ 0 := hz
      field_simp
  have h2 : Tendsto (fun z : ℂ => z ^ 6) (𝓝[≠] 0) (𝓝 0) :=
    ((continuous_pow 6).tendsto' (0 : ℂ) 0 (by simp)).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun z : ℂ => f z * z⁻¹) (𝓝[≠] 0) (𝓝 0) := h1.trans_tendsto h2
  have h4 : Tendsto (fun z : ℂ => (1 : ℂ) / 6 + 7 / 360 * z ^ 2 + 31 / 15120 * z ^ 4)
      (𝓝[≠] 0) (𝓝 (1 / 6 + 7 / 360 * 0 ^ 2 + 31 / 15120 * 0 ^ 4)) :=
    ((by fun_prop :
      Continuous fun z : ℂ => (1 : ℂ) / 6 + 7 / 360 * z ^ 2 + 31 / 15120 * z ^ 4).tendsto
      0).mono_left nhdsWithin_le_nhds
  have h5 := h3.add h4
  norm_num at h5
  refine h5.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z ≠ 0 := hz
  simp only [hf]
  field_simp
  ring

/-- Beck Example 8.3.4: the function `g z = 1/sin z - 1/z` (`z ≠ 0`), `g 0 = 0`, is
differentiable at `0` with derivative `1/6`. -/
@[kb "beck2025" "Example 8.3.4, p. 139"]
theorem hasDerivAt_inv_sin_sub_inv :
    HasDerivAt (fun z : ℂ => if z = 0 then 0 else 1 / Complex.sin z - 1 / z) (1 / 6) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_inv_sin_sub_inv_div.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z ≠ 0 := hz
  simp [slope_def_field, this, div_eq_inv_mul]

end UndergradKB.ComplexAnalysis

