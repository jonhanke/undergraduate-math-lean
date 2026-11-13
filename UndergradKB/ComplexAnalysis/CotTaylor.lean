import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import UndergradKB.ComplexAnalysis.Residue

/-!
# Residues of `π cot(πz)/z^p` and `π/(z^p sin(πz))`

Beck et al., *A First Course in Complex Analysis*, Section 10.1. At a nonzero integer the
residues come from the simple zeros of `sin (π z)`; at `0` they come from Taylor coefficients
of `sin z / z`, computed with the Leibniz rule.
-/

open Complex Metric Set Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- `sin z / z`, extended by `1` at `0`. -/
noncomputable def sinc' : ℂ → ℂ := dslope Complex.sin 0

/-- `cos (k π) = (-1)^k` for an integer `k`, in `ℂ`. -/
lemma cos_int_mul_pi_complex (k : ℤ) : Complex.cos (k * π) = (-1) ^ k := by
  have h : Complex.cos (k * π) = ((Real.cos (k * π) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]; push_cast; rfl
  rw [h, Real.cos_int_mul_pi]; push_cast; rfl

/-- Shared setup at a nonzero integer: the residue of `F / sin (π z)` is `F k / (π (-1)^k)`
provided `F` is holomorphic on the ball of radius `1/2` about `k`. -/
lemma residue_div_sin_pi {F : ℂ → ℂ} {k : ℤ} (hF : DifferentiableOn ℂ F (ball (k : ℂ) (1 / 2))) :
    residue (fun z => F z / Complex.sin (π * z)) k = F k / (π * (-1) ^ k) := by
  have hd : ∀ z, HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * z) * π) z := by
    intro z
    simpa using ((hasDerivAt_id z).const_mul (π : ℂ)).csin
  have hder : deriv (fun z : ℂ => Complex.sin (π * z)) k = π * (-1) ^ k := by
    rw [(hd k).deriv]
    rw [show (π : ℂ) * k = k * π from mul_comm _ _, cos_int_mul_pi_complex, mul_comm]
  have hgd : DifferentiableOn ℂ (fun z : ℂ => Complex.sin (π * z)) (ball (k : ℂ) (1 / 2)) :=
    fun z _ => (hd z).differentiableAt.differentiableWithinAt
  have h0 : Complex.sin (π * (k : ℂ)) = 0 := by
    rw [mul_comm]; exact_mod_cast Real.sin_int_mul_pi k |> fun _ => Complex.sin_int_mul_pi k
  have hne : π * (-1 : ℂ) ^ k ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (zpow_ne_zero _ (by norm_num))
  rw [residue_div_of_simple_zero (by norm_num) hF hgd h0 (by rw [hder]; exact hne), hder]

lemma ne_zero_of_mem_ball {k : ℤ} (hk : k ≠ 0) {z : ℂ} (hz : z ∈ ball (k : ℂ) (1 / 2)) :
    z ≠ 0 := by
  rintro rfl
  rw [mem_ball, dist_zero_left, norm_intCast] at hz
  have : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  linarith

/-- The residue of `π cot(πz)/z^p` at a nonzero integer `k` is `1/k^p`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_cot_div_pow {p : ℕ} {k : ℤ} (hk : k ≠ 0) :
    residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) k = 1 / (k : ℂ) ^ p := by
  have hF : DifferentiableOn ℂ (fun z : ℂ => π * Complex.cos (π * z) / z ^ p)
      (ball (k : ℂ) (1 / 2)) := by
    intro z hz
    have := ne_zero_of_mem_ball hk hz
    exact (by fun_prop (disch := exact pow_ne_zero _ this) :
      DifferentiableAt ℂ (fun z : ℂ => π * Complex.cos (π * z) / z ^ p) z).differentiableWithinAt
  have e : (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) =
      fun z => (π * Complex.cos (π * z) / z ^ p) / Complex.sin (π * z) := by
    funext z; rw [Complex.cot_eq_cos_div_sin]; ring
  rw [e, residue_div_sin_pi hF]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hc : Complex.cos (π * k) = (-1) ^ k := by
    rw [mul_comm]; exact cos_int_mul_pi_complex k
  have hne : (-1 : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [hc]
  field_simp

/-- The residue of `π/(z^p sin(πz))` at a nonzero integer `k` is `(-1)^k / k^p`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_div_pow_mul_sin {p : ℕ} {k : ℤ} (hk : k ≠ 0) :
    residue (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) k = (-1) ^ k / (k : ℂ) ^ p := by
  have hF : DifferentiableOn ℂ (fun z : ℂ => π / z ^ p) (ball (k : ℂ) (1 / 2)) := by
    intro z hz
    have := ne_zero_of_mem_ball hk hz
    exact (by fun_prop (disch := exact pow_ne_zero _ this) :
      DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) / z ^ p) z).differentiableWithinAt
  have e : (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) =
      fun z => (π / z ^ p) / Complex.sin (π * z) := by
    funext z; rw [div_div]
  rw [e, residue_div_sin_pi hF]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hne : (-1 : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  field_simp
  linear_combination (-1 : ℂ) * hsq

/-! ### Taylor coefficients at `0` -/

lemma sinc'_differentiable : Differentiable ℂ sinc' := by
  have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).2
    Complex.differentiable_sin.differentiableOn
  exact differentiableOn_univ.1 this

lemma sinc'_contDiff (n : ℕ∞) : ContDiff ℂ n sinc' := sinc'_differentiable.contDiff

lemma sin_eq_mul_sinc' (z : ℂ) : Complex.sin z = z * sinc' z := by
  have := sub_smul_dslope Complex.sin 0 z
  simpa [sinc'] using this.symm

lemma sinc'_zero : sinc' 0 = 1 := by
  simp [sinc', dslope_same]

lemma iteratedDeriv_sin_one : iteratedDeriv 1 Complex.sin = Complex.cos := by
  simp [iteratedDeriv_succ]

lemma iteratedDeriv_sin_two : iteratedDeriv 2 Complex.sin = fun z => -Complex.sin z := by
  rw [iteratedDeriv_succ, iteratedDeriv_sin_one]; funext z; simp

lemma iteratedDeriv_sin_three : iteratedDeriv 3 Complex.sin = fun z => -Complex.cos z := by
  rw [iteratedDeriv_succ, iteratedDeriv_sin_two]; funext z
  simp

lemma iteratedDeriv_sin_four : iteratedDeriv 4 Complex.sin = Complex.sin := by
  rw [iteratedDeriv_succ, iteratedDeriv_sin_three]; funext z
  simp

lemma iteratedDeriv_sin_five : iteratedDeriv 5 Complex.sin = Complex.cos := by
  rw [iteratedDeriv_succ, iteratedDeriv_sin_four]; funext z; simp

lemma iteratedDeriv_cos_succ (k : ℕ) :
    iteratedDeriv k Complex.cos = iteratedDeriv (k + 1) Complex.sin := by
  rw [iteratedDeriv_succ']
  congr 1
  funext z; simp

/-- Leibniz rule applied to `sin z = z * sinc' z` at `0`. -/
lemma iteratedDeriv_sin_zero_succ (m : ℕ) :
    iteratedDeriv (m + 1) Complex.sin 0 = (m + 1) * iteratedDeriv m sinc' 0 := by
  have e : Complex.sin = fun z : ℂ => z * sinc' z := by
    funext z; exact sin_eq_mul_sinc' z
  have key := iteratedDeriv_fun_mul (n := m + 1) (x := (0 : ℂ)) (f := fun z : ℂ => z)
    (g := sinc') contDiffAt_id ((sinc'_contDiff _).contDiffAt)
  rw [e]
  refine key.trans ?_
  rw [Finset.sum_eq_single 1]
  · have : iteratedDeriv 1 (fun a : ℂ => a) 0 = 1 := by simp [iteratedDeriv_fun_id_zero]
    rw [this]; simp
  · intro i _ hi
    rw [iteratedDeriv_fun_id_zero]; simp [hi]
  · intro h; exfalso; apply h; simp

lemma sinc'_iter_zero : iteratedDeriv 0 sinc' 0 = 1 := by
  simp [sinc'_zero]

lemma sinc'_iter_one : iteratedDeriv 1 sinc' 0 = 0 := by
  have h := iteratedDeriv_sin_zero_succ 1
  rw [iteratedDeriv_sin_two] at h
  simpa using h.symm

lemma sinc'_iter_two : iteratedDeriv 2 sinc' 0 = -(1 / 3) := by
  have h := iteratedDeriv_sin_zero_succ 2
  rw [iteratedDeriv_sin_three] at h
  simp at h
  linear_combination (-1 / 3 : ℂ) * h

lemma sinc'_iter_three : iteratedDeriv 3 sinc' 0 = 0 := by
  have h := iteratedDeriv_sin_zero_succ 3
  rw [iteratedDeriv_sin_four] at h
  norm_num at h
  exact h

lemma sinc'_iter_four : iteratedDeriv 4 sinc' 0 = 1 / 5 := by
  have h := iteratedDeriv_sin_zero_succ 4
  rw [iteratedDeriv_sin_five] at h
  simp at h
  linear_combination (-1 / 5 : ℂ) * h

/-- `T z = sinc' (π z)`, so that `sin (π z) = π z T z`. -/
noncomputable def sincPi (z : ℂ) : ℂ := sinc' (π * z)

/-- The reciprocal `1 / T`, holomorphic near `0`. -/
noncomputable def invSincPi (z : ℂ) : ℂ := (sincPi z)⁻¹

lemma sincPi_zero : sincPi 0 = 1 := by simp [sincPi, sinc'_zero]

lemma sin_pi_mul_eq (z : ℂ) : Complex.sin (π * z) = π * z * sincPi z := sin_eq_mul_sinc' _

lemma sincPi_ne_zero {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : sincPi z ≠ 0 := by
  intro h0
  by_cases hz0 : z = 0
  · rw [hz0, sincPi_zero] at h0; exact one_ne_zero h0
  · have hs : Complex.sin (π * z) = 0 := by rw [sin_pi_mul_eq, h0, mul_zero]
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.1 hs
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hzn : z = n := by
      apply mul_left_cancel₀ hpi; rw [hn]; ring
    rw [mem_ball, dist_zero_right, hzn, norm_intCast] at hz
    have h1 : |(n : ℝ)| < 1 := hz
    have : n = 0 := by
      rw [← Int.cast_abs] at h1
      have : |n| < 1 := by exact_mod_cast h1
      have := abs_lt.1 this
      omega
    exact hz0 (by rw [hzn, this]; simp)

lemma sincPi_differentiable : Differentiable ℂ sincPi := by
  intro z; exact (sinc'_differentiable (π * z)).comp z ((differentiableAt_id).const_mul _)

lemma invSincPi_differentiableOn : DifferentiableOn ℂ invSincPi (ball (0 : ℂ) 1) :=
  fun z hz => ((sincPi_differentiable z).inv (sincPi_ne_zero hz)).differentiableWithinAt

lemma invSincPi_contDiffAt (n : ℕ) : ContDiffAt ℂ n invSincPi 0 :=
  ((invSincPi_differentiableOn.analyticAt (ball_mem_nhds 0 one_pos))).contDiffAt

lemma sincPi_contDiff (n : ℕ) : ContDiff ℂ n sincPi := sincPi_differentiable.contDiff

lemma sincPi_iter (k : ℕ) : iteratedDeriv k sincPi 0 = π ^ k * iteratedDeriv k sinc' 0 := by
  have := congrFun (iteratedDeriv_comp_const_mul (n := k) (sinc'_contDiff k) (π : ℂ)) 0
  have h2 : sincPi = fun x => sinc' (π * x) := rfl
  rw [h2]; simpa using this

lemma invSincPi_mul_sincPi : (fun z => invSincPi z * sincPi z) =ᶠ[𝓝 0] fun _ => 1 := by
  filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with z hz
  simp [invSincPi, inv_mul_cancel₀ (sincPi_ne_zero hz)]

/-- Leibniz identity from `invSincPi * sincPi = 1`. -/
lemma leibniz_inv (n : ℕ) :
    iteratedDeriv n (fun z => invSincPi z * sincPi z) 0 = if n = 0 then 1 else 0 := by
  rw [(invSincPi_mul_sincPi).iteratedDeriv_eq n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [iteratedDeriv_const, hn.ne']

lemma leibniz_inv' (n : ℕ) :
    iteratedDeriv n (fun z => invSincPi z * sincPi z) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i invSincPi 0 * iteratedDeriv (n - i) sincPi 0 :=
  iteratedDeriv_fun_mul (invSincPi_contDiffAt n) ((sincPi_contDiff n).contDiffAt)

lemma sincPi_i0 : iteratedDeriv 0 sincPi 0 = 1 := by simp [sincPi_zero]
lemma sincPi_i1 : iteratedDeriv 1 sincPi 0 = 0 := by rw [sincPi_iter, sinc'_iter_one]; simp
lemma sincPi_i2 : iteratedDeriv 2 sincPi 0 = -(π ^ 2 / 3) := by
  rw [sincPi_iter, sinc'_iter_two]; ring
lemma sincPi_i3 : iteratedDeriv 3 sincPi 0 = 0 := by rw [sincPi_iter, sinc'_iter_three]; simp
lemma sincPi_i4 : iteratedDeriv 4 sincPi 0 = π ^ 4 / 5 := by
  rw [sincPi_iter, sinc'_iter_four]; ring

lemma invSincPi_i0 : iteratedDeriv 0 invSincPi 0 = 1 := by
  have h := leibniz_inv 0
  rw [leibniz_inv'] at h
  simpa [sincPi_i0] using h

lemma invSincPi_i1 : iteratedDeriv 1 invSincPi 0 = 0 := by
  have h := leibniz_inv 1
  rw [leibniz_inv'] at h
  simp [Finset.sum_range_succ, sincPi_i0, sincPi_i1, invSincPi_i0] at h
  simpa using h

lemma invSincPi_i2 : iteratedDeriv 2 invSincPi 0 = π ^ 2 / 3 := by
  have h := leibniz_inv 2
  rw [leibniz_inv'] at h
  simp [Finset.sum_range_succ, Nat.choose, sincPi_i0, sincPi_i1, sincPi_i2, invSincPi_i0,
    invSincPi_i1] at h
  linear_combination h

lemma invSincPi_i3 : iteratedDeriv 3 invSincPi 0 = 0 := by
  have h := leibniz_inv 3
  rw [leibniz_inv'] at h
  simp [Finset.sum_range_succ, Nat.choose, sincPi_i0, sincPi_i1, sincPi_i2, sincPi_i3,
    invSincPi_i0, invSincPi_i1, invSincPi_i2] at h
  simpa using h

lemma invSincPi_i4 : iteratedDeriv 4 invSincPi 0 = 7 * π ^ 4 / 15 := by
  have h := leibniz_inv 4
  rw [leibniz_inv'] at h
  simp [Finset.sum_range_succ, Nat.choose, sincPi_i0, sincPi_i1, sincPi_i2, sincPi_i3,
    sincPi_i4, invSincPi_i0, invSincPi_i1, invSincPi_i2, invSincPi_i3] at h
  linear_combination h

/-- `C z = cos (π z)`. -/
noncomputable def cosPi (z : ℂ) : ℂ := Complex.cos (π * z)

lemma cosPi_contDiff (n : ℕ) : ContDiff ℂ n cosPi := by
  have : Differentiable ℂ cosPi := by unfold cosPi; fun_prop
  exact this.contDiff

lemma cosPi_iter (k : ℕ) :
    iteratedDeriv k cosPi 0 = π ^ k * iteratedDeriv (k + 1) Complex.sin 0 := by
  have := congrFun (iteratedDeriv_comp_const_mul (n := k)
    (Complex.differentiable_cos.contDiff : ContDiff ℂ k Complex.cos) (π : ℂ)) 0
  have h2 : cosPi = fun x => Complex.cos (π * x) := rfl
  rw [h2, ← iteratedDeriv_cos_succ]; simpa using this

lemma cosPi_i0 : iteratedDeriv 0 cosPi 0 = 1 := by
  rw [cosPi_iter]; simp
lemma cosPi_i1 : iteratedDeriv 1 cosPi 0 = 0 := by
  rw [cosPi_iter]; simp
lemma cosPi_i2 : iteratedDeriv 2 cosPi 0 = -π ^ 2 := by
  rw [cosPi_iter]; simp
lemma cosPi_i3 : iteratedDeriv 3 cosPi 0 = 0 := by
  rw [cosPi_iter]; simp
lemma cosPi_i4 : iteratedDeriv 4 cosPi 0 = π ^ 4 := by
  rw [cosPi_iter]; simp

lemma cosPi_mul_inv_iter (n : ℕ) :
    iteratedDeriv n (fun z => cosPi z * invSincPi z) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i cosPi 0 * iteratedDeriv (n - i) invSincPi 0 :=
  iteratedDeriv_fun_mul ((cosPi_contDiff n).contDiffAt) (invSincPi_contDiffAt n)

lemma cosPi_mul_inv_two :
    iteratedDeriv 2 (fun z => cosPi z * invSincPi z) 0 = -(2 * π ^ 2 / 3) := by
  rw [cosPi_mul_inv_iter]
  simp [Finset.sum_range_succ, Nat.choose, cosPi_i0, cosPi_i1, cosPi_i2, invSincPi_i0,
    invSincPi_i1, invSincPi_i2]
  ring

lemma cosPi_mul_inv_four :
    iteratedDeriv 4 (fun z => cosPi z * invSincPi z) 0 = -(8 * π ^ 4 / 15) := by
  rw [cosPi_mul_inv_iter]
  simp [Finset.sum_range_succ, Nat.choose, cosPi_i0, cosPi_i1, cosPi_i2, cosPi_i3, cosPi_i4,
    invSincPi_i0, invSincPi_i1, invSincPi_i2, invSincPi_i3, invSincPi_i4]
  ring

lemma residue_sin_zero (p : ℕ) :
    residue (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) 0 =
      iteratedDeriv p invSincPi 0 / p.factorial := by
  refine residue_of_eq_div_pow one_pos invSincPi_differentiableOn p fun z hz => ?_
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz0 : z ≠ 0 := hz.2
  have h1 := sincPi_ne_zero hz.1
  rw [sin_pi_mul_eq, invSincPi, sub_zero]
  field_simp
  ring

lemma residue_cot_zero (p : ℕ) :
    residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) 0 =
      iteratedDeriv p (fun z => cosPi z * invSincPi z) 0 / p.factorial := by
  refine residue_of_eq_div_pow (g := fun z => cosPi z * invSincPi z) one_pos ?_ p fun z hz => ?_
  · intro z hz
    exact (((cosPi_contDiff 1).differentiable one_ne_zero z).mul
      (invSincPi_differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  · have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hz0 : z ≠ 0 := hz.2
    have h1 := sincPi_ne_zero hz.1
    rw [Complex.cot_eq_cos_div_sin, sin_pi_mul_eq, cosPi, invSincPi, sub_zero]
    field_simp
    ring

/-- The residue of `π cot(πz)/z^2` at `0` is `-π²/3`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_cot_div_sq_zero :
    residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ 2) 0 = -(π ^ 2 / 3 : ℂ) := by
  rw [residue_cot_zero, cosPi_mul_inv_two]
  simp [Nat.factorial]
  ring

/-- The residue of `π cot(πz)/z^4` at `0` is `-π⁴/45`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_cot_div_pow_four_zero :
    residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ 4) 0 = -(π ^ 4 / 45 : ℂ) := by
  rw [residue_cot_zero, cosPi_mul_inv_four]
  simp [Nat.factorial]
  ring

/-- The residue of `π/(z^2 sin(πz))` at `0` is `π²/6`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_div_sq_mul_sin_zero :
    residue (fun z : ℂ => π / (z ^ 2 * Complex.sin (π * z))) 0 = (π ^ 2 / 6 : ℂ) := by
  rw [residue_sin_zero, invSincPi_i2]
  simp [Nat.factorial]
  ring

/-- The residue of `π/(z^4 sin(πz))` at `0` is `7π⁴/360`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem residue_pi_div_pow_four_mul_sin_zero :
    residue (fun z : ℂ => π / (z ^ 4 * Complex.sin (π * z))) 0 = (7 * π ^ 4 / 360 : ℂ) := by
  rw [residue_sin_zero, invSincPi_i4]
  simp [Nat.factorial]
  ring

end UndergradKB.ComplexAnalysis
