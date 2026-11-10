import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import UndergradKB.Trigonometry.Reciprocal
import UndergradKB.Trigonometry.Equations

/-! # Periods, amplitude, phase shift (Corral §5.1-5.2; OpenStax §8.1-8.2)

The period of a periodic function is its least positive period (Corral eq 5.1, OpenStax §8.1); we express
"`p` is the period of `f`" as `IsLeast {p | 0 < p ∧ Function.Periodic f p} p`. Mathlib proves that `sin`, `cos`
have period `2π` and `tan`, `cot` period `π` (`Real.sin_periodic`, …) but not that these are the least periods.

* `isLeast_period_sin`, `…_cos`, `…_tan`, `…_cot`, `…_sec`, `…_csc` (Corral Example 5.3, OpenStax §8.1-8.2);
* `isLeast_period_sin_mul`, `…_cos_mul`, `…_tan_mul`: `sin ωx`, `cos ωx` have period `2π/ω` and `tan ωx` period
  `π/ω` for `ω > 0` (Corral §5.2, OpenStax §8.1);
* `range_sinusoid`, `amplitude_sinusoid`, `midline_sinusoid`: `y = A sin(Bx - C) + D` takes exactly the values
  in `[D - |A|, D + |A|]`; its amplitude (half the difference of the largest and smallest values) is `|A|` and its
  midline is `y = D` (Corral §5.2, OpenStax §8.1);
* `sinusoid_phase_shift`: `A sin(ωx - φ)` is `A sin ωx` shifted right by `φ/ω`;
* `range_tan_transformed`: `y = A tan(Bx - C) + D` takes every real value (OpenStax §8.2).
-/

namespace UndergradKB.Trigonometry

open Real Set Function

/-- If `sin` has period `p > 0` then `cos p = 1`. -/
private lemma cos_eq_one_of_periodic_sin {p : ℝ} (h : Periodic sin p) : cos p = 1 := by
  have := h (π / 2)
  rw [show π / 2 + p = p + π / 2 by ring, sin_add_pi_div_two, sin_pi_div_two] at this
  exact this

/-- A positive real with `cos p = 1` is at least `2π`. -/
private lemma two_pi_le_of_cos_eq_one {p : ℝ} (hp : 0 < p) (h : cos p = 1) : 2 * π ≤ p := by
  obtain ⟨n, hn⟩ := (cos_eq_one_iff p).1 h
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < n := by
      by_contra hneg
      have hneg := not_lt.1 hneg
      nlinarith [pi_pos]
    have : (0 : ℤ) < n := by exact_mod_cast this
    have : (1 : ℤ) ≤ n := by omega
    exact_mod_cast this
  nlinarith [pi_pos]

/-- **The period of the sine is `2π`**: `2π` is the least positive period of `sin`. (TR-122) -/
@[kb "corraltrig" "Example 5.3, p. 117"]
theorem isLeast_period_sin : IsLeast {p | 0 < p ∧ Periodic sin p} (2 * π) :=
  ⟨⟨by positivity, sin_periodic⟩, fun _ ⟨hp, h⟩ => two_pi_le_of_cos_eq_one hp
    (cos_eq_one_of_periodic_sin h)⟩

/-- The period of the cosine is `2π`. (TR-122) -/
theorem isLeast_period_cos : IsLeast {p | 0 < p ∧ Periodic cos p} (2 * π) := by
  refine ⟨⟨by positivity, cos_periodic⟩, fun p ⟨hp, h⟩ => two_pi_le_of_cos_eq_one hp ?_⟩
  have := h 0
  rwa [zero_add, cos_zero] at this

/-- The period of the secant is `2π`. (TR-122) -/
theorem isLeast_period_sec : IsLeast {p | 0 < p ∧ Periodic sec p} (2 * π) := by
  refine ⟨⟨by positivity, sec_periodic⟩, fun p ⟨hp, h⟩ => two_pi_le_of_cos_eq_one hp ?_⟩
  have := h 0
  rw [zero_add, sec, sec, cos_zero, inv_one, inv_eq_one] at this
  exact this

/-- The period of the cosecant is `2π`. (TR-122) -/
theorem isLeast_period_csc : IsLeast {p | 0 < p ∧ Periodic csc p} (2 * π) := by
  refine ⟨⟨by positivity, csc_periodic⟩, fun p ⟨hp, h⟩ => two_pi_le_of_cos_eq_one hp ?_⟩
  have := h (π / 2)
  rw [csc, csc, show π / 2 + p = p + π / 2 by ring, sin_add_pi_div_two, sin_pi_div_two, inv_one,
    inv_eq_one] at this
  exact this

/-- A positive period `p` of a function with `f (π/4 + p) = 1`, where `f = tan`: then `p ≥ π`. -/
private lemma pi_le_of_tan_eq_one {p : ℝ} (hp : 0 < p) (h : tan (π / 4 + p) = 1) : π ≤ p := by
  have hc : cos (π / 4 + p) ≠ 0 := by
    intro hc
    rw [tan_eq_sin_div_cos, hc, div_zero] at h
    exact zero_ne_one h
  obtain ⟨k, hk⟩ := (tan_eq_iff hc).1 h
  rw [arctan_one] at hk
  have hk' : p = k * π := by linarith
  have : (0 : ℝ) < k := by
    by_contra hneg
    have hneg := not_lt.1 hneg
    nlinarith [pi_pos]
  have : (0 : ℤ) < k := by exact_mod_cast this
  have : (1 : ℤ) ≤ k := by omega
  have : (1 : ℝ) ≤ k := by exact_mod_cast this
  nlinarith [pi_pos]

/-- **The period of the tangent is `π`**: `π` is the least positive period of `tan`. (TR-122) -/
@[kb "openstaxalgtrig2e" "§8.2 (period of the tangent), p. 770"]
theorem isLeast_period_tan : IsLeast {p | 0 < p ∧ Periodic tan p} π := by
  refine ⟨⟨pi_pos, tan_periodic⟩, fun p ⟨hp, h⟩ => pi_le_of_tan_eq_one hp ?_⟩
  rw [h (π / 4), tan_pi_div_four]

/-- The period of the cotangent is `π`. (TR-122) -/
theorem isLeast_period_cot : IsLeast {p | 0 < p ∧ Periodic cot p} π := by
  refine ⟨⟨pi_pos, cot_periodic⟩, fun p ⟨hp, h⟩ => ?_⟩
  -- `tan` has period `p` too, since `tan x = cot (π/2 - x)`
  refine pi_le_of_tan_eq_one hp ?_
  have h' : ∀ x, tan x = cot (π / 2 - x) := fun x => (cot_pi_div_two_sub x).symm
  have hper : Periodic tan p := by
    intro x
    rw [h', h', show π / 2 - x = π / 2 - (x + p) + p by ring, h]
  rw [hper (π / 4), tan_pi_div_four]

/-- Rescaling the variable rescales the periods: `x ↦ f (ω x)` has period `p` iff `f` has period `ωp`. -/
private lemma periodic_comp_mul_iff {f : ℝ → ℝ} {ω p : ℝ} (hω : ω ≠ 0) :
    Periodic (fun x => f (ω * x)) p ↔ Periodic f (ω * p) := by
  constructor
  · intro h y
    have := h (y / ω)
    simp only at this
    rwa [mul_add, mul_div_cancel₀ y hω] at this
  · intro h x
    show f (ω * (x + p)) = f (ω * x)
    rw [mul_add, h]

private lemma isLeast_period_comp_mul {f : ℝ → ℝ} {T ω : ℝ} (hω : 0 < ω)
    (hf : IsLeast {p | 0 < p ∧ Periodic f p} T) :
    IsLeast {p | 0 < p ∧ Periodic (fun x => f (ω * x)) p} (T / ω) := by
  refine ⟨⟨div_pos hf.1.1 hω, (periodic_comp_mul_iff hω.ne').2 ?_⟩, fun p ⟨hp, h⟩ => ?_⟩
  · rw [mul_div_cancel₀ T hω.ne']; exact hf.1.2
  · have := hf.2 ⟨mul_pos hω hp, (periodic_comp_mul_iff hω.ne').1 h⟩
    rw [div_le_iff₀ hω]; linarith

/-- **Period of `sin ωx`**: for `ω > 0` the function `x ↦ sin (ωx)` has period `2π/ω`. (TR-124) -/
@[kb "corraltrig" "Box §5.2 (period 2π/ω), p. 118"]
theorem isLeast_period_sin_mul {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Periodic (fun x => sin (ω * x)) p} (2 * π / ω) :=
  isLeast_period_comp_mul hω isLeast_period_sin

/-- Period of `cos ωx`: `2π/ω` for `ω > 0`. (TR-124) -/
theorem isLeast_period_cos_mul {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Periodic (fun x => cos (ω * x)) p} (2 * π / ω) :=
  isLeast_period_comp_mul hω isLeast_period_cos

/-- Period of `tan ωx`: `π/ω` for `ω > 0`. (TR-124) -/
theorem isLeast_period_tan_mul {ω : ℝ} (hω : 0 < ω) :
    IsLeast {p | 0 < p ∧ Periodic (fun x => tan (ω * x)) p} (π / ω) :=
  isLeast_period_comp_mul hω isLeast_period_tan

/-- **Range of a sinusoid**: for `B ≠ 0`, `y = A sin (Bx - C) + D` takes exactly the values in
`[D - |A|, D + |A|]`. (TR-127, TR-128) -/
@[kb "openstaxalgtrig2e" "§8.1 (amplitude, midline, vertical shift), p. 757"]
theorem range_sinusoid (A B C D : ℝ) (hB : B ≠ 0) :
    range (fun x => A * sin (B * x - C) + D) = Icc (D - |A|) (D + |A|) := by
  ext y
  simp only [mem_range, mem_Icc]
  constructor
  · rintro ⟨x, rfl⟩
    have h1 : |A * sin (B * x - C)| ≤ |A| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg A) (abs_sin_le_one _)
    constructor <;> linarith [(abs_le.1 h1).1, (abs_le.1 h1).2]
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne A 0 with rfl | hA
    · exact ⟨0, by simp at h1 h2 ⊢; linarith⟩
    · set s := (y - D) / A with hs
      have hs1 : |s| ≤ 1 := by
        rw [hs, abs_div, div_le_one (abs_pos.2 hA), abs_le]
        constructor <;> linarith
      refine ⟨(arcsin s + C) / B, ?_⟩
      rw [mul_div_cancel₀ _ hB, add_sub_cancel_right, sin_arcsin (abs_le.1 hs1).1 (abs_le.1 hs1).2,
        hs]
      field_simp
      ring

/-- The amplitude of a function: half the difference of its largest and smallest values (Corral §5.2). -/
noncomputable def amplitude (f : ℝ → ℝ) : ℝ := (sSup (range f) - sInf (range f)) / 2

/-- The midline of a function: the average of its largest and smallest values (OpenStax §8.1). -/
noncomputable def midline (f : ℝ → ℝ) : ℝ := (sSup (range f) + sInf (range f)) / 2

/-- **Amplitude of a sinusoid**: `y = A sin (Bx - C) + D` (`B ≠ 0`) has amplitude `|A|`. (TR-127) -/
@[kb "corraltrig" "Box §5.2 (amplitude), p. 119"]
theorem amplitude_sinusoid (A B C D : ℝ) (hB : B ≠ 0) :
    amplitude (fun x => A * sin (B * x - C) + D) = |A| := by
  have hle : D - |A| ≤ D + |A| := by linarith [abs_nonneg A]
  rw [amplitude, range_sinusoid A B C D hB, csSup_Icc hle, csInf_Icc hle]
  ring

/-- **Midline of a sinusoid**: `y = A sin (Bx - C) + D` (`B ≠ 0`) has midline `y = D`. (TR-128) -/
theorem midline_sinusoid (A B C D : ℝ) (hB : B ≠ 0) :
    midline (fun x => A * sin (B * x - C) + D) = D := by
  have hle : D - |A| ≤ D + |A| := by linarith [abs_nonneg A]
  rw [midline, range_sinusoid A B C D hB, csSup_Icc hle, csInf_Icc hle]
  ring

/-- **Phase shift**: for `ω ≠ 0`, the graph of `A sin (ωx - φ)` is that of `A sin ωx` shifted horizontally by
`φ/ω`. (TR-123) -/
@[kb "corraltrig" "Box §5.2 (phase shift), p. 117"]
theorem sinusoid_phase_shift (A ω φ : ℝ) (hω : ω ≠ 0) (x : ℝ) :
    A * sin (ω * x - φ) = A * sin (ω * (x - φ / ω)) := by
  rw [mul_sub, mul_div_cancel₀ φ hω]

/-- **Range of a transformed tangent**: for `A ≠ 0`, `B ≠ 0`, `y = A tan (Bx - C) + D` takes every real value.
(TR-130) -/
@[kb "openstaxalgtrig2e" "§8.2 (properties of y = A tan(Bx - C) + D), p. 773"]
theorem range_tan_transformed (A B C D : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    range (fun x => A * tan (B * x - C) + D) = univ := by
  refine eq_univ_of_forall fun y => ?_
  obtain ⟨u, hu⟩ := tan_surjective ((y - D) / A)
  refine ⟨(u + C) / B, ?_⟩
  simp only
  rw [mul_div_cancel₀ _ hB, add_sub_cancel_right, hu]
  field_simp
  ring

end UndergradKB.Trigonometry
