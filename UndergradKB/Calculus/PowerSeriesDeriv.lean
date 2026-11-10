import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology FormalMultilinearSeries
open scoped ENNReal NNReal Nat

private theorem norm_ofScalars_real' (c : ℕ → ℝ) (n : ℕ) : ‖ofScalars ℝ c n‖ = |c n| := by
  rw [ofScalars_norm, Real.norm_eq_abs]

/-- OpenStax Calculus 2:Theorem 6.4 (CA-368). Term-by-term differentiation: inside the radius of convergence
`|y - a| < R` of `∑ c n (x-a)ⁿ`, the sum is differentiable at `y` with derivative `∑ n c n (y-a)^(n-1)`
(which converges absolutely). -/
@[kb "openstaxcalculus2016" "2:Theorem 6.4, p. 497"]
theorem power_series_hasDerivAt {c : ℕ → ℝ} {a y : ℝ}
    (hy : (‖y - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius) :
    HasDerivAt (fun z => ∑' n, c n * (z - a) ^ n) (∑' n, c n * (n * (y - a) ^ (n - 1))) y ∧
    Summable (fun n : ℕ => |c n * (n * (y - a) ^ (n - 1))|) := by
  obtain ⟨r, hyr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hy
  obtain ⟨s, hrs, hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hrR
  have hyr' : |y - a| < r := by
    have : (‖y - a‖₊ : ℝ≥0) < r := by exact_mod_cast hyr
    have h2 : ‖y - a‖ < (r : ℝ) := by exact_mod_cast this
    rwa [Real.norm_eq_abs] at h2
  have hrs' : (r : ℝ) < s := by exact_mod_cast hrs
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (abs_nonneg _) hyr'
  have hs0 : (0 : ℝ) < s := hr0.trans hrs'
  obtain ⟨C, hC0, hC⟩ := (ofScalars ℝ c).norm_mul_pow_le_of_lt_radius hsR
  have hcn : ∀ n : ℕ, |c n| * (s : ℝ) ^ n ≤ C := fun n => by
    simpa [norm_ofScalars_real'] using hC n
  have hq : ‖(r : ℝ) / s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one hs0]
    exact hrs'
  set u : ℕ → ℝ := fun n => (C / r) * ((n : ℝ) * ((r : ℝ) / s) ^ n) with hu_def
  have hu : Summable u := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left ((C : ℝ) / r)
    simpa [hu_def] using this
  have hbound : ∀ z : ℝ, |z - a| < r → ∀ n : ℕ, |c n * (n * (z - a) ^ (n - 1))| ≤ u n := by
    intro z hz n
    rcases n with _ | m
    · simp [hu_def]
    · have h1 : |z - a| ^ m ≤ (r : ℝ) ^ m := pow_le_pow_left₀ (abs_nonneg _) hz.le m
      have h2 : |c (m + 1)| ≤ C / (s : ℝ) ^ (m + 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact hcn (m + 1)
      rw [abs_mul, abs_mul, abs_pow, Nat.add_sub_cancel]
      have h3 : |((m + 1 : ℕ) : ℝ)| = (m : ℝ) + 1 := by
        rw [abs_of_nonneg (by positivity)]; push_cast; ring
      rw [h3]
      have h4 : u (m + 1) = C / (s : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * (r : ℝ) ^ m) := by
        simp only [hu_def]
        push_cast
        rw [div_pow]
        field_simp
        ring
      rw [h4]
      have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      have h5 : |c (m + 1)| * (((m : ℝ) + 1) * |z - a| ^ m)
          ≤ (C / (s : ℝ) ^ (m + 1)) * (((m : ℝ) + 1) * (r : ℝ) ^ m) := by
        gcongr
      exact h5
  have ht : IsOpen (Set.Ioo (a - r) (a + r)) := isOpen_Ioo
  have hmem : ∀ z, z ∈ Set.Ioo (a - (r : ℝ)) (a + r) ↔ |z - a| < r := fun z => by
    rw [abs_lt, Set.mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun n z => c n * (z - a) ^ n)
    (g' := fun n z => c n * (n * (z - a) ^ (n - 1))) (u := u) (t := Set.Ioo (a - r) (a + r))
    (y₀ := a) hu ht isPreconnected_Ioo
    (fun n z _ => by
      have hid : HasDerivAt (fun z : ℝ => z - a) 1 z := (hasDerivAt_id z).sub_const a
      have := (hid.fun_pow n).const_mul (c n)
      simpa using this)
    (fun n z hz => by
      rw [Real.norm_eq_abs]
      exact hbound z ((hmem z).mp hz) n)
    (by rw [hmem]; simpa using hr0)
    (by
      refine (hasSum_single 0 (fun n hn => ?_)).summable
      simp [hn])
    ((hmem y).mpr hyr')
  have hsm : Summable (fun n : ℕ => |c n * (n * (y - a) ^ (n - 1))|) := by
    refine Summable.of_norm_bounded hu ?_
    intro n
    rw [Real.norm_eq_abs, abs_abs]
    exact hbound y hyr' n
  exact ⟨hd, hsm⟩

/-- OpenStax Calculus 2:Theorem 6.4 (CA-368). Term-by-term integration: inside the radius of convergence
`|y - a| < R` of `∑ c n (x-a)ⁿ`, the series `F x = ∑ c n (x-a)^(n+1)/(n+1)` is differentiable at `y` with
derivative `∑ c n (y-a)ⁿ`, i.e. `F` is an antiderivative of the sum. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.4, p. 497"]
theorem power_series_integral_hasDerivAt {c : ℕ → ℝ} {a y : ℝ}
    (hy : (‖y - a‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius) :
    HasDerivAt (fun z => ∑' n : ℕ, c n * (z - a) ^ (n + 1) / ((n : ℝ) + 1))
      (∑' n, c n * (y - a) ^ n) y := by
  obtain ⟨r, hyr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hy
  have hyr' : |y - a| < r := by
    have : (‖y - a‖₊ : ℝ≥0) < r := by exact_mod_cast hyr
    have h2 : ‖y - a‖ < (r : ℝ) := by exact_mod_cast this
    rwa [Real.norm_eq_abs] at h2
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (abs_nonneg _) hyr'
  have hu : Summable (fun n : ℕ => |c n| * (r : ℝ) ^ n) := by
    have := (ofScalars ℝ c).summable_norm_mul_pow hrR
    simpa [norm_ofScalars_real'] using this
  have hmem : ∀ z, z ∈ Set.Ioo (a - (r : ℝ)) (a + r) ↔ |z - a| < r := fun z => by
    rw [abs_lt, Set.mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => c n * (z - a) ^ (n + 1) / ((n : ℝ) + 1))
    (g' := fun n z => c n * (z - a) ^ n) (u := fun n => |c n| * (r : ℝ) ^ n)
    (t := Set.Ioo (a - r) (a + r)) (y₀ := a) hu isOpen_Ioo isPreconnected_Ioo
    (fun n z _ => by
      have hid : HasDerivAt (fun z : ℝ => z - a) 1 z := (hasDerivAt_id z).sub_const a
      have := ((hid.fun_pow (n + 1)).const_mul (c n)).div_const ((n : ℝ) + 1)
      convert this using 1
      push_cast
      field_simp)
    (fun n z hz => by
      have hz' := (hmem z).mp hz
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      gcongr)
    (by rw [hmem]; simpa using hr0)
    (by
      refine (hasSum_single 0 (fun n hn => ?_)).summable
      simp [hn])
    ((hmem y).mpr hyr')

end UndergradKB.Calculus
