import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import UndergradKB.ComplexAnalysis.CauchyFormula

/-!
# The separation half of the Jordan curve theorem (rows CX-161, CX-071)

Beck et al. assume the Jordan curve theorem (Section 4.4): a simple closed path divides the plane into
a bounded inside and an unbounded outside. Here the *separation* half is proved for every piecewise
smooth simple closed path `γ` on `[0, 1]`: the complement of the path is not connected, and the inside
`insideOf γ` (the points whose component in the complement is bounded) is not empty. So the field
`inside_nonempty` of Definition 4.4.4 (`IsPositivelyOrientedSimpleClosed`) holds for every such path.

The proof uses the integral `∮_γ dz / (z - a)` (`2 π i` times the winding number):
1. it lies in `2 π i ℤ` for every `a` off the path (`exists_int_pathIntegral_inv_sub`: the function
   `(γ t - a) exp (-∫_0^t γ' / (γ - a))` has derivative zero);
2. it depends continuously on `a` off the path, hence is constant on every connected subset of the
   complement (`pathIntegral_inv_sub_eq_of_isPreconnected`), and it vanishes far from the path;
3. at a regular point `w₀ = γ t₀` (`γ'(t₀) = v ≠ 0`; one exists because a simple closed path is not
   constant) the integrals at `w₀ ± i ε v` differ by nearly `2 π i` for small `ε > 0`: near `t₀` the
   path is a graph over its tangent line, so `log (± i (z - w₀) / v + ε)` are primitives along the
   local arc, and the rest of the path stays away from `w₀`.
So some point off the path has nonzero integral, and its component in the complement is bounded.

The other half of the theorem (the complement has *exactly* two components) is not proved here.
-/

open Set Filter Topology MeasureTheory intervalIntegral Complex
open scoped Real

namespace UndergradKB.ComplexAnalysis

variable {γ : ℝ → ℂ}

/-! ### Off the path, the integrand is continuous -/

lemma continuousOn_inv_sub_image {a : ℂ} {u v : ℝ} (ha : ∀ t ∈ Icc u v, γ t ≠ a) :
    ContinuousOn (fun z => (z - a)⁻¹) (γ '' Icc u v) := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ((continuous_id.sub continuous_const).continuousAt.inv₀
    (sub_ne_zero.2 (ha t ht))).continuousWithinAt

lemma intervalIntegrable_inv_sub_mul {a : ℂ} {u v : ℝ} (hγ : IsPiecewiseSmooth γ u v)
    (huv : u ≤ v) (ha : ∀ t ∈ Icc u v, γ t ≠ a) :
    IntervalIntegrable (fun t => (γ t - a)⁻¹ * deriv γ t) volume u v :=
  IsPiecewiseSmooth.intervalIntegrable_integrand (f := fun z => (z - a)⁻¹) hγ huv
    (continuousOn_inv_sub_image ha)

/-- Splitting `∮_γ dz / (z - a)` at an interior parameter. -/
lemma pathIntegral_inv_sub_add_adjacent {a : ℂ} {u c v : ℝ} (hγ : IsPiecewiseSmooth γ u v)
    (huc : u ≤ c) (hcv : c ≤ v) (ha : ∀ t ∈ Icc u v, γ t ≠ a) :
    pathIntegral (fun z => (z - a)⁻¹) γ u c + pathIntegral (fun z => (z - a)⁻¹) γ c v =
      pathIntegral (fun z => (z - a)⁻¹) γ u v :=
  pathIntegral_add_adjacent
    (intervalIntegrable_inv_sub_mul (hγ.mono le_rfl hcv) huc
      fun t ht => ha t ⟨ht.1, ht.2.trans hcv⟩)
    (intervalIntegrable_inv_sub_mul (hγ.mono huc le_rfl) hcv
      fun t ht => ha t ⟨huc.trans ht.1, ht.2⟩)

/-! ### Step 1: the integral is an integer multiple of `2 π i` -/

/-- For a closed piecewise smooth path and a point `a` off it, `∮_γ dz / (z - a) ∈ 2 π i ℤ`. -/
theorem exists_int_pathIntegral_inv_sub (hγ : IsPiecewiseSmooth γ 0 1) (hcl : γ 0 = γ 1)
    {a : ℂ} (ha : a ∉ pathImage γ) :
    ∃ n : ℤ, pathIntegral (fun z => (z - a)⁻¹) γ 0 1 = n * (2 * π * I) := by
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ a := fun t ht h => ha ⟨t, ht, h⟩
  set h : ℝ → ℂ := fun t => (γ t - a)⁻¹ * deriv γ t with hh
  have hint : IntervalIntegrable h volume 0 1 :=
    intervalIntegrable_inv_sub_mul hγ zero_le_one hne
  have hintOn : IntegrableOn h (uIcc 0 1) volume := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 hint
  set Φ : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, h s with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval hintOn
    rwa [uIcc_of_le zero_le_one] at this
  obtain ⟨S, hd, hdc, -⟩ := hγ.2
  set U : Set ℝ := Ioo 0 1 \ ↑S
  have hU : IsOpen U := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have hhc : ContinuousOn h U := by
    refine ContinuousOn.mul ?_ hdc
    refine ContinuousOn.inv₀ ?_ (fun t ht => sub_ne_zero.2 (hne t (Ioo_subset_Icc_self ht.1)))
    exact (fun t ht => (hd t ht.1 ht.2).continuousAt.continuousWithinAt.sub
      continuousWithinAt_const)
  set g : ℝ → ℂ := fun t => (γ t - a) * exp (-Φ t)
  have hg : ∫ _ in (0 : ℝ)..1, (0 : ℂ) = g 1 - g 0 := by
    refine integral_eq_of_hasDerivAt_off_countable_of_le g (fun _ => 0) zero_le_one
      S.countable_toSet ((hγ.continuousOn.sub continuousOn_const).mul
        (continuous_exp.comp_continuousOn hΦc.neg)) (fun t ht => ?_) intervalIntegrable_const
    have htU : t ∈ U := ht
    have hΦd : HasDerivAt Φ (h t) t :=
      integral_hasDerivAt_right (hint.mono_set (by
          rw [uIcc_of_le zero_le_one, uIcc_of_le ht.1.1.le]
          exact Icc_subset_Icc le_rfl ht.1.2.le))
        (hhc.stronglyMeasurableAtFilter hU t htU) ((hhc t htU).continuousAt (hU.mem_nhds htU))
    have hγd : HasDerivAt γ (deriv γ t) t := (hd t ht.1 ht.2).hasDerivAt
    have h2 := (hγd.sub_const a).mul (hΦd.neg.cexp)
    convert h2 using 1
    have : γ t - a ≠ 0 := sub_ne_zero.2 (hne t (Ioo_subset_Icc_self ht.1))
    simp only [hh]
    field_simp
    ring
  simp only [intervalIntegral.integral_zero, g] at hg
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  rw [hΦ0, neg_zero, exp_zero, mul_one, ← hcl] at hg
  have h0 : γ 0 - a ≠ 0 := sub_ne_zero.2 (hne 0 ⟨le_rfl, zero_le_one⟩)
  have hexp : exp (-Φ 1) = 1 := by
    have := sub_eq_zero.1 hg.symm
    exact (mul_eq_left₀ h0).1 this
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 hexp
  refine ⟨-n, ?_⟩
  have : pathIntegral (fun z => (z - a)⁻¹) γ 0 1 = Φ 1 := rfl
  rw [this, show Φ 1 = -(-Φ 1) by ring, hn]
  push_cast
  ring

/-! ### Step 2: estimates, continuity, constancy on connected sets, vanishing far away -/

/-- The difference of the integrals at two points `x`, `y` at distance at least `r` from the path. -/
lemma norm_pathIntegral_inv_sub_sub_le {u v M r : ℝ} {x y : ℂ} (hγ : IsPiecewiseSmooth γ u v)
    (huv : u ≤ v) (hM : ∀ t ∈ Icc u v, ‖deriv γ t‖ ≤ M) (hr : 0 < r)
    (hx : ∀ t ∈ Icc u v, r ≤ ‖γ t - x‖) (hy : ∀ t ∈ Icc u v, r ≤ ‖γ t - y‖) :
    ‖pathIntegral (fun z => (z - x)⁻¹) γ u v - pathIntegral (fun z => (z - y)⁻¹) γ u v‖ ≤
      M * ‖x - y‖ / r ^ 2 * (v - u) := by
  have hx0 : ∀ t ∈ Icc u v, γ t ≠ x := fun t ht h => by
    have := hx t ht; rw [h, sub_self, norm_zero] at this; linarith
  have hy0 : ∀ t ∈ Icc u v, γ t ≠ y := fun t ht h => by
    have := hy t ht; rw [h, sub_self, norm_zero] at this; linarith
  unfold pathIntegral
  rw [← intervalIntegral.integral_sub (intervalIntegrable_inv_sub_mul hγ huv hx0)
    (intervalIntegrable_inv_sub_mul hγ huv hy0)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
    (C := M * ‖x - y‖ / r ^ 2)
    (f := fun t => (γ t - x)⁻¹ * deriv γ t - (γ t - y)⁻¹ * deriv γ t) (fun t ht => ?_)
  · rwa [abs_of_nonneg (sub_nonneg.2 huv)] at this
  rw [uIoc_of_le huv] at ht
  have ht' : t ∈ Icc u v := Ioc_subset_Icc_self ht
  have hxt : γ t - x ≠ 0 := sub_ne_zero.2 (hx0 t ht')
  have hyt : γ t - y ≠ 0 := sub_ne_zero.2 (hy0 t ht')
  have key : (γ t - x)⁻¹ * deriv γ t - (γ t - y)⁻¹ * deriv γ t =
      (x - y) * deriv γ t / ((γ t - x) * (γ t - y)) := by
    field_simp
    ring
  rw [key, norm_div, norm_mul, norm_mul]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t ht')
  have hden : r ^ 2 ≤ ‖γ t - x‖ * ‖γ t - y‖ := by
    rw [sq]; exact mul_le_mul (hx t ht') (hy t ht') hr.le (norm_nonneg _)
  rw [div_le_div_iff₀ (mul_pos (norm_pos_iff.2 hxt) (norm_pos_iff.2 hyt)) (by positivity)]
  calc ‖x - y‖ * ‖deriv γ t‖ * r ^ 2 ≤ ‖x - y‖ * M * (‖γ t - x‖ * ‖γ t - y‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hM t ht') (norm_nonneg _)) hden
          (by positivity) (by positivity)
    _ = M * ‖x - y‖ * (‖γ t - x‖ * ‖γ t - y‖) := by ring

/-- A point off a compact path has a positive distance from it. -/
lemma exists_pos_le_norm_sub {u v : ℝ} (hc : ContinuousOn γ (Icc u v)) {x : ℂ}
    (hx : x ∉ γ '' Icc u v) : ∃ r > 0, ∀ t ∈ Icc u v, r ≤ ‖γ t - x‖ := by
  have hcl : IsClosed (γ '' Icc u v) := (isCompact_Icc.image_of_continuousOn hc).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x hx
  refine ⟨r, hr, fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt) ⟨t, ht, rfl⟩

/-- `a ↦ ∮_γ dz / (z - a)` is continuous off the path. -/
theorem continuousOn_pathIntegral_inv_sub (hγ : IsPiecewiseSmooth γ 0 1) :
    ContinuousOn (fun a => pathIntegral (fun z => (z - a)⁻¹) γ 0 1) (pathImage γ)ᶜ := by
  obtain ⟨-, -, -, -, M, hM⟩ := id hγ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  intro x hx
  obtain ⟨r, hr, hxr⟩ := exists_pos_le_norm_sub hγ.continuousOn hx
  refine (ContinuousAt.continuousWithinAt ?_)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (r / 2) (ε * (r / 2) ^ 2 / (M + 1)), lt_min (by positivity) (by positivity),
    fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  have hy1 : ‖y - x‖ < r / 2 := hy.trans_le (min_le_left _ _)
  have hy2 : ‖y - x‖ < ε * (r / 2) ^ 2 / (M + 1) := hy.trans_le (min_le_right _ _)
  have hyr : ∀ t ∈ Icc (0 : ℝ) 1, r / 2 ≤ ‖γ t - y‖ := fun t ht => by
    have := norm_sub_le_norm_sub_add_norm_sub (γ t) y x
    have h2 := hxr t ht
    linarith
  have hxr2 : ∀ t ∈ Icc (0 : ℝ) 1, r / 2 ≤ ‖γ t - x‖ := fun t ht => by
    linarith [hxr t ht]
  have := norm_pathIntegral_inv_sub_sub_le hγ zero_le_one hM (by positivity) hyr hxr2
  rw [sub_zero, mul_one] at this
  refine this.trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  rw [lt_div_iff₀ (by positivity)] at hy2
  nlinarith [norm_nonneg (y - x)]

/-- `∮_γ dz / (z - a)` is constant on every connected set off the closed path. -/
theorem pathIntegral_inv_sub_eq_of_isPreconnected (hγ : IsPiecewiseSmooth γ 0 1)
    (hcl : γ 0 = γ 1) {C : Set ℂ} (hC : IsPreconnected C) (hCs : C ⊆ (pathImage γ)ᶜ) {x y : ℂ}
    (hx : x ∈ C) (hy : y ∈ C) :
    pathIntegral (fun z => (z - x)⁻¹) γ 0 1 = pathIntegral (fun z => (z - y)⁻¹) γ 0 1 := by
  set W : ℂ → ℂ := fun a => pathIntegral (fun z => (z - a)⁻¹) γ 0 1
  set f : ℂ → ℝ := fun a => (W a / (2 * π * I)).re
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hint : ∀ a ∈ C, ∃ n : ℤ, W a = n * (2 * π * I) ∧ f a = n := fun a ha => by
    obtain ⟨n, hn⟩ := exists_int_pathIntegral_inv_sub hγ hcl (hCs ha)
    refine ⟨n, hn, ?_⟩
    simp only [f, W] at hn ⊢
    rw [hn, mul_div_cancel_right₀ _ hπ]
    simp
  have hfc : ContinuousOn f C := by
    refine Complex.continuous_re.comp_continuousOn ?_
    exact ((continuousOn_pathIntegral_inv_sub hγ).mono hCs).div_const _
  obtain ⟨m, hm, hfm⟩ := hint x hx
  obtain ⟨n, hn, hfn⟩ := hint y hy
  suffices hmn : m = n by simp only [W] at hm hn; rw [hm, hn, hmn]
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hsub := hC.intermediate_value hx hy hfc
    obtain ⟨z, hz, hfz⟩ := hsub (show (m : ℝ) + 1 / 2 ∈ Icc (f x) (f y) by
      rw [hfm, hfn]
      have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      constructor <;> linarith)
    obtain ⟨k, -, hk⟩ := hint z hz
    rw [hk] at hfz
    have h1 : (m : ℝ) < k := by linarith
    have h2 : (k : ℝ) < m + 1 := by linarith
    have h1' : m < k := by exact_mod_cast h1
    have h2' : k < m + 1 := by exact_mod_cast h2
    omega
  · have hsub := hC.intermediate_value hy hx hfc
    obtain ⟨z, hz, hfz⟩ := hsub (show (n : ℝ) + 1 / 2 ∈ Icc (f y) (f x) by
      rw [hfm, hfn]
      have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      constructor <;> linarith)
    obtain ⟨k, -, hk⟩ := hint z hz
    rw [hk] at hfz
    have h1 : (n : ℝ) < k := by linarith
    have h2 : (k : ℝ) < n + 1 := by linarith
    have h1' : n < k := by exact_mod_cast h1
    have h2' : k < n + 1 := by exact_mod_cast h2
    omega

/-- Far from a closed path, `∮_γ dz / (z - a) = 0`. -/
theorem exists_pathIntegral_inv_sub_eq_zero_far (hγ : IsPiecewiseSmooth γ 0 1) (hcl : γ 0 = γ 1) :
    ∃ R : ℝ, ∀ a : ℂ, R < ‖a‖ → a ∉ pathImage γ ∧ pathIntegral (fun z => (z - a)⁻¹) γ 0 1 = 0 := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hγ.continuousOn).isBounded.exists_norm_le
  obtain ⟨-, -, -, -, M, hM⟩ := id hγ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨B + M + 1, fun a ha => ?_⟩
  have hfar : ∀ t ∈ Icc (0 : ℝ) 1, M + 1 ≤ ‖γ t - a‖ := fun t ht => by
    have h1 := hB _ ⟨t, ht, rfl⟩
    have h2 := norm_sub_norm_le a (γ t)
    rw [norm_sub_rev] at h2
    linarith
  have hnot : a ∉ pathImage γ := by
    rintro ⟨t, ht, rfl⟩
    have := hfar t ht
    rw [sub_self, norm_zero] at this
    linarith
  refine ⟨hnot, ?_⟩
  obtain ⟨n, hn⟩ := exists_int_pathIntegral_inv_sub hγ hcl hnot
  have hle : ‖pathIntegral (fun z => (z - a)⁻¹) γ 0 1‖ ≤ M / (M + 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := M / (M + 1)) (f := fun t => (γ t - a)⁻¹ * deriv γ t) (fun t ht => ?_)
    · simpa [pathIntegral] using this
    rw [uIoc_of_le zero_le_one] at ht
    have ht' := Ioc_subset_Icc_self ht
    rw [norm_mul, norm_inv, inv_mul_eq_div]
    exact div_le_div₀ hM0 (hM t ht') (by positivity) (hfar t ht')
  have hlt : ‖pathIntegral (fun z => (z - a)⁻¹) γ 0 1‖ < 1 :=
    hle.trans_lt ((div_lt_one (by positivity)).2 (by linarith))
  rw [hn] at hlt ⊢
  rcases eq_or_ne n 0 with h0 | h0
  · simp [h0]
  exfalso
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one] at hlt
  have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
    rw [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs h0
  have : ‖(2 : ℂ)‖ * ‖(π : ℂ)‖ = 2 * π := by
    rw [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [this] at hlt
  nlinarith [Real.two_le_pi]

/-- A point off a closed path with nonzero integral `∮_γ dz / (z - a)` lies inside the path. -/
theorem mem_insideOf_of_pathIntegral_inv_sub_ne_zero (hγ : IsPiecewiseSmooth γ 0 1)
    (hcl : γ 0 = γ 1) {a : ℂ} (ha : a ∉ pathImage γ)
    (hW : pathIntegral (fun z => (z - a)⁻¹) γ 0 1 ≠ 0) : a ∈ insideOf γ := by
  refine ⟨ha, ?_⟩
  obtain ⟨R, hR⟩ := exists_pathIntegral_inv_sub_eq_zero_far hγ hcl
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨R, fun z hz => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hzR
  push Not at hzR
  have hC := isPreconnected_connectedComponentIn (F := (pathImage γ)ᶜ) (x := a)
  have := pathIntegral_inv_sub_eq_of_isPreconnected hγ hcl hC (connectedComponentIn_subset _ _)
    hz (mem_connectedComponentIn ha)
  rw [(hR z hzR).2] at this
  exact hW this.symm

/-! ### Step 3: a regular point, and the jump across the path -/

/-- A simple closed piecewise smooth path has a regular point: a parameter `t₀ ∈ (0, 1)` off the
corners with `γ'(t₀) ≠ 0` (otherwise `γ` would be constant on `[0, 1/2]`). -/
lemma exists_regular_point (hγ : IsPiecewiseSmooth γ 0 1) (hinj : InjOn γ (Ico 0 1))
    {S : Finset ℝ} (hd : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ S → DifferentiableAt ℝ γ t) :
    ∃ t₀ ∈ Ioo (0 : ℝ) 1, t₀ ∉ S ∧ deriv γ t₀ ≠ 0 := by
  by_contra hno
  push Not at hno
  have h := integral_eq_of_hasDerivAt_off_countable_of_le γ (fun _ => (0 : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) S.countable_toSet
    (hγ.continuousOn.mono (Icc_subset_Icc le_rfl (by norm_num))) (fun t ht => by
      have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.1, ht.1.2.trans (by norm_num)⟩
      have := (hd t ht1 ht.2).hasDerivAt
      rwa [hno t ht1 ht.2] at this) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  have h2 : γ (1 / 2) = γ 0 := (sub_eq_zero.1 h.symm)
  have := hinj ⟨by norm_num, by norm_num⟩ ⟨le_rfl, by norm_num⟩ h2
  norm_num at this

/-- A point of the slit plane is not zero; the point `w₀ - ε v / c` is where
`c (z - w₀) / v + ε` vanishes. -/
lemma sub_ne_zero_of_mem_slitPlane {w₀ v c z : ℂ} {ε : ℝ} (hv : v ≠ 0) (hc : c ≠ 0)
    (hz : c * ((z - w₀) / v) + ε ∈ slitPlane) : z - (w₀ - ε * v / c) ≠ 0 := by
  intro h
  have hz' : z = w₀ - ε * v / c := sub_eq_zero.1 h
  apply slitPlane_ne_zero hz
  rw [hz']
  field_simp
  ring

/-- On an arc along which `c (γ t - w₀) / v + ε` stays in the slit plane, `log (c (z - w₀) / v + ε)`
is a primitive of `1 / (z - a)` for `a = w₀ - ε v / c`. -/
lemma pathIntegral_inv_sub_eq_log {u u' : ℝ} {w₀ v c : ℂ} {ε : ℝ} (hv : v ≠ 0) (hc : c ≠ 0)
    (hγ : IsC1On γ u u') (hslit : ∀ t ∈ uIcc u u', c * ((γ t - w₀) / v) + ε ∈ slitPlane) :
    pathIntegral (fun z => (z - (w₀ - ε * v / c))⁻¹) γ u u' =
      log (c * ((γ u' - w₀) / v) + ε) - log (c * ((γ u - w₀) / v) + ε) := by
  set U : Set ℂ := {z | c * ((z - w₀) / v) + ε ∈ slitPlane}
  refine pathIntegral_eq_sub (U := U) (F := fun z => log (c * ((z - w₀) / v) + ε)) hγ hslit
    (fun z hz => ?_) (fun z hz => ?_)
  · have h1 : HasDerivAt (fun z => c * ((z - w₀) / v) + ε) (c * (1 / v)) z :=
      ((((hasDerivAt_id z).sub_const w₀).div_const v).const_mul c).add_const _
    have h2 := h1.clog hz
    convert h2 using 1
    have hne := sub_ne_zero_of_mem_slitPlane hv hc hz
    rw [show c * ((z - w₀) / v) + ε = c / v * (z - (w₀ - ε * v / c)) by field_simp; ring]
    field_simp
  · exact ((continuous_id.sub continuous_const).continuousAt.inv₀
      (sub_ne_zero_of_mem_slitPlane hv hc hz)).continuousWithinAt

lemma log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) : log z - log (-z) = π * I := by
  apply Complex.ext <;>
    simp [log_re, log_im, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz]

lemma log_sub_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) : log z - log (-z) = -(π * I) := by
  apply Complex.ext <;>
    simp [log_re, log_im, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- **The jump.** Every piecewise smooth simple closed path has a point `a` off it with
`∮_γ dz / (z - a) ≠ 0`: at a regular point `w₀ = γ t₀`, the integrals at `w₀ + i ε γ'(t₀)` and
`w₀ - i ε γ'(t₀)` differ by nearly `2 π i` when `ε > 0` is small. -/
theorem exists_pathIntegral_inv_sub_ne_zero (hγ : IsPiecewiseSmooth γ 0 1) (hcl : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) :
    ∃ a ∉ pathImage γ, pathIntegral (fun z => (z - a)⁻¹) γ 0 1 ≠ 0 := by
  obtain ⟨-, S, hd, hdc, M, hM⟩ := id hγ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨t₀, ht₀, ht₀S, hv⟩ := exists_regular_point hγ hinj hd
  set v := deriv γ t₀ with hvdef
  set w₀ := γ t₀ with hw₀
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set U : Set ℝ := Ioo 0 1 \ ↑S
  have hU : IsOpen U := isOpen_Ioo.sdiff S.finite_toSet.isClosed
  have ht₀U : t₀ ∈ U := ⟨ht₀, ht₀S⟩
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.1 hU t₀ ht₀U
  obtain ⟨δ₂, hδ₂, hδ₂v⟩ := Metric.continuousAt_iff.1
    ((hdc t₀ ht₀U).continuousAt (hU.mem_nhds ht₀U)) ‖v‖ hvpos
  set δ := min δ₁ δ₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδlt : δ < min δ₁ δ₂ := half_lt_self (lt_min hδ₁ hδ₂)
  have hIU : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), t ∈ U ∧ ‖deriv γ t - v‖ < ‖v‖ := by
    intro t ht
    have hdist : dist t t₀ < min δ₁ δ₂ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    refine ⟨hδ₁U (lt_of_lt_of_le hdist (min_le_left _ _)), ?_⟩
    rw [← dist_eq_norm]
    exact hδ₂v (lt_of_lt_of_le hdist (min_le_right _ _))
  have hsub01 : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), t ∈ Ioo (0 : ℝ) 1 := fun t ht => (hIU t ht).1.1
  have h0δ : 0 < t₀ - δ := (hsub01 _ ⟨le_rfl, by linarith⟩).1
  have hδ1 : t₀ + δ < 1 := (hsub01 _ ⟨by linarith, le_rfl⟩).2
  -- the local arc is a graph over the tangent line
  set ψ : ℝ → ℝ := fun t => ((γ t - w₀) / v).re with hψ
  have hψd : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), HasDerivAt ψ ((deriv γ t / v).re) t := by
    intro t ht
    have h1 := ((hd t (hIU t ht).1.1 (hIU t ht).1.2).hasDerivAt.sub_const w₀).div_const v
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have hpos : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), 0 < (deriv γ t / v).re := by
    intro t ht
    have h1 : ‖deriv γ t / v - 1‖ < 1 := by
      rw [show deriv γ t / v - 1 = (deriv γ t - v) / v by field_simp, norm_div,
        div_lt_one hvpos]
      exact (hIU t ht).2
    have h2 := Complex.abs_re_le_norm (deriv γ t / v - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [neg_abs_le ((deriv γ t / v).re - 1)]
  have hmono : StrictMonoOn ψ (Icc (t₀ - δ) (t₀ + δ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hψd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_)
    rw [interior_Icc] at ht
    rw [(hψd t (Ioo_subset_Icc_self ht)).deriv]
    exact hpos t (Ioo_subset_Icc_self ht)
  have ht₀I : t₀ ∈ Icc (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hψ0 : ψ t₀ = 0 := by simp [hψ, hw₀]
  have hp : 0 < ψ (t₀ + δ) := hψ0 ▸ hmono ht₀I ⟨by linarith, le_rfl⟩ (by linarith)
  have hq : ψ (t₀ - δ) < 0 := hψ0 ▸ hmono ⟨le_rfl, by linarith⟩ ht₀I (by linarith)
  have hzero : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), ψ t = 0 → t = t₀ := fun t ht h =>
    hmono.injOn ht ht₀I (h.trans hψ0.symm)
  have hC1 : IsC1On γ (t₀ - δ) (t₀ + δ) := by
    rw [IsC1On, uIcc_of_le (by linarith)]
    exact ⟨fun t ht => hd t (hIU t ht).1.1 (hIU t ht).1.2,
      hdc.mono (fun t ht => (hIU t ht).1)⟩
  -- the two logarithms stay in the slit plane along the local arc
  have hslit : ∀ (c : ℂ), (c = I ∨ c = -I) → ∀ ε : ℝ, 0 < ε →
      ∀ t ∈ uIcc (t₀ - δ) (t₀ + δ), c * ((γ t - w₀) / v) + ε ∈ slitPlane := by
    intro c hc ε hε t ht
    rw [uIcc_of_le (by linarith)] at ht
    rw [mem_slitPlane_iff]
    by_cases h : ψ t = 0
    · left
      rw [hzero t ht h, show γ t₀ - w₀ = 0 from sub_eq_zero.2 hw₀.symm]
      simp [hε]
    · right
      rcases hc with rfl | rfl
      · simpa [hψ] using h
      · simpa [hψ] using h
  -- the local integrals, as a function of `ε`
  set p := (γ (t₀ + δ) - w₀) / v
  set q := (γ (t₀ - δ) - w₀) / v
  set L : ℝ → ℂ := fun ε => (log (I * p + ε) - log (I * q + ε)) -
    (log (-I * p + ε) - log (-I * q + ε)) with hL
  have hpre : p.re = ψ (t₀ + δ) := rfl
  have hqre : q.re = ψ (t₀ - δ) := rfl
  have hL0 : L 0 = 2 * π * I := by
    simp only [hL, Complex.ofReal_zero, add_zero]
    have e1 := log_sub_log_neg_of_im_pos (z := I * p) (by simpa [hpre] using hp)
    have e2 := log_sub_log_neg_of_im_neg (z := I * q) (by simpa [hqre] using hq)
    rw [neg_mul, neg_mul]
    linear_combination e1 - e2
  have hLc : ContinuousAt L 0 := by
    have hcont : ∀ z : ℂ, z ∈ slitPlane → ContinuousAt (fun ε : ℝ => log (z + ε)) 0 := by
      intro z hz
      refine ContinuousAt.clog (continuousAt_const.add Complex.continuous_ofReal.continuousAt) ?_
      simpa using hz
    have m1 : I * p ∈ slitPlane := by rw [mem_slitPlane_iff]; right; simpa [hpre] using hp.ne'
    have m2 : I * q ∈ slitPlane := by rw [mem_slitPlane_iff]; right; simpa [hqre] using hq.ne
    have m3 : -I * p ∈ slitPlane := by rw [mem_slitPlane_iff]; right; simpa [hpre] using hp.ne'
    have m4 : -I * q ∈ slitPlane := by rw [mem_slitPlane_iff]; right; simpa [hqre] using hq.ne
    exact ((hcont _ m1).sub (hcont _ m2)).sub ((hcont _ m3).sub (hcont _ m4))
  obtain ⟨ε₁, hε₁, hLε⟩ := Metric.continuousAt_iff.1 hLc (1 / 2) (by norm_num)
  -- the rest of the path stays away from `w₀`
  have hfar₁ : w₀ ∉ γ '' Icc 0 (t₀ - δ) := by
    rintro ⟨t, ht, he⟩
    have := hinj ⟨ht.1, by linarith [ht.2]⟩ ⟨ht₀.1.le, ht₀.2⟩ he
    linarith [ht.2]
  have hfar₂ : w₀ ∉ γ '' Icc (t₀ + δ) 1 := by
    rintro ⟨t, ht, he⟩
    rcases ht.2.lt_or_eq with h1 | h1
    · have := hinj ⟨by linarith [ht.1], h1⟩ ⟨ht₀.1.le, ht₀.2⟩ he
      linarith [ht.1]
    · rw [h1, ← hcl] at he
      have := hinj ⟨le_rfl, zero_lt_one⟩ ⟨ht₀.1.le, ht₀.2⟩ he
      linarith [ht₀.1]
  obtain ⟨d₁, hd₁, hfd₁⟩ := exists_pos_le_norm_sub
    (hγ.continuousOn.mono (Icc_subset_Icc le_rfl (by linarith))) hfar₁
  obtain ⟨d₂, hd₂, hfd₂⟩ := exists_pos_le_norm_sub
    (hγ.continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl)) hfar₂
  set d := min d₁ d₂
  have hd : 0 < d := lt_min hd₁ hd₂
  set A : ℝ := M * (2 * ‖v‖) / (d / 2) ^ 2
  have hA : 0 ≤ A := by positivity
  -- the choice of `ε`
  set ε : ℝ := min (ε₁ / 2) (min (d / (2 * ‖v‖)) (1 / (4 * (A + 1)))) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεε₁ : ε < ε₁ := (min_le_left _ _).trans_lt (half_lt_self hε₁)
  have hεd : ε * ‖v‖ ≤ d / 2 := by
    have : ε ≤ d / (2 * ‖v‖) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hεA : ε * (A + 1) ≤ 1 / 4 := by
    have : ε ≤ 1 / (4 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- the two points
  set a : ℂ := w₀ - ε * v / I
  set b : ℂ := w₀ - ε * v / (-I)
  have hna : ‖a - w₀‖ = ε * ‖v‖ := by
    simp [a, abs_of_pos hε]
  have hnb : ‖b - w₀‖ = ε * ‖v‖ := by
    simp [b, abs_of_pos hε]
  have hab : ‖a - b‖ = 2 * ε * ‖v‖ := by
    have : a - b = -(2 * ε * v / I) := by simp only [a, b, div_neg]; ring
    rw [this, norm_neg, norm_div, Complex.norm_I, div_one, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, Complex.norm_ofNat]
  -- distances on the rest of the path
  have hrest : ∀ x : ℂ, ‖x - w₀‖ = ε * ‖v‖ → ∀ t ∈ Icc (0 : ℝ) (t₀ - δ) ∪ Icc (t₀ + δ) 1,
      d / 2 ≤ ‖γ t - x‖ := by
    intro x hx t ht
    have hdt : d ≤ ‖γ t - w₀‖ := by
      rcases ht with ht | ht
      · exact (min_le_left _ _).trans (hfd₁ t ht)
      · exact (min_le_right _ _).trans (hfd₂ t ht)
    have := norm_sub_le_norm_sub_add_norm_sub (γ t) x w₀
    linarith
  -- points off the path
  have hoff : ∀ c : ℂ, (c = I ∨ c = -I) → ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀ - ε * v / c := by
    intro c hc t ht he
    have hc0 : c ≠ 0 := by rcases hc with rfl | rfl <;> simp
    by_cases hloc : t ∈ Icc (t₀ - δ) (t₀ + δ)
    · have := hslit c hc ε hε t (by rw [uIcc_of_le (by linarith)]; exact hloc)
      exact sub_ne_zero_of_mem_slitPlane hv hc0 this (sub_eq_zero.2 he)
    · have ht' : t ∈ Icc (0 : ℝ) (t₀ - δ) ∪ Icc (t₀ + δ) 1 := by
        simp only [mem_Icc, not_and_or, not_le] at hloc
        rcases hloc with h | h
        · exact Or.inl ⟨ht.1, h.le⟩
        · exact Or.inr ⟨h.le, ht.2⟩
      have hx : ‖(w₀ - ε * v / c) - w₀‖ = ε * ‖v‖ := by
        rcases hc with rfl | rfl
        · exact hna
        · exact hnb
      have := hrest _ hx t ht'
      rw [he, sub_self, norm_zero] at this
      linarith
  have hoffa : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ a := hoff I (Or.inl rfl)
  have hoffb : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ b := hoff (-I) (Or.inr rfl)
  -- splitting the integrals into three pieces
  have hsplit : ∀ x : ℂ, (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ x) →
      pathIntegral (fun z => (z - x)⁻¹) γ 0 1 =
        pathIntegral (fun z => (z - x)⁻¹) γ 0 (t₀ - δ) +
        pathIntegral (fun z => (z - x)⁻¹) γ (t₀ - δ) (t₀ + δ) +
        pathIntegral (fun z => (z - x)⁻¹) γ (t₀ + δ) 1 := by
    intro x hx
    rw [← pathIntegral_inv_sub_add_adjacent hγ h0δ.le (by linarith) hx,
      ← pathIntegral_inv_sub_add_adjacent (hγ.mono h0δ.le le_rfl) (by linarith) hδ1.le
        (fun t ht => hx t ⟨h0δ.le.trans ht.1, ht.2⟩)]
    ring
  have hloca : pathIntegral (fun z => (z - a)⁻¹) γ (t₀ - δ) (t₀ + δ) =
      log (I * p + ε) - log (I * q + ε) :=
    pathIntegral_inv_sub_eq_log hv I_ne_zero hC1 (hslit I (Or.inl rfl) ε hε)
  have hlocb : pathIntegral (fun z => (z - b)⁻¹) γ (t₀ - δ) (t₀ + δ) =
      log (-I * p + ε) - log (-I * q + ε) :=
    pathIntegral_inv_sub_eq_log hv (neg_ne_zero.2 I_ne_zero) hC1 (hslit (-I) (Or.inr rfl) ε hε)
  -- the estimates on the rest
  have hR₁ := norm_pathIntegral_inv_sub_sub_le (hγ.mono le_rfl (by linarith)) h0δ.le
    (fun t ht => hM t ⟨ht.1, by linarith [ht.2]⟩) (by positivity : 0 < d / 2)
    (fun t ht => hrest a hna t (Or.inl ht)) (fun t ht => hrest b hnb t (Or.inl ht))
  have hR₂ := norm_pathIntegral_inv_sub_sub_le (hγ.mono (by linarith) le_rfl) hδ1.le
    (fun t ht => hM t ⟨by linarith [ht.1], ht.2⟩) (by positivity : 0 < d / 2)
    (fun t ht => hrest a hna t (Or.inr ht)) (fun t ht => hrest b hnb t (Or.inr ht))
  rw [hab] at hR₁ hR₂
  have hX : M * (2 * ε * ‖v‖) / (d / 2) ^ 2 = ε * A := by simp only [A]; ring
  rw [hX] at hR₁ hR₂
  have hsum : ε * A * (t₀ - δ - 0) + ε * A * (1 - (t₀ + δ)) < 1 / 2 := by
    have h0 : 0 ≤ ε * A := by positivity
    have h1 : ε * A * (t₀ - δ - 0) + ε * A * (1 - (t₀ + δ)) ≤ ε * A := by nlinarith
    have h2 : ε * A ≤ 1 / 4 := by nlinarith
    linarith
  -- conclusion
  have hdiff : ‖(pathIntegral (fun z => (z - a)⁻¹) γ 0 1 -
      pathIntegral (fun z => (z - b)⁻¹) γ 0 1) - 2 * π * I‖ < 1 := by
    rw [hsplit a hoffa, hsplit b hoffb, hloca, hlocb, ← hL0]
    have hLe : ‖L ε - L 0‖ < 1 / 2 := by
      rw [← dist_eq_norm]
      exact hLε (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεε₁)
    have heq : pathIntegral (fun z => (z - a)⁻¹) γ 0 (t₀ - δ) +
        (log (I * p + ↑ε) - log (I * q + ↑ε)) + pathIntegral (fun z => (z - a)⁻¹) γ (t₀ + δ) 1 -
        (pathIntegral (fun z => (z - b)⁻¹) γ 0 (t₀ - δ) +
          (log (-I * p + ↑ε) - log (-I * q + ↑ε)) +
          pathIntegral (fun z => (z - b)⁻¹) γ (t₀ + δ) 1) - L 0 =
        (pathIntegral (fun z => (z - a)⁻¹) γ 0 (t₀ - δ) -
          pathIntegral (fun z => (z - b)⁻¹) γ 0 (t₀ - δ)) +
        (pathIntegral (fun z => (z - a)⁻¹) γ (t₀ + δ) 1 -
          pathIntegral (fun z => (z - b)⁻¹) γ (t₀ + δ) 1) + (L ε - L 0) := by
      simp only [hL]; ring
    rw [heq]
    calc _ ≤ ‖pathIntegral (fun z => (z - a)⁻¹) γ 0 (t₀ - δ) -
          pathIntegral (fun z => (z - b)⁻¹) γ 0 (t₀ - δ)‖ +
        ‖pathIntegral (fun z => (z - a)⁻¹) γ (t₀ + δ) 1 -
          pathIntegral (fun z => (z - b)⁻¹) γ (t₀ + δ) 1‖ + ‖L ε - L 0‖ :=
          norm_add₃_le
      _ < 1 / 2 + 1 / 2 := by linarith
      _ = 1 := by norm_num
  have h2π : (1 : ℝ) < ‖(2 * π * I : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    nlinarith [Real.two_le_pi]
  have hne : pathIntegral (fun z => (z - a)⁻¹) γ 0 1 -
      pathIntegral (fun z => (z - b)⁻¹) γ 0 1 ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at hdiff
    linarith
  by_cases ha0 : pathIntegral (fun z => (z - a)⁻¹) γ 0 1 = 0
  · refine ⟨b, fun ⟨t, ht, he⟩ => hoffb t ht he, fun hb0 => hne (by rw [ha0, hb0, sub_zero])⟩
  · exact ⟨a, fun ⟨t, ht, he⟩ => hoffa t ht he, ha0⟩

/-! ### The separation half of the Jordan curve theorem -/

/-- **Jordan curve theorem, separation half** (Beck, Section 4.4, assumed in the book; CX-161): every
piecewise smooth simple closed path has a nonempty inside, i.e. a point off the path whose component
in the complement of the path is bounded. This is the field `inside_nonempty` of Definition 4.4.4 for
every such path. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem insideOf_nonempty (hγ : IsPiecewiseSmooth γ 0 1) (hcl : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) : (insideOf γ).Nonempty := by
  obtain ⟨a, ha, hW⟩ := exists_pathIntegral_inv_sub_ne_zero hγ hcl hinj
  exact ⟨a, mem_insideOf_of_pathIntegral_inv_sub_ne_zero hγ hcl ha hW⟩

/-- **Jordan curve theorem, separation half** (Beck, Section 4.4; CX-161): the complement of a
piecewise smooth simple closed path is not connected. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem not_isConnected_compl_pathImage (hγ : IsPiecewiseSmooth γ 0 1) (hcl : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) : ¬ IsConnected (pathImage γ)ᶜ := by
  intro hconn
  obtain ⟨a, ha, hW⟩ := exists_pathIntegral_inv_sub_ne_zero hγ hcl hinj
  obtain ⟨R, hR⟩ := exists_pathIntegral_inv_sub_eq_zero_far hγ hcl
  set z : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have hz : R < ‖z‖ := by
    simp only [z, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have := pathIntegral_inv_sub_eq_of_isPreconnected hγ hcl hconn.isPreconnected subset_rfl
    ha (hR z hz).1
  rw [(hR z hz).2] at this
  exact hW this

/-- Beck Definition 4.4.4 (CX-071): for a piecewise smooth simple closed path, only the annulus field
of `IsPositivelyOrientedSimpleClosed` remains to be checked; the inside is never empty. -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem IsPositivelyOrientedSimpleClosed.of_annulus (hγ : IsPiecewiseSmooth γ 0 1)
    (hcl : γ 0 = γ 1) (hinj : InjOn γ (Ico 0 1))
    (hann : ∀ (w : ℂ) (R : ℝ), 0 < R → Metric.closedBall w R ⊆ insideOf γ →
      IsGHomotopic ((insideOf γ ∪ pathImage γ) \ Metric.ball w R) γ (circlePath w R)) :
    IsPositivelyOrientedSimpleClosed γ :=
  ⟨hγ, hcl, hinj, insideOf_nonempty hγ hcl hinj, hann⟩

end UndergradKB.ComplexAnalysis
