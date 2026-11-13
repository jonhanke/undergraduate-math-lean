import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import UndergradKB.ComplexAnalysis.Rectangle
import UndergradKB.ComplexAnalysis.ResidueGeneral
import UndergradKB.ComplexAnalysis.CotBound
import UndergradKB.ComplexAnalysis.CotTaylor
import UndergradKB.ComplexAnalysis.Series

/-!
# Sums of reciprocal powers from the residue theorem (Beck et al., Section 10.1)

We integrate `π cot(πz)/z^p` and `π/(z^p sin(πz))` over the rectangles `γ_N` with corners
`±(N + 1/2) ± iN`. The residue theorem turns the integral into `2πi` times the sum of the residues
at the integers in the rectangle; on the rectangle the functions are bounded by `3π/N^p`, so for
`p ≥ 2` the integral tends to `0`. Reading off the residue at the origin (from `CotTaylor.lean`)
gives the values of `∑ 1/k²`, `∑ (-1)^k/k²`, `∑ 1/k⁴` and `∑ (-1)^k/k⁴`, and hence `ζ(2)` and
`ζ(4)`. None of Mathlib's evaluations of these sums is used.
-/

open Complex Metric Set Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### The rectangles and the pole set -/

/-- Beck's rectangle γ_N. -/
noncomputable def gammaN (N : ℕ) : ℝ → ℂ := rectPath (-(N + 1 / 2)) (N + 1 / 2) (-N) N

lemma gammaN_lt {N : ℕ} (hN : 1 ≤ N) :
    (-((N : ℝ) + 1 / 2) < (N : ℝ) + 1 / 2) ∧ (-(N : ℝ) < N) := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor <;> linarith

theorem isPositivelyOrientedSimpleClosed_gammaN {N : ℕ} (hN : 1 ≤ N) :
    IsPositivelyOrientedSimpleClosed (gammaN N) :=
  isPositivelyOrientedSimpleClosed_rectPath (gammaN_lt hN).1 (gammaN_lt hN).2

/-- A slightly larger open square, on which the integrands are holomorphic off the poles. -/
abbrev bigRect (N : ℕ) : Set ℂ :=
  openRect (-((N : ℝ) + 1)) ((N : ℝ) + 1) (-((N : ℝ) + 1)) ((N : ℝ) + 1)

lemma isOpen_bigRect (N : ℕ) : IsOpen (bigRect N) := isOpen_Ioo.reProdIm isOpen_Ioo

open Classical in
/-- The integers `-N, …, N` as a finset of complex numbers. -/
noncomputable def polesN (N : ℕ) : Finset ℂ :=
  {0} ∪ (Finset.range N).image (fun n : ℕ => (n : ℂ) + 1) ∪
    (Finset.range N).image (fun n : ℕ => -((n : ℂ) + 1))

lemma zero_mem_polesN (N : ℕ) : (0 : ℂ) ∈ polesN N := by
  simp [polesN]

lemma intCast_mem_polesN {N : ℕ} {k : ℤ} (h1 : -(N : ℤ) ≤ k) (h2 : k ≤ N) :
    (k : ℂ) ∈ polesN N := by
  simp only [polesN, Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_range]
  rcases lt_trichotomy k 0 with h | h | h
  · right
    obtain ⟨n, hn, hk⟩ : ∃ n : ℕ, n < N ∧ k = -((n : ℤ) + 1) :=
      ⟨(-k - 1).toNat, by omega, by omega⟩
    exact ⟨n, hn, by rw [hk]; push_cast; ring⟩
  · left; left; rw [h]; simp
  · left; right
    obtain ⟨n, hn, hk⟩ : ∃ n : ℕ, n < N ∧ k = (n : ℤ) + 1 :=
      ⟨(k - 1).toNat, by omega, by omega⟩
    exact ⟨n, hn, by rw [hk]; push_cast; ring⟩

lemma polesN_mem_openRect {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : s ∈ polesN N) :
    s ∈ openRect (-((N : ℝ) + 1 / 2)) ((N : ℝ) + 1 / 2) (-(N : ℝ)) N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [polesN, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_range] at hs
  simp only [mem_reProdIm, mem_Ioo]
  rcases hs with (rfl | ⟨n, hn, rfl⟩) | ⟨n, hn, rfl⟩
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
  · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith

lemma gammaN_mem {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    gammaN N t ∈ bigRect N \ polesN N := by
  unfold gammaN
  obtain ⟨h1, h2⟩ := rectPath_mem_boundary (gammaN_lt hN).1 (gammaN_lt hN).2 ht
  refine ⟨?_, fun hs => h2 (polesN_mem_openRect hN hs)⟩
  simp only [mem_reProdIm, mem_Icc, mem_Ioo] at h1 ⊢
  obtain ⟨⟨a, b⟩, c, d⟩ := h1
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma inside_gammaN_subset {N : ℕ} (hN : 1 ≤ N) : insideOf (gammaN N) ⊆ bigRect N := by
  unfold gammaN
  rw [insideOf_rectPath (gammaN_lt hN).1 (gammaN_lt hN).2]
  intro z hz
  simp only [mem_reProdIm, mem_Ioo] at hz ⊢
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨⟨a, b⟩, c, d⟩ := hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### The residue theorem on γ_N -/

open Classical in
/-- The residue theorem on `γ_N`, summed over the integer poles `-N, …, N`. -/
lemma pathIntegral_gammaN_eq {f : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hf : DifferentiableOn ℂ f (bigRect N \ polesN N)) :
    pathIntegral f (gammaN N) 0 1 = 2 * π * I * (residue f 0 +
      (∑ n ∈ Finset.range N, residue f ((n : ℂ) + 1) +
        ∑ n ∈ Finset.range N, residue f (-((n : ℂ) + 1)))) := by
  have hγ := isPositivelyOrientedSimpleClosed_gammaN hN
  have himg : ∀ t ∈ Icc (0 : ℝ) 1, gammaN N t ∈ bigRect N := fun t ht => (gammaN_mem hN ht).1
  obtain ⟨c, hc⟩ := (hγ.contractible_iff_inside_subset (isOpen_bigRect N) himg).2
    (inside_gammaN_subset hN)
  have hin : ∀ s ∈ polesN N, s ∈ insideOf (gammaN N) := by
    intro s hs
    unfold gammaN
    rw [insideOf_rectPath (gammaN_lt hN).1 (gammaN_lt hN).2]
    exact polesN_mem_openRect hN hs
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, gammaN N t ∉ polesN N := fun t ht => (gammaN_mem hN ht).2
  rw [residue_theorem (isOpen_bigRect N) hf hγ hpath hc,
    Finset.filter_true_of_mem hin]
  have hd1 : Disjoint ({0} : Finset ℂ) ((Finset.range N).image (fun n : ℕ => (n : ℂ) + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_singleton] at ha
    simp only [Finset.mem_image, Finset.mem_range] at hb
    obtain ⟨n, _, rfl⟩ := hb
    exact Nat.cast_add_one_ne_zero n ha
  have hd2 : Disjoint ({0} ∪ (Finset.range N).image (fun n : ℕ => (n : ℂ) + 1))
      ((Finset.range N).image (fun n : ℕ => -((n : ℂ) + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image, Finset.mem_range] at hb
    obtain ⟨m, _, rfl⟩ := hb
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_range] at ha
    rcases ha with ha | ⟨n, _, hn⟩
    · have := congrArg Complex.re ha
      simp at this
      linarith
    · have := congrArg Complex.re hn
      have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp at this
      linarith
  rw [polesN, Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton,
    Finset.sum_image (fun x _ y _ h => by simpa using h),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  ring

/-! ### Holomorphy off the poles -/

lemma ne_zero_of_mem_bigRect_sdiff {N : ℕ} {z : ℂ} (hz : z ∈ bigRect N \ polesN N) : z ≠ 0 :=
  fun h => hz.2 (h ▸ zero_mem_polesN N)

lemma sin_ne_zero_of_mem_bigRect_sdiff {N : ℕ} {z : ℂ} (hz : z ∈ bigRect N \ polesN N) :
    Complex.sin (π * z) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hzk : z = (k : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hk]; ring
  obtain ⟨hz1, hz2⟩ := hz
  have hre : z.re = (k : ℝ) := by rw [hzk]; simp
  simp only [mem_reProdIm, mem_Ioo] at hz1
  have h1 : -(N : ℝ) - 1 < k := by rw [← hre]; linarith [hz1.1.1]
  have h2 : (k : ℝ) < N + 1 := by rw [← hre]; exact hz1.1.2
  have h1' : -(N : ℤ) - 1 < k := by exact_mod_cast h1
  have h2' : k < (N : ℤ) + 1 := by exact_mod_cast h2
  exact hz2 (hzk ▸ intCast_mem_polesN (by omega) (by omega))

lemma differentiableOn_cot_div (N p : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) (bigRect N \ polesN N) := by
  intro z hz
  have hs := sin_ne_zero_of_mem_bigRect_sdiff hz
  have h0 := ne_zero_of_mem_bigRect_sdiff hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hp0 : z ^ p ≠ 0 := pow_ne_zero p h0
  simp only [Complex.cot_eq_cos_div_sin]
  fun_prop (disch := assumption)

lemma differentiableOn_sin_div (N p : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) (bigRect N \ polesN N) := by
  intro z hz
  have hs := sin_ne_zero_of_mem_bigRect_sdiff hz
  have h0 := ne_zero_of_mem_bigRect_sdiff hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hd : DifferentiableAt ℂ (fun z : ℂ => z ^ p * Complex.sin (π * z)) z := by fun_prop
  exact (differentiableAt_const (π : ℂ)).div hd (mul_ne_zero (pow_ne_zero p h0) hs)

/-! ### The residue theorem for the two integrands -/

/-- The residue theorem on `γ_N` for `π cot(πz)/z^p`, `p` even. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem pathIntegral_gammaN_cot {N p : ℕ} (hN : 1 ≤ N) (hp : Even p) :
    pathIntegral (fun z => π * Complex.cot (π * z) / z ^ p) (gammaN N) 0 1 =
      2 * π * I * (residue (fun z => π * Complex.cot (π * z) / z ^ p) 0 +
        2 * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ p) := by
  rw [pathIntegral_gammaN_eq hN (differentiableOn_cot_div N p)]
  have hpos : ∀ n : ℕ, residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) ((n : ℂ) + 1) =
      1 / ((n : ℂ) + 1) ^ p := by
    intro n
    have := residue_pi_cot_div_pow (p := p) (k := ((n + 1 : ℕ) : ℤ)) (by omega)
    push_cast at this
    exact this
  have hneg : ∀ n : ℕ, residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ p)
      (-((n : ℂ) + 1)) = 1 / ((n : ℂ) + 1) ^ p := by
    intro n
    have := residue_pi_cot_div_pow (p := p) (k := -((n + 1 : ℕ) : ℤ)) (by omega)
    push_cast at this
    rw [this, hp.neg_pow]
  simp only [hpos, hneg]
  ring

/-- The residue theorem on `γ_N` for `π/(z^p sin(πz))`, `p` even. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem pathIntegral_gammaN_sin {N p : ℕ} (hN : 1 ≤ N) (hp : Even p) :
    pathIntegral (fun z => π / (z ^ p * Complex.sin (π * z))) (gammaN N) 0 1 =
      2 * π * I * (residue (fun z => π / (z ^ p * Complex.sin (π * z))) 0 +
        2 * ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / ((n : ℂ) + 1) ^ p) := by
  rw [pathIntegral_gammaN_eq hN (differentiableOn_sin_div N p)]
  have hpos : ∀ n : ℕ, residue (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) ((n : ℂ) + 1) =
      (-1) ^ (n + 1) / ((n : ℂ) + 1) ^ p := by
    intro n
    have := residue_pi_div_pow_mul_sin (p := p) (k := ((n + 1 : ℕ) : ℤ)) (by omega)
    rw [zpow_natCast] at this
    push_cast at this
    exact this
  have hneg : ∀ n : ℕ, residue (fun z : ℂ => π / (z ^ p * Complex.sin (π * z)))
      (-((n : ℂ) + 1)) = (-1) ^ (n + 1) / ((n : ℂ) + 1) ^ p := by
    intro n
    have := residue_pi_div_pow_mul_sin (p := p) (k := -((n + 1 : ℕ) : ℤ)) (by omega)
    rw [zpow_neg, zpow_natCast] at this
    push_cast at this
    rw [this, hp.neg_pow, ← inv_pow, inv_neg, inv_one]
  simp only [hpos, hneg]
  ring

/-! ### The bound on γ_N -/

lemma gammaN_re_or_im {N : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(gammaN N t).re| = N + 1 / 2 ∨ |(gammaN N t).im| = N := by
  unfold gammaN
  rcases rectPath_cases (x₀ := -((N : ℝ) + 1 / 2)) (x₁ := (N : ℝ) + 1 / 2) (y₀ := -(N : ℝ))
    (y₁ := (N : ℝ)) ht with ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [e]
  · left
    exact abs_of_nonneg (by positivity)
  · right
    exact abs_of_nonneg (Nat.cast_nonneg N)
  · left
    show |-((N : ℝ) + 1 / 2)| = _
    rw [abs_neg]
    exact abs_of_nonneg (by positivity)
  · right
    show |-(N : ℝ)| = _
    rw [abs_neg]
    exact abs_of_nonneg (Nat.cast_nonneg N)

lemma norm_ge_of_re_or_im {N : ℕ} {z : ℂ} (h : |z.re| = N + 1 / 2 ∨ |z.im| = N) :
    (N : ℝ) ≤ ‖z‖ := by
  rcases h with h | h
  · have := Complex.abs_re_le_norm z; linarith
  · have := Complex.abs_im_le_norm z; linarith

lemma norm_pathIntegral_gammaN_le {f : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hf : DifferentiableOn ℂ f (bigRect N \ polesN N)) {M : ℝ}
    (hM : ∀ z : ℂ, (|z.re| = N + 1 / 2 ∨ |z.im| = N) → ‖f z‖ ≤ M) :
    ‖pathIntegral f (gammaN N) 0 1‖ ≤ M * (8 * N + 2) := by
  have hcont : ContinuousOn f
      (pathImage (rectPath (-((N : ℝ) + 1 / 2)) ((N : ℝ) + 1 / 2) (-(N : ℝ)) N)) :=
    hf.continuousOn.mono (by rintro _ ⟨t, ht, rfl⟩; exact gammaN_mem hN ht)
  have h := norm_pathIntegral_rectPath_le (f := f) (M := M) (gammaN_lt hN).1.le
    (gammaN_lt hN).2.le hcont (by
      rintro _ ⟨t, ht, rfl⟩
      exact hM _ (gammaN_re_or_im ht))
  unfold gammaN
  refine h.trans (le_of_eq ?_)
  ring

lemma norm_cot_term_le {N p : ℕ} (hN : 1 ≤ N) {z : ℂ} (h : |z.re| = N + 1 / 2 ∨ |z.im| = N) :
    ‖π * Complex.cot (π * z) / z ^ p‖ ≤ 3 * π / (N : ℝ) ^ p := by
  have hc : ‖Complex.cot (π * z)‖ ≤ 2 := by
    rcases h with h | h
    · exact (norm_cot_pi_mul_lt_two_of_re h).le
    · exact (norm_cot_pi_mul_lt_two_of_im hN h).le
  have hz := norm_ge_of_re_or_im h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  refine div_le_div₀ (by positivity) ?_ (by positivity) (pow_le_pow_left₀ hN0.le hz p)
  nlinarith [Real.pi_pos]

lemma norm_sin_term_le {N p : ℕ} (hN : 1 ≤ N) {z : ℂ} (h : |z.re| = N + 1 / 2 ∨ |z.im| = N) :
    ‖π / (z ^ p * Complex.sin (π * z))‖ ≤ 3 * π / (N : ℝ) ^ p := by
  have hc : ‖(Complex.sin (π * z))⁻¹‖ ≤ 3 := by
    rcases h with h | h
    · exact (norm_inv_sin_pi_mul_lt_three_of_re h).le
    · exact (norm_inv_sin_pi_mul_lt_three_of_im hN h).le
  have hz := norm_ge_of_re_or_im h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (π : ℂ) / (z ^ p * Complex.sin (π * z)) = π * (Complex.sin (π * z))⁻¹ / z ^ p := by
    ring
  rw [e, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  refine div_le_div₀ (by positivity) ?_ (by positivity) (pow_le_pow_left₀ hN0.le hz p)
  nlinarith [Real.pi_pos]

lemma bound_arith {N p : ℕ} (hN : 1 ≤ N) (hp : 2 ≤ p) :
    3 * π / (N : ℝ) ^ p * (8 * N + 2) ≤ 30 * π / N := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ p := pow_le_pow_right₀ hN0 hp
  have hpi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 3 * π * (8 * N + 2) * N ≤ 3 * π * (10 * N) * N := by gcongr; linarith
    _ = 30 * π * (N : ℝ) ^ 2 := by ring
    _ ≤ 30 * π * (N : ℝ) ^ p := by gcongr

/-- The integral of `π cot(πz)/z^p` over `γ_N` tends to `0` for `p ≥ 2`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem tendsto_pathIntegral_gammaN_cot {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun N : ℕ => pathIntegral (fun z => π * Complex.cot (π * z) / z ^ p) (gammaN N) 0 1)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ => 30 * π / N) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (norm_pathIntegral_gammaN_le hN (differentiableOn_cot_div N p)
    (fun z hz => norm_cot_term_le hN hz)).trans (bound_arith hN hp)

/-- The integral of `π/(z^p sin(πz))` over `γ_N` tends to `0` for `p ≥ 2`. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem tendsto_pathIntegral_gammaN_sin {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun N : ℕ => pathIntegral (fun z => π / (z ^ p * Complex.sin (π * z))) (gammaN N) 0 1)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ => 30 * π / N) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (norm_pathIntegral_gammaN_le hN (differentiableOn_sin_div N p)
    (fun z hz => norm_sin_term_le hN hz)).trans (bound_arith hN hp)

/-! ### From residues to sums -/

/-- If `I_N = 2πi (R + 2 S_N)` tends to `0` with `R = -2c` real, then `S_N → c`. -/
lemma tendsto_partial_sums {a : ℕ → ℝ} {I' : ℕ → ℂ} {c : ℝ} (hI : Tendsto I' atTop (𝓝 0))
    (hform : ∀ N : ℕ, 1 ≤ N →
      I' N = 2 * π * I * (((-2 * c : ℝ) : ℂ) + 2 * ((∑ n ∈ Finset.range N, a n : ℝ) : ℂ))) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n) atTop (𝓝 c) := by
  have h1 : Tendsto (fun N => (2 * π * I : ℂ)⁻¹ * I' N) atTop (𝓝 ((2 * π * I : ℂ)⁻¹ * 0)) :=
    hI.const_mul _
  have h2 : Tendsto (fun N : ℕ => (((-2 * c : ℝ) : ℂ) + 2 * ((∑ n ∈ Finset.range N, a n : ℝ) : ℂ)))
      atTop (𝓝 0) := by
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hform N hN, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have h3 : Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N, a n : ℝ) : ℂ)) atTop (𝓝 (c : ℂ)) := by
    have h4 := ((h2.sub_const ((-2 * c : ℝ) : ℂ)).div_const 2)
    have e : (0 - ((-2 * c : ℝ) : ℂ)) / 2 = (c : ℂ) := by push_cast; ring
    rw [e] at h4
    refine h4.congr (fun N => ?_)
    ring
  have h5 := (Complex.continuous_re.tendsto _).comp h3
  simpa only [Function.comp_def, Complex.ofReal_re] using h5

lemma tendsto_cot_sums {p : ℕ} (hp : 2 ≤ p) (hpe : Even p) {c : ℝ}
    (hc : residue (fun z : ℂ => π * Complex.cot (π * z) / z ^ p) 0 = ((-2 * c : ℝ) : ℂ)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ p) atTop (𝓝 c) := by
  refine tendsto_partial_sums (tendsto_pathIntegral_gammaN_cot hp) (fun N hN => ?_)
  rw [pathIntegral_gammaN_cot hN hpe, hc]
  push_cast
  rfl

lemma tendsto_sin_sums {p : ℕ} (hp : 2 ≤ p) (hpe : Even p) {c : ℝ}
    (hc : residue (fun z : ℂ => π / (z ^ p * Complex.sin (π * z))) 0 = ((-2 * c : ℝ) : ℂ)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1) ^ (n + 1) / ((n : ℝ) + 1) ^ p)
      atTop (𝓝 c) := by
  refine tendsto_partial_sums (tendsto_pathIntegral_gammaN_sin hp) (fun N hN => ?_)
  rw [pathIntegral_gammaN_sin hN hpe, hc]
  push_cast
  rfl

lemma hasSum_of_tendsto_shift {g : ℕ → ℝ} (hg : g 0 = 0) (hs : Summable g) {c : ℝ}
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g (n + 1)) atTop (𝓝 c)) : HasSum g c := by
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n) atTop (𝓝 c) := by
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    simpa [Finset.sum_range_succ', hg] using h
  have := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat h2
  rw [← this]
  exact hs.hasSum

lemma summable_alt_pow {p : ℕ} (hp : 2 ≤ p) : Summable (fun k : ℕ => (-1) ^ k / (k : ℝ) ^ p) := by
  refine Summable.of_norm_bounded ((Real.summable_one_div_nat_pow (p := p)).2 (by omega)) (fun k => ?_)
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs, abs_pow,
    Nat.abs_cast]

/-- `∑_{k ≥ 1} 1/k² = π²/6`, from the residue theorem. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem hasSum_inv_sq_via_residues : HasSum (fun k : ℕ => 1 / (k : ℝ) ^ 2) (π ^ 2 / 6) := by
  refine hasSum_of_tendsto_shift (by simp) (Real.summable_one_div_nat_pow.2 (by norm_num)) ?_
  have := tendsto_cot_sums (p := 2) le_rfl (by decide) (c := π ^ 2 / 6) (by
    rw [residue_pi_cot_div_sq_zero]; push_cast; ring)
  simpa using this

/-- `∑_{k ≥ 1} (-1)^k/k² = -π²/12`, from the residue theorem. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem hasSum_neg_one_pow_div_sq_via_residues :
    HasSum (fun k : ℕ => (-1) ^ k / (k : ℝ) ^ 2) (-(π ^ 2 / 12)) := by
  refine hasSum_of_tendsto_shift (by simp) (summable_alt_pow le_rfl) ?_
  have := tendsto_sin_sums (p := 2) le_rfl (by decide) (c := -(π ^ 2 / 12)) (by
    rw [residue_pi_div_sq_mul_sin_zero]; push_cast; ring)
  simpa using this

/-- `∑_{k ≥ 1} 1/k⁴ = π⁴/90`, from the residue theorem. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem hasSum_inv_pow_four_via_residues : HasSum (fun k : ℕ => 1 / (k : ℝ) ^ 4) (π ^ 4 / 90) := by
  refine hasSum_of_tendsto_shift (by simp) (Real.summable_one_div_nat_pow.2 (by norm_num)) ?_
  have := tendsto_cot_sums (p := 4) (by norm_num) (by decide) (c := π ^ 4 / 90) (by
    rw [residue_pi_cot_div_pow_four_zero]; push_cast; ring)
  simpa using this

/-- `∑_{k ≥ 1} (-1)^k/k⁴ = -7π⁴/720`, from the residue theorem. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem hasSum_neg_one_pow_div_pow_four_via_residues :
    HasSum (fun k : ℕ => (-1) ^ k / (k : ℝ) ^ 4) (-(7 * π ^ 4 / 720)) := by
  refine hasSum_of_tendsto_shift (by simp) (summable_alt_pow (by norm_num)) ?_
  have := tendsto_sin_sums (p := 4) (by norm_num) (by decide) (c := -(7 * π ^ 4 / 720)) (by
    rw [residue_pi_div_pow_four_mul_sin_zero]; push_cast; ring)
  simpa using this

/-- `ζ(2) = π²/6`, via the residue computation. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem riemannZeta_two_via_residues : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  have h := Complex.hasSum_ofReal.mpr hasSum_inv_sq_via_residues
  have h2 : riemannZeta ((2 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (2 : ℕ) :=
    zeta_nat_eq_tsum_of_gt_one (by norm_num)
  have h3 := h.tsum_eq
  push_cast at h2 h3
  rw [h2]
  exact h3

/-- `ζ(4) = π⁴/90`, via the residue computation. -/
@[kb "beck2025" "Section 10.1, p. 163"]
theorem riemannZeta_four_via_residues : riemannZeta 4 = (π : ℂ) ^ 4 / 90 := by
  have h := Complex.hasSum_ofReal.mpr hasSum_inv_pow_four_via_residues
  have h2 : riemannZeta ((4 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (4 : ℕ) :=
    zeta_nat_eq_tsum_of_gt_one (by norm_num)
  have h3 := h.tsum_eq
  push_cast at h2 h3
  rw [h2]
  exact h3

end UndergradKB.ComplexAnalysis
