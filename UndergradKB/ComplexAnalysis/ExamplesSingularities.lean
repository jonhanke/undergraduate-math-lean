import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import UndergradKB.ComplexAnalysis.Singularities
import UndergradKB.ComplexAnalysis.Residue
import UndergradKB.ComplexAnalysis.ArgumentPrinciple
import UndergradKB.ComplexAnalysis.CotTaylor
import UndergradKB.Common.Attr

/-! # Worked examples on singularities, residues and Rouche's theorem (Beck et al., Ch. 9)

Examples 9.1.2 to 9.1.5, 9.1.11, 9.2.5, 9.2.6, 9.2.8 and 9.3.4, stated in the book's terms and
proved from the definitions of `Singularities.lean`, the residue calculus of `Residue.lean` and
`rouche_circle`. -/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### Poles from a nonvanishing numerator -/

/-- If `f z = g z / z ^ (n+1)` off the origin with `g` continuous and nonzero at `0`, then `f` has
a pole at `0`. -/
lemma hasPole_of_div_pow {f g : ℂ → ℂ} (hg : ContinuousAt g 0) (hg0 : g 0 ≠ 0) (n : ℕ)
    (hf : ∀ z, z ≠ 0 → f z = g z / z ^ (n + 1)) : HasPole f 0 := by
  have h1 : Tendsto (fun z : ℂ => ‖z - 0‖⁻¹ ^ (n + 1)) (𝓝[≠] 0) atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero n)).comp (tendsto_inv_norm_sub_atTop 0)
  have h2 := Filter.Tendsto.pos_mul_atTop (norm_pos_iff.2 hg0)
    (hg.norm.tendsto.mono_left nhdsWithin_le_nhds) h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hf z hz, norm_div, norm_pow]
  simp [div_eq_mul_inv]

/-! ### Section 9.1 -/

/-- Example 9.1.2: `(e^z - 1)/z` has a removable singularity at the origin. -/
@[kb "beck2025" "Example 9.1.2, p. 149"]
theorem example_9_1_2 : HasRemovableSingularity (fun z => (Complex.exp z - 1) / z) 0 := by
  refine ⟨1, one_pos, dslope Complex.exp 0,
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).2
      Complex.differentiable_exp.differentiableOn, fun z hz => ?_⟩
  rw [dslope_of_ne _ hz.2, slope_def_field]
  simp

/-- Example 9.1.3: `1/sin z - 1/z` has a removable singularity at the origin. -/
@[kb "beck2025" "Example 9.1.3, p. 149"]
theorem example_9_1_3 : HasRemovableSingularity (fun z => 1 / Complex.sin z - 1 / z) 0 := by
  obtain ⟨ε, hε, hs⟩ : ∃ ε > 0, ∀ z ∈ ball (0 : ℂ) ε, sinc' z ≠ 0 := by
    have hc : ContinuousAt sinc' 0 := sinc'_differentiable.continuous.continuousAt
    have := hc.eventually_ne (by rw [sinc'_zero]; exact one_ne_zero)
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ε, hε, fun z hz => h hz⟩
  have hdt : DifferentiableOn ℂ (dslope sinc' 0) (ball 0 ε) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 hε)).2 sinc'_differentiable.differentiableOn
  refine ⟨ε, hε, fun z => -dslope sinc' 0 z / sinc' z, hdt.neg.div
    sinc'_differentiable.differentiableOn hs, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := hz.2
  have hsz := hs z hz.1
  have e := sub_smul_dslope sinc' 0 z
  rw [smul_eq_mul, sub_zero, sinc'_zero] at e
  show 1 / Complex.sin z - 1 / z = -dslope sinc' 0 z / sinc' z
  rw [sin_eq_mul_sinc' z, eq_div_iff hsz]
  field_simp
  linear_combination e

/-- Example 9.1.4: `1/z⁴` has a pole at the origin. -/
@[kb "beck2025" "Example 9.1.4, p. 149"]
theorem example_9_1_4 : HasPole (fun z : ℂ => 1 / z ^ 4) 0 :=
  hasPole_of_div_pow (g := fun _ => 1) continuousAt_const one_ne_zero 3 fun _ _ => rfl

/-- Example 9.1.5: `exp(1/z)` has an essential singularity at the origin (it blows up along the
positive reals and tends to zero along the negative reals). -/
@[kb "beck2025" "Example 9.1.5, p. 149"]
theorem example_9_1_5 : HasEssentialSingularity (fun z : ℂ => Complex.exp (1 / z)) 0 := by
  have hpos : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun t ht => by
        simpa using (ne_of_gt ht)⟩
  have hneg : Tendsto (fun t : ℝ => -(t : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
    · have : Tendsto (fun t : ℝ => -(t : ℂ)) (𝓝 0) (𝓝 0) := by
        have := (Complex.continuous_ofReal.neg).tendsto (0 : ℝ)
        exact this
      exact this.mono_left nhdsWithin_le_nhds
    · simpa using (ne_of_gt ht)
  have hnorm_pos : ∀ t : ℝ, ‖Complex.exp (1 / (t : ℂ))‖ = Real.exp t⁻¹ := fun t => by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hnorm_neg : ∀ t : ℝ, ‖Complex.exp (1 / (-(t : ℂ)))‖ = Real.exp (-t⁻¹) := fun t => by
    rw [Complex.norm_exp]
    congr 1
    simp [one_div]
  have hbig : Tendsto (fun t : ℝ => ‖Complex.exp (1 / (t : ℂ))‖) (𝓝[>] 0) atTop := by
    simp only [hnorm_pos]
    exact Real.tendsto_exp_atTop.comp tendsto_inv_nhdsGT_zero
  have hsmall : Tendsto (fun t : ℝ => ‖Complex.exp (1 / (-(t : ℂ)))‖) (𝓝[>] 0) (𝓝 0) := by
    simp only [hnorm_neg]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_inv_nhdsGT_zero
  constructor
  · rintro ⟨R, hR, g, hg, hfg⟩
    have hgc : ContinuousAt g 0 := (hg.differentiableAt (ball_mem_nhds 0 hR)).continuousAt
    have h1 : Tendsto (fun t : ℝ => ‖g (t : ℂ)‖) (𝓝[>] 0) (𝓝 ‖g 0‖) := by
      have : Tendsto (fun t : ℝ => g (t : ℂ)) (𝓝[>] 0) (𝓝 (g 0)) :=
        hgc.tendsto.comp (hpos.mono_right nhdsWithin_le_nhds)
      exact this.norm
    have h2 : Tendsto (fun t : ℝ => ‖Complex.exp (1 / (t : ℂ))‖) (𝓝[>] 0) (𝓝 ‖g 0‖) := by
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hR] with t ht
      have hm : (t : ℂ) ∈ ball (0 : ℂ) R \ {0} :=
        ⟨by simpa [abs_of_pos ht.1] using ht.2, by simpa using ne_of_gt ht.1⟩
      exact (congrArg norm (hfg hm)).symm
    exact not_tendsto_nhds_of_tendsto_atTop hbig _ h2
  · intro hp
    have := (hp.comp hneg)
    exact not_tendsto_nhds_of_tendsto_atTop this _ hsmall

/-- Example 9.1.11: `sin z / z³` has a pole of order 2 at the origin, i.e. it is
`g z / z²` with `g` holomorphic and nonzero at `0`. -/
@[kb "beck2025" "Example 9.1.11, p. 153"]
theorem example_9_1_11 :
    HasPole (fun z => Complex.sin z / z ^ 3) 0 ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ z, z ≠ 0 → Complex.sin z / z ^ 3 = g z / z ^ 2 := by
  have key : ∀ z : ℂ, z ≠ 0 → Complex.sin z / z ^ 3 = sinc' z / z ^ (1 + 1) := fun z hz => by
    rw [sin_eq_mul_sinc' z]
    field_simp
    ring
  refine ⟨hasPole_of_div_pow sinc'_differentiable.continuous.continuousAt
    (by rw [sinc'_zero]; exact one_ne_zero) 1 key, sinc', sinc'_differentiable.analyticAt 0,
    by rw [sinc'_zero]; exact one_ne_zero, fun z hz => key z hz⟩

/-! ### Section 9.2 -/

/-- Example 9.2.5: the residue of `e^z / sin z` at `0` is `1`. -/
@[kb "beck2025" "Example 9.2.5, p. 155"]
theorem example_9_2_5 : residue (fun z => Complex.exp z / Complex.sin z) 0 = 1 := by
  rw [residue_div_of_simple_zero (f := Complex.exp) (g := Complex.sin) one_pos
    Complex.differentiable_exp.differentiableOn Complex.differentiable_sin.differentiableOn
    Complex.sin_zero (by simp)]
  simp

/-- Example 9.2.6: the residue of `sin z / z³` at `0` is `0`. -/
@[kb "beck2025" "Example 9.2.6, p. 155"]
theorem example_9_2_6 : residue (fun z => Complex.sin z / z ^ 3) 0 = 0 := by
  have := residue_of_eq_div_pow (f := fun z => Complex.sin z / z ^ 3) (g := Complex.sin) (c := 0)
    one_pos Complex.differentiable_sin.differentiableOn 2 fun z _ => by simp
  rw [this]
  have h2 : iteratedDeriv 2 Complex.sin 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have : deriv Complex.sin = Complex.cos := Complex.deriv_sin
    rw [this]
    simp
  rw [h2]
  simp

/-- Example 9.2.8: the residue of `e^z / sin z` at `π` is `-e^π`. -/
@[kb "beck2025" "Example 9.2.8, p. 156"]
theorem example_9_2_8 :
    residue (fun z => Complex.exp z / Complex.sin z) π = -(Real.exp π : ℂ) := by
  rw [residue_div_of_simple_zero (f := Complex.exp) (g := Complex.sin) one_pos
    Complex.differentiable_exp.differentiableOn Complex.differentiable_sin.differentiableOn
    Complex.sin_pi (by simp)]
  simp [← Complex.ofReal_exp]; ring

/-! ### Section 9.3 -/

/-- Rouche comparison on the circle `|z| = 2` for `z⁵` and `z⁴ + z³ + z² + z + 1`. -/
lemma norm_lt_on_sphere_two {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 2) :
    ‖z ^ 4 + z ^ 3 + z ^ 2 + z + 1‖ < ‖z ^ 5‖ := by
  have hz2 : ‖z‖ = 2 := by simpa using hz
  have h1 := norm_add_le (z ^ 4 + z ^ 3 + z ^ 2 + z) 1
  have h2 := norm_add_le (z ^ 4 + z ^ 3 + z ^ 2) z
  have h3 := norm_add_le (z ^ 4 + z ^ 3) (z ^ 2)
  have h4 := norm_add_le (z ^ 4) (z ^ 3)
  simp only [norm_pow, hz2, norm_one] at h1 h2 h3 h4 ⊢
  linarith

/-- Example 9.3.4 (first part): the polynomial `z⁵ + z⁴ + z³ + z² + z + 1` has five zeros, counted
with multiplicity, in the disc `|z| < 2`; by Rouche's theorem with `f = z⁵`. -/
@[kb "beck2025" "Example 9.3.4, p. 159"]
theorem example_9_3_4_zeroCount :
    zeroCount (fun z : ℂ => z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1) 0 2 = 5 := by
  have hR := rouche_circle (f := fun z : ℂ => z ^ 5) (g := fun z : ℂ => z ^ 4 + z ^ 3 + z ^ 2 + z + 1)
    (c := 0) (R := 2) (by norm_num) (fun z _ => by fun_prop) (fun z _ => by fun_prop)
    (fun z hz => norm_lt_on_sphere_two hz)
  have e : (fun z : ℂ => z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1) =
      fun z : ℂ => z ^ 5 + (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) := by
    funext z; ring
  rw [e, hR]
  -- the only zero of `z ^ 5` is `0`, of order `5`
  have hord : ∀ z : ℂ, analyticOrderNatAt (fun z : ℂ => z ^ 5) z = if z = 0 then 5 else 0 := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : (fun z : ℂ => z ^ 5) = (fun z : ℂ => z - 0) ^ 5 := by funext z; simp
      simp only [ite_true, analyticOrderNatAt, this, analyticOrderAt_centeredMonomial]
      rfl
    · have han : AnalyticAt ℂ (fun z : ℂ => z ^ 5) z := by fun_prop
      simp [analyticOrderNatAt, hz, han.analyticOrderAt_eq_zero.2 (pow_ne_zero 5 hz)]
  unfold zeroCount
  simp only [hord]
  rw [finsum_mem_eq_sum_of_inter_support_eq (s := ball (0 : ℂ) 2) (t := {0})]
  · simp
  · ext z
    simp only [mem_inter_iff, Function.mem_support, Finset.coe_singleton, mem_singleton_iff]
    constructor
    · rintro ⟨_, h⟩
      refine ⟨?_, h⟩
      by_contra hz
      simp [hz] at h
    · rintro ⟨rfl, h⟩
      exact ⟨mem_ball_self (by norm_num), h⟩

/-- Example 9.3.4 (second part), proved directly by the estimate `|z⁴+z³+z²+z+1| < |z⁵|` for
`|z| ≥ 2` (rather than from the zero count): every root of `z⁵ + z⁴ + z³ + z² + z + 1` has modulus
less than 2. -/
@[kb "beck2025" "Example 9.3.4, p. 159"]
theorem example_9_3_4_roots :
    ∀ z : ℂ, z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 → ‖z‖ < 2 := by
  intro z hz
  by_contra hcon
  push Not at hcon
  have heq : z ^ 5 = -(z ^ 4 + z ^ 3 + z ^ 2 + z + 1) := by linear_combination hz
  have hn : ‖z‖ ^ 5 = ‖z ^ 4 + z ^ 3 + z ^ 2 + z + 1‖ := by
    rw [← norm_pow, heq, norm_neg]
  have h1 := norm_add_le (z ^ 4 + z ^ 3 + z ^ 2 + z) 1
  have h2 := norm_add_le (z ^ 4 + z ^ 3 + z ^ 2) z
  have h3 := norm_add_le (z ^ 4 + z ^ 3) (z ^ 2)
  have h4 := norm_add_le (z ^ 4) (z ^ 3)
  simp only [norm_pow, norm_one] at h1 h2 h3 h4
  set r := ‖z‖ with hr
  have hr2 : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 < r ^ 5 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hcon 2, pow_le_pow_left₀
      (by norm_num : (0:ℝ) ≤ 2) hcon 3, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hcon 4]
  linarith

end UndergradKB.ComplexAnalysis
