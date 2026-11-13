import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import UndergradKB.ComplexAnalysis.Rectangle

/-!
# Green's theorem for a rectangle

Beck et al. (Theorem A.0.10) state Green's theorem for a region bounded by a piecewise smooth
closed path.  Here the theorem is proved for the counterclockwise boundary `rectPath` of a
rectangle `[x₀, x₁] × [y₀, y₁]`: for real `C¹` functions `f, g` on an open set containing the
rectangle,
`∫_γ f dx + g dy = ∬ (∂g/∂x - ∂f/∂y) dx dy`.

The proof splits the line integral into the four sides, rewrites each as a one-variable integral
by an affine change of variables, and compares with the divergence theorem of Mathlib on a box
(`integral2_divergence_prod_of_hasFDerivAt_off_countable`).
-/

open Set Metric Complex Filter Topology MeasureTheory
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- The line integral `∫_γ f dx + g dy` of real functions along a path on `[0, 1]`. -/
noncomputable def lineIntegral (f g : ℂ → ℝ) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im)

/-! ### Reduction of the four sides to one-variable integrals -/

lemma continuous_mk (p : ℝ) : Continuous (fun y : ℝ => (⟨p, y⟩ : ℂ)) := by
  have : (fun y : ℝ => (⟨p, y⟩ : ℂ)) = fun y : ℝ => (p : ℂ) + (y : ℂ) * I := by
    funext y; apply Complex.ext <;> simp
  rw [this]; fun_prop

lemma continuous_mk' (q : ℝ) : Continuous (fun x : ℝ => (⟨x, q⟩ : ℂ)) := by
  have : (fun x : ℝ => (⟨x, q⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (q : ℂ) * I := by
    funext y; apply Complex.ext <;> simp
  rw [this]; fun_prop

/-- A vertical side: the integrand of the line integral along `t ↦ (p, q + c t)`. -/
lemma vert_side (f g : ℂ → ℝ) (p q c a b m M u v : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn (fun y : ℝ => g ⟨p, y⟩) (Icc m M))
    (hm : ∀ t ∈ Icc a b, c * t + q ∈ Icc m M) (hu : c * a + q = u) (hv : c * b + q = v) :
    IntervalIntegrable (fun t : ℝ => f ⟨p + 0 * t, q + c * t⟩ * 0 + g ⟨p + 0 * t, q + c * t⟩ * c)
      volume a b ∧
    ∫ t in a..b, (f ⟨p + 0 * t, q + c * t⟩ * 0 + g ⟨p + 0 * t, q + c * t⟩ * c) =
      ∫ y in u..v, g ⟨p, y⟩ := by
  have e : (fun t : ℝ => f ⟨p + 0 * t, q + c * t⟩ * 0 + g ⟨p + 0 * t, q + c * t⟩ * c) =
      fun t => (fun y : ℝ => g ⟨p, y⟩) (c * t + q) * c := by
    funext t
    have : (⟨p + 0 * t, q + c * t⟩ : ℂ) = ⟨p, c * t + q⟩ := by
      apply Complex.ext <;> simp [add_comm]
    rw [this]; ring
  rw [e]
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (hg.comp (by fun_prop) hm).mul continuousOn_const
  · rw [intervalIntegral.integral_mul_const, mul_comm, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_add (fun y : ℝ => g ⟨p, y⟩), hu, hv]

/-- A horizontal side: the integrand of the line integral along `t ↦ (p + c t, q)`. -/
lemma horiz_side (f g : ℂ → ℝ) (p q c a b m M u v : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn (fun x : ℝ => f ⟨x, q⟩) (Icc m M))
    (hm : ∀ t ∈ Icc a b, c * t + p ∈ Icc m M) (hu : c * a + p = u) (hv : c * b + p = v) :
    IntervalIntegrable (fun t : ℝ => f ⟨p + c * t, q + 0 * t⟩ * c + g ⟨p + c * t, q + 0 * t⟩ * 0)
      volume a b ∧
    ∫ t in a..b, (f ⟨p + c * t, q + 0 * t⟩ * c + g ⟨p + c * t, q + 0 * t⟩ * 0) =
      ∫ x in u..v, f ⟨x, q⟩ := by
  have e : (fun t : ℝ => f ⟨p + c * t, q + 0 * t⟩ * c + g ⟨p + c * t, q + 0 * t⟩ * 0) =
      fun t => (fun x : ℝ => f ⟨x, q⟩) (c * t + p) * c := by
    funext t
    have : (⟨p + c * t, q + 0 * t⟩ : ℂ) = ⟨c * t + p, q⟩ := by
      apply Complex.ext <;> simp [add_comm]
    rw [this]; ring
  rw [e]
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact (hf.comp (by fun_prop) hm).mul continuousOn_const
  · rw [intervalIntegral.integral_mul_const, mul_comm, ← smul_eq_mul,
      intervalIntegral.smul_integral_comp_mul_add (fun x : ℝ => f ⟨x, q⟩), hu, hv]

/-- If `γ` is locally affine near each interior point of `(a, b)`, its line-integral integrand
agrees there with the one of the affine path. -/
lemma lineIntegrand_eqOn (f g : ℂ → ℝ) {γ : ℝ → ℂ} {a b px py cx cy : ℝ}
    (h : ∀ t ∈ Ioo a b, γ =ᶠ[𝓝 t] fun s => (⟨px + cx * s, py + cy * s⟩ : ℂ)) :
    EqOn (fun t => f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im)
      (fun t => f ⟨px + cx * t, py + cy * t⟩ * cx + g ⟨px + cx * t, py + cy * t⟩ * cy)
      (Ioo a b) := by
  intro t ht
  have h1 := h t ht
  have hfun : (fun s : ℝ => (⟨px + cx * s, py + cy * s⟩ : ℂ)) =
      fun s => (⟨px, py⟩ : ℂ) + s • (⟨cx, cy⟩ : ℂ) := by
    funext s; apply Complex.ext <;> simp [mul_comm]
  have hd : HasDerivAt (fun s : ℝ => (⟨px + cx * s, py + cy * s⟩ : ℂ)) (⟨cx, cy⟩ : ℂ) t := by
    rw [hfun]
    simpa using ((hasDerivAt_id t).smul_const (⟨cx, cy⟩ : ℂ)).const_add (⟨px, py⟩ : ℂ)
  have hder : deriv γ t = ⟨cx, cy⟩ := by rw [h1.deriv_eq]; exact hd.deriv
  simp only [h1.eq_of_nhds, hder]

lemma integral_quarter (f g : ℂ → ℝ) {γ : ℝ → ℂ} {a b px py cx cy : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Ioo a b, γ =ᶠ[𝓝 t] fun s => (⟨px + cx * s, py + cy * s⟩ : ℂ))
    (hI : IntervalIntegrable
      (fun t => f ⟨px + cx * t, py + cy * t⟩ * cx + g ⟨px + cx * t, py + cy * t⟩ * cy)
      volume a b) :
    IntervalIntegrable (fun t => f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im) volume a b ∧
    ∫ t in a..b, (f (γ t) * (deriv γ t).re + g (γ t) * (deriv γ t).im) =
      ∫ t in a..b,
        (f ⟨px + cx * t, py + cy * t⟩ * cx + g ⟨px + cx * t, py + cy * t⟩ * cy) := by
  have hE := lineIntegrand_eqOn f g h
  refine ⟨(intervalIntegrable_congr_uIoo ?_).2 hI, intervalIntegral.integral_congr_Ioo_of_le hab hE⟩
  rwa [uIoo_of_le hab]

/-- The line integral around the rectangle as four one-variable integrals. -/
lemma lineIntegral_rectPath {x₀ x₁ y₀ y₁ : ℝ} {f g : ℂ → ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hf : ContinuousOn f (closedRect x₀ x₁ y₀ y₁))
    (hg : ContinuousOn g (closedRect x₀ x₁ y₀ y₁)) :
    lineIntegral f g (rectPath x₀ x₁ y₀ y₁) =
      ((∫ y in y₀..y₁, g ⟨x₁, y⟩) - ∫ x in x₀..x₁, f ⟨x, y₁⟩) -
        (∫ y in y₀..y₁, g ⟨x₀, y⟩) + ∫ x in x₀..x₁, f ⟨x, y₀⟩ := by
  have hdx : 0 < x₁ - x₀ := sub_pos.2 hx
  have hdy : 0 < y₁ - y₀ := sub_pos.2 hy
  have hgv : ∀ p ∈ Icc x₀ x₁, ContinuousOn (fun y : ℝ => g ⟨p, y⟩) (Icc y₀ y₁) := fun p hp =>
    hg.comp (continuous_mk p).continuousOn (fun y hy => ⟨hp, hy⟩)
  have hfh : ∀ q ∈ Icc y₀ y₁, ContinuousOn (fun x : ℝ => f ⟨x, q⟩) (Icc x₀ x₁) := fun q hq =>
    hf.comp (continuous_mk' q).continuousOn (fun x hx => ⟨hx, hq⟩)
  have hx₀ : x₀ ∈ Icc x₀ x₁ := ⟨le_rfl, hx.le⟩
  have hx₁ : x₁ ∈ Icc x₀ x₁ := ⟨hx.le, le_rfl⟩
  have hy₀ : y₀ ∈ Icc y₀ y₁ := ⟨le_rfl, hy.le⟩
  have hy₁ : y₁ ∈ Icc y₀ y₁ := ⟨hy.le, le_rfl⟩
  -- the four quarters
  obtain ⟨i1, v1⟩ := vert_side f g x₁ y₀ (4 * (y₁ - y₀)) 0 (1 / 4) y₀ y₁ y₀ y₁ (by norm_num)
    (hgv _ hx₁) (fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩) (by ring) (by ring)
  obtain ⟨i2, v2⟩ := horiz_side f g (x₁ + (x₁ - x₀)) y₁ (-(4 * (x₁ - x₀))) (1 / 4) (1 / 2)
    x₀ x₁ x₁ x₀ (by norm_num) (hfh _ hy₁)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩) (by ring) (by ring)
  obtain ⟨i3, v3⟩ := vert_side f g x₀ (y₁ + 2 * (y₁ - y₀)) (-(4 * (y₁ - y₀))) (1 / 2) (3 / 4)
    y₀ y₁ y₁ y₀ (by norm_num) (hgv _ hx₀)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩) (by ring) (by ring)
  obtain ⟨i4, v4⟩ := horiz_side f g (x₀ - 3 * (x₁ - x₀)) y₀ (4 * (x₁ - x₀)) (3 / 4) 1
    x₀ x₁ x₀ x₁ (by norm_num) (hfh _ hy₀)
    (fun t ht => ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩) (by ring) (by ring)
  obtain ⟨j1, w1⟩ := integral_quarter f g (γ := rectPath x₀ x₁ y₀ y₁) (a := 0) (b := 1 / 4)
    (px := x₁) (py := y₀) (cx := 0) (cy := 4 * (y₁ - y₀)) (by norm_num)
    (fun t ht => by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      rw [rectPath_q1 (le_of_lt hs)]
      apply Complex.ext <;> simp; ring) i1
  obtain ⟨j2, w2⟩ := integral_quarter f g (γ := rectPath x₀ x₁ y₀ y₁) (a := 1 / 4) (b := 1 / 2)
    (px := x₁ + (x₁ - x₀)) (py := y₁) (cx := -(4 * (x₁ - x₀))) (cy := 0) (by norm_num)
    (fun t ht => by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [rectPath_q2 hs.1 hs.2.le]
      apply Complex.ext <;> simp; ring) i2
  obtain ⟨j3, w3⟩ := integral_quarter f g (γ := rectPath x₀ x₁ y₀ y₁) (a := 1 / 2) (b := 3 / 4)
    (px := x₀) (py := y₁ + 2 * (y₁ - y₀)) (cx := 0) (cy := -(4 * (y₁ - y₀))) (by norm_num)
    (fun t ht => by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [rectPath_q3 hs.1 hs.2.le]
      apply Complex.ext <;> simp; ring) i3
  obtain ⟨j4, w4⟩ := integral_quarter f g (γ := rectPath x₀ x₁ y₀ y₁) (a := 3 / 4) (b := 1)
    (px := x₀ - 3 * (x₁ - x₀)) (py := y₀) (cx := 4 * (x₁ - x₀)) (cy := 0) (by norm_num)
    (fun t ht => by
      filter_upwards [Ioi_mem_nhds ht.1] with s hs
      rw [rectPath_q4 hs]
      apply Complex.ext <;> simp; ring) i4
  unfold lineIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (j1.trans j2) (j3.trans j4),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 4) j1 j2,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 4) j3 j4,
    w1, w2, w3, w4, v1, v2, v3, v4, intervalIntegral.integral_symm x₀ x₁,
    intervalIntegral.integral_symm y₀ y₁]
  ring

/-! ### Green's theorem -/

/-- **Green's theorem for a rectangle.** For real `C¹` functions `f, g` on an open set containing
the closed rectangle, the line integral `∫ f dx + g dy` along the counterclockwise boundary equals
the double integral of `∂g/∂x - ∂f/∂y` over the rectangle. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_rectPath {x₀ x₁ y₀ y₁ : ℝ} {f g : ℂ → ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    {U : Set ℂ} (hU : IsOpen U) (hR : closedRect x₀ x₁ y₀ y₁ ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g (rectPath x₀ x₁ y₀ y₁) =
      ∫ x in x₀..x₁, ∫ y in y₀..y₁, (fderiv ℝ g ⟨x, y⟩ 1 - fderiv ℝ f ⟨x, y⟩ I) := by
  have hfc : ContinuousOn f (closedRect x₀ x₁ y₀ y₁) := hf.continuousOn.mono hR
  have hgc : ContinuousOn g (closedRect x₀ x₁ y₀ y₁) := hg.continuousOn.mono hR
  rw [lineIntegral_rectPath hx hy hfc hgc]
  set L : ℝ × ℝ →L[ℝ] ℂ := (Complex.equivRealProdCLM.symm : (ℝ × ℝ) ≃L[ℝ] ℂ).toContinuousLinearMap
    with hLdef
  have hL : ∀ p : ℝ × ℝ, L p = ⟨p.1, p.2⟩ := fun p => by
    apply Complex.ext <;> simp [hLdef, Complex.equivRealProdCLM_symm_apply]
  have hL1 : L (1, 0) = 1 := by rw [hL]; apply Complex.ext <;> simp
  have hL2 : L (0, 1) = I := by rw [hL]; apply Complex.ext <;> simp
  have hbox : uIcc x₀ x₁ ×ˢ uIcc y₀ y₁ = Icc x₀ x₁ ×ˢ Icc y₀ y₁ := by
    rw [uIcc_of_le hx.le, uIcc_of_le hy.le]
  have hmapC : MapsTo L (Icc x₀ x₁ ×ˢ Icc y₀ y₁) U := fun p hp => hR (by rw [hL]; exact hp)
  have hmapO : ∀ p ∈ Ioo x₀ x₁ ×ˢ Ioo y₀ y₁, L p ∈ U := fun p hp =>
    hR (by rw [hL]; exact ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
  have hdf : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
  have hdg : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
  have hcont : ∀ h : ℂ → ℝ, ContinuousOn h U →
      ContinuousOn (fun p : ℝ × ℝ => h (L p)) (Icc x₀ x₁ ×ˢ Icc y₀ y₁) := fun h hh =>
    hh.comp L.continuous.continuousOn hmapC
  have hF := hcont g hg.continuousOn
  have hG := (hcont f hf.continuousOn).neg
  have hFd : ∀ p ∈ Ioo (min x₀ x₁) (max x₀ x₁) ×ˢ Ioo (min y₀ y₁) (max y₀ y₁) \ (∅ : Set (ℝ × ℝ)),
      HasFDerivAt (fun p : ℝ × ℝ => g (L p)) ((fderiv ℝ g (L p)).comp L) p := by
    intro p hp
    rw [min_eq_left hx.le, max_eq_right hx.le, min_eq_left hy.le, max_eq_right hy.le] at hp
    exact (hdg _ (hmapO p hp.1)).hasFDerivAt.comp p L.hasFDerivAt
  have hGd : ∀ p ∈ Ioo (min x₀ x₁) (max x₀ x₁) ×ˢ Ioo (min y₀ y₁) (max y₀ y₁) \ (∅ : Set (ℝ × ℝ)),
      HasFDerivAt (fun p : ℝ × ℝ => -f (L p)) (-((fderiv ℝ f (L p)).comp L)) p := by
    intro p hp
    rw [min_eq_left hx.le, max_eq_right hx.le, min_eq_left hy.le, max_eq_right hy.le] at hp
    exact ((hdf _ (hmapO p hp.1)).hasFDerivAt.comp p L.hasFDerivAt).neg
  have hcg : ContinuousOn (fun z => fderiv ℝ g z 1) U :=
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcf : ContinuousOn (fun z => fderiv ℝ f z I) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hInt : IntegrableOn (fun p : ℝ × ℝ => ((fderiv ℝ g (L p)).comp L) (1, 0) +
      (-((fderiv ℝ f (L p)).comp L)) (0, 1)) (uIcc x₀ x₁ ×ˢ uIcc y₀ y₁) := by
    rw [hbox]
    refine ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_
    have := (hcont _ hcg).sub (hcont _ hcf)
    refine this.congr fun p _ => ?_
    simp [hL1, hL2, sub_eq_add_neg]
  have H := integral2_divergence_prod_of_hasFDerivAt_off_countable
    (fun p : ℝ × ℝ => g (L p)) (fun p : ℝ × ℝ => -f (L p))
    (fun p => (fderiv ℝ g (L p)).comp L) (fun p => -((fderiv ℝ f (L p)).comp L))
    x₀ y₀ x₁ y₁ ∅ countable_empty (by rw [hbox]; exact hF) (by rw [hbox]; exact hG)
    hFd hGd hInt
  have hlhs : (∫ x in x₀..x₁, ∫ y in y₀..y₁,
      (((fderiv ℝ g (L (x, y))).comp L) (1, 0) + (-((fderiv ℝ f (L (x, y))).comp L)) (0, 1))) =
      ∫ x in x₀..x₁, ∫ y in y₀..y₁, (fderiv ℝ g ⟨x, y⟩ 1 - fderiv ℝ f ⟨x, y⟩ I) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp [hL1, hL2, hL,
      sub_eq_add_neg]
  rw [← hlhs, H]
  simp only [hL, intervalIntegral.integral_neg]
  ring

/-- The integral over the open rectangle of a function continuous on the closed rectangle is the
iterated interval integral. -/
lemma setIntegral_openRect {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) {h : ℂ → ℝ}
    (hc : ContinuousOn h (closedRect x₀ x₁ y₀ y₁)) :
    ∫ z in openRect x₀ x₁ y₀ y₁, h z = ∫ x in x₀..x₁, ∫ y in y₀..y₁, h ⟨x, y⟩ := by
  have hm := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => h ⟨p.1, p.2⟩)
    (Ioo x₀ x₁ ×ˢ Ioo y₀ y₁)
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioo x₀ x₁ ×ˢ Ioo y₀ y₁) =
      openRect x₀ x₁ y₀ y₁ := by
    ext z; simp [mem_reProdIm, Complex.measurableEquivRealProd]
  have hk : ContinuousOn (fun p : ℝ × ℝ => h ⟨p.1, p.2⟩) (Icc x₀ x₁ ×ˢ Icc y₀ y₁) :=
    hc.comp (Complex.equivRealProdCLM.symm.continuous.continuousOn) (fun p hp => by
      exact hp)
  have hint : IntegrableOn (fun p : ℝ × ℝ => h ⟨p.1, p.2⟩) (Ioo x₀ x₁ ×ˢ Ioo y₀ y₁)
      (volume.prod volume) :=
    ((hk.integrableOn_compact (μ := volume.prod volume)
      (isCompact_Icc.prod isCompact_Icc))).mono_set (prod_mono Ioo_subset_Icc_self
        Ioo_subset_Icc_self)
  have hz : (fun z : ℂ => h ⟨(Complex.measurableEquivRealProd z).1,
      (Complex.measurableEquivRealProd z).2⟩) = h := by
    funext z; rfl
  rw [hpre, hz] at hm
  rw [hm, Measure.volume_eq_prod, setIntegral_prod _ hint]
  simp only [intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_of_le hy.le,
    integral_Ioc_eq_integral_Ioo]

/-- **Green's theorem for a rectangle**, with the double integral over the inside of the path as an
integral over a subset of `ℂ`. -/
@[kb "beck2025" "Theorem A.0.10, p. 167"]
theorem green_rectPath_insideOf {x₀ x₁ y₀ y₁ : ℝ} {f g : ℂ → ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    {U : Set ℂ} (hU : IsOpen U) (hR : closedRect x₀ x₁ y₀ y₁ ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U) :
    lineIntegral f g (rectPath x₀ x₁ y₀ y₁) =
      ∫ z in insideOf (rectPath x₀ x₁ y₀ y₁), (fderiv ℝ g z 1 - fderiv ℝ f z I) := by
  rw [green_rectPath hx hy hU hR hf hg, insideOf_rectPath hx hy,
    setIntegral_openRect hx hy]
  have hcg : ContinuousOn (fun z => fderiv ℝ g z 1) U :=
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcf : ContinuousOn (fun z => fderiv ℝ f z I) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  exact (hcg.sub hcf).mono hR

end UndergradKB.ComplexAnalysis
