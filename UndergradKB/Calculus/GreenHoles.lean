import UndergradKB.Common.Attr
import UndergradKB.Calculus.GreenRegions

/-! # Calculus: Green's theorem on regions with holes, homotopy invariance, the swirl field

OpenStax Calculus 3 §6.4 (Green's theorem on general regions, Example 6.47). Consequences of
`green_param_image` and `green_param`:
* a region with a hole, swept by the segments from an inner closed curve to an outer closed curve: the double
  integral of `Q_x - P_y` is the circulation around the outer curve minus that around the inner one;
* the circulation of a curl-free field is invariant under `C²` homotopies of closed curves inside its domain;
* the swirl field `(-y, x)/(x²+y²)` is curl free off the origin; its circulation is `0` around closed curves that
  miss a ray from the origin and `2π` around closed polar graphs `r = ρ(θ) > 0` and around curves homotopic to the
  unit circle in the punctured plane.

Missing for the book's general statements (every piecewise smooth simple closed curve): the Jordan curve theorem
and the fact that a Jordan curve around the origin is homotopic in the punctured plane to the circle (winding
number `±1`); not in Mathlib. -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-! ### Regions with a hole -/

/-- OpenStax Calculus 3:§6.4 Theorem (Green's theorem on general regions) (CA-639), region with one hole: let
`D` be swept by the segments from an inner closed curve `γ₀` to an outer closed curve `γ₁` (`t ∈ [a,b]`), i.e.
`D = Φ(S)` with `Φ(s, t) = (1 - s) γ₀(t) + s γ₁(t)`, injective and orientation preserving on `S`,
`(0,1)×(a,b) ⊆ S ⊆ [0,1]×[a,b]`. Then `∬_D (Q_x - P_y) dA = ∮_{γ₁} P dx + Q dy - ∮_{γ₀} P dx + Q dy`: the outer
boundary counterclockwise plus the inner boundary clockwise (the segments `t = a` and `t = b` coincide and their
contributions cancel). -/
@[kb "openstaxcalculus2016" "3:§6.4 Theorem (Green's theorem on general regions), p. 656"]
theorem green_between_curves (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (γ₀ γ₁ : ℝ → ℝ × ℝ) (h₀ : ContDiff ℝ 2 γ₀)
    (h₁ : ContDiff ℝ 2 γ₁) {a b : ℝ} (hab : a ≤ b) (hc₀ : γ₀ a = γ₀ b) (hc₁ : γ₁ a = γ₁ b)
    (hΦU : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, (1 - s) • γ₀ t + s • γ₁ t ∈ U) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc 0 1 ×ˢ Icc a b) (hSsup : Ioo 0 1 ×ˢ Ioo a b ⊆ S)
    (hinj : InjOn (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) S)
    (hjac : ∀ z ∈ S, 0 ≤ jacobian2 (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) z) :
    ∫ p in (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) '' S, curl2 P Q p =
      greenLineIntegral P Q (fun t => (γ₁ t).1) (fun t => (γ₁ t).2) a b -
        greenLineIntegral P Q (fun t => (γ₀ t).1) (fun t => (γ₀ t).2) a b := by
  set Φ : ℝ × ℝ → ℝ × ℝ := fun z => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2 with hΦdef
  have hΦ : ContDiff ℝ 2 Φ :=
    ((contDiff_const.sub contDiff_fst).smul (h₀.comp contDiff_snd)).add
      (contDiff_fst.smul (h₁.comp contDiff_snd))
  rw [green_param_image P Q Φ hU hP hQ hΦ zero_le_one hab (fun z hz => hΦU z.1 hz.1 z.2 hz.2) hS hSsub
    hSsup hinj hjac]
  have f₁ : ∀ t, Φ (t, a) = Φ (t, b) := fun t => by simp only [hΦdef, hc₀, hc₁]
  have f₂ : ∀ t, Φ (1, t) = γ₁ t := fun t => by simp [hΦdef]
  have f₃ : ∀ t, Φ (0, t) = γ₀ t := fun t => by simp [hΦdef]
  simp only [f₁, f₂, f₃]
  ring

/-! ### Homotopy invariance -/

/-- The circulation of a curl-free field (`Q_x = P_y` on an open set `U`) is unchanged under a `C²` homotopy of
closed curves in `U`: if `H(s, a) = H(s, b)` for every `s`, the circulations along `H(0, ·)` and `H(1, ·)` over
`[a, b]` are equal. -/
theorem circulation_homotopy (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hcurl : ∀ p ∈ U, curl2 P Q p = 0)
    (H : ℝ × ℝ → ℝ × ℝ) (hH : ContDiff ℝ 2 H) {a b : ℝ} (hab : a ≤ b)
    (hHU : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, H (s, t) ∈ U) (hcl : ∀ s, H (s, a) = H (s, b)) :
    greenLineIntegral P Q (fun t => (H (0, t)).1) (fun t => (H (0, t)).2) a b =
      greenLineIntegral P Q (fun t => (H (1, t)).1) (fun t => (H (1, t)).2) a b := by
  have hHU' : ∀ z ∈ uIcc 0 1 ×ˢ uIcc a b, H z ∈ U := by
    intro z hz
    rw [uIcc_of_le zero_le_one, uIcc_of_le hab] at hz
    exact hHU z.1 hz.1 z.2 hz.2
  have key := green_param P Q H hU hP hQ hH hHU'
  have h0 : (∫ x in (0 : ℝ)..1, ∫ y in a..b, curl2 P Q (H (x, y)) * jacobian2 H (x, y)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun x hx => ?_)]
    · simp
    · simp only
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
      · simp
      · rw [hcurl _ (hHU' (x, y) ⟨hx, hy⟩), zero_mul]
  simp only [hcl] at key
  linarith

/-! ### The swirl field `(-y, x)/(x²+y²)` -/

theorem sq_add_sq_ne_zero_of_ne {p : ℝ × ℝ} (hp : p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≠ 0 := by
  intro h
  apply hp
  have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have h2 : p.2 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  exact Prod.ext h1 h2

theorem contDiffOn_swirlP : ContDiffOn ℝ 1 swirlP {p | p ≠ 0} := by
  unfold swirlP
  exact (contDiff_snd.neg.contDiffOn).div (by fun_prop) (fun p hp => sq_add_sq_ne_zero_of_ne hp)

theorem contDiffOn_swirlQ : ContDiffOn ℝ 1 swirlQ {p | p ≠ 0} := by
  unfold swirlQ
  exact (contDiff_fst.contDiffOn).div (by fun_prop) (fun p hp => sq_add_sq_ne_zero_of_ne hp)

theorem isOpen_ne_zero_plane : IsOpen {p : ℝ × ℝ | p ≠ 0} := isOpen_ne

/-- OpenStax Calculus 3:Example 6.47 (CA-640): the swirl field `(-y, x)/(x²+y²)` is curl free away from the
origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem curl2_swirl {p : ℝ × ℝ} (hp : p ≠ 0) : curl2 swirlP swirlQ p = 0 := by
  obtain ⟨x, y⟩ := p
  have hd : x ^ 2 + y ^ 2 ≠ 0 := sq_add_sq_ne_zero_of_ne hp
  have hPd : DifferentiableAt ℝ swirlP (x, y) :=
    (contDiffOn_swirlP.differentiableOn one_ne_zero _ hp).differentiableAt (isOpen_ne_zero_plane.mem_nhds hp)
  have hQd : DifferentiableAt ℝ swirlQ (x, y) :=
    (contDiffOn_swirlQ.differentiableOn one_ne_zero _ hp).differentiableAt (isOpen_ne_zero_plane.mem_nhds hp)
  have hQ1 := hasDerivAt_horizontal hQd
  have hP1 := hasDerivAt_vertical hPd
  have hQ2 : HasDerivAt (fun t => swirlQ (t, y))
      ((1 * (x ^ 2 + y ^ 2) - x * (2 * x)) / (x ^ 2 + y ^ 2) ^ 2) x := by
    have hq : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    exact (hasDerivAt_id' x).div hq hd
  have hP2 : HasDerivAt (fun t => swirlP (x, t))
      ((-1 * (x ^ 2 + y ^ 2) - (-y) * (2 * y)) / (x ^ 2 + y ^ 2) ^ 2) y := by
    have hq : HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (x ^ 2)
    exact (hasDerivAt_id' y).neg.div hq hd
  rw [curl2, pdx2, pdy2, hQ1.unique hQ2, hP1.unique hP2]
  field_simp
  ring

/-- OpenStax Calculus 3:Example 6.47 (CA-640), curves not enclosing the origin: the circulation of
`(-y, x)/(x²+y²)` around a `C²` closed curve that misses a ray `{τ u : τ ≥ 0}` from the origin is `0` (the curve
is contracted, along segments, to the point `-u` without meeting the origin). -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_avoiding_ray (γ : ℝ → ℝ × ℝ) (hγ : ContDiff ℝ 2 γ) {a b : ℝ} (hab : a ≤ b)
    (hcl : γ a = γ b) (u : ℝ × ℝ) (hu : u ≠ 0) (hray : ∀ t ∈ Icc a b, ∀ τ : ℝ, 0 ≤ τ → γ t ≠ τ • u) :
    greenLineIntegral swirlP swirlQ (fun t => (γ t).1) (fun t => (γ t).2) a b = 0 := by
  set H : ℝ × ℝ → ℝ × ℝ := fun z => (1 - z.1) • γ z.2 + z.1 • (-u) with hHdef
  have hH : ContDiff ℝ 2 H :=
    ((contDiff_const.sub contDiff_fst).smul (hγ.comp contDiff_snd)).add (contDiff_fst.smul contDiff_const)
  have hHU : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, H (s, t) ∈ {p : ℝ × ℝ | p ≠ 0} := by
    intro s hs t ht h0
    simp only [hHdef] at h0
    rcases eq_or_lt_of_le hs.2 with rfl | hs1
    · apply hu
      simpa using h0
    · have h1 : 0 < 1 - s := by linarith
      apply hray t ht (s / (1 - s)) (div_nonneg hs.1 h1.le)
      have h2 : (1 - s) • γ t = s • u := by
        have := congrArg (· + s • u) h0
        simpa using this
      calc γ t = (1 - s)⁻¹ • ((1 - s) • γ t) := by rw [smul_smul, inv_mul_cancel₀ h1.ne', one_smul]
        _ = (s / (1 - s)) • u := by rw [h2, smul_smul, div_eq_inv_mul]
  have key := circulation_homotopy swirlP swirlQ isOpen_ne_zero_plane contDiffOn_swirlP contDiffOn_swirlQ
    (fun p hp => curl2_swirl hp) H hH hab hHU (fun s => by simp only [hHdef, hcl])
  have e0 : ∀ t, H (0, t) = γ t := fun t => by simp [hHdef]
  have e1 : ∀ t, H (1, t) = -u := fun t => by simp [hHdef]
  simp only [e0, e1] at key
  rw [key, greenLineIntegral]
  simp

/-- OpenStax Calculus 3:Example 6.47 (CA-640), curves enclosing the origin: the circulation of
`(-y, x)/(x²+y²)` around the polar graph `r = ρ(θ)`, `0 ≤ θ ≤ 2π`, with `ρ` differentiable and positive (for
`ρ(0) = ρ(2π)` a positively oriented simple closed curve around the origin, star shaped about it) is `2π`. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_polar_graph (ρ : ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hpos : ∀ θ ∈ Icc 0 (2 * π), 0 < ρ θ) :
    greenLineIntegral swirlP swirlQ (fun θ => ρ θ * Real.cos θ) (fun θ => ρ θ * Real.sin θ) 0 (2 * π) =
      2 * π := by
  rw [greenLineIntegral, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun θ hθ => ?_)]
  · simp
  · rw [uIcc_of_le (by positivity)] at hθ
    have hr := hpos θ hθ
    have hx : deriv (fun θ => ρ θ * Real.cos θ) θ = deriv ρ θ * Real.cos θ - ρ θ * Real.sin θ := by
      have h : HasDerivAt (fun θ => ρ θ * Real.cos θ) (deriv ρ θ * Real.cos θ + ρ θ * -Real.sin θ) θ :=
        (hρ θ).hasDerivAt.mul (Real.hasDerivAt_cos θ)
      rw [h.deriv]
      ring
    have hy : deriv (fun θ => ρ θ * Real.sin θ) θ = deriv ρ θ * Real.sin θ + ρ θ * Real.cos θ := by
      have h : HasDerivAt (fun θ => ρ θ * Real.sin θ) (deriv ρ θ * Real.sin θ + ρ θ * Real.cos θ) θ :=
        (hρ θ).hasDerivAt.mul (Real.hasDerivAt_sin θ)
      rw [h.deriv]
    have hs : (ρ θ * Real.cos θ) ^ 2 + (ρ θ * Real.sin θ) ^ 2 = ρ θ ^ 2 := by
      linear_combination ρ θ ^ 2 * Real.sin_sq_add_cos_sq θ
    simp only [swirlP, swirlQ, hx, hy, hs]
    have hr2 : ρ θ ^ 2 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hr2]
    linear_combination ρ θ ^ 2 * Real.sin_sq_add_cos_sq θ

/-- OpenStax Calculus 3:Example 6.47 (CA-640), general form: the circulation of `(-y, x)/(x²+y²)` along a `C²`
closed curve that is `C²`-homotopic, through closed curves avoiding the origin, to the unit circle is `2π`. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_homotopic_circle (H : ℝ × ℝ → ℝ × ℝ) (hH : ContDiff ℝ 2 H)
    (hHU : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 (2 * π), H (s, t) ≠ 0) (hcl : ∀ s, H (s, 0) = H (s, 2 * π))
    (h1 : ∀ t, H (1, t) = (Real.cos t, Real.sin t)) :
    greenLineIntegral swirlP swirlQ (fun t => (H (0, t)).1) (fun t => (H (0, t)).2) 0 (2 * π) = 2 * π := by
  rw [circulation_homotopy swirlP swirlQ isOpen_ne_zero_plane contDiffOn_swirlP contDiffOn_swirlQ
    (fun p hp => curl2_swirl hp) H hH (by positivity) hHU hcl]
  simp only [h1]
  simpa using swirl_circulation_origin_circle 1 one_pos

end UndergradKB.Calculus
