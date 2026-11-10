import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HyperbolicDisc

/-! # The conformal disc model, continued (Petrunin, chapters 12, 13, 18)

Schwarz-Pick theorem (Theorem 18.19), the conformal factor (Lemma 13.13), additivity of the
h-distance along a diameter (Lemma 12.9), the inverse-point formula for `cosh` of the h-distance
(Exercise 12.25), and the circumference identity for the centred h-circle (Proposition 13.14). -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate Filter Topology

section SchwarzPick

variable {a z w x y : ℂ}

theorem hdist_zero_mono (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (hxy : ‖x‖ ≤ ‖y‖) :
    hdist 0 x ≤ hdist 0 y := by
  rw [hdist_zero_eq_log hx, hdist_zero_eq_log hy]
  have h1 : 0 < 1 - ‖x‖ := by linarith
  have h2 : 0 < 1 - ‖y‖ := by linarith
  have h0 := norm_nonneg x
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem mobius_neg_mobius (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mobius (-a) (mobius a z) = z := by
  have hD := mobius_den_ne ha hz
  have e : (‖a‖ : ℂ) ^ 2 = a * conj a := by
    have := Complex.mul_conj a
    rw [Complex.normSq_eq_norm_sq] at this
    rw [this]; push_cast; ring
  have hk : (1 - (‖a‖ : ℂ) ^ 2) ≠ 0 := by
    have := one_sub_sq_pos ha
    have h2 : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simpa using h2
  unfold mobius
  rw [map_neg]
  have h1 : (z - a) / (1 - conj a * z) + a = z * (1 - (‖a‖ : ℂ) ^ 2) / (1 - conj a * z) := by
    rw [e, div_add' _ _ _ hD]
    congr 1; ring
  have h2 : 1 - -conj a * ((z - a) / (1 - conj a * z)) = (1 - (‖a‖ : ℂ) ^ 2) / (1 - conj a * z) := by
    rw [eq_div_iff hD, e]
    have := div_mul_cancel₀ (z - a) hD
    linear_combination (conj a) * this
  rw [sub_neg_eq_add, h1, h2, div_div_div_cancel_right₀ hD, mul_div_cancel_right₀ _ hk]

theorem differentiableOn_mobius (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (mobius a) (Metric.ball 0 1) := by
  have h1 : DifferentiableOn ℂ (fun z : ℂ => z - a) (Metric.ball 0 1) :=
    differentiableOn_id.sub_const a
  have h2 : DifferentiableOn ℂ (fun z : ℂ => 1 - conj a * z) (Metric.ball 0 1) :=
    (differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)
  exact h1.div h2 (fun x hx => mobius_den_ne ha (by simpa using hx))

/-- Theorem 18.19 (Schwarz-Pick, inequality part): a holomorphic self-map of the open unit disc
does not increase the h-distance.  The rigidity statement for the equality case is not
formalized. -/
@[kb "petrunin2025" "Theorem 18.19, pp. 155-156"]
theorem schwarz_pick {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hmaps : ∀ z, ‖z‖ < 1 → ‖f z‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hdist (f z) (f w) ≤ hdist z w := by
  have hfw := hmaps w hw
  have hnw : ‖-w‖ < 1 := by simpa using hw
  set g : ℂ → ℂ := fun u => mobius (f w) (f (mobius (-w) u)) with hg
  have hm1 : Set.MapsTo (mobius (-w)) (Metric.ball 0 1) (Metric.ball 0 1) := fun u hu => by
    simpa using norm_mobius_lt_one hnw (by simpa using hu)
  have hm2 : Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) := fun u hu => by
    simpa using hmaps u (by simpa using hu)
  have hd : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    (differentiableOn_mobius hfw).comp (hf.comp (differentiableOn_mobius hnw) hm1) (hm2.comp hm1)
  have hmap : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1) := fun u hu => by
    have := norm_mobius_lt_one hfw (hmaps _ (norm_mobius_lt_one hnw (by simpa using hu)))
    simpa using this.le
  have h0 : g 0 = 0 := by
    have : mobius (-w) 0 = w := by simp [mobius]
    simp only [hg, this]
    exact mobius_self hfw
  have hu : ‖mobius w z‖ < 1 := norm_mobius_lt_one hw hz
  have key := Complex.norm_le_norm_of_mapsTo_ball hd hmap h0 (by simpa using hu)
  have e : g (mobius w z) = mobius (f w) (f z) := by
    simp only [hg, mobius_neg_mobius hw hz]
  rw [e] at key
  have hlt := norm_mobius_lt_one hfw (hmaps z hz)
  have h3 := hdist_zero_mono hlt hu key
  have e1 : hdist (f z) (f w) = hdist 0 (mobius (f w) (f z)) := by
    rw [← hdist_mobius hfw (hmaps z hz) hfw, mobius_self hfw, hdist_comm]
  have e2 : hdist z w = hdist 0 (mobius w z) := by
    rw [← hdist_mobius hw hz hw, mobius_self hw, hdist_comm]
  rw [e1, e2]
  exact h3

end SchwarzPick

/-! ### The conformal factor (Lemma 13.13) -/

section Conformal

variable {P Q : ℂ}

/-- The auxiliary scale `((1-‖P‖²)(1-‖Q‖²))^{-1/2}`. -/
noncomputable def hscale (P Q : ℂ) : ℝ := (Real.sqrt ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)))⁻¹

theorem hscale_pos (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) : 0 < hscale P Q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (one_sub_sq_pos hP) (one_sub_sq_pos hQ)))

/-- The h-distance in terms of `arsinh`: `PQ_h = 2 arsinh (‖P - Q‖ / √((1-‖P‖²)(1-‖Q‖²)))`. -/
theorem hdist_eq_two_arsinh (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    hdist P Q = 2 * Real.arsinh (‖P - Q‖ * hscale P Q) := by
  set s := ‖P - Q‖ * hscale P Q with hs
  have hsc := hscale_pos hP hQ
  have hs0 : 0 ≤ s := mul_nonneg (norm_nonneg _) hsc.le
  have hD := mul_pos (one_sub_sq_pos hP) (one_sub_sq_pos hQ)
  have hs2 : s ^ 2 = ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) := by
    rw [hs, mul_pow, hscale, inv_pow, Real.sq_sqrt hD.le]
    field_simp
  have hc : hcosh P Q = Real.cosh (2 * Real.arsinh s) := by
    rw [Real.cosh_two_mul, Real.cosh_sq, Real.sinh_arsinh, hs2]
    unfold hcosh
    ring
  unfold hdist
  rw [hc]
  exact Real.arcosh_cosh (by have := Real.arsinh_nonneg_iff.mpr hs0; linarith)

/-- Lemma 13.13: the conformal factor.  As `Q → P` (`Q ≠ P`), `PQ_h / ‖P - Q‖` tends to
`2 / (1 - ‖P‖²)`. -/
@[kb "petrunin2025" "Lemma 13.13, p. 108"]
theorem tendsto_hdist_div_norm (hP : ‖P‖ < 1) :
    Tendsto (fun Q : ℂ => hdist P Q / ‖P - Q‖) (𝓝[≠] P) (𝓝 (2 / (1 - ‖P‖ ^ 2))) := by
  have hev : ∀ᶠ Q in 𝓝 P, ‖Q‖ < 1 := (continuous_norm.tendsto P).eventually (gt_mem_nhds hP)
  have hev' : ∀ᶠ Q in 𝓝[≠] P, ‖Q‖ < 1 := eventually_nhdsWithin_of_eventually_nhds hev
  have hne : ∀ᶠ Q in 𝓝[≠] P, Q ≠ P := eventually_nhdsWithin_of_forall (fun Q hQ => hQ)
  -- continuity of the scale
  have hc : Tendsto (fun Q : ℂ => hscale P Q) (𝓝 P) (𝓝 (1 / (1 - ‖P‖ ^ 2))) := by
    have h1 : Tendsto (fun Q : ℂ => Real.sqrt ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2))) (𝓝 P)
        (𝓝 (Real.sqrt ((1 - ‖P‖ ^ 2) * (1 - ‖P‖ ^ 2)))) := by
      have : Continuous fun Q : ℂ => Real.sqrt ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) := by fun_prop
      exact this.tendsto P
    have e : Real.sqrt ((1 - ‖P‖ ^ 2) * (1 - ‖P‖ ^ 2)) = 1 - ‖P‖ ^ 2 :=
      Real.sqrt_mul_self (one_sub_sq_pos hP).le
    rw [e] at h1
    have := h1.inv₀ (one_sub_sq_pos hP).ne'
    simpa [hscale, one_div] using this
  have hs : Tendsto (fun Q : ℂ => ‖P - Q‖ * hscale P Q) (𝓝[≠] P) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun Q : ℂ => ‖P - Q‖) (𝓝 P) (𝓝 0) := by
        have : Continuous fun Q : ℂ => ‖P - Q‖ := by fun_prop
        simpa using this.tendsto P
      have := h0.mul hc
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [hev', hne] with Q hQ hQP
      have : 0 < ‖P - Q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hQP.symm)
      have := mul_pos this (hscale_pos hP hQ)
      exact this.ne'
  have hd : Tendsto (fun y : ℝ => y⁻¹ * Real.arsinh y) (𝓝[≠] 0) (𝓝 1) := by
    have := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_arsinh 0))
    have h1 : (√(1 + (0:ℝ) ^ 2))⁻¹ = 1 := by simp
    rw [h1] at this
    refine this.congr (fun y => ?_)
    simp [slope_def_module, Real.arsinh_zero]
  have hlim : Tendsto (fun Q : ℂ => 2 * ((‖P - Q‖ * hscale P Q)⁻¹ * Real.arsinh (‖P - Q‖ * hscale P Q))
      * hscale P Q) (𝓝[≠] P) (𝓝 (2 * 1 * (1 / (1 - ‖P‖ ^ 2)))) :=
    (((hd.comp hs).const_mul 2).mul (hc.mono_left nhdsWithin_le_nhds))
  have : 2 * 1 * (1 / (1 - ‖P‖ ^ 2)) = 2 / (1 - ‖P‖ ^ 2) := by ring
  rw [this] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev', hne] with Q hQ hQP
  have h1 : 0 < ‖P - Q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hQP.symm)
  have h2 := hscale_pos hP hQ
  rw [hdist_eq_two_arsinh hP hQ]
  field_simp

/-! ### Additivity along a diameter (Lemma 12.9) -/

section Diameter

/-- The arclength coordinate `ln ((1+t)/(1-t))` along the diameter `(-1, 1)`. -/
noncomputable def hcoord (t : ℝ) : ℝ := Real.log ((1 + t) / (1 - t))

theorem hdist_ofReal_of_le {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x ≤ y) :
    hdist (x : ℂ) (y : ℂ) = hcoord y - hcoord x := by
  have hx1 : x < 1 := by linarith
  have hy1 : -1 < y := by linarith
  have hnx : ‖(x : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hx, hx1⟩
  have hny : ‖(y : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; exact ⟨hy1, hy⟩
  have hd : 0 < 1 - x * y := by nlinarith
  have e1 : mobius (x : ℂ) (y : ℂ) = (((y - x) / (1 - x * y) : ℝ) : ℂ) := by
    simp [mobius]
  have ht0 : 0 ≤ (y - x) / (1 - x * y) := div_nonneg (by linarith) hd.le
  have ht1 : (y - x) / (1 - x * y) < 1 := by
    rw [div_lt_one hd]; nlinarith
  rw [← hdist_mobius hnx hnx hny, mobius_self hnx, e1, hdist_zero_ofReal ht0 ht1]
  unfold hcoord
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - y := by linarith
  have h3 : 0 < 1 + x := by linarith
  have h4 : 0 < 1 + y := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  have hd' : 1 - x * y ≠ 0 := hd.ne'
  congr 1
  rw [show 1 + (y - x) / (1 - x * y) = (1 + y) * (1 - x) / (1 - x * y) by rw [add_div' _ _ _ hd']; congr 1; ring,
    show 1 - (y - x) / (1 - x * y) = (1 - y) * (1 + x) / (1 - x * y) by
      rw [sub_div' hd']; congr 1; ring,
    div_div_div_cancel_right₀ hd.ne']
  field_simp

/-- Lemma 12.9 for points of a diameter through the centre: if the real points `x ≤ y ≤ z` of the
open unit disc lie in this order, then `xy_h + yz_h = xz_h`.  (The book states it for an arbitrary
h-line; the case of a diameter is the one reduced to by Möbius motions.) -/
@[kb "petrunin2025" "Lemma 12.9, p. 95"]
theorem hdist_add_ofReal {x y z : ℝ} (hx : -1 < x) (hz : z < 1) (hxy : x ≤ y) (hyz : y ≤ z) :
    hdist (x : ℂ) (y : ℂ) + hdist (y : ℂ) (z : ℂ) = hdist (x : ℂ) (z : ℂ) := by
  rw [hdist_ofReal_of_le hx (by linarith) hxy, hdist_ofReal_of_le (by linarith) hz hyz,
    hdist_ofReal_of_le hx hz (hxy.trans hyz)]
  ring

end Diameter

/-! ### The inverse-point formula (Exercise 12.25) -/

section InversePoints

variable {P Q : ℂ}

/-- The inverse of `P` in the unit circle. -/
noncomputable def invPt (P : ℂ) : ℂ := (conj P)⁻¹

theorem norm_invPt_sub (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ‖invPt P - invPt Q‖ = ‖P - Q‖ / (‖P‖ * ‖Q‖) := by
  have h1 : conj P ≠ 0 := by simpa using hP
  have h2 : conj Q ≠ 0 := by simpa using hQ
  have : invPt P - invPt Q = conj (Q - P) / (conj P * conj Q) := by
    unfold invPt; rw [map_sub]; field_simp
  rw [this, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj,
    norm_sub_rev]

theorem norm_sub_invPt (hQ : Q ≠ 0) :
    ‖P - invPt Q‖ = ‖1 - P * conj Q‖ / ‖Q‖ := by
  have h2 : conj Q ≠ 0 := by simpa using hQ
  have : P - invPt Q = -(1 - P * conj Q) / conj Q := by
    unfold invPt; field_simp; ring
  rw [this, norm_div, norm_neg, Complex.norm_conj]

/-- Exercise 12.25: `ch PQ_h = (PQ·P'Q' + PQ'·P'Q)/(PP'·QQ')`, where `P'`, `Q'` are the inverses
of `P`, `Q` in the absolute (the unit circle); `P, Q ≠ 0`. -/
@[kb "petrunin2025" "Exercise 12.25, p. 102"]
theorem cosh_hdist_eq_inverse_points (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    Real.cosh (hdist P Q) =
      (‖P - Q‖ * ‖invPt P - invPt Q‖ + ‖P - invPt Q‖ * ‖invPt P - Q‖) /
        (‖P - invPt P‖ * ‖Q - invPt Q‖) := by
  have p0 : 0 < ‖P‖ := norm_pos_iff.mpr hP0
  have q0 : 0 < ‖Q‖ := norm_pos_iff.mpr hQ0
  have hP' := one_sub_sq_pos hP
  have hQ' := one_sub_sq_pos hQ
  have hPP : ‖P - invPt P‖ = (1 - ‖P‖ ^ 2) / ‖P‖ := by
    have := norm_sub_invPt (P := P) hP0
    rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : ‖(1 : ℂ) - ((‖P‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖P‖ ^ 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg hP'.le]
    rw [this]
  have hQQ : ‖Q - invPt Q‖ = (1 - ‖Q‖ ^ 2) / ‖Q‖ := by
    have := norm_sub_invPt (P := Q) hQ0
    rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : ‖(1 : ℂ) - ((‖Q‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖Q‖ ^ 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg hQ'.le]
    rw [this]
  have e2 : ‖invPt P - Q‖ = ‖1 - conj P * Q‖ / ‖P‖ := by
    have := norm_sub_invPt (P := Q) (Q := P) hP0
    rw [norm_sub_rev, this, mul_comm]
  have e3 : ‖1 - P * conj Q‖ = ‖1 - conj P * Q‖ := by
    have : 1 - P * conj Q = conj (1 - conj P * Q) := by simp [mul_comm]
    rw [this, Complex.norm_conj]
  have key := normSq_den_sub P Q
  rw [norm_sub_rev Q P] at key
  rw [cosh_hdist hP hQ, norm_invPt_sub hP0 hQ0, norm_sub_invPt hQ0, e2, e3, hPP, hQQ]
  unfold hcosh
  have hD := mul_pos hP' hQ'
  set d := ‖P - Q‖
  set e := ‖1 - conj P * Q‖
  have : e ^ 2 = d ^ 2 + (1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2) := by linarith
  field_simp
  nlinarith [this]

end InversePoints

/-! ### H-lines and their ideal points (chapter 12, p. 92) -/

section Lines

/-- The h-line with parameters `(α, c)`: the part inside the unit disc of the circline
`α (‖z‖² + 1) = 2 Re (c̄ z)`.  The circlines orthogonal to the unit circle are exactly these, with
`α² < ‖c‖²`: for `α = 0` a line through the centre (a diameter, perpendicular to `c`); for
`α ≠ 0` the circle with centre `c/α` and radius² `‖c/α‖² - 1` (`mem_hline_circle`). -/
def hline (α : ℝ) (c : ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ α * (‖z‖ ^ 2 + 1) = 2 * (conj c * z).re}

/-- The ideal points of `hline α c`: the points of the absolute (unit circle) on its circline. -/
def idealPts (α : ℝ) (c : ℂ) : Set ℂ := {z | ‖z‖ = 1 ∧ (conj c * z).re = α}

/-- The h-circle with centre `P` and h-radius `r` (book p. 96). -/
def hcircle (P : ℂ) (r : ℝ) : Set ℂ := {Q | ‖Q‖ < 1 ∧ hdist P Q = r}

theorem re_conj_mul (c z : ℂ) : (conj c * z).re = c.re * z.re + c.im * z.im := by
  simp [Complex.mul_re]

theorem sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Definition of h-circles at the centre (p. 96, Lemma 12.10 form): the h-circle about `0` of
h-radius `r` is the Euclidean circle of radius `tanh (r/2)`. -/
theorem mem_hcircle_zero {r : ℝ} {Q : ℂ} : Q ∈ hcircle 0 r ↔ ‖Q‖ < 1 ∧ ‖Q‖ = Real.tanh (r / 2) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hdist_zero_eq_iff h1).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (hdist_zero_eq_iff h1).mpr h2⟩

/-- Book p. 92 (h-lines through the centre): `hline 0 c` consists of the points of the disc on
the line through `0` perpendicular to `c`, i.e. the real multiples of `i c`. -/
theorem mem_hline_zero {c z : ℂ} (hc : c ≠ 0) :
    z ∈ hline 0 c ↔ ‖z‖ < 1 ∧ ∃ t : ℝ, z = (t : ℂ) * (Complex.I * c) := by
  have hc2 : c.re ^ 2 + c.im ^ 2 ≠ 0 := by
    rw [← sq_norm_eq]; simpa using hc
  simp only [hline, Set.mem_ofPred_eq, zero_mul, re_conj_mul]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h
    have h0 : c.re * z.re + c.im * z.im = 0 := by linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t * (c.re ^ 2 + c.im ^ 2) = c.re * z.im - c.im * z.re :=
      ⟨_, div_mul_cancel₀ _ hc2⟩
    refine ⟨t, Complex.ext ?_ ?_⟩
    · simp
      apply mul_right_cancel₀ hc2
      linear_combination c.re * h0 + c.im * ht
    · simp
      apply mul_right_cancel₀ hc2
      linear_combination c.im * h0 - c.re * ht
  · rintro ⟨t, rfl⟩
    simp
    ring

/-- Book p. 92 (h-lines that are arcs): for `α ≠ 0` the h-line `hline α c` is the part in the disc
of the circle with centre `c/α` and radius² `‖c/α‖² - 1`; the centre lies outside the closed disc. -/
theorem mem_hline_circle {α : ℝ} {c z : ℂ} (hα : α ≠ 0) :
    z ∈ hline α c ↔ ‖z‖ < 1 ∧ ‖z - c / (α : ℂ)‖ ^ 2 = ‖c / (α : ℂ)‖ ^ 2 - 1 := by
  simp only [hline, Set.mem_ofPred_eq]
  refine and_congr_right (fun _ => ?_)
  have e1 : (c / (α : ℂ)).re = c.re / α := by simp [Complex.div_ofReal_re]
  have e2 : (c / (α : ℂ)).im = c.im / α := by simp [Complex.div_ofReal_im]
  simp only [sq_norm_eq, Complex.sub_re, Complex.sub_im, e1, e2, re_conj_mul]
  constructor
  · intro h
    field_simp
    linear_combination α * h
  · intro h
    field_simp at h
    apply mul_left_cancel₀ hα
    linear_combination h

/-- Book p. 92: the circle of an h-line which is not a diameter has its centre outside the closed
disc, `1 < ‖c/α‖`, when `α² < ‖c‖²`... more precisely `‖c/α‖ > 1` iff `α² < ‖c‖²`. -/
theorem one_lt_norm_div {α : ℝ} {c : ℂ} (hα : α ≠ 0) : 1 < ‖c / (α : ℂ)‖ ↔ α ^ 2 < ‖c‖ ^ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, lt_div_iff₀ (abs_pos.mpr hα), one_mul]
  rw [← sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs]

/-- Book p. 92: the two ideal points of `hline α c` (when `α² < ‖c‖²`), explicitly. -/
theorem idealPts_eq {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) :
    idealPts α c = {(α + Real.sqrt (‖c‖ ^ 2 - α ^ 2) * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ),
      (α - Real.sqrt (‖c‖ ^ 2 - α ^ 2) * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ)} := by
  have hN : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
  have hc : c ≠ 0 := by
    rintro rfl; simp at hN
  have hk : Real.sqrt (‖c‖ ^ 2 - α ^ 2) ^ 2 = ‖c‖ ^ 2 - α ^ 2 := Real.sq_sqrt (by linarith)
  set k := Real.sqrt (‖c‖ ^ 2 - α ^ 2) with hkdef
  have hNc : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcc : conj c ≠ 0 := by simpa using hc
  have hmc : conj c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ext z
  simp only [idealPts, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hre⟩
    -- w = c̄ z has real part α and norm ‖c‖
    set w := conj c * z with hw
    have hwn : ‖w‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [hw, norm_mul, Complex.norm_conj, hz]; ring
    have him : w.im ^ 2 = k ^ 2 := by
      rw [hk]; rw [sq_norm_eq, hre] at hwn; linarith
    have hz' : z = w * c / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [hw, mul_comm (conj c) z, mul_assoc, hmc]; field_simp
    have hwe : w = α + k * Complex.I ∨ w = α - k * Complex.I := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h1 | h1
      · left; apply Complex.ext <;> simp [hre, h1]
      · right; apply Complex.ext <;> simp [hre, h1]
    rcases hwe with e | e
    · left; rw [hz', e]
    · right; rw [hz', e]
  · have key : ∀ s : ℝ, s ^ 2 = k ^ 2 → ‖((α : ℂ) + s * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ)‖ = 1 ∧
        (conj c * (((α : ℂ) + s * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ))).re = α := by
      intro s hs
      have e : conj c * (((α : ℂ) + s * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ)) =
          (α : ℂ) + s * Complex.I := by
        calc conj c * (((α : ℂ) + s * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ))
            = ((α : ℂ) + s * Complex.I) * (conj c * c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by ring
          _ = _ := by rw [hmc, mul_div_cancel_right₀ _ hNc]
      have hX : ‖(α : ℂ) + s * Complex.I‖ = ‖c‖ := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_eq]
        simp
        nlinarith [hs, hk]
      refine ⟨?_, by rw [e]; simp⟩
      rw [norm_div, norm_mul, hX, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have : 0 < ‖c‖ := norm_pos_iff.mpr hc
      field_simp
    rintro (rfl | rfl)
    · exact key k rfl
    · have := key (-k) (by ring)
      simpa [sub_eq_add_neg] using this

theorem hline_eq_of_proportional {α α' μ : ℝ} {c c' : ℂ} (hμ : μ ≠ 0) (h1 : c'.re = μ * c.re)
    (h2 : c'.im = μ * c.im) (hα : α' = μ * α) : hline α' c' = hline α c := by
  ext z
  simp only [hline, Set.mem_ofPred_eq, re_conj_mul, h1, h2, hα]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h
    apply mul_left_cancel₀ hμ
    linear_combination h
  · intro h
    linear_combination μ * h

/-- Exercise 12.1: an h-line is determined by its two ideal points.  If two distinct points
`A ≠ B` of the absolute are ideal points of both `hline α c` and `hline α' c'` (with
`α² < ‖c‖²`, `α'² < ‖c'‖²`), then the two h-lines coincide. -/
@[kb "petrunin2025" "Exercise 12.1, p. 92"]
theorem hline_eq_of_idealPts {α α' : ℝ} {c c' A B : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (h' : α' ^ 2 < ‖c'‖ ^ 2) (hAB : A ≠ B) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hA' : A ∈ idealPts α' c') (hB' : B ∈ idealPts α' c') : hline α c = hline α' c' := by
  simp only [idealPts, Set.mem_ofPred_eq, re_conj_mul] at hA hB hA' hB'
  have hN : 0 < c.re ^ 2 + c.im ^ 2 := by rw [← sq_norm_eq]; nlinarith [sq_nonneg α]
  have hN' : 0 < c'.re ^ 2 + c'.im ^ 2 := by rw [← sq_norm_eq]; nlinarith [sq_nonneg α']
  have e1 : c.re * (A.re - B.re) + c.im * (A.im - B.im) = 0 := by linarith [hA.2, hB.2]
  have e2 : c'.re * (A.re - B.re) + c'.im * (A.im - B.im) = 0 := by linarith [hA'.2, hB'.2]
  have hx : c.re * c'.im - c.im * c'.re = 0 := by
    have hv : A.re - B.re ≠ 0 ∨ A.im - B.im ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hAB (Complex.ext (by linarith [hcon.1]) (by linarith [hcon.2]))
    rcases hv with hv | hv
    · have : (A.re - B.re) * (c.re * c'.im - c.im * c'.re) = 0 := by
        linear_combination c'.im * e1 - c.im * e2
      exact (mul_eq_zero.mp this).resolve_left hv
    · have : (A.im - B.im) * (c.re * c'.im - c.im * c'.re) = 0 := by
        linear_combination c.re * e2 - c'.re * e1
      exact (mul_eq_zero.mp this).resolve_left hv
  set μ := (c.re * c'.re + c.im * c'.im) / (c.re ^ 2 + c.im ^ 2) with hμ
  have hc1 : c'.re = μ * c.re := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-c.im) * hx
  have hc2 : c'.im = μ * c.im := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination c.re * hx
  have hα : α' = μ * α := by
    have : α' = c'.re * A.re + c'.im * A.im := hA'.2.symm
    rw [this, hc1, hc2, ← hA.2]; ring
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc1 hc2
    rw [hc1, hc2] at hN'
    simp at hN'
  exact (hline_eq_of_proportional hμ0 hc1 hc2 hα).symm

/-- Claim 12.20 (h-V, concrete form).  Let `ℓ` be the diameter `hline 0 i` (the real axis) and `P`
a point of the disc off it.  Then through `P` pass two h-lines, `hline 1 (1 + s i)` and
`hline 1 (-1 + s' i)`, disjoint from `ℓ`; they are different since their ideal-point sets are
(the first has the ideal point `1`, the second does not).  The general case follows by moving
`ℓ` to the diameter with a Möbius motion (not formalized). -/
@[kb "petrunin2025" "Claim 12.20, p. 101"]
theorem hV_exists_two_parallels {P : ℂ} (hP : ‖P‖ < 1) (hPL : P.im ≠ 0) :
    ∃ (c₁ c₂ : ℂ), 1 ^ 2 < ‖c₁‖ ^ 2 ∧ 1 ^ 2 < ‖c₂‖ ^ 2 ∧ P ∈ hline 1 c₁ ∧ P ∈ hline 1 c₂ ∧
      Disjoint (hline 1 c₁) (hline 0 Complex.I) ∧ Disjoint (hline 1 c₂) (hline 0 Complex.I) ∧
      idealPts 1 c₁ ≠ idealPts 1 c₂ := by
  set s : ℝ := ((P.re - 1) ^ 2 + P.im ^ 2) / (2 * P.im) with hs
  set s' : ℝ := ((P.re + 1) ^ 2 + P.im ^ 2) / (2 * P.im) with hs'
  have hP2 : P.re ^ 2 + P.im ^ 2 < 1 := by rw [← sq_norm_eq]; nlinarith [norm_nonneg P]
  have hpos : 0 < P.im ^ 2 := by positivity
  have hsne : s ≠ 0 := by
    rw [hs]; apply div_ne_zero (by positivity) (by simpa using hPL)
  have hs'ne : s' ≠ 0 := by
    rw [hs']; apply div_ne_zero (by positivity) (by simpa using hPL)
  refine ⟨⟨1, s⟩, ⟨-1, s'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq_norm_eq]; simp only; have := sq_pos_of_ne_zero hsne; nlinarith
  · rw [sq_norm_eq]; simp only; have := sq_pos_of_ne_zero hs'ne; nlinarith
  · refine ⟨hP, ?_⟩
    rw [re_conj_mul, sq_norm_eq]
    simp only
    have : s * P.im = ((P.re - 1) ^ 2 + P.im ^ 2) / 2 := by
      rw [hs]; field_simp
    linear_combination (-2 : ℝ) * this
  · refine ⟨hP, ?_⟩
    rw [re_conj_mul, sq_norm_eq]
    simp only
    have : s' * P.im = ((P.re + 1) ^ 2 + P.im ^ 2) / 2 := by
      rw [hs']; field_simp
    linear_combination (-2 : ℝ) * this
  · rw [Set.disjoint_left]
    rintro z ⟨hz, hz2⟩ ⟨_, hz3⟩
    rw [re_conj_mul] at hz2 hz3
    simp at hz3
    rw [sq_norm_eq] at hz2
    simp only [hz3] at hz2
    have : (z.re - 1) ^ 2 = 0 := by nlinarith
    have h1 : z.re = 1 := by nlinarith [pow_eq_zero_iff (two_ne_zero) |>.mp this]
    have := sq_norm_eq z
    rw [hz3, h1] at this
    nlinarith [norm_nonneg z]
  · rw [Set.disjoint_left]
    rintro z ⟨hz, hz2⟩ ⟨_, hz3⟩
    rw [re_conj_mul] at hz2 hz3
    simp at hz3
    rw [sq_norm_eq] at hz2
    simp only [hz3] at hz2
    have : (z.re + 1) ^ 2 = 0 := by nlinarith
    have h1 : z.re = -1 := by nlinarith [pow_eq_zero_iff (two_ne_zero) |>.mp this]
    have := sq_norm_eq z
    rw [hz3, h1] at this
    nlinarith [norm_nonneg z]
  · intro h
    have h1 : (1 : ℂ) ∈ idealPts 1 ⟨1, s⟩ := by
      refine ⟨by simp, ?_⟩
      rw [re_conj_mul]; simp
    rw [h] at h1
    have := h1.2
    rw [re_conj_mul] at this
    simp at this
    norm_num at this

end Lines

/-- Proposition 13.14 (circumference of the centred h-circle).  The h-circle about the centre of
h-radius `r` is the Euclidean circle of radius `tanh (r/2)` (`hdist_zero_eq_iff`), whose
Euclidean circumference `2π tanh (r/2)` multiplied by the conformal factor `2/(1 - tanh²(r/2))`
at that radius is `2π sinh r`. -/
@[kb "petrunin2025" "Proposition 13.14, p. 109"]
theorem circumference_identity (r : ℝ) :
    2 * π * Real.tanh (r / 2) * (2 / (1 - Real.tanh (r / 2) ^ 2)) = 2 * π * Real.sinh r := by
  have hc := Real.cosh_pos (r / 2)
  have hsq := Real.cosh_sq (r / 2)
  have h1 : 1 - Real.tanh (r / 2) ^ 2 = 1 / Real.cosh (r / 2) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    linarith
  have h2 : Real.sinh r = 2 * Real.sinh (r / 2) * Real.cosh (r / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  rw [h1, h2, Real.tanh_eq_sinh_div_cosh]
  field_simp

end Conformal

end UndergradKB.Geometry
