import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 10 (extra rows restated from the Trigonometry topic)

Further chapter 10 results in the book's terms: angles and their measure, coterminal angles, arc
length, reference angles, exact values, domains and ranges of the circular functions, periodicity,
sinusoids, `arcsec`/`arccsc`, and the solutions of basic trigonometric equations. Everything is proved
from Mathlib (the Trigonometry topic cannot be imported). Arc length is the total variation
`eVariationOn` of the arc parametrisation `φ ↦ c + r e^{iφ}`.
-/

namespace UndergradKB.Precalculus.Course

open Real Set
open Complex (I)

/-! ### Helpers -/

private theorem dist_arc_aux (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    dist (c + r * Complex.exp (a * I)) (c + r * Complex.exp (b * I)) =
      r * (2 * |Real.sin ((a - b) / 2)|) := by
  have h : Complex.exp (a * I) = Complex.exp (b * I) * Complex.exp (I * ↑(a - b)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [Complex.dist_eq, h,
    show c + ↑r * (Complex.exp (↑b * I) * Complex.exp (I * ↑(a - b))) - (c + ↑r * Complex.exp (↑b * I))
      = ↑r * Complex.exp (↑b * I) * (Complex.exp (I * ↑(a - b)) - 1) by ring,
    norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_I_mul_ofReal_sub_one,
    Complex.norm_real, Real.norm_of_nonneg hr, Real.norm_eq_abs, abs_mul, abs_two]
  ring

/-- The arc `φ ↦ c + r e^{iφ}`, `α ≤ φ ≤ β`, has length `r (β - α)` (total variation). -/
private theorem arc_aux (c : ℂ) {r α β : ℝ} (hr : 0 ≤ r) (hαβ : α ≤ β) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc α β) =
      ENNReal.ofReal (r * (β - α)) := by
  set γ : ℝ → ℂ := fun φ => c + r * Complex.exp (φ * I) with hγ
  apply le_antisymm
  · have hL : LipschitzWith r.toNNReal γ := LipschitzWith.of_dist_le_mul fun a b => by
      rw [hγ, dist_arc_aux c hr, Real.dist_eq, Real.coe_toNNReal r hr]
      apply mul_le_mul_of_nonneg_left _ hr
      have := Real.abs_sin_le_abs (x := (a - b) / 2)
      rw [abs_div, abs_two] at this
      linarith
    have := (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (g := id) (s := Icc α β)
      (mapsTo_univ _ _)
    rw [Function.comp_id, eVariationOn_id_Icc] at this
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hr]
    rfl
  · set L := β - α with hL
    have hL0 : 0 ≤ L := by rw [hL]; linarith
    have poly : ∀ N : ℕ, 0 < N →
        ENNReal.ofReal (r * (2 * N * |Real.sin (L / (2 * N))|)) ≤ eVariationOn γ (Icc α β) := by
      intro N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      set u : ℕ → ℝ := fun i => α + L * (min i N : ℕ) / N with hu
      have hmono : Monotone u := by
        intro i j hij
        simp only [hu]
        have : ((min i N : ℕ) : ℝ) ≤ (min j N : ℕ) := by exact_mod_cast min_le_min_right N hij
        have := mul_le_mul_of_nonneg_left this hL0
        have := div_le_div_of_nonneg_right this hNr.le
        linarith
      have hmem : ∀ i, u i ∈ Icc α β := by
        intro i
        simp only [hu, mem_Icc]
        have h1 : ((min i N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right i N
        have h0 : (0 : ℝ) ≤ (min i N : ℕ) := Nat.cast_nonneg _
        constructor
        · have : 0 ≤ L * (min i N : ℕ) / N := by positivity
          linarith
        · have : L * (min i N : ℕ) / N ≤ L := by
            rw [div_le_iff₀ hNr]; exact mul_le_mul_of_nonneg_left h1 hL0
          linarith
      have hsum := eVariationOn.sum_le (f := γ) (n := N) hmono hmem
      refine le_trans (le_of_eq ?_) hsum
      have hterm : ∀ i ∈ Finset.range N, edist (γ (u (i + 1))) (γ (u i)) =
          ENNReal.ofReal (r * (2 * |Real.sin (L / (2 * N))|)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [edist_dist, hγ, dist_arc_aux c hr]
        have hi1 : min (i + 1) N = i + 1 := min_eq_left hi
        have hi2 : min i N = i := min_eq_left hi.le
        simp only [hu, hi1, hi2]
        congr 5
        push_cast
        field_simp
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1; ring
    rcases hL0.eq_or_lt with hL' | hL'
    · rw [← hL', mul_zero, ENNReal.ofReal_zero]; exact zero_le
    have bound : ∀ N : ℕ, ENNReal.ofReal (r * (L - L ^ 3 / 24 * (1 / ((N : ℝ) + 1)) ^ 2)) ≤
        eVariationOn γ (Icc α β) := by
      intro N
      have hp := poly (N + 1) N.succ_pos
      push_cast at hp
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hp
      apply mul_le_mul_of_nonneg_left _ hr
      have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hx : 0 < L / (2 * ((N : ℝ) + 1)) := by positivity
      have hs := Real.sin_gt_sub_cube hx
      have habs := le_abs_self (Real.sin (L / (2 * ((N : ℝ) + 1))))
      have key : L - L ^ 3 / 24 * (1 / ((N : ℝ) + 1)) ^ 2 =
          2 * ((N : ℝ) + 1) * (L / (2 * ((N : ℝ) + 1)) - (L / (2 * ((N : ℝ) + 1))) ^ 3 / 6) := by
        field_simp; ring
      rw [key]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have hT : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (r * (L - L ^ 3 / 24 * (1 / ((N : ℝ) + 1)) ^ 2)))
        Filter.atTop (nhds (ENNReal.ofReal (r * L))) := by
      apply ENNReal.tendsto_ofReal
      have := (((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul (L ^ 3 / 24)).const_sub
        L).const_mul r
      simpa using this
    exact le_of_tendsto' hT bound

private theorem cos_eq_one_aux {x : ℝ} (h : Real.cos x = 1) : ∃ k : ℤ, x = k * (2 * π) :=
  ((Real.cos_eq_one_iff x).1 h).imp fun _ hk => hk.symm

/-- If `cos x = 1` and `x > 0` then `x ≥ 2π`. -/
private theorem two_pi_le_of_cos_one {x : ℝ} (hx : 0 < x) (h : Real.cos x = 1) : 2 * π ≤ x := by
  obtain ⟨k, hk⟩ := cos_eq_one_aux h
  have hp := pi_pos
  have hk0 : (0 : ℤ) < k := by
    by_contra hneg
    have : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hneg
    nlinarith
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast (hk0 : (1 : ℤ) ≤ k)
  nlinarith

/-- If `sin x = 0` and `x > 0` then `x ≥ π`. -/
private theorem pi_le_of_sin_zero {x : ℝ} (hx : 0 < x) (h : Real.sin x = 0) : π ≤ x := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h
  have hp := pi_pos
  have hk0 : (0 : ℤ) < k := by
    by_contra hneg
    have : (k : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hneg
    nlinarith
  have h1 : (1 : ℝ) ≤ k := by exact_mod_cast (hk0 : (1 : ℤ) ≤ k)
  nlinarith

private theorem coterminal_aux (α β : ℝ) :
    (Real.cos α = Real.cos β ∧ Real.sin α = Real.sin β) ↔ ∃ k : ℤ, β = α + k * (2 * π) := by
  constructor
  · rintro ⟨hc, hs⟩
    have h1 := Real.sin_sq_add_cos_sq α
    have : Real.cos (β - α) = 1 := by
      rw [Real.cos_sub, ← hc, ← hs]; nlinarith
    obtain ⟨k, hk⟩ := cos_eq_one_aux this
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(Real.cos_add_int_mul_two_pi α k).symm, (Real.sin_add_int_mul_two_pi α k).symm⟩

/-- Two angles with `tan` equal (and nonvanishing cosines) differ by a multiple of `π`. -/
private theorem tan_eq_tan_aux {u v : ℝ} (hu : Real.cos u ≠ 0) (hv : Real.cos v ≠ 0)
    (h : Real.tan u = Real.tan v) : ∃ k : ℤ, u = v + k * π := by
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_eq_div_iff hu hv] at h
  have : Real.sin (u - v) = 0 := by rw [Real.sin_sub]; linarith
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 this
  exact ⟨k, by linarith⟩

private theorem sin_zero_of_quarter {c : ℝ}
    (h : Real.sin (π / 4 + c) = Real.cos (π / 4 + c)) : Real.sin c = 0 := by
  rw [Real.sin_add, Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  have hs : 0 < √2 / 2 := by positivity
  have : (√2 / 2) * (2 * Real.sin c) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-! ### Section 10.1 -/

/-- Scaling the two arms of an angle by positive factors (moving along the rays) does not change the
angle; the measure of an angle between two rays is in `[0, π]` (PC-186). -/
@[kb "stitzzeager2013" "§10.1, p. 705"]
theorem box_10_1_angle_of_rays (u v : EuclideanSpace ℝ (Fin 2)) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    InnerProductGeometry.angle (s • u) (t • v) = InnerProductGeometry.angle u v ∧
      0 ≤ InnerProductGeometry.angle u v ∧ InnerProductGeometry.angle u v ≤ π := by
  refine ⟨?_, InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

/-- An angle of `θ` degrees is acute (`θ < 90`), right (`θ = 90`) or obtuse (`90 < θ`), and exactly one
of these holds (PC-187). -/
@[kb "stitzzeager2013" "§10.1, p. 706"]
theorem box_10_1_angle_kinds (θ : ℝ) :
    (θ < 90 ∨ θ = 90 ∨ 90 < θ) ∧ ¬(θ < 90 ∧ θ = 90) ∧ ¬(θ = 90 ∧ 90 < θ) ∧ ¬(θ < 90 ∧ 90 < θ) := by
  refine ⟨lt_trichotomy θ 90, ?_, ?_, ?_⟩ <;> rintro ⟨a, b⟩ <;> linarith

/-- Complementary angles (degrees summing to `90`) have `sin α = cos β`, supplementary ones (summing
to `180`) have `sin α = sin β` and `cos α = -cos β` (PC-187). -/
@[kb "stitzzeager2013" "§10.1, p. 708"]
theorem box_10_1_complementary_supplementary (α β : ℝ) :
    (α + β = 90 → Real.sin (α * π / 180) = Real.cos (β * π / 180) ∧
      Real.cos (α * π / 180) = Real.sin (β * π / 180)) ∧
    (α + β = 180 → Real.sin (α * π / 180) = Real.sin (β * π / 180) ∧
      Real.cos (α * π / 180) = -Real.cos (β * π / 180)) := by
  constructor
  · intro h
    have e : α * π / 180 = π / 2 - β * π / 180 := by
      have : α = 90 - β := by linarith
      subst this; ring
    rw [e]
    exact ⟨Real.sin_pi_div_two_sub _, Real.cos_pi_div_two_sub _⟩
  · intro h
    have e : α * π / 180 = π - β * π / 180 := by
      have : α = 180 - β := by linarith
      subst this; ring
    rw [e]
    exact ⟨Real.sin_pi_sub _, Real.cos_pi_sub _⟩

/-- Degrees, minutes, seconds: `d` degrees, `m` minutes, `s` seconds make `d + m/60 + s/3600`
degrees. -/
noncomputable def dmsToDeg (d m s : ℝ) : ℝ := d + m / 60 + s / 3600

/-- `60` minutes make one degree, `60` seconds make one minute, and the result in radians is
`dmsToDeg · π/180` (PC-188). -/
@[kb "stitzzeager2013" "§10.1, p. 707"]
theorem box_10_1_degree_minute_second (d m s : ℝ) :
    dmsToDeg 0 60 0 = 1 ∧ dmsToDeg 0 0 60 = dmsToDeg 0 1 0 ∧ dmsToDeg 0 0 3600 = 1 ∧
      dmsToDeg d m s * π / 180 = (d + m / 60 + s / 3600) * π / 180 := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> simp only [dmsToDeg] <;> norm_num

/-- Standard position: the initial side points to `(1, 0)` (angle `0`), a quarter turn
counterclockwise (positive angle `π/2`) ends at `(0, 1)`, a quarter turn clockwise (negative angle
`-π/2`) ends at `(0, -1)`, and reversing the sense of rotation reflects the terminal point in the
horizontal axis (PC-189). -/
@[kb "stitzzeager2013" "§10.1, p. 710"]
theorem box_10_1_standard_position (θ : ℝ) :
    (Real.cos 0, Real.sin 0) = (1, 0) ∧ (Real.cos (π / 2), Real.sin (π / 2)) = (0, 1) ∧
      (Real.cos (-(π / 2)), Real.sin (-(π / 2))) = (0, -1) ∧
      (Real.cos (-θ), Real.sin (-θ)) = (Real.cos θ, -Real.sin θ) := by
  simp

/-- An angle in standard position is quadrantal (terminal side on an axis) exactly when
`sin θ cos θ = 0`, i.e. when `θ` is an integer multiple of `π/2` (PC-190). -/
@[kb "stitzzeager2013" "§10.1, p. 710"]
theorem box_10_1_quadrantal (θ : ℝ) :
    Real.sin θ * Real.cos θ = 0 ↔ ∃ k : ℤ, θ = k * (π / 2) := by
  have h : Real.sin θ * Real.cos θ = 0 ↔ Real.sin (2 * θ) = 0 := by
    rw [Real.sin_two_mul]; constructor <;> intro h <;> linarith
  rw [h, Real.sin_eq_zero_iff]
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linarith⟩

/-- An angle in standard position is a quadrant angle (terminal side inside a quadrant) exactly when
`(cos θ, sin θ)` has both coordinates nonzero, and then it lies in one of the four open quadrants
(PC-190). -/
@[kb "stitzzeager2013" "§10.1, p. 710"]
theorem box_10_1_quadrant_angle (θ : ℝ) :
    Real.sin θ * Real.cos θ ≠ 0 ↔
      ((0 < Real.cos θ ∧ 0 < Real.sin θ) ∨ (Real.cos θ < 0 ∧ 0 < Real.sin θ) ∨
        (Real.cos θ < 0 ∧ Real.sin θ < 0) ∨ (0 < Real.cos θ ∧ Real.sin θ < 0)) := by
  rw [Ne, mul_eq_zero]
  constructor
  · intro h
    push_neg at h
    obtain ⟨hs, hc⟩ := h
    rcases hs.lt_or_gt with a | a <;> rcases hc.lt_or_gt with b | b <;> tauto
  · rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩) <;> rintro (h | h) <;> linarith

/-- Angles `α`, `β` (radians) in standard position are coterminal, i.e. have the same terminal point
`(cos, sin)`, exactly when `β = α + 2πk` for an integer `k` (PC-191). -/
@[kb "stitzzeager2013" "§10.1, p. 714"]
theorem box_10_1_coterminal (α β : ℝ) :
    (Real.cos α, Real.sin α) = (Real.cos β, Real.sin β) ↔ ∃ k : ℤ, β = α + k * (2 * π) := by
  rw [← coterminal_aux, Prod.mk.injEq]

/-- The same in degrees: `α°` and `β°` are coterminal iff `β = α + 360 k` for an integer `k`
(PC-191). -/
@[kb "stitzzeager2013" "§10.1, p. 710"]
theorem box_10_1_coterminal_degrees (α β : ℝ) :
    (Real.cos (α * π / 180), Real.sin (α * π / 180)) =
        (Real.cos (β * π / 180), Real.sin (β * π / 180)) ↔ ∃ k : ℤ, β = α + k * 360 := by
  rw [box_10_1_coterminal]
  have hp := pi_pos
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h0 : (β - α - k * 360) * π = 0 := by linarith
    have := (mul_eq_zero.1 h0).resolve_right pi_ne_zero
    linarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-- The length of the arc of the circle with centre `c` and radius `r` traced by the angle parameter
`φ ∈ [a, b]` (the total variation of `φ ↦ c + r e^{iφ}`). -/
noncomputable def circleArcLength (c : ℂ) (r a b : ℝ) : ℝ :=
  (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc a b)).toReal

private theorem circleArcLength_eq (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    circleArcLength c r 0 θ = r * θ := by
  unfold circleArcLength
  rw [arc_aux c hr hθ, sub_zero, ENNReal.toReal_ofReal (mul_nonneg hr hθ)]

/-- A circle of radius `r > 0` has circumference (the length of the full arc, `φ ∈ [0, 2π]`) equal
to `2πr`; so circumference over diameter is `π` and circumference over radius is `2π` (PC-192). -/
@[kb "stitzzeager2013" "Definition 10.1, p. 712"]
theorem def_10_1_pi_circumference (c : ℂ) {r : ℝ} (hr : 0 < r) :
    circleArcLength c r 0 (2 * π) = 2 * π * r ∧ circleArcLength c r 0 (2 * π) / (2 * r) = π ∧
      circleArcLength c r 0 (2 * π) / r = 2 * π := by
  have h := circleArcLength_eq c hr.le (by positivity : (0 : ℝ) ≤ 2 * π)
  refine ⟨by rw [h]; ring, ?_, ?_⟩ <;> rw [h] <;> field_simp

/-- Radian measure: a central angle of `θ ≥ 0` radians cuts off an arc of length `s = rθ` on the
circle of radius `r > 0`, so `θ = s / r`, and one revolution is `2π` radians (PC-193). -/
@[kb "stitzzeager2013" "§10.1, p. 713"]
theorem box_10_1_radian_arc_length (c : ℂ) {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) :
    circleArcLength c r 0 θ = r * θ ∧ circleArcLength c r 0 θ / r = θ ∧
      circleArcLength c r 0 (2 * π) / r = 2 * π := by
  have h := circleArcLength_eq c hr.le hθ
  refine ⟨h, by rw [h]; field_simp, ?_⟩
  rw [circleArcLength_eq c hr.le (by positivity : (0 : ℝ) ≤ 2 * π)]
  field_simp

/-- Degrees to radians is multiplication by `π/180`, radians to degrees is multiplication by `180/π`,
and the two conversions are inverse to each other (PC-194). -/
@[kb "stitzzeager2013" "Equation 10.1, p. 716"]
theorem eq_10_1_degrees_radians (θ t : ℝ) :
    θ * π / 180 = θ * (π / 180) ∧ (θ * π / 180) * (180 / π) = θ ∧
      (t * (180 / π)) * π / 180 = t ∧ (180 : ℝ) * π / 180 = π := by
  have hp := pi_ne_zero
  refine ⟨by ring, ?_, ?_, by ring⟩ <;> field_simp

/-- Wrapping the real line around the unit circle: for `t ≥ 0` the point `(cos t, sin t)` is reached
from `(1, 0)` after travelling the counterclockwise arc of length `t`, and for `t ≤ 0` after the
clockwise arc of length `-t` (PC-195). -/
@[kb "stitzzeager2013" "§10.1, p. 716"]
theorem box_10_1_wrapping_function (t : ℝ) :
    (0 ≤ t → circleArcLength 0 1 0 t = t) ∧ (t ≤ 0 → circleArcLength 0 1 t 0 = -t) ∧
      Complex.exp (t * I) = ⟨Real.cos t, Real.sin t⟩ := by
  refine ⟨fun h => ?_, fun h => ?_,
    Complex.ext (Complex.exp_ofReal_mul_I_re t) (Complex.exp_ofReal_mul_I_im t)⟩
  · have := circleArcLength_eq 0 zero_le_one h
    simpa using this
  · unfold circleArcLength
    rw [arc_aux 0 zero_le_one h]
    simp [ENNReal.toReal_ofReal (neg_nonneg.2 h)]

/-- Circular motion at constant angular velocity `ω ≥ 0` on a circle of radius `r ≥ 0`: in time
`t > 0` the angle swept is `ωt` and the arc travelled is `ω r t`, so the average angular velocity is
`ω` and the average linear velocity is `v = rω` (PC-196). -/
@[kb "stitzzeager2013" "Equation 10.2, p. 719"]
theorem eq_10_2_linear_velocity (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 < t) :
    (eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * I)) (Icc 0 t)).toReal / t = r * ω ∧
      (ω * t) / t = ω := by
  have hmono : MonotoneOn (fun τ : ℝ => ω * τ) (Icc 0 t) := fun x _ y _ hxy =>
    mul_le_mul_of_nonneg_left hxy hω
  have := eVariationOn.comp_eq_of_monotoneOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) _ hmono
  rw [Function.comp_def] at this
  rw [this, image_mul_left_Icc hω ht.le, mul_zero, arc_aux c hr (by positivity),
    sub_zero, ENNReal.toReal_ofReal (by positivity)]
  constructor <;> field_simp

/-! ### Section 10.2 and 10.3: reference angles and exact values -/

/-- The reference angle of `φ ∈ [0, 2π)`: the acute angle between its terminal side and the
horizontal axis. -/
noncomputable def refAngleIco (φ : ℝ) : ℝ :=
  if φ ≤ π / 2 then φ else if φ ≤ π then π - φ else if φ ≤ 3 * π / 2 then φ - π else 2 * π - φ

/-- The reference angle of any angle: that of the coterminal angle in `[0, 2π)`. -/
noncomputable def refAngle (θ : ℝ) : ℝ := refAngleIco (toIcoMod two_pi_pos 0 θ)

private theorem abs_sin_cos_refAngleIco {θ : ℝ} (h : θ ∈ Ico 0 (2 * π)) :
    refAngleIco θ ∈ Icc 0 (π / 2) ∧
      |Real.sin θ| = Real.sin (refAngleIco θ) ∧ |Real.cos θ| = Real.cos (refAngleIco θ) := by
  obtain ⟨h₀, h₁⟩ := h
  have hp := pi_pos
  unfold refAngleIco
  split_ifs with a b c
  · refine ⟨⟨h₀, a⟩, ?_⟩
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h₀ (by linarith)),
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, a⟩)]
    exact ⟨rfl, rfl⟩
  · have hc := Real.cos_nonneg_of_mem_Icc (x := π - θ) ⟨by linarith, by linarith⟩
    rw [Real.cos_pi_sub] at hc
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h₀ b), abs_of_nonpos (by linarith),
      Real.sin_pi_sub, Real.cos_pi_sub]
    exact ⟨rfl, by ring⟩
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ - π) (by linarith) (by linarith)
    have hc := Real.cos_nonneg_of_mem_Icc (x := θ - π) ⟨by linarith, by linarith⟩
    rw [Real.sin_sub_pi] at hs
    rw [Real.cos_sub_pi] at hc
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [Real.sin_sub_pi, Real.cos_sub_pi, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    exact ⟨rfl, rfl⟩
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * π - θ) (by linarith) (by linarith)
    have hc := Real.cos_nonneg_of_mem_Icc (x := 2 * π - θ) ⟨by linarith, by linarith⟩
    rw [Real.sin_two_pi_sub] at hs
    rw [Real.cos_two_pi_sub] at hc
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rw [Real.sin_two_pi_sub, Real.cos_two_pi_sub, abs_of_nonpos (by linarith), abs_of_nonneg hc]
    exact ⟨rfl, rfl⟩

/-- Reference angles: the reference angle of `θ` is an acute angle in `[0, π/2]`, and `sin` and `cos`
of `θ` equal those of the reference angle up to a sign, i.e. `|sin θ| = sin (ref θ)` and
`|cos θ| = cos (ref θ)` (PC-200). -/
@[kb "stitzzeager2013" "Theorem 10.2, p. 734"]
theorem thm_10_2_reference_angle (θ : ℝ) :
    refAngle θ ∈ Icc 0 (π / 2) ∧
      |Real.sin θ| = Real.sin (refAngle θ) ∧ |Real.cos θ| = Real.cos (refAngle θ) := by
  have hmem := toIcoMod_mem_Ico' two_pi_pos θ
  have hθ : θ = toIcoMod two_pi_pos 0 θ + (toIcoDiv two_pi_pos 0 θ : ℝ) * (2 * π) :=
    (toIcoMod_add_toIcoDiv_mul two_pi_pos 0 θ).symm
  have hmem' : toIcoMod two_pi_pos 0 θ ∈ Ico 0 (2 * π) := hmem
  obtain ⟨h1, h2, h3⟩ := abs_sin_cos_refAngleIco hmem'
  have hs : Real.sin θ = Real.sin (toIcoMod two_pi_pos 0 θ) := by
    conv_lhs => rw [hθ]
    exact Real.sin_add_int_mul_two_pi _ _
  have hc : Real.cos θ = Real.cos (toIcoMod two_pi_pos 0 θ) := by
    conv_lhs => rw [hθ]
    exact Real.cos_add_int_mul_two_pi _ _
  exact ⟨h1, by rw [hs]; exact h2, by rw [hc]; exact h3⟩

/-- Exact values of `cos` and `sin` at `0°`, `30°`, `45°`, `60°` and `90°` (PC-201). -/
@[kb "stitzzeager2013" "§10.2, p. 734"]
theorem box_10_2_special_angles :
    (Real.cos (0 * π / 180) = 1 ∧ Real.sin (0 * π / 180) = 0) ∧
    (Real.cos (30 * π / 180) = √3 / 2 ∧ Real.sin (30 * π / 180) = 1 / 2) ∧
    (Real.cos (45 * π / 180) = √2 / 2 ∧ Real.sin (45 * π / 180) = √2 / 2) ∧
    (Real.cos (60 * π / 180) = 1 / 2 ∧ Real.sin (60 * π / 180) = √3 / 2) ∧
    (Real.cos (90 * π / 180) = 0 ∧ Real.sin (90 * π / 180) = 1) := by
  have e0 : (0 : ℝ) * π / 180 = 0 := by ring
  have e30 : (30 : ℝ) * π / 180 = π / 6 := by ring
  have e45 : (45 : ℝ) * π / 180 = π / 4 := by ring
  have e60 : (60 : ℝ) * π / 180 = π / 3 := by ring
  have e90 : (90 : ℝ) * π / 180 = π / 2 := by ring
  rw [e0, e30, e45, e60, e90]
  simp [Real.cos_pi_div_six, Real.sin_pi_div_six, Real.cos_pi_div_four, Real.sin_pi_div_four,
    Real.cos_pi_div_three, Real.sin_pi_div_three]

/-- Exact values of `cos` and `sin` at the multiples of `30°` and `45°` in quadrants II, III and IV,
obtained from the reference angles (PC-201). -/
@[kb "stitzzeager2013" "§10.2, p. 736"]
theorem ex_10_2_1_special_multiples :
    (Real.cos (120 * π / 180) = -(1 / 2) ∧ Real.sin (120 * π / 180) = √3 / 2) ∧
    (Real.cos (135 * π / 180) = -(√2 / 2) ∧ Real.sin (135 * π / 180) = √2 / 2) ∧
    (Real.cos (150 * π / 180) = -(√3 / 2) ∧ Real.sin (150 * π / 180) = 1 / 2) ∧
    (Real.cos (210 * π / 180) = -(√3 / 2) ∧ Real.sin (210 * π / 180) = -(1 / 2)) ∧
    (Real.cos (225 * π / 180) = -(√2 / 2) ∧ Real.sin (225 * π / 180) = -(√2 / 2)) ∧
    (Real.cos (240 * π / 180) = -(1 / 2) ∧ Real.sin (240 * π / 180) = -(√3 / 2)) ∧
    (Real.cos (300 * π / 180) = 1 / 2 ∧ Real.sin (300 * π / 180) = -(√3 / 2)) ∧
    (Real.cos (315 * π / 180) = √2 / 2 ∧ Real.sin (315 * π / 180) = -(√2 / 2)) ∧
    (Real.cos (330 * π / 180) = √3 / 2 ∧ Real.sin (330 * π / 180) = -(1 / 2)) := by
  have e120 : (120 : ℝ) * π / 180 = π - π / 3 := by ring
  have e135 : (135 : ℝ) * π / 180 = π - π / 4 := by ring
  have e150 : (150 : ℝ) * π / 180 = π - π / 6 := by ring
  have e210 : (210 : ℝ) * π / 180 = π / 6 + π := by ring
  have e225 : (225 : ℝ) * π / 180 = π / 4 + π := by ring
  have e240 : (240 : ℝ) * π / 180 = π / 3 + π := by ring
  have e300 : (300 : ℝ) * π / 180 = 2 * π - π / 3 := by ring
  have e315 : (315 : ℝ) * π / 180 = 2 * π - π / 4 := by ring
  have e330 : (330 : ℝ) * π / 180 = 2 * π - π / 6 := by ring
  rw [e120, e135, e150, e210, e225, e240, e300, e315, e330]
  simp [Real.cos_pi_div_six, Real.sin_pi_div_six, Real.cos_pi_div_four, Real.sin_pi_div_four,
    Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_add_pi, Real.sin_add_pi, Real.cos_two_pi_sub, Real.sin_two_pi_sub]

/-- Table of `tan` and `cot = cos / sin` at `0°`, `30°`, `45°`, `60°`, `90°`: `tan 0° = 0`,
`tan 30° = 1/√3`, `tan 45° = 1`, `tan 60° = √3`, `cot 30° = √3`, `cot 45° = 1`, `cot 60° = 1/√3`,
`cot 90° = 0`; `tan` is undefined at `90°` (`cos 90° = 0`) and `cot` at `0°` (`sin 0° = 0`)
(PC-209). -/
@[kb "stitzzeager2013" "§10.3, p. 759"]
theorem box_10_3_special_tan_cot :
    Real.tan (0 * π / 180) = 0 ∧ Real.tan (30 * π / 180) = 1 / √3 ∧ Real.tan (45 * π / 180) = 1 ∧
      Real.tan (60 * π / 180) = √3 ∧ Real.cos (90 * π / 180) = 0 ∧
      Real.cos (30 * π / 180) / Real.sin (30 * π / 180) = √3 ∧
      Real.cos (45 * π / 180) / Real.sin (45 * π / 180) = 1 ∧
      Real.cos (60 * π / 180) / Real.sin (60 * π / 180) = 1 / √3 ∧
      Real.cos (90 * π / 180) / Real.sin (90 * π / 180) = 0 ∧ Real.sin (0 * π / 180) = 0 := by
  obtain ⟨⟨_, h0⟩, ⟨c30, s30⟩, ⟨c45, s45⟩, ⟨c60, s60⟩, ⟨c90, s90⟩⟩ := box_10_2_special_angles
  have e0 : (0 : ℝ) * π / 180 = 0 := by ring
  have e30 : (30 : ℝ) * π / 180 = π / 6 := by ring
  have e45 : (45 : ℝ) * π / 180 = π / 4 := by ring
  have e60 : (60 : ℝ) * π / 180 = π / 3 := by ring
  have h3 : (0 : ℝ) < √3 := by positivity
  have h3' : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, c90, ?_, ?_, ?_, ?_, h0⟩
  · rw [e0]; simp
  · rw [e30, Real.tan_pi_div_six]
  · rw [e45, Real.tan_pi_div_four]
  · rw [e60, Real.tan_pi_div_three]
  · rw [c30, s30]; field_simp
  · rw [c45, s45]; field_simp
  · rw [c60, s60]; field_simp
  · rw [c90, s90]; simp

/-- Every circular function of an angle equals, up to sign, that of its reference angle:
`|tan θ| = tan (ref θ)`, `|cot θ| = cot (ref θ)`, `|sec θ| = sec (ref θ)`, `|csc θ| = csc (ref θ)`
(with `sec = 1/cos`, `csc = 1/sin`, `cot = cos/sin`) (PC-210). -/
@[kb "stitzzeager2013" "Theorem 10.7, p. 759"]
theorem thm_10_7_reference_angle_all (θ : ℝ) :
    |Real.tan θ| = Real.tan (refAngle θ) ∧
      |Real.cos θ / Real.sin θ| = Real.cos (refAngle θ) / Real.sin (refAngle θ) ∧
      |1 / Real.cos θ| = 1 / Real.cos (refAngle θ) ∧ |1 / Real.sin θ| = 1 / Real.sin (refAngle θ) := by
  obtain ⟨-, hs, hc⟩ := thm_10_2_reference_angle θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, abs_div, hs, hc]
  · rw [abs_div, hs, hc]
  · rw [abs_div, abs_one, hc]
  · rw [abs_div, abs_one, hs]

/-! ### Section 10.4 to 10.6: domains, ranges, periodicity, sinusoids -/

private theorem sec_image :
    (fun x : ℝ => 1 / Real.cos x) '' {x | Real.cos x ≠ 0} = {y | 1 ≤ |y|} := by
  ext y
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [abs_div, abs_one, one_le_div (abs_pos.2 hx)]
    exact Real.abs_cos_le_one x
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
    have h1 : |1 / y| ≤ 1 := by
      rw [abs_div, abs_one, div_le_one (abs_pos.2 hy0)]; exact hy
    obtain ⟨hl, hr⟩ := abs_le.1 h1
    have hc : Real.cos (Real.arccos (1 / y)) = 1 / y := Real.cos_arccos hl hr
    refine ⟨Real.arccos (1 / y), ?_, ?_⟩
    · rw [hc]; simpa using hy0
    · rw [hc, one_div_one_div]

private theorem csc_image :
    (fun x : ℝ => 1 / Real.sin x) '' {x | Real.sin x ≠ 0} = {y | 1 ≤ |y|} := by
  ext y
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [abs_div, abs_one, one_le_div (abs_pos.2 hx)]
    exact Real.abs_sin_le_one x
  · intro hy
    have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
    have h1 : |1 / y| ≤ 1 := by
      rw [abs_div, abs_one, div_le_one (abs_pos.2 hy0)]; exact hy
    obtain ⟨hl, hr⟩ := abs_le.1 h1
    have hc : Real.sin (Real.arcsin (1 / y)) = 1 / y := Real.sin_arcsin hl hr
    refine ⟨Real.arcsin (1 / y), ?_, ?_⟩
    · rw [hc]; simpa using hy0
    · rw [hc, one_div_one_div]

private theorem tan_image : Real.tan '' {x : ℝ | Real.cos x ≠ 0} = univ := by
  ext y
  simp only [mem_image, mem_setOf_eq, mem_univ, iff_true]
  exact ⟨Real.arctan y, (Real.cos_arctan_pos y).ne', Real.tan_arctan y⟩

private theorem cot_image :
    (fun x : ℝ => Real.cos x / Real.sin x) '' {x | Real.sin x ≠ 0} = univ := by
  ext y
  simp only [mem_image, mem_setOf_eq, mem_univ, iff_true]
  have hpos := Real.cos_arctan_pos y
  refine ⟨π / 2 - Real.arctan y, ?_, ?_⟩
  · rw [Real.sin_pi_div_two_sub]; exact hpos.ne'
  · rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, ← Real.tan_eq_sin_div_cos,
      Real.tan_arctan]

/-- Domains and ranges of the six circular functions: `cos` and `sin` have range `[-1, 1]`; `tan`
(on the points where `cos ≠ 0`) and `cot` (where `sin ≠ 0`) take every real value; `sec` and `csc`
take exactly the values `y` with `|y| ≥ 1`; and `cos x = 0` exactly at the odd multiples of `π/2`,
`sin x = 0` exactly at the multiples of `π` (PC-215). -/
@[kb "stitzzeager2013" "Theorem 10.11, p. 769"]
theorem thm_10_11_domains_and_ranges :
    range Real.sin = Icc (-1) 1 ∧ range Real.cos = Icc (-1) 1 ∧
      Real.tan '' {x | Real.cos x ≠ 0} = univ ∧
      (fun x => Real.cos x / Real.sin x) '' {x | Real.sin x ≠ 0} = univ ∧
      (fun x => 1 / Real.cos x) '' {x | Real.cos x ≠ 0} = {y | 1 ≤ |y|} ∧
      (fun x => 1 / Real.sin x) '' {x | Real.sin x ≠ 0} = {y | 1 ≤ |y|} ∧
      (∀ x, Real.cos x = 0 ↔ ∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧
      (∀ x, Real.sin x = 0 ↔ ∃ k : ℤ, x = k * π) :=
  ⟨Real.range_sin, Real.range_cos, tan_image, cot_image, sec_image, csc_image,
    fun _ => Real.cos_eq_zero_iff,
    fun x => Real.sin_eq_zero_iff.trans (exists_congr fun k => eq_comm)⟩

private theorem isLeast_of_cos_one (f : ℝ → ℝ) (hf : Function.Periodic f (2 * π))
    (h : ∀ c, 0 < c → Function.Periodic f c → Real.cos c = 1) :
    IsLeast {c | 0 < c ∧ Function.Periodic f c} (2 * π) :=
  ⟨⟨two_pi_pos, hf⟩, fun c ⟨hc, hper⟩ => two_pi_le_of_cos_one hc (h c hc hper)⟩

private theorem sin_least : IsLeast {c | 0 < c ∧ Function.Periodic Real.sin c} (2 * π) :=
  isLeast_of_cos_one _ Real.sin_periodic fun c _ hper => by
    have := hper (π / 2)
    rwa [add_comm, Real.sin_add_pi_div_two, Real.sin_pi_div_two] at this

private theorem cos_least : IsLeast {c | 0 < c ∧ Function.Periodic Real.cos c} (2 * π) :=
  isLeast_of_cos_one _ Real.cos_periodic fun c _ hper => by
    have := hper 0
    simpa using this

/-- Periodic functions: if `f (t + c) = f t` for all `t` then every positive integer multiple of `c`
is also a period; the period of `sin` and of `cos` is `2π`, the smallest positive such number
(PC-227). -/
@[kb "stitzzeager2013" "Definition 10.3, p. 802"]
theorem def_10_3_periodic (f : ℝ → ℝ) (c : ℝ) (h : Function.Periodic f c) :
    (∀ n : ℕ, Function.Periodic f (n * c)) ∧
      IsLeast {c | 0 < c ∧ Function.Periodic Real.sin c} (2 * π) ∧
      IsLeast {c | 0 < c ∧ Function.Periodic Real.cos c} (2 * π) :=
  ⟨fun n => h.nat_mul n, sin_least, cos_least⟩

/-- The cosine and sine functions: domain all reals, range `[-1, 1]`, continuous, `cos` even and
`sin` odd, and both have least positive period `2π` (PC-228). -/
@[kb "stitzzeager2013" "Theorem 10.22, p. 803"]
theorem thm_10_22_cos_sin :
    range Real.cos = Icc (-1) 1 ∧ range Real.sin = Icc (-1) 1 ∧ Continuous Real.cos ∧
      Continuous Real.sin ∧ (∀ x, Real.cos (-x) = Real.cos x) ∧ (∀ x, Real.sin (-x) = -Real.sin x) ∧
      IsLeast {c | 0 < c ∧ Function.Periodic Real.cos c} (2 * π) ∧
      IsLeast {c | 0 < c ∧ Function.Periodic Real.sin c} (2 * π) :=
  ⟨Real.range_cos, Real.range_sin, Real.continuous_cos, Real.continuous_sin, Real.cos_neg,
    Real.sin_neg, cos_least, sin_least⟩

private theorem sinusoid_cos_aux (A B φ ω : ℝ) (hA : A ≠ 0) (hω : 0 < ω) :
    IsLeast {c | 0 < c ∧ Function.Periodic (fun x : ℝ => A * Real.cos (ω * x + φ) + B) c} (2 * π / ω) ∧
      Function.Periodic (fun x : ℝ => A * Real.cos (ω * x + φ) + B) (2 * π / ω) ∧
      range (fun x : ℝ => A * Real.cos (ω * x + φ) + B) = Icc (B - |A|) (B + |A|) := by
  have hω0 : ω ≠ 0 := hω.ne'
  have per : Function.Periodic (fun x : ℝ => A * Real.cos (ω * x + φ) + B) (2 * π / ω) := by
    intro x
    have : ω * (x + 2 * π / ω) + φ = (ω * x + φ) + 2 * π := by field_simp; ring
    simp only [this, Real.cos_add_two_pi]
  refine ⟨⟨⟨by positivity, per⟩, ?_⟩, per, ?_⟩
  · rintro c ⟨hc, hper⟩
    have h := hper (-φ / ω)
    have e1 : ω * (-φ / ω + c) + φ = ω * c := by field_simp; ring
    have e2 : ω * (-φ / ω) + φ = 0 := by field_simp; ring
    simp only [e1, e2, Real.cos_zero] at h
    have h1 : Real.cos (ω * c) = 1 := mul_left_cancel₀ hA (by linarith : A * Real.cos (ω * c) = A * 1)
    have := two_pi_le_of_cos_one (by positivity : 0 < ω * c) h1
    rw [div_le_iff₀ hω]
    linarith
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      have h1 : |A * Real.cos (ω * x + φ)| ≤ |A| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      obtain ⟨l, r⟩ := abs_le.1 h1
      exact ⟨by simp only; linarith, by simp only; linarith⟩
    · rintro ⟨h1, h2⟩
      have hAp : 0 < |A| := abs_pos.2 hA
      have h3 : |(y - B) / A| ≤ 1 := by
        rw [abs_div, div_le_one hAp]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      obtain ⟨hl, hr⟩ := abs_le.1 h3
      refine ⟨(Real.arccos ((y - B) / A) - φ) / ω, ?_⟩
      have : ω * ((Real.arccos ((y - B) / A) - φ) / ω) + φ = Real.arccos ((y - B) / A) := by
        field_simp; ring
      simp only [this, Real.cos_arccos hl hr]
      field_simp; ring

/-- For `ω > 0` and `A ≠ 0` the function `x ↦ A cos (ωx + φ) + B` has least positive period `2π/ω`,
range `[B - |A|, B + |A|]` (amplitude `|A|`, vertical shift `B`), and is the graph of
`x ↦ A cos (ω (x - s)) + B` with phase shift `s = -φ/ω` (PC-230). -/
@[kb "stitzzeager2013" "Theorem 10.23, p. 807"]
theorem thm_10_23_sinusoid_cos (A B φ ω : ℝ) (hA : A ≠ 0) (hω : 0 < ω) :
    IsLeast {c | 0 < c ∧ Function.Periodic (fun x : ℝ => A * Real.cos (ω * x + φ) + B) c} (2 * π / ω) ∧
      range (fun x : ℝ => A * Real.cos (ω * x + φ) + B) = Icc (B - |A|) (B + |A|) ∧
      ∀ x, A * Real.cos (ω * x + φ) + B = A * Real.cos (ω * (x - (-φ / ω))) + B := by
  obtain ⟨h1, -, h3⟩ := sinusoid_cos_aux A B φ ω hA hω
  refine ⟨h1, h3, fun x => ?_⟩
  have : ω * (x - -φ / ω) = ω * x + φ := by field_simp; ring
  rw [this]

/-- The sine version of the previous theorem: `x ↦ A sin (ωx + φ) + B` has least positive period
`2π/ω`, range `[B - |A|, B + |A|]` and phase shift `-φ/ω` (PC-230). -/
@[kb "stitzzeager2013" "Theorem 10.23, p. 807"]
theorem thm_10_23_sinusoid_sin (A B φ ω : ℝ) (hA : A ≠ 0) (hω : 0 < ω) :
    IsLeast {c | 0 < c ∧ Function.Periodic (fun x : ℝ => A * Real.sin (ω * x + φ) + B) c} (2 * π / ω) ∧
      range (fun x : ℝ => A * Real.sin (ω * x + φ) + B) = Icc (B - |A|) (B + |A|) ∧
      ∀ x, A * Real.sin (ω * x + φ) + B = A * Real.sin (ω * (x - (-φ / ω))) + B := by
  have hf : (fun x : ℝ => A * Real.sin (ω * x + φ) + B) =
      fun x : ℝ => A * Real.cos (ω * x + (φ - π / 2)) + B := by
    funext x
    rw [← Real.cos_sub_pi_div_two]
    congr 3; ring
  obtain ⟨h1, -, h3⟩ := sinusoid_cos_aux A B (φ - π / 2) ω hA hω
  rw [hf]
  refine ⟨h1, h3, fun x => ?_⟩
  have : ω * (x - -φ / ω) = ω * x + φ := by field_simp; ring
  rw [this]

/-- `a cos (ωx) + b sin (ωx)` is a single sinusoid with amplitude `√(a² + b²)`: there is a phase
`φ` with `a cos (ωx) + b sin (ωx) = √(a² + b²) cos (ωx - φ)` for all `x` (PC-231). -/
@[kb "stitzzeager2013" "Example 10.5.3, p. 810"]
theorem ex_10_5_3_single_sinusoid (a b ω : ℝ) :
    ∃ φ : ℝ, ∀ x, a * Real.cos (ω * x) + b * Real.sin (ω * x) =
      √(a ^ 2 + b ^ 2) * Real.cos (ω * x - φ) := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hn : ‖z‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1; simp [hz]; ring
  refine ⟨Complex.arg z, fun x => ?_⟩
  have ha : a = √(a ^ 2 + b ^ 2) * Real.cos (Complex.arg z) := by
    rw [← hn]; exact (Complex.norm_mul_cos_arg z).symm
  have hb : b = √(a ^ 2 + b ^ 2) * Real.sin (Complex.arg z) := by
    rw [← hn]; exact (Complex.norm_mul_sin_arg z).symm
  generalize √(a ^ 2 + b ^ 2) = r at ha hb ⊢
  rw [Real.cos_sub, ha, hb]
  ring

/-- Secant and cosecant (`sec = 1/cos`, `csc = 1/sin`): `sec` is even and `csc` is odd; both are
continuous on their domains (where the denominator is nonzero), take exactly the values with
`|y| ≥ 1`, and have least positive period `2π` (PC-232). -/
@[kb "stitzzeager2013" "Theorem 10.24, p. 814"]
theorem thm_10_24_sec_csc :
    (∀ x, 1 / Real.cos (-x) = 1 / Real.cos x) ∧ (∀ x, 1 / Real.sin (-x) = -(1 / Real.sin x)) ∧
      ContinuousOn (fun x => 1 / Real.cos x) {x | Real.cos x ≠ 0} ∧
      ContinuousOn (fun x => 1 / Real.sin x) {x | Real.sin x ≠ 0} ∧
      (fun x => 1 / Real.cos x) '' {x | Real.cos x ≠ 0} = {y | 1 ≤ |y|} ∧
      (fun x => 1 / Real.sin x) '' {x | Real.sin x ≠ 0} = {y | 1 ≤ |y|} ∧
      IsLeast {c | 0 < c ∧ Function.Periodic (fun x => 1 / Real.cos x) c} (2 * π) ∧
      IsLeast {c | 0 < c ∧ Function.Periodic (fun x => 1 / Real.sin x) c} (2 * π) := by
  refine ⟨fun x => by rw [Real.cos_neg], fun x => by rw [Real.sin_neg, div_neg],
    continuousOn_const.div Real.continuous_cos.continuousOn fun x hx => hx,
    continuousOn_const.div Real.continuous_sin.continuousOn fun x hx => hx,
    sec_image, csc_image, ?_, ?_⟩
  · refine isLeast_of_cos_one _ (fun x => by simp [Real.cos_add_two_pi]) fun c _ hper => ?_
    have := hper 0
    simp only [zero_add, Real.cos_zero, div_one] at this
    have h : (Real.cos c)⁻¹ = 1 := by simpa using this
    exact inv_eq_one.1 h
  · refine isLeast_of_cos_one _ (fun x => by simp [Real.sin_add_two_pi]) fun c _ hper => ?_
    have h2 : 1 / Real.sin (π / 2 + c) = 1 / Real.sin (π / 2) := hper (π / 2)
    rw [add_comm, Real.sin_add_pi_div_two, Real.sin_pi_div_two, div_one] at h2
    have h : (Real.cos c)⁻¹ = 1 := by simpa using h2
    exact inv_eq_one.1 h

/-- Tangent and cotangent (`cot = cos/sin`): both are odd, continuous on their domains, take every
real value, and have least positive period `π` (PC-233). -/
@[kb "stitzzeager2013" "Theorem 10.25, p. 818"]
theorem thm_10_25_tan_cot :
    (∀ x, Real.tan (-x) = -Real.tan x) ∧
      (∀ x, Real.cos (-x) / Real.sin (-x) = -(Real.cos x / Real.sin x)) ∧
      ContinuousOn Real.tan {x | Real.cos x ≠ 0} ∧
      ContinuousOn (fun x => Real.cos x / Real.sin x) {x | Real.sin x ≠ 0} ∧
      Real.tan '' {x | Real.cos x ≠ 0} = univ ∧
      (fun x => Real.cos x / Real.sin x) '' {x | Real.sin x ≠ 0} = univ ∧
      IsLeast {c | 0 < c ∧ Function.Periodic Real.tan c} π ∧
      IsLeast {c | 0 < c ∧ Function.Periodic (fun x => Real.cos x / Real.sin x) c} π := by
  refine ⟨Real.tan_neg, fun x => by rw [Real.cos_neg, Real.sin_neg, div_neg],
    Real.continuousOn_tan,
    Real.continuous_cos.continuousOn.div Real.continuous_sin.continuousOn fun x hx => hx,
    tan_image, cot_image, ⟨⟨pi_pos, Real.tan_periodic⟩, ?_⟩,
    ⟨⟨pi_pos, fun x => by simp [Real.cos_add_pi, Real.sin_add_pi]⟩, ?_⟩⟩
  · rintro c ⟨hc, hper⟩
    have h := hper (π / 4)
    rw [Real.tan_pi_div_four, Real.tan_eq_sin_div_cos] at h
    have hne : Real.cos (π / 4 + c) ≠ 0 := by
      intro h0; rw [h0, div_zero] at h; norm_num at h
    exact pi_le_of_sin_zero hc (sin_zero_of_quarter ((div_eq_one_iff_eq hne).1 h))
  · rintro c ⟨hc, hper⟩
    have h := hper (π / 4)
    simp only [Real.cos_pi_div_four, Real.sin_pi_div_four] at h
    have e : √2 / 2 / (√2 / 2) = 1 := div_self (by positivity)
    rw [e] at h
    have hne : Real.sin (π / 4 + c) ≠ 0 := by
      intro h0; rw [h0, div_zero] at h; norm_num at h
    exact pi_le_of_sin_zero hc (sin_zero_of_quarter ((div_eq_one_iff_eq hne).1 h).symm)

/-! ### Inverse functions and equations -/

/-- The arcsecant, `arcsec x = arccos (1/x)` (the trigonometry-friendly branch, range `[0, π]` without
`π/2`). -/
noncomputable def arcsec (x : ℝ) : ℝ := Real.arccos (1 / x)

/-- The arccosecant, `arccsc x = arcsin (1/x)` (range `[-π/2, π/2]` without `0`). -/
noncomputable def arccsc (x : ℝ) : ℝ := Real.arcsin (1 / x)

/-- `arcsec` is defined for `|x| ≥ 1`, takes values in `[0, π]` other than `π/2`, satisfies
`sec (arcsec x) = x`, and `arcsec (sec θ) = θ` for `θ ∈ [0, π]`, `θ ≠ π/2`; here `arcsec x = arccos (1/x)`
(PC-236). -/
@[kb "stitzzeager2013" "Theorem 10.28, p. 840"]
theorem thm_10_28_arcsec :
    (∀ x : ℝ, 1 ≤ |x| → arcsec x ∈ Icc 0 π ∧ arcsec x ≠ π / 2 ∧ 1 / Real.cos (arcsec x) = x) ∧
      ∀ θ ∈ Icc 0 π, θ ≠ π / 2 → arcsec (1 / Real.cos θ) = θ := by
  constructor
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    have h1 : |1 / x| ≤ 1 := by rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
    obtain ⟨hl, hr⟩ := abs_le.1 h1
    refine ⟨⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_, ?_⟩
    · unfold arcsec
      rw [Ne, Real.arccos_eq_pi_div_two]; simpa using hx0
    · unfold arcsec
      rw [Real.cos_arccos hl hr, one_div_one_div]
  · rintro θ ⟨h0, h1⟩ -
    unfold arcsec
    rw [one_div_one_div, Real.arccos_cos h0 h1]

/-- `arccsc` is defined for `|x| ≥ 1`, takes values in `[-π/2, π/2]` other than `0`, satisfies
`csc (arccsc x) = x`, and `arccsc (csc θ) = θ` for `θ ∈ [-π/2, π/2]`, `θ ≠ 0`; here
`arccsc x = arcsin (1/x)` (PC-236). -/
@[kb "stitzzeager2013" "Theorem 10.28, p. 840"]
theorem thm_10_28_arccsc :
    (∀ x : ℝ, 1 ≤ |x| → arccsc x ∈ Icc (-(π / 2)) (π / 2) ∧ arccsc x ≠ 0 ∧
        1 / Real.sin (arccsc x) = x) ∧
      ∀ θ ∈ Icc (-(π / 2)) (π / 2), θ ≠ 0 → arccsc (1 / Real.sin θ) = θ := by
  constructor
  · intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    have h1 : |1 / x| ≤ 1 := by rw [abs_div, abs_one, div_le_one (abs_pos.2 hx0)]; exact hx
    obtain ⟨hl, hr⟩ := abs_le.1 h1
    refine ⟨⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩, ?_, ?_⟩
    · unfold arccsc
      rw [Ne, Real.arcsin_eq_zero_iff]; simpa using hx0
    · unfold arccsc
      rw [Real.sin_arcsin hl hr, one_div_one_div]
  · rintro θ ⟨h0, h1⟩ -
    unfold arccsc
    rw [one_div_one_div, Real.arcsin_sin h0 h1]

/-- All angles with `sin θ = c` (`|c| ≤ 1`) are `arcsin c + 2πk` or `π - arcsin c + 2πk`; all angles
with `cos θ = c` are `arccos c + 2πk` or `-arccos c + 2πk`; and (when `cos θ ≠ 0`) all angles with
`tan θ = c` are `arctan c + πk` (PC-240). -/
@[kb "stitzzeager2013" "Example 10.6.7, p. 850"]
theorem ex_10_6_7_all_solutions :
    (∀ c θ : ℝ, |c| ≤ 1 → (Real.sin θ = c ↔ ∃ k : ℤ,
      θ = Real.arcsin c + k * (2 * π) ∨ θ = π - Real.arcsin c + k * (2 * π))) ∧
    (∀ c θ : ℝ, |c| ≤ 1 → (Real.cos θ = c ↔ ∃ k : ℤ,
      θ = Real.arccos c + k * (2 * π) ∨ θ = -Real.arccos c + k * (2 * π))) ∧
    (∀ c θ : ℝ, Real.cos θ ≠ 0 → (Real.tan θ = c ↔ ∃ k : ℤ, θ = Real.arctan c + k * π)) := by
  refine ⟨fun c θ hc => ?_, fun c θ hc => ?_, fun c θ hθ => ?_⟩
  · obtain ⟨hl, hr⟩ := abs_le.1 hc
    have e := Real.sin_arcsin hl hr
    constructor
    · intro h
      rw [← e] at h
      obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.1 h.symm
      · exact ⟨k, Or.inl (by linarith)⟩
      · exact ⟨k, Or.inr (by linarith)⟩
    · rintro ⟨k, rfl | rfl⟩
      · rw [Real.sin_add_int_mul_two_pi, e]
      · rw [Real.sin_add_int_mul_two_pi, Real.sin_pi_sub, e]
  · obtain ⟨hl, hr⟩ := abs_le.1 hc
    have e := Real.cos_arccos hl hr
    constructor
    · intro h
      rw [← e] at h
      obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.1 h.symm
      · exact ⟨k, Or.inl (by linarith)⟩
      · exact ⟨k, Or.inr (by linarith)⟩
    · rintro ⟨k, rfl | rfl⟩
      · rw [Real.cos_add_int_mul_two_pi, e]
      · rw [Real.cos_add_int_mul_two_pi, Real.cos_neg, e]
  · constructor
    · intro h
      have := tan_eq_tan_aux hθ (Real.cos_arctan_pos c).ne' (by rw [h, Real.tan_arctan])
      exact this
    · rintro ⟨k, rfl⟩
      rw [Real.tan_add_int_mul_pi, Real.tan_arctan]

private theorem periodic_solutions {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : Function.Periodic f p) (c : ℝ)
    (u : ℝ) : f u = c ↔ ∃ v ∈ Ico 0 p, f v = c ∧ ∃ k : ℤ, u = v + k * p := by
  constructor
  · intro h
    refine ⟨toIcoMod hp 0 u, toIcoMod_mem_Ico' hp u, ?_,
      toIcoDiv hp 0 u, (toIcoMod_add_toIcoDiv_mul hp 0 u).symm⟩
    rw [← h]
    have := (hf.int_mul (toIcoDiv hp 0 u)) (toIcoMod hp 0 u)
    rw [toIcoMod_add_toIcoDiv_mul] at this
    exact this.symm
  · rintro ⟨v, -, hv, k, rfl⟩
    rw [(hf.int_mul k) v]; exact hv

/-- Solving basic trigonometric equations: the solutions of `cos u = c` or `sin u = c` are the
solutions in `[0, 2π)` plus multiples of `2π` (and there are none if `|c| > 1`); `sec u = c` and
`csc u = c` reduce to `cos u = 1/c` and `sin u = 1/c` (no solutions if `0 < |c| < 1`); solutions of
`tan u = c` repeat every `π` and any two agree up to a multiple of `π`; and `cot u = 0` exactly when
`u = π/2 + πk` (PC-241). -/
@[kb "stitzzeager2013" "§10.7, p. 869"]
theorem box_10_7_solving_basic_equations :
    (∀ c u : ℝ, Real.cos u = c ↔ ∃ v ∈ Ico 0 (2 * π), Real.cos v = c ∧ ∃ k : ℤ, u = v + k * (2 * π)) ∧
    (∀ c u : ℝ, Real.sin u = c ↔ ∃ v ∈ Ico 0 (2 * π), Real.sin v = c ∧ ∃ k : ℤ, u = v + k * (2 * π)) ∧
    (∀ c : ℝ, 1 < |c| → ∀ u, Real.cos u ≠ c ∧ Real.sin u ≠ c) ∧
    (∀ c u : ℝ, 1 / Real.cos u = c ↔ Real.cos u = 1 / c) ∧
    (∀ c u : ℝ, 1 / Real.sin u = c ↔ Real.sin u = 1 / c) ∧
    (∀ c : ℝ, 0 < |c| → |c| < 1 → ∀ u, 1 / Real.cos u ≠ c ∧ 1 / Real.sin u ≠ c) ∧
    (∀ u c : ℝ, Real.tan u = c → ∀ k : ℤ, Real.tan (u + k * π) = c) ∧
    (∀ u v : ℝ, Real.cos u ≠ 0 → Real.cos v ≠ 0 → Real.tan u = Real.tan v →
      ∃ k : ℤ, u = v + k * π) ∧
    (∀ u : ℝ, (Real.sin u ≠ 0 ∧ Real.cos u / Real.sin u = 0) ↔ ∃ k : ℤ, u = π / 2 + k * π) := by
  have hsec : ∀ (g : ℝ → ℝ) (c u : ℝ), 1 / g u = c ↔ g u = 1 / c := fun g c u => by
    constructor
    · intro h; rw [← h, one_div_one_div]
    · intro h; rw [h, one_div_one_div]
  have habs : ∀ (g : ℝ → ℝ), (∀ x, |g x| ≤ 1) → ∀ c : ℝ, 0 < |c| → |c| < 1 → ∀ u, 1 / g u ≠ c := by
    intro g hg c hc0 hc1 u h
    by_cases hu : g u = 0
    · rw [hu, div_zero] at h; rw [← h] at hc0; simp at hc0
    · have := hg u
      have h2 : |1 / g u| = 1 / |g u| := by rw [abs_div, abs_one]
      rw [h, ← one_div_one_div |c|] at *
      have h3 : 1 ≤ 1 / |g u| := by rw [one_le_div (abs_pos.2 hu)]; exact this
      linarith
  refine ⟨periodic_solutions two_pi_pos Real.cos_periodic, periodic_solutions two_pi_pos Real.sin_periodic,
    fun c hc u => ⟨fun h => ?_, fun h => ?_⟩, hsec Real.cos, hsec Real.sin,
    fun c h0 h1 u => ⟨habs Real.cos Real.abs_cos_le_one c h0 h1 u, habs Real.sin Real.abs_sin_le_one c h0 h1 u⟩,
    fun u c h k => ?_, fun u v => tan_eq_tan_aux, fun u => ?_⟩
  · have := Real.abs_cos_le_one u; rw [h] at this; linarith
  · have := Real.abs_sin_le_one u; rw [h] at this; linarith
  · rw [Real.tan_add_int_mul_pi]; exact h
  · constructor
    · rintro ⟨hs, h⟩
      have hc : Real.cos u = 0 := (div_eq_zero_iff.1 h).resolve_right hs
      obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 hc
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have hc : Real.cos u = 0 := Real.cos_eq_zero_iff.2 ⟨k, by linarith⟩
      have h1 := Real.sin_sq_add_cos_sq u
      rw [hc] at h1
      refine ⟨?_, by rw [hc, zero_div]⟩
      intro hs; rw [hs] at h1; norm_num at h1

end UndergradKB.Precalculus.Course
