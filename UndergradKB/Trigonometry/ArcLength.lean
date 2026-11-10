import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.EMetricSpace.BoundedVariation
import UndergradKB.Common.Attr

/-! # Arc length and radian measure (Corral §4.1, §4.2, §4.4; OpenStax §7.1)

The length of a curve `γ : ℝ → ℂ` over an interval is its total variation `eVariationOn γ (Icc α β)`
(Mathlib's notion: the supremum of the lengths of inscribed polygons). For the circle arc
`φ ↦ c + r e^{iφ}` with `α ≤ φ ≤ β` we prove that this length is `r (β - α)` (`eVariationOn_arc`):
the upper bound because the parametrisation is `r`-Lipschitz, the lower bound from the inscribed regular
polygons, whose perimeters `2Nr sin ((β - α)/2N)` tend to `r (β - α)`.

Consequences in the books' terms: the arc cut off by a central angle of `θ` radians has length `s = rθ`
(`arc_length`); the radian measure `θ = s / r` of a central angle does not depend on the radius
(`radian_eq_arc_div_radius`); the circumference is `2πr` (`circumference`); an object moving on a circle of
radius `r` with angular speed `ω` covers the distance `r ω t` in time `t`, so its linear speed is `v = ωr`
(`linear_speed`).
-/

namespace UndergradKB.Trigonometry

open Real Set Complex

/-- The chord between the points of angles `a` and `b` on the circle of radius `r ≥ 0` centred at `c` has
length `2r |sin ((a - b)/2)|`. -/
lemma dist_arc (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    dist (c + r * Complex.exp (a * I)) (c + r * Complex.exp (b * I)) =
      r * (2 * |Real.sin ((a - b) / 2)|) := by
  have h : Complex.exp (a * I) = Complex.exp (b * I) * Complex.exp (I * ↑(a - b)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [Complex.dist_eq, h,
    show c + ↑r * (Complex.exp (↑b * I) * Complex.exp (I * ↑(a - b))) - (c + ↑r * Complex.exp (↑b * I))
      = ↑r * Complex.exp (↑b * I) * (Complex.exp (I * ↑(a - b)) - 1) by ring,
    norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_exp_I_mul_ofReal_sub_one,
    Complex.norm_real, Real.norm_of_nonneg hr, Real.norm_eq_abs, abs_mul, abs_two]
  ring

/-- **Length of a circular arc**: the arc `φ ↦ c + r e^{iφ}`, `α ≤ φ ≤ β`, has length `r (β - α)`. -/
theorem eVariationOn_arc (c : ℂ) {r α β : ℝ} (hr : 0 ≤ r) (hαβ : α ≤ β) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc α β) =
      ENNReal.ofReal (r * (β - α)) := by
  set γ : ℝ → ℂ := fun φ => c + r * Complex.exp (φ * I) with hγ
  apply le_antisymm
  · -- upper bound: `γ` is `r`-Lipschitz
    have hL : LipschitzWith r.toNNReal γ := LipschitzWith.of_dist_le_mul fun a b => by
      rw [hγ, dist_arc c hr, Real.dist_eq, Real.coe_toNNReal r hr]
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
  · -- lower bound: inscribed regular polygons
    set L := β - α with hL
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
        rw [edist_dist, hγ, dist_arc c hr]
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

/-- **Arc length**: on a circle of radius `r`, the arc cut off by a central angle of `θ ≥ 0` radians has
length `s = rθ`. (TR-102) -/
@[kb "corraltrig" "Box §4.2 (s = rθ), p. 98"]
theorem arc_length (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc 0 θ) = ENNReal.ofReal (r * θ) := by
  rw [eVariationOn_arc c hr hθ, sub_zero]

/-- OpenStax's form: the arc length `s` and the angle `θ` (in radians) satisfy `s = rθ`. (TR-102) -/
@[kb "openstaxalgtrig2e" "§7.1 Arc length on a circle, p. 689"]
theorem arc_length' (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc 0 θ)).toReal = r * θ := by
  rw [arc_length c hr hθ, ENNReal.toReal_ofReal (mul_nonneg hr hθ)]

/-- **Radian measure**: a central angle of `θ` radians cuts off an arc of length `s` with `θ = s / r`, the same
for every radius `r > 0` (one radian subtends an arc equal to the radius). (TR-100) -/
@[kb "corraltrig" "Box §4.1 (radian measure), p. 95"]
theorem radian_eq_arc_div_radius (c : ℂ) {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ θ) :
    (eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc 0 θ)).toReal / r = θ := by
  rw [arc_length' c hr.le hθ]
  field_simp

/-- **Circumference**: a circle of radius `r` has length `2πr`, so circumference over radius is `2π` for every
circle. (TR-111) -/
@[kb "openstaxalgtrig2e" "§7.1 (circumference 2πr), p. 680"]
theorem circumference (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    eVariationOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) (Icc 0 (2 * π)) =
      ENNReal.ofReal (2 * π * r) := by
  rw [arc_length c hr (by positivity), mul_comm]

/-- **Linear and angular speed**: an object moving on a circle of radius `r` with constant angular speed
`ω ≥ 0` (angle `ωτ` at time `τ`) travels the distance `ω r t` during the time `t ≥ 0`, so its linear speed is
`v = ωr`. (TR-108) -/
@[kb "corraltrig" "Box §4.4 (ν = ωr), p. 107"]
theorem linear_speed (c : ℂ) {r ω t : ℝ} (hr : 0 ≤ r) (hω : 0 ≤ ω) (ht : 0 ≤ t) :
    eVariationOn (fun τ : ℝ => c + r * Complex.exp ((ω * τ : ℝ) * I)) (Icc 0 t) =
      ENNReal.ofReal ((ω * r) * t) := by
  have hmono : MonotoneOn (fun τ : ℝ => ω * τ) (Icc 0 t) := fun x _ y _ hxy =>
    mul_le_mul_of_nonneg_left hxy hω
  have := eVariationOn.comp_eq_of_monotoneOn (fun φ : ℝ => c + r * Complex.exp (φ * I)) _ hmono
  rw [Function.comp_def] at this
  rw [this, image_mul_left_Icc hω ht, mul_zero, eVariationOn_arc c hr (by positivity)]
  congr 1; ring

end UndergradKB.Trigonometry
