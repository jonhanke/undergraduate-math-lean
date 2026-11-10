import UndergradKB.Trigonometry.Triangle.Area
import UndergradKB.Trigonometry.HalfAngle

/-! # Heron's formula, circumradius and inradius in terms of the sides (Corral §2.4, §2.5; OpenStax §10.2)

Notation of the books: `a = BC`, `b = CA`, `c = AB` for the triangle with vertices `A = t.points 0`,
`B = t.points 1`, `C = t.points 2`; `s = (a + b + c)/2`; `K` the area (`UndergradKB.Trigonometry.area`),
`R = t.circumradius` and `r = t.inradius` (Mathlib's circumradius and inradius of a simplex).
Statements take `a b c s` as real numbers with defining equations, so that they read as in the books.
-/

namespace UndergradKB.Trigonometry

open EuclideanGeometry Real
open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable (t : Affine.Triangle ℝ P)

/-- Four times the square of the area: `4K² = a²c² - ((a² + c² - b²)/2)²` (the angle at `B` eliminated by
the law of cosines). -/
private lemma four_mul_area_sq :
    4 * area t ^ 2 = dist (t.points 1) (t.points 2) ^ 2 * dist (t.points 0) (t.points 1) ^ 2 -
      ((dist (t.points 1) (t.points 2) ^ 2 + dist (t.points 0) (t.points 1) ^ 2 -
        dist (t.points 0) (t.points 2) ^ 2) / 2) ^ 2 := by
  have hK := area_eq_mul_mul_sin_div_two t (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have hcos := law_cos (t.points 0) (t.points 1) (t.points 2)
  have hsc := sin_sq_add_cos_sq (∠ (t.points 0) (t.points 1) (t.points 2))
  rw [dist_comm (t.points 2) (t.points 1)] at hcos
  rw [hK, dist_comm (t.points 1) (t.points 0)]
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 0) (t.points 2)
  set c := dist (t.points 0) (t.points 1)
  set C := Real.cos (∠ (t.points 0) (t.points 1) (t.points 2))
  linear_combination (c ^ 2 * a ^ 2) * hsc - (a ^ 2 + c ^ 2 - b ^ 2 + 2 * a * c * C) / 4 * hcos

/-- **Qin Jiushao's form** of the area: `K = ½ √(a²c² - ((a² + c² - b²)/2)²)`. -/
@[kb "corraltrig" "Box §2.4 (Qin Jiushao's formula), p. 66"]
theorem area_eq_qin_jiushao {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    area t = 1 / 2 * √(a ^ 2 * c ^ 2 - ((a ^ 2 + c ^ 2 - b ^ 2) / 2) ^ 2) := by
  subst ha hb hc
  rw [← four_mul_area_sq, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (area_pos t).le,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  ring

private lemma sixteen_mul_area_sq {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    16 * area t ^ 2 = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) := by
  have h := four_mul_area_sq t
  rw [← ha, ← hb, ← hc] at h
  linear_combination 4 * h

/-- **Heron's formula**: with `s` the semiperimeter, the area is `√(s(s-a)(s-b)(s-c))`. -/
@[kb "corraltrig" "Box §2.4 (Heron's formula), p. 63"]
theorem heron {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    area t = √(s * (s - a) * (s - b) * (s - c)) := by
  have h := sixteen_mul_area_sq t ha hb hc
  rw [← Real.sqrt_sq (area_pos t).le]
  congr 1
  subst hs
  linear_combination h / 16

/-- Heron's formula as stated in OpenStax §10.2. -/
@[kb "openstaxalgtrig2e" "§10.2 Heron's formula, p. 903"]
theorem heron_openstax {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    area t = √(s * (s - a) * (s - b) * (s - c)) :=
  heron t ha hb hc hs

/-- **Kahan's form** of Heron's formula, `K = ¼ √((a + (b + c))(c - (a - b))(c + (a - b))(a + (b - c)))`.
Corral states it for `a ≥ b ≥ c` (the ordering matters for floating-point accuracy, not for the identity,
which holds for every labelling). -/
@[kb "corraltrig" "Box §2.4 (Kahan's stable form of Heron's formula), p. 65"]
theorem heron_kahan {a b c : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1)) :
    area t = 1 / 4 * √((a + (b + c)) * (c - (a - b)) * (c + (a - b)) * (a + (b - c))) := by
  have h := sixteen_mul_area_sq t ha hb hc
  rw [show (a + (b + c)) * (c - (a - b)) * (c + (a - b)) * (a + (b - c)) = 4 ^ 2 * area t ^ 2 by
    linear_combination -h, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (area_pos t).le,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  ring

/-- **Area from one side and the angles**: `K = a² sin B sin C / (2 sin A)` (and cyclic versions). -/
@[kb "corraltrig" "Box §2.4 (area from one side and two angles), p. 63"]
theorem area_eq_sq_mul_sin_mul_sin_div_sin {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    area t = dist (t.points i₂) (t.points i₃) ^ 2 *
      Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) *
      Real.sin (∠ (t.points i₁) (t.points i₃) (t.points i₂)) /
      (2 * Real.sin (∠ (t.points i₂) (t.points i₁) (t.points i₃))) := by
  have hA := sin_angle_points_pos t (Ne.symm h₁₂) h₂₃ h₁₃
  have hK := area_eq_mul_mul_sin_div_two t (Ne.symm h₁₂) h₂₃ h₁₃
  -- law of sines `c sin A = a sin C`
  have hs := law_sin (t.points i₃) (t.points i₁) (t.points i₂)
  rw [angle_comm (t.points i₃) (t.points i₁) (t.points i₂),
    angle_comm (t.points i₂) (t.points i₃) (t.points i₁)] at hs
  rw [hK, eq_div_iff (by positivity), dist_comm (t.points i₂) (t.points i₁)]
  linear_combination dist (t.points i₂) (t.points i₃) *
    Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) * hs

/-- **Area and circumradius**: `K = abc / (4R)`, equivalently `R = abc / (4K)`. -/
@[kb "corraltrig" "Theorem 2.8, p. 70"]
theorem area_eq_mul_mul_mul_div_four_mul_circumradius {a b c : ℝ}
    (ha : a = dist (t.points 1) (t.points 2)) (hb : b = dist (t.points 0) (t.points 2))
    (hc : c = dist (t.points 0) (t.points 1)) :
    area t = a * b * c / (4 * t.circumradius) ∧ t.circumradius = a * b * c / (4 * area t) := by
  have hR := t.dist_div_sin_angle_eq_two_mul_circumradius (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  have hsin := sin_angle_points_pos t (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have hRpos := t.circumradius_pos
  have hK := area_eq_mul_mul_sin_div_two t (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have hKpos := area_pos t
  rw [div_eq_iff hsin.ne'] at hR
  subst ha hb hc
  rw [dist_comm (t.points 1) (t.points 0)] at hK
  constructor
  · rw [hK, eq_div_iff (by positivity), hR]; ring
  · rw [eq_div_iff (by positivity), hK, hR]; ring

/-- **Circumradius from the sides**: `R = abc / (4 √(s(s-a)(s-b)(s-c)))`. -/
@[kb "corraltrig" "Corollary 2.9, p. 70"]
theorem circumradius_eq_heron {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    t.circumradius = a * b * c / (4 * √(s * (s - a) * (s - b) * (s - c))) := by
  rw [← heron t ha hb hc hs]
  exact (area_eq_mul_mul_mul_div_four_mul_circumradius t ha hb hc).2

/-- The height of each vertex is twice the area divided by the opposite side. -/
private lemma height_eq {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    t.height i₁ = 2 * area t / dist (t.points i₂) (t.points i₃) := by
  rw [area_eq_dist_mul_height_div_two t h₁₂ h₁₃ h₂₃]
  have := dist_points_pos t h₂₃
  field_simp

/-- **Inradius and area**: `K = r s`, i.e. `r = K / s`. -/
@[kb "corraltrig" "Theorem 2.11, p. 71"]
theorem inradius_eq_area_div_semiperimeter {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    t.inradius = area t / s := by
  have hKpos := area_pos t
  have h0 := height_eq t (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  have h1 := height_eq t (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have h2 := height_eq t (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide) (by decide)
  have pa := dist_points_pos t (i := 1) (j := 2) (by decide)
  have pb := dist_points_pos t (i := 0) (j := 2) (by decide)
  have pc := dist_points_pos t (i := 0) (j := 1) (by decide)
  rw [Affine.Simplex.inradius, ← Affine.Simplex.exradius,
    Affine.Simplex.exradius_eq_abs_inv_sum]
  simp only [Affine.Simplex.excenterWeightsUnnorm, Finset.notMem_empty, ite_false, one_mul]
  rw [Fin.sum_univ_three, h0, h1, h2]
  subst ha hb hc hs
  rw [abs_of_pos (by positivity)]
  field_simp

/-- **Inradius from the sides**: `r = √((s-a)(s-b)(s-c)/s)`. -/
@[kb "corraltrig" "Theorem 2.11, p. 71"]
theorem inradius_eq_sqrt {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    t.inradius = √((s - a) * (s - b) * (s - c) / s) := by
  have hspos : 0 < s := by
    rw [hs, ha, hb, hc]
    have := dist_points_pos t (i := 1) (j := 2) (by decide)
    have := dist_points_pos t (i := 0) (j := 2) (by decide)
    have := dist_points_pos t (i := 0) (j := 1) (by decide)
    positivity
  rw [inradius_eq_area_div_semiperimeter t ha hb hc hs, heron t ha hb hc hs,
    ← Real.sqrt_sq hspos.le, ← Real.sqrt_div' _ (sq_nonneg s), Real.sqrt_sq hspos.le]
  congr 1
  field_simp

/-- **Inradius and half angles**: `r = (s - a) tan ½A` (and cyclic versions, Corral Theorem 2.10), with
`A` the angle at vertex `0`, opposite the side `a`. -/
@[kb "corraltrig" "Theorem 2.10, p. 71"]
theorem inradius_eq_mul_tan_half {a b c s : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hs : s = (a + b + c) / 2) :
    t.inradius = (s - a) * Real.tan (∠ (t.points 1) (t.points 0) (t.points 2) / 2) := by
  have hK := area_eq_mul_mul_sin_div_two t (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have hcos := law_cos (t.points 1) (t.points 0) (t.points 2)
  rw [dist_comm (t.points 1) (t.points 0), dist_comm (t.points 2) (t.points 0)] at hcos
  have pa := dist_points_pos t (i := 1) (j := 2) (by decide)
  have pb := dist_points_pos t (i := 0) (j := 2) (by decide)
  have pc := dist_points_pos t (i := 0) (j := 1) (by decide)
  have hApi : ∠ (t.points 1) (t.points 0) (t.points 2) < π := angle_lt_pi_of_not_collinear
    (not_collinear_of_ne t (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide))
  have h1cos : 0 < 1 + Real.cos (∠ (t.points 1) (t.points 0) (t.points 2)) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg _ _ _) le_rfl hApi
    rw [Real.cos_pi] at this
    linarith
  rw [inradius_eq_area_div_semiperimeter t ha hb hc hs, tan_half_eq_sin_div_one_add_cos, hK]
  rw [← ha, ← hb, ← hc] at hcos
  rw [← hb, ← hc]
  rw [← hb] at pb
  rw [← hc] at pc
  rw [← ha] at pa
  set S := Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))
  set C := Real.cos (∠ (t.points 1) (t.points 0) (t.points 2))
  subst hs
  rw [div_div, show (a + b + c) / 2 - a = (b + c - a) / 2 by ring]
  field_simp
  linear_combination S * hcos

end UndergradKB.Trigonometry
