import UndergradKB.Trigonometry.Triangle.Area

/-! # Law of tangents and Mollweide's equations (Corral §2.3, Exercises 3.16-3.17)

For a triangle `t` with vertices `A = t.points 0`, `B = t.points 1`, `C = t.points 2`, the books write
`a = BC`, `b = CA`, `c = AB` and `A, B, C` for the angles at the vertices. The cyclic versions follow by
relabelling the vertices (`Affine.Simplex.reindex`).

The proofs follow Corral: by the law of sines `a, b, c` are proportional to `sin A, sin B, sin C`, and the
sum-to-product formulas turn `sin A ± sin B` into products of half-angle functions. They go through real
lemmas (`law_of_tangents_real`, `mollweide_real`) about numbers `a, b, c, A, B, C` with the law of sines
relations, which may also be used directly.
-/

namespace UndergradKB.Trigonometry

open EuclideanGeometry Real
open scoped EuclideanGeometry

section real

variable {a b c A B C : ℝ}

/-- Half-angle facts for angles of a triangle: with `x = (A - B)/2` and `y = (A + B)/2`,
`cos x > 0`, `sin y > 0`, `cos y > 0`. -/
private lemma half_facts (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hs : A + B + C = π) :
    0 < cos ((A - B) / 2) ∧ 0 < sin ((A + B) / 2) ∧ 0 < cos ((A + B) / 2) := by
  refine ⟨cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩, sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith), cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩⟩

private lemma sin_A (A B : ℝ) : sin A = sin ((A + B) / 2) * cos ((A - B) / 2) +
    cos ((A + B) / 2) * sin ((A - B) / 2) := by
  rw [← sin_add]; ring_nf

private lemma sin_B (A B : ℝ) : sin B = sin ((A + B) / 2) * cos ((A - B) / 2) -
    cos ((A + B) / 2) * sin ((A - B) / 2) := by
  rw [← sin_sub]; ring_nf

private lemma sin_C (hs : A + B + C = π) :
    sin C = 2 * sin ((A + B) / 2) * cos ((A + B) / 2) := by
  rw [← sin_two_mul, show C = π - 2 * ((A + B) / 2) by linarith, sin_pi_sub]

/-- **Law of tangents**, for real numbers: if `A, B, C > 0` with `A + B + C = π` and `a sin B = b sin A`,
with `a, b > 0`, then `(a - b)/(a + b) = tan ½(A - B) / tan ½(A + B)`. -/
theorem law_of_tangents_real (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hs : A + B + C = π) (hab : a * sin B = b * sin A) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) := by
  obtain ⟨hcx, hsy, hcy⟩ := half_facts hA hB hC hs
  rw [sin_A A B, sin_B A B] at hab
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_div_div_eq, div_eq_div_iff (add_pos ha hb).ne'
    (by positivity)]
  linear_combination hab

/-- **Mollweide's equations**, for real numbers: if `A, B, C > 0` with `A + B + C = π`,
`a sin B = b sin A` and `a sin C = c sin A`, with `c > 0`, then `(a - b)/c = sin ½(A - B) / cos ½C` and
`(a + b)/c = cos ½(A - B) / sin ½C`. -/
theorem mollweide_real (hc : 0 < c) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hs : A + B + C = π) (hab : a * sin B = b * sin A) (hac : a * sin C = c * sin A) :
    (a - b) / c = sin ((A - B) / 2) / cos (C / 2) ∧
      (a + b) / c = cos ((A - B) / 2) / sin (C / 2) := by
  obtain ⟨hcx, hsy, hcy⟩ := half_facts hA hB hC hs
  have hC2 : C / 2 = π / 2 - (A + B) / 2 := by linarith
  have hsinA : 0 < sin A := sin_pos_of_pos_of_lt_pi hA (by linarith)
  rw [hC2, cos_pi_div_two_sub, sin_pi_div_two_sub]
  rw [sin_C hs] at hac
  rw [sin_B A B] at hab
  set sx := sin ((A - B) / 2)
  set cx := cos ((A - B) / 2)
  set sy := sin ((A + B) / 2)
  set cy := cos ((A + B) / 2)
  have hsA : sin A = sy * cx + cy * sx := by rw [sin_A A B]
  constructor
  · rw [div_eq_div_iff hc.ne' hsy.ne']
    have key : sin A * ((a - b) * sy - sx * c) = 0 := by
      rw [hsA] at hab hac ⊢
      linear_combination sy * hab + sx * hac
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hsinA.ne'
    · linarith
  · rw [div_eq_div_iff hc.ne' hcy.ne']
    have key : sin A * ((a + b) * cy - cx * c) = 0 := by
      rw [hsA] at hab hac ⊢
      linear_combination (-cy) * hab + cx * hac
    rcases mul_eq_zero.1 key with h | h
    · exact absurd h hsinA.ne'
    · linarith

end real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable (t : Affine.Triangle ℝ P)

/-- The angles of a triangle are positive and sum to `π`, and the law of sines holds; in the books'
labels `a = BC`, `b = CA`, `c = AB`. -/
private lemma triangle_facts :
    0 < ∠ (t.points 1) (t.points 0) (t.points 2) ∧ 0 < ∠ (t.points 0) (t.points 1) (t.points 2) ∧
    0 < ∠ (t.points 0) (t.points 2) (t.points 1) ∧
    ∠ (t.points 1) (t.points 0) (t.points 2) + ∠ (t.points 0) (t.points 1) (t.points 2) +
      ∠ (t.points 0) (t.points 2) (t.points 1) = π ∧
    dist (t.points 1) (t.points 2) * sin (∠ (t.points 0) (t.points 1) (t.points 2)) =
      dist (t.points 0) (t.points 2) * sin (∠ (t.points 1) (t.points 0) (t.points 2)) ∧
    dist (t.points 1) (t.points 2) * sin (∠ (t.points 0) (t.points 2) (t.points 1)) =
      dist (t.points 0) (t.points 1) * sin (∠ (t.points 1) (t.points 0) (t.points 2)) := by
  refine ⟨angle_pos_of_not_collinear (not_collinear_of_ne t (by decide) (by decide) (by decide)),
    angle_pos_of_not_collinear (not_collinear_of_ne t (by decide) (by decide) (by decide)),
    angle_pos_of_not_collinear (not_collinear_of_ne t (by decide) (by decide) (by decide)), ?_, ?_,
    ?_⟩
  · have h := angle_add_angle_add_angle_eq_pi (p₁ := t.points 0) (p₂ := t.points 1) (t.points 2)
      (t.independent.injective.ne (by decide))
    rw [angle_comm (t.points 1) (t.points 2) (t.points 0),
      angle_comm (t.points 2) (t.points 0) (t.points 1)] at h
    linarith
  · have h := law_sin (t.points 0) (t.points 1) (t.points 2)
    rw [dist_comm (t.points 2) (t.points 0), angle_comm (t.points 2) (t.points 0) (t.points 1)] at h
    linarith
  · have h := law_sin (t.points 0) (t.points 2) (t.points 1)
    rw [dist_comm (t.points 2) (t.points 1), dist_comm (t.points 1) (t.points 0)] at h
    linarith

/-- **Law of tangents**: `(a - b)/(a + b) = tan ½(A - B) / tan ½(A + B)` in any triangle. -/
@[kb "corraltrig" "Theorem 2.3, p. 59"]
theorem law_of_tangents {a b A B : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hA : A = ∠ (t.points 1) (t.points 0) (t.points 2))
    (hB : B = ∠ (t.points 0) (t.points 1) (t.points 2)) :
    (a - b) / (a + b) = tan ((A - B) / 2) / tan ((A + B) / 2) := by
  obtain ⟨h0, h1, h2, hs, hab, -⟩ := triangle_facts t
  subst ha hb hA hB
  exact law_of_tangents_real (dist_points_pos t (by decide)) (dist_points_pos t (by decide)) h0 h1
    h2 hs hab

/-- **Mollweide's equations**: `(a - b)/c = sin ½(A - B) / cos ½C` and
`(a + b)/c = cos ½(A - B) / sin ½C` in any triangle. -/
@[kb "corraltrig" "Box §2.3 (Mollweide's equations), p. 60"]
theorem mollweide {a b c A B C : ℝ} (ha : a = dist (t.points 1) (t.points 2))
    (hb : b = dist (t.points 0) (t.points 2)) (hc : c = dist (t.points 0) (t.points 1))
    (hA : A = ∠ (t.points 1) (t.points 0) (t.points 2))
    (hB : B = ∠ (t.points 0) (t.points 1) (t.points 2))
    (hC : C = ∠ (t.points 0) (t.points 2) (t.points 1)) :
    (a - b) / c = sin ((A - B) / 2) / cos (C / 2) ∧
      (a + b) / c = cos ((A - B) / 2) / sin (C / 2) := by
  obtain ⟨h0, h1, h2, hs, hab, hac⟩ := triangle_facts t
  subst ha hb hc hA hB hC
  exact mollweide_real (dist_points_pos t (by decide)) h0 h1 h2 hs hab hac

end UndergradKB.Trigonometry
