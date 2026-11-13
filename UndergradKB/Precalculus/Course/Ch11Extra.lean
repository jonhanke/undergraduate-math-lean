import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (extra rows restated from the Trigonometry topic)

The ambiguous (SSA) case, the area of a triangle, Heron's formula, and polar coordinates with their
non-uniqueness, in the book's terms and proved from Mathlib alone. Triangles live in
`EuclideanSpace ℝ (Fin 2)`; polar points are pairs of reals.
-/

namespace UndergradKB.Precalculus.Course

open Real Set EuclideanGeometry

/-! ### The ambiguous case (Theorem 11.3) -/

/-- The possible lengths `b > 0` of the third side of a triangle with the angle `α` between the
sides `b` and `c`, and the side `a` opposite `α` (the law of cosines `a² = b² + c² - 2bc cos α`). -/
def ssaSides (a c α : ℝ) : Set ℝ :=
  {b | 0 < b ∧ a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α}

/-- Ambiguous case: given an acute angle `α`, the side `c` adjacent to it and the opposite side `a`,
put `h = c sin α`. Then no triangle exists if `a < h`, exactly one if `a = h`, exactly two if
`h < a < c`, and exactly one if `a ≥ c`; the triangles are counted by the possible third sides `b`
(the obtuse case: `thm_11_3_ambiguous_case_obtuse`) (PC-244). -/
@[kb "stitzzeager2013" "Theorem 11.3, p. 913"]
theorem thm_11_3_ambiguous_case {a c α : ℝ} (ha : 0 < a) (hc : 0 < c) (hα0 : 0 < α)
    (hα : α < π / 2) :
    (a < c * Real.sin α → (ssaSides a c α).ncard = 0) ∧
    (a = c * Real.sin α → (ssaSides a c α).ncard = 1) ∧
    (c * Real.sin α < a → a < c → (ssaSides a c α).ncard = 2) ∧
    (c ≤ a → (ssaSides a c α).ncard = 1) := by
  have hk : 0 < c * Real.cos α := mul_pos hc (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα⟩)
  have hh : 0 < c * Real.sin α := mul_pos hc (Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [pi_pos]))
  have e : (c * Real.cos α) ^ 2 + (c * Real.sin α) ^ 2 = c ^ 2 := by
    have := Real.cos_sq_add_sin_sq α
    calc _ = c ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) := by ring
      _ = c ^ 2 := by rw [this, mul_one]
  have hS : ∀ b, b ∈ ssaSides a c α ↔
      0 < b ∧ (b - c * Real.cos α) ^ 2 = a ^ 2 - (c * Real.sin α) ^ 2 := by
    intro b
    constructor <;> rintro ⟨hb, h⟩ <;> exact ⟨hb, by nlinarith⟩
  generalize c * Real.cos α = k at hk e hS
  generalize c * Real.sin α = h at hh e hS ⊢
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · have : ssaSides a c α = ∅ := by
      ext b
      simp only [hS, mem_empty_iff_false, iff_false, not_and]
      intro _ hb; nlinarith [sq_nonneg (b - k)]
    rw [this, Set.ncard_empty]
  · subst h1
    have : ssaSides a c α = {k} := by
      ext b
      rw [hS, mem_singleton_iff]
      constructor
      · rintro ⟨_, hb⟩
        have : (b - k) ^ 2 = 0 := by linarith
        have := pow_eq_zero_iff (two_ne_zero) |>.1 this
        linarith
      · rintro rfl; exact ⟨hk, by ring⟩
    rw [this, Set.ncard_singleton]
  · have hD : 0 < a ^ 2 - h ^ 2 := by nlinarith
    have hs := Real.sq_sqrt hD.le
    have hs0 := Real.sqrt_pos.2 hD
    have hsk : √(a ^ 2 - h ^ 2) < k := by nlinarith
    have : ssaSides a c α = {k + √(a ^ 2 - h ^ 2), k - √(a ^ 2 - h ^ 2)} := by
      ext b
      rw [hS]
      simp only [mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨_, hb⟩
        have : (b - k) ^ 2 = √(a ^ 2 - h ^ 2) ^ 2 := by rw [hs]; exact hb
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h3 | h3
        · left; linarith
        · right; linarith
      · rintro (rfl | rfl)
        · exact ⟨by linarith, by rw [add_sub_cancel_left, hs]⟩
        · exact ⟨by linarith, by rw [sub_sub_cancel_left, neg_sq, hs]⟩
    rw [this]
    exact Set.ncard_pair (by linarith)
  · have hD : 0 < a ^ 2 - h ^ 2 := by nlinarith
    have hs := Real.sq_sqrt hD.le
    have hs0 := Real.sqrt_pos.2 hD
    have hsk : k ≤ √(a ^ 2 - h ^ 2) := by nlinarith
    have : ssaSides a c α = {k + √(a ^ 2 - h ^ 2)} := by
      ext b
      rw [hS]
      simp only [mem_singleton_iff]
      constructor
      · rintro ⟨hb0, hb⟩
        have : (b - k) ^ 2 = √(a ^ 2 - h ^ 2) ^ 2 := by rw [hs]; exact hb
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h3 | h3
        · linarith
        · exfalso; linarith
      · rintro rfl
        exact ⟨by linarith, by rw [add_sub_cancel_left, hs]⟩
    rw [this, Set.ncard_singleton]

/-- Ambiguous case, obtuse or right angle: given `π/2 ≤ α < π`, the side `c` adjacent to it and the opposite
side `a`, no triangle exists if `a ≤ c` and exactly one if `a > c`; counted by the possible third sides `b`
(PC-244). -/
@[kb "stitzzeager2013" "Theorem 11.3, p. 913"]
theorem thm_11_3_ambiguous_case_obtuse {a c α : ℝ} (ha : 0 < a) (hc : 0 < c) (hα0 : π / 2 ≤ α)
    (hα : α < π) :
    (a ≤ c → (ssaSides a c α).ncard = 0) ∧ (c < a → (ssaSides a c α).ncard = 1) := by
  have hk : c * Real.cos α ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le (Real.cos_nonpos_of_pi_div_two_le_of_le hα0 (by linarith))
  have e : (c * Real.cos α) ^ 2 + (c * Real.sin α) ^ 2 = c ^ 2 := by
    have := Real.cos_sq_add_sin_sq α
    calc _ = c ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) := by ring
      _ = c ^ 2 := by rw [this, mul_one]
  have hS : ∀ b, b ∈ ssaSides a c α ↔
      0 < b ∧ (b - c * Real.cos α) ^ 2 = a ^ 2 - (c * Real.sin α) ^ 2 := by
    intro b
    constructor <;> rintro ⟨hb, h⟩ <;> exact ⟨hb, by nlinarith⟩
  generalize c * Real.cos α = k at hk e hS
  generalize c * Real.sin α = h at e hS
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have : ssaSides a c α = ∅ := by
      ext b
      simp only [hS, mem_empty_iff_false, iff_false, not_and]
      intro hb hb2
      -- `(b - k)^2 = a^2 - h^2 ≤ c^2 - h^2 = k^2` with `b - k > -k ≥ 0`
      have h3 : (b - k) ^ 2 ≤ k ^ 2 := by nlinarith
      nlinarith
    rw [this, Set.ncard_empty]
  · have hD : 0 < a ^ 2 - h ^ 2 := by nlinarith
    have hs := Real.sq_sqrt hD.le
    have hs0 := Real.sqrt_pos.2 hD
    have hsk : -k < √(a ^ 2 - h ^ 2) := by nlinarith
    have : ssaSides a c α = {k + √(a ^ 2 - h ^ 2)} := by
      ext b
      rw [hS]
      simp only [mem_singleton_iff]
      constructor
      · rintro ⟨hb0, hb⟩
        have : (b - k) ^ 2 = √(a ^ 2 - h ^ 2) ^ 2 := by rw [hs]; exact hb
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h3 | h3
        · linarith
        · exfalso; linarith
      · rintro rfl
        exact ⟨by linarith, by rw [add_sub_cancel_left, hs]⟩
    rw [this, Set.ncard_singleton]

/-! ### Area of a triangle (Theorems 11.4 and 11.6) -/

/-- The area of the triangle `ABC` in the plane: half the absolute value of the cross product of the
side vectors `B - A` and `C - A`. -/
noncomputable def triangleArea (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)| / 2

private theorem cross_eq_sin (P Q R : EuclideanSpace ℝ (Fin 2)) :
    |(Q 0 - P 0) * (R 1 - P 1) - (R 0 - P 0) * (Q 1 - P 1)| =
      dist P Q * dist P R * Real.sin (∠ Q P R) := by
  have h := InnerProductGeometry.sin_angle_mul_norm_mul_norm (Q -ᵥ P) (R -ᵥ P)
  have e1 : dist P Q = ‖Q -ᵥ P‖ := by rw [dist_comm, dist_eq_norm_vsub]
  have e2 : dist P R = ‖R -ᵥ P‖ := by rw [dist_comm, dist_eq_norm_vsub]
  rw [e1, e2, EuclideanGeometry.angle, mul_comm (‖Q -ᵥ P‖ * ‖R -ᵥ P‖), h, ← Real.sqrt_sq_eq_abs]
  congr 1
  simp only [PiLp.inner_apply, Fin.sum_univ_two, vsub_eq_sub, PiLp.sub_apply, RCLike.inner_apply,
    conj_trivial]
  ring

/-- Area of a triangle: with `a = |BC|`, `b = |CA|`, `c = |AB|` and the angles `α`, `β`, `γ` at `A`, `B`,
`C`, the area is `½ bc sin α = ½ ac sin β = ½ ab sin γ` (PC-245). -/
@[kb "stitzzeager2013" "Theorem 11.4, p. 915"]
theorem thm_11_4_triangle_area (A B C : EuclideanSpace ℝ (Fin 2)) :
    triangleArea A B C = 1 / 2 * dist C A * dist A B * Real.sin (∠ B A C) ∧
      triangleArea A B C = 1 / 2 * dist B C * dist A B * Real.sin (∠ A B C) ∧
      triangleArea A B C = 1 / 2 * dist B C * dist C A * Real.sin (∠ B C A) := by
  have h1 := cross_eq_sin A B C
  have h2 := cross_eq_sin B C A
  have h3 := cross_eq_sin C A B
  have a1 : triangleArea A B C = |(B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)| / 2 := rfl
  have a2 : |(C 0 - B 0) * (A 1 - B 1) - (A 0 - B 0) * (C 1 - B 1)| =
      |(B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)| := by
    congr 1; ring
  have a3 : |(A 0 - C 0) * (B 1 - C 1) - (B 0 - C 0) * (A 1 - C 1)| =
      |(B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)| := by
    congr 1; ring
  rw [a2] at h2
  rw [a3] at h3
  refine ⟨?_, ?_, ?_⟩
  · rw [a1, h1, dist_comm A C]; ring
  · rw [a1, h2, dist_comm B A, EuclideanGeometry.angle_comm C B A]; ring
  · rw [a1, h3, dist_comm C B, EuclideanGeometry.angle_comm A C B]; ring

/-- Heron's formula: a triangle with side lengths `a`, `b`, `c` and semiperimeter `s = (a+b+c)/2`
has area `√(s (s-a) (s-b) (s-c))` (PC-247). -/
@[kb "stitzzeager2013" "Theorem 11.6, p. 926"]
theorem thm_11_6_heron (A B C : EuclideanSpace ℝ (Fin 2)) :
    triangleArea A B C =
      √(((dist B C + dist C A + dist A B) / 2) * ((dist B C + dist C A + dist A B) / 2 - dist B C) *
        ((dist B C + dist C A + dist A B) / 2 - dist C A) *
        ((dist B C + dist C A + dist A B) / 2 - dist A B)) := by
  have sq2 : ∀ P Q : EuclideanSpace ℝ (Fin 2), dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
    intro P Q
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two, Real.dist_eq,
      Real.dist_eq, sq_abs, sq_abs]
  have key : ∀ a b c : ℝ, (a + b + c) / 2 * ((a + b + c) / 2 - a) * ((a + b + c) / 2 - b) *
      ((a + b + c) / 2 - c) =
      (2 * (a ^ 2 * b ^ 2) + 2 * (b ^ 2 * c ^ 2) + 2 * (c ^ 2 * a ^ 2) - (a ^ 2) ^ 2 - (b ^ 2) ^ 2 -
        (c ^ 2) ^ 2) / 16 := fun a b c => by ring
  rw [key, sq2 B C, sq2 C A, sq2 A B]
  have : (2 * (((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2) * ((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2)) +
      2 * (((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2) * ((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2)) +
      2 * (((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2) * ((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2)) -
      (((B 0 - C 0) ^ 2 + (B 1 - C 1) ^ 2)) ^ 2 - (((C 0 - A 0) ^ 2 + (C 1 - A 1) ^ 2)) ^ 2 -
      (((A 0 - B 0) ^ 2 + (A 1 - B 1) ^ 2)) ^ 2) / 16 =
      ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) ^ 2 / 4 := by ring
  rw [this, show ((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) ^ 2 / 4 =
    (((B 0 - A 0) * (C 1 - A 1) - (C 0 - A 0) * (B 1 - A 1)) / 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_div, abs_two]
  rfl

/-! ### Polar coordinates (Section 11.4) -/

/-- The point of the plane with polar coordinates `(r, θ)`: `r` is the directed distance from the pole
and `θ` the angle from the polar axis (the positive `x`-axis), so the rectangular coordinates are
`(r cos θ, r sin θ)`. -/
noncomputable def polarPoint (r θ : ℝ) : ℝ × ℝ := (r * Real.cos θ, r * Real.sin θ)

/-- Polar coordinates: the point `(r, θ)` is at distance `|r|` from the pole; a negative `r` means the
point lies in the direction opposite to the angle, `(-r, θ)` is the reflection of `(r, θ)` in the
pole and equals `(r, θ + π)`; adding a multiple of `2π` to the angle does not change the point; and
`(0, θ)` is the pole (PC-248). -/
@[kb "stitzzeager2013" "§11.4, p. 931"]
theorem box_11_4_polar_coordinates (r θ : ℝ) :
    √((polarPoint r θ).1 ^ 2 + (polarPoint r θ).2 ^ 2) = |r| ∧
      polarPoint (-r) θ = -polarPoint r θ ∧ polarPoint (-r) θ = polarPoint r (θ + π) ∧
      (∀ k : ℤ, polarPoint r (θ + k * (2 * π)) = polarPoint r θ) ∧ polarPoint 0 θ = (0, 0) := by
  refine ⟨?_, ?_, ?_, fun k => ?_, ?_⟩
  · have : (polarPoint r θ).1 ^ 2 + (polarPoint r θ).2 ^ 2 = r ^ 2 := by
      simp only [polarPoint]
      have := Real.cos_sq_add_sin_sq θ
      calc _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
        _ = r ^ 2 := by rw [this, mul_one]
    rw [this, Real.sqrt_sq_eq_abs]
  · simp [polarPoint]
  · simp [polarPoint, Real.cos_add_pi, Real.sin_add_pi]
  · simp [polarPoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  · simp [polarPoint]

private theorem coterminal_aux (α β : ℝ) :
    (Real.cos α = Real.cos β ∧ Real.sin α = Real.sin β) → ∃ k : ℤ, β = α + k * (2 * π) := by
  rintro ⟨hc, hs⟩
  have h1 := Real.sin_sq_add_cos_sq α
  have : Real.cos (β - α) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]; nlinarith
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 this
  exact ⟨k, by linarith⟩

/-- Two polar pairs with nonzero radii name the same point exactly when `(r', θ') = (r, θ + 2πk)` or
`(r', θ') = (-r, θ + (2k + 1)π)` for an integer `k`; and `(r, θ)` is the pole exactly when
`r = 0` (PC-249). -/
@[kb "stitzzeager2013" "§11.4, p. 935"]
theorem box_11_4_same_point (r θ r' θ' : ℝ) (hr : r ≠ 0) (hr' : r' ≠ 0) :
    polarPoint r' θ' = polarPoint r θ ↔
      ∃ k : ℤ, (r' = r ∧ θ' = θ + k * (2 * π)) ∨ (r' = -r ∧ θ' = θ + (2 * k + 1) * π) := by
  constructor
  · intro h
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hsq : r' ^ 2 = r ^ 2 := by
      have e1 := Real.cos_sq_add_sin_sq θ
      have e2 := Real.cos_sq_add_sin_sq θ'
      have : (r' * Real.cos θ') ^ 2 + (r' * Real.sin θ') ^ 2 = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by
        rw [h1, h2]
      calc r' ^ 2 = r' ^ 2 * (Real.cos θ' ^ 2 + Real.sin θ' ^ 2) := by rw [e2, mul_one]
        _ = (r' * Real.cos θ') ^ 2 + (r' * Real.sin θ') ^ 2 := by ring
        _ = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := this
        _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
        _ = r ^ 2 := by rw [e1, mul_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hr2 | hr2
    · rw [hr2] at h1 h2
      have hc : Real.cos θ = Real.cos θ' := (mul_left_cancel₀ hr h1).symm
      have hs : Real.sin θ = Real.sin θ' := (mul_left_cancel₀ hr h2).symm
      obtain ⟨k, hk⟩ := coterminal_aux θ θ' ⟨hc, hs⟩
      exact ⟨k, Or.inl ⟨hr2, hk⟩⟩
    · rw [hr2] at h1 h2
      have hc : Real.cos (θ + π) = Real.cos θ' := by
        rw [Real.cos_add_pi]
        have : -r * Real.cos θ' = -r * (-Real.cos θ) := by rw [h1]; ring
        exact (mul_left_cancel₀ (neg_ne_zero.2 hr) this).symm
      have hs : Real.sin (θ + π) = Real.sin θ' := by
        rw [Real.sin_add_pi]
        have : -r * Real.sin θ' = -r * (-Real.sin θ) := by rw [h2]; ring
        exact (mul_left_cancel₀ (neg_ne_zero.2 hr) this).symm
      obtain ⟨k, hk⟩ := coterminal_aux _ _ ⟨hc, hs⟩
      exact ⟨k, Or.inr ⟨hr2, by linarith⟩⟩
  · rintro ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp [polarPoint, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    · have e : θ + (2 * k + 1) * π = (θ + π) + k * (2 * π) := by ring
      simp [polarPoint, e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi,
        Real.cos_add_pi, Real.sin_add_pi]

/-- A polar pair is the pole exactly when its radius is `0` (the angle is then arbitrary) (PC-249). -/
@[kb "stitzzeager2013" "§11.4, p. 935"]
theorem box_11_4_pole (r θ : ℝ) : polarPoint r θ = (0, 0) ↔ r = 0 := by
  constructor
  · intro h
    simp only [polarPoint, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e := Real.cos_sq_add_sin_sq θ
    have : r ^ 2 = 0 := by
      calc r ^ 2 = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by rw [e, mul_one]
        _ = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by ring
        _ = 0 := by rw [h1, h2]; norm_num
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · rintro rfl; simp [polarPoint]

end UndergradKB.Precalculus.Course
