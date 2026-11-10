import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import UndergradKB.Common.Attr

/-! Plane sections of the double cone `x² + y² = z²` by the plane `z = m x + d`
(OpenStax Calculus Volume 2, §7.5). -/

namespace UndergradKB.Calculus.ConeSections

/-- The point `(x, y, z)` lies on the double cone `x² + y² = z²` and on the plane
`z = m x + d`. -/
def OnConeSection (m d x y z : ℝ) : Prop := x ^ 2 + y ^ 2 = z ^ 2 ∧ z = m * x + d

/-- The projection of the section to the `xy`-plane is the curve
`(1 - m²) x² - 2 m d x + y² - d² = 0`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_projection (m d x y : ℝ) :
    (∃ z, OnConeSection m d x y z) ↔ (1 - m ^ 2) * x ^ 2 - 2 * m * d * x + y ^ 2 - d ^ 2 = 0 := by
  constructor
  · rintro ⟨z, h1, h2⟩
    subst h2
    linear_combination h1
  · intro h
    exact ⟨m * x + d, by linear_combination h, rfl⟩

/-- Key identity for the ellipse and hyperbola forms. -/
lemma cone_section_key (m d x y : ℝ) (hu : 1 - m ^ 2 ≠ 0) (hd : d ≠ 0) :
    (x - m * d / (1 - m ^ 2)) ^ 2 / (d / (1 - m ^ 2)) ^ 2 + y ^ 2 / (d ^ 2 / (1 - m ^ 2)) - 1
      = (1 - m ^ 2) * ((1 - m ^ 2) * x ^ 2 - 2 * m * d * x + y ^ 2 - d ^ 2) / d ^ 2 := by
  field_simp
  ring

/-- OpenStax Calculus 2:§7.5 (CA-409), ellipse. For `|m| < 1`, `d ≠ 0` the projected section is the
ellipse `(x - x₀)²/a² + y²/b² = 1` with `x₀ = m d/(1-m²)`, `a = d/(1-m²)`, `b² = d²/(1-m²)`
(a circle `x² + y² = d²` when `m = 0`). -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_ellipse (m d : ℝ) (hm : |m| < 1) (hd : d ≠ 0) (x y : ℝ) :
    (∃ z, OnConeSection m d x y z) ↔
      (x - m * d / (1 - m ^ 2)) ^ 2 / (d / (1 - m ^ 2)) ^ 2 + y ^ 2 / (d ^ 2 / (1 - m ^ 2)) = 1 := by
  have hm2 : m ^ 2 < 1 := by
    have := sq_lt_one_iff_abs_lt_one m |>.mpr hm
    exact this
  have hu : 1 - m ^ 2 ≠ 0 := by linarith
  rw [cone_section_projection, ← sub_eq_zero (a := _ + _), cone_section_key m d x y hu hd]
  simp [hu, hd]

/-- OpenStax Calculus 2:§7.5 (CA-409), hyperbola. For `|m| > 1`, `d ≠ 0` the projected section is the
hyperbola `(x - x₀)²/a² - y²/b² = 1` with `x₀ = m d/(1-m²)`, `a = d/(1-m²)`, `b² = d²/(m²-1)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_hyperbola (m d : ℝ) (hm : 1 < |m|) (hd : d ≠ 0) (x y : ℝ) :
    (∃ z, OnConeSection m d x y z) ↔
      (x - m * d / (1 - m ^ 2)) ^ 2 / (d / (1 - m ^ 2)) ^ 2 - y ^ 2 / (d ^ 2 / (m ^ 2 - 1)) = 1 := by
  have hm2 : 1 < m ^ 2 := by
    have := one_lt_sq_iff_one_lt_abs m |>.mpr hm
    exact this
  have hu : 1 - m ^ 2 ≠ 0 := by linarith
  have hu' : m ^ 2 - 1 ≠ 0 := by linarith
  have e : y ^ 2 / (d ^ 2 / (m ^ 2 - 1)) = -(y ^ 2 / (d ^ 2 / (1 - m ^ 2))) := by
    field_simp
    ring
  rw [cone_section_projection, e, sub_neg_eq_add, ← sub_eq_zero (a := _ + _),
    cone_section_key m d x y hu hd]
  simp [hu, hd]

/-- OpenStax Calculus 2:§7.5 (CA-409), parabola. For `|m| = 1`, `d ≠ 0` (plane parallel to a
generating line) the projected section is the parabola `x = (y² - d²)/(2 m d)`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_parabola (m d : ℝ) (hm : |m| = 1) (hd : d ≠ 0) (x y : ℝ) :
    (∃ z, OnConeSection m d x y z) ↔ x = (y ^ 2 - d ^ 2) / (2 * m * d) := by
  have hm2 : m ^ 2 = 1 := by
    have := sq_abs m
    rw [hm] at this; linarith
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm2
  rw [cone_section_projection, eq_div_iff (by positivity)]
  constructor
  · intro h; linear_combination (-1 : ℝ) * h - (x ^ 2) * hm2
  · intro h; linear_combination (-1 : ℝ) * h - (x ^ 2) * hm2

/-- OpenStax Calculus 2:§7.5 (CA-409), circle. A plane perpendicular to the axis (`m = 0`,
`d ≠ 0`) cuts the cone in the circle `x² + y² = d²`. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_circle (d x y : ℝ) :
    (∃ z, OnConeSection 0 d x y z) ↔ x ^ 2 + y ^ 2 = d ^ 2 := by
  rw [cone_section_projection]
  constructor <;> intro h <;> linear_combination h

/-- On the section, `z ≠ 0` when `d ≠ 0` (the plane misses the vertex). -/
lemma cone_section_z_ne_zero {m d x y z : ℝ} (hd : d ≠ 0) (h : OnConeSection m d x y z) :
    z ≠ 0 := by
  rintro rfl
  obtain ⟨h1, h2⟩ := h
  have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  apply hd
  rw [hx] at h2
  linarith

/-- For `|m| ≤ 1` the sign of `z` on the section equals the sign of `d`. -/
lemma cone_section_sign {m d x y z : ℝ} (hm : |m| ≤ 1) (h : OnConeSection m d x y z) :
    ¬ (0 < z ∧ d < 0) ∧ ¬ (z < 0 ∧ 0 < d) := by
  obtain ⟨h1, h2⟩ := h
  have hm2 : m ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one m |>.mpr hm
    exact this
  have hmx : (m * x) ^ 2 ≤ z ^ 2 := by
    rw [← h1]
    have : (m * x) ^ 2 = m ^ 2 * x ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg x, sq_nonneg y, mul_le_mul_of_nonneg_right hm2 (sq_nonneg x)]
  constructor
  · rintro ⟨hz, hd⟩
    have : m * x ≤ z := by nlinarith [abs_le_of_sq_le_sq' hmx hz.le]
    linarith
  · rintro ⟨hz, hd⟩
    have h3 : (m * x) ^ 2 ≤ (-z) ^ 2 := by rw [neg_sq]; exact hmx
    have := abs_le_of_sq_le_sq' h3 (by linarith : 0 ≤ -z)
    linarith [this.1]

/-- OpenStax Calculus 2:§7.5 (CA-409). The plane `z = m x + d` (`d ≠ 0`) meets both nappes of the
cone (contains points with `z > 0` and points with `z < 0`) exactly when `|m| > 1`, that is
exactly when the section is a hyperbola. -/
@[kb "openstaxcalculus2016" "2:§7.5 Conic sections as plane sections of a cone, p. 600"]
theorem cone_section_both_nappes (m d : ℝ) (hd : d ≠ 0) :
    ((∃ x y z, OnConeSection m d x y z ∧ 0 < z) ∧ (∃ x y z, OnConeSection m d x y z ∧ z < 0))
      ↔ 1 < |m| := by
  constructor
  · rintro ⟨⟨x, y, z, h, hz⟩, ⟨x', y', z', h', hz'⟩⟩
    by_contra hm
    have hm := not_lt.mp hm
    obtain ⟨a1, a2⟩ := cone_section_sign hm h
    obtain ⟨b1, b2⟩ := cone_section_sign hm h'
    rcases lt_or_gt_of_ne hd with hd' | hd'
    · exact a1 ⟨hz, hd'⟩
    · exact b2 ⟨hz', hd'⟩
  · intro hm
    have hm2 : 1 < m ^ 2 := (one_lt_sq_iff_one_lt_abs m).mpr hm
    have h1 : 1 - m ≠ 0 := by
      intro h; have : m = 1 := by linarith
      rw [this] at hm2; norm_num at hm2
    have h2 : 1 + m ≠ 0 := by
      intro h; have : m = -1 := by linarith
      rw [this] at hm2; norm_num at hm2
    have p1 : OnConeSection m d (d / (1 - m)) 0 (d / (1 - m)) := by
      constructor
      · ring
      · field_simp; ring
    have p2 : OnConeSection m d (-d / (1 + m)) 0 (d / (1 + m)) := by
      constructor
      · field_simp; ring
      · field_simp; ring
    have hprod : d / (1 - m) * (d / (1 + m)) < 0 := by
      rw [div_mul_div_comm]
      apply div_neg_of_pos_of_neg (mul_self_pos.mpr hd)
      nlinarith
    rcases lt_or_gt_of_ne (cone_section_z_ne_zero hd p1) with hz | hz
    · refine ⟨⟨_, _, _, p2, ?_⟩, ⟨_, _, _, p1, hz⟩⟩
      nlinarith
    · refine ⟨⟨_, _, _, p1, hz⟩, ⟨_, _, _, p2, ?_⟩⟩
      nlinarith

end UndergradKB.Calculus.ConeSections
