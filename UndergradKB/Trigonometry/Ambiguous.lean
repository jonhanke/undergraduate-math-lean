import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Triangle
import UndergradKB.Common.Attr

/-! # The ambiguous case SSA (Corral Table 2.1; OpenStax §10.1)

Given two sides `a, b` and the angle `A` opposite `a`, the third side `c` of a triangle with these data
must satisfy the law of cosines `a² = b² + c² - 2bc cos A` and be positive. `ssaSolutions a b A` is the set
of such `c`; its size (0, 1 or 2) is the number of triangles. We solve the quadratic in `c` explicitly
and count the solutions in each case of Corral's table.
-/

namespace UndergradKB.Trigonometry

open Real

/-- The possible third sides `c > 0` of a triangle with sides `a, b` and angle `A` opposite `a`, i.e. the
positive solutions of the law of cosines `a² = b² + c² - 2bc cos A`. (TR-075) -/
def ssaSolutions (a b A : ℝ) : Set ℝ :=
  {c | 0 < c ∧ a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos A}

private lemma mem_iff (a b A c : ℝ) :
    c ∈ ssaSolutions a b A ↔ 0 < c ∧ (c - b * cos A) ^ 2 = a ^ 2 - (b * sin A) ^ 2 := by
  unfold ssaSolutions
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  constructor <;> intro h
  · linear_combination (-1) * h + b ^ 2 * sin_sq_add_cos_sq A
  · linear_combination (-1) * h + b ^ 2 * sin_sq_add_cos_sq A

private lemma sq_eq_iff {D p c : ℝ} (hD : 0 < D) :
    (c - p) ^ 2 = D ↔ c = p - √D ∨ c = p + √D := by
  have hs : √D ^ 2 = D := Real.sq_sqrt hD.le
  rw [show ((c - p) ^ 2 = D) = ((c - p) ^ 2 = √D ^ 2) by rw [hs], sq_eq_sq_iff_eq_or_eq_neg]
  constructor <;> rintro (h | h)
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith

private lemma sin_gt {A : ℝ} (h0 : 0 < A) (h1 : A < π) : 0 < sin A := sin_pos_of_pos_of_lt_pi h0 h1

private lemma sinsq_add (b A : ℝ) : (b * sin A) ^ 2 + (b * cos A) ^ 2 = b ^ 2 := by
  linear_combination b ^ 2 * sin_sq_add_cos_sq A

/-- `a < b sin A`: no triangle (the acute case of the table; the angle plays no further role). (TR-075) -/
theorem ssaSolutions_acute_lt {a b A : ℝ} (h : a < b * sin A)
    (h0 : 0 < a) : ssaSolutions a b A = ∅ := by
  ext c
  simp only [mem_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ e
  nlinarith [sq_nonneg (c - b * cos A), mul_pos h0 h0, mul_pos h0 (by linarith : 0 < b * sin A)]

/-- Acute angle, `a = b sin A`: exactly one (right) triangle, with `c = b cos A`. (TR-075) -/
theorem ssaSolutions_acute_eq {a b A : ℝ} (hb : 0 < b) (h0 : 0 < A) (hA : A < π / 2)
    (h : a = b * sin A) : ssaSolutions a b A = {b * cos A} := by
  have hc : 0 < cos A := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hA⟩
  ext c
  simp only [mem_iff, Set.mem_singleton_iff, h, sub_self]
  constructor
  · rintro ⟨_, e⟩
    have := pow_eq_zero_iff (two_ne_zero) |>.1 e
    linarith
  · rintro rfl
    exact ⟨by positivity, by ring⟩

/-- Acute angle, `b sin A < a < b`: two triangles, `c = b cos A ± √(a² - (b sin A)²)`. (TR-075) -/
theorem ssaSolutions_acute_two {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA : A < π / 2)
    (h1 : b * sin A < a) (h2 : a < b) :
    ssaSolutions a b A =
      {b * cos A - √(a ^ 2 - (b * sin A) ^ 2), b * cos A + √(a ^ 2 - (b * sin A) ^ 2)} := by
  have hc : 0 < cos A := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hA⟩
  have hs := sin_gt hA0 (by linarith)
  have hsb : 0 < b * sin A := by positivity
  have hD : 0 < a ^ 2 - (b * sin A) ^ 2 := by nlinarith
  have hp : 0 < b * cos A := by positivity
  have hlt : √(a ^ 2 - (b * sin A) ^ 2) < b * cos A := by
    rw [Real.sqrt_lt' hp]
    nlinarith [sinsq_add b A]
  ext c
  rw [mem_iff, sq_eq_iff hD]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have := Real.sqrt_nonneg (a ^ 2 - (b * sin A) ^ 2)
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with rfl | rfl <;> linarith

/-- Acute angle, `b sin A < a < b`: exactly two triangles. (TR-075) -/
theorem ncard_ssaSolutions_acute_two {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A)
    (hA : A < π / 2) (h1 : b * sin A < a) (h2 : a < b) : (ssaSolutions a b A).ncard = 2 := by
  have hs := sin_gt hA0 (by linarith)
  have hsb : 0 < b * sin A := by positivity
  have hD : 0 < a ^ 2 - (b * sin A) ^ 2 := by nlinarith
  rw [ssaSolutions_acute_two h0 hb hA0 hA h1 h2]
  apply Set.ncard_pair
  have := Real.sqrt_pos.2 hD
  intro e; linarith

/-- Acute angle, `b ≤ a`: exactly one triangle, `c = b cos A + √(a² - (b sin A)²)`. (TR-075) -/
theorem ssaSolutions_acute_ge {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA : A < π / 2)
    (h : b ≤ a) :
    ssaSolutions a b A = {b * cos A + √(a ^ 2 - (b * sin A) ^ 2)} := by
  have hc : 0 < cos A := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hA⟩
  have hp : 0 < b * cos A := by positivity
  have hD : b * cos A ≤ √(a ^ 2 - (b * sin A) ^ 2) := by
    apply (Real.le_sqrt' hp).2
    nlinarith [sinsq_add b A]
  have hD' : 0 < a ^ 2 - (b * sin A) ^ 2 := by
    have : 0 < √(a ^ 2 - (b * sin A) ^ 2) := by linarith
    exact Real.sqrt_pos.1 this
  ext c
  rw [mem_iff, sq_eq_iff hD']
  simp only [Set.mem_singleton_iff]
  have := Real.sqrt_nonneg (a ^ 2 - (b * sin A) ^ 2)
  constructor
  · rintro ⟨hc0, h | h⟩
    · linarith
    · exact h
  · intro h
    exact ⟨by linarith, Or.inr h⟩

/-- Right or obtuse angle, `a ≤ b`: no triangle. (TR-075) -/
theorem ssaSolutions_obtuse_le {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π)
    (hA : π / 2 ≤ A) (h : a ≤ b) : ssaSolutions a b A = ∅ := by
  have hc : cos A ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hA (by linarith)
  ext c
  simp only [mem_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hc0 e
  have h1 : a ^ 2 ≤ b ^ 2 := by nlinarith
  have h2 : 0 ≤ -(b * cos A) * c := by
    have : 0 ≤ -(b * cos A) := by nlinarith
    positivity
  nlinarith [sinsq_add b A, mul_pos hc0 hc0]

/-- Right or obtuse angle, `b < a`: exactly one triangle, `c = b cos A + √(a² - (b sin A)²)`. (TR-075) -/
theorem ssaSolutions_obtuse_gt {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π)
    (hA : π / 2 ≤ A) (h : b < a) :
    ssaSolutions a b A = {b * cos A + √(a ^ 2 - (b * sin A) ^ 2)} := by
  have hc : cos A ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hA (by linarith)
  have hlt : -(b * cos A) < √(a ^ 2 - (b * sin A) ^ 2) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [sinsq_add b A]
  have hD' : 0 < a ^ 2 - (b * sin A) ^ 2 := by
    have : 0 ≤ -(b * cos A) := by nlinarith
    have : 0 < √(a ^ 2 - (b * sin A) ^ 2) := by linarith
    exact Real.sqrt_pos.1 this
  ext c
  rw [mem_iff, sq_eq_iff hD']
  simp only [Set.mem_singleton_iff]
  have := Real.sqrt_pos.2 hD'
  have hp : b * cos A ≤ 0 := by nlinarith
  constructor
  · rintro ⟨hc0, h | h⟩
    · linarith
    · exact h
  · intro h
    exact ⟨by linarith, Or.inr h⟩

/-- **The ambiguous case (SSA) solution count**: for sides `a, b > 0` and angle `A ∈ (0, π)` opposite `a`,
there are 0, 1 or 2 triangles. For acute `A`: none if `a < b sin A`, one if `a = b sin A`, two if
`b sin A < a < b`, one if `b ≤ a`. For `A ≥ π/2`: none if `a ≤ b`, one if `b < a`. (TR-075) -/
@[kb "corraltrig" "Table 2.1, p. 50"]
theorem ncard_ssaSolutions {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 →
      (a < b * sin A → (ssaSolutions a b A).ncard = 0) ∧
      (a = b * sin A → (ssaSolutions a b A).ncard = 1) ∧
      (b * sin A < a → a < b → (ssaSolutions a b A).ncard = 2) ∧
      (b ≤ a → (ssaSolutions a b A).ncard = 1)) ∧
    (π / 2 ≤ A →
      (a ≤ b → (ssaSolutions a b A).ncard = 0) ∧
      (b < a → (ssaSolutions a b A).ncard = 1)) := by
  refine ⟨fun hA => ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩,
    fun hA => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [ssaSolutions_acute_lt h h0]; simp
  · rw [ssaSolutions_acute_eq hb hA0 hA h]; simp
  · exact ncard_ssaSolutions_acute_two h0 hb hA0 hA h1 h2
  · rw [ssaSolutions_acute_ge h0 hb hA0 hA h]; simp
  · rw [ssaSolutions_obtuse_le h0 hb hA0 hA1 hA h]; simp
  · rw [ssaSolutions_obtuse_gt h0 hb hA0 hA1 hA h]; simp

/-- The same solution count, as in OpenStax §10.1. (TR-075) -/
@[kb "openstaxalgtrig2e" "§10.1 (ambiguous case SSA), p. 883"]
theorem ncard_ssaSolutions' {a b A : ℝ} (h0 : 0 < a) (hb : 0 < b) (hA0 : 0 < A) (hA1 : A < π) :
    (A < π / 2 →
      (a < b * sin A → (ssaSolutions a b A).ncard = 0) ∧
      (a = b * sin A → (ssaSolutions a b A).ncard = 1) ∧
      (b * sin A < a → a < b → (ssaSolutions a b A).ncard = 2) ∧
      (b ≤ a → (ssaSolutions a b A).ncard = 1)) ∧
    (π / 2 ≤ A →
      (a ≤ b → (ssaSolutions a b A).ncard = 0) ∧
      (b < a → (ssaSolutions a b A).ncard = 1)) :=
  ncard_ssaSolutions h0 hb hA0 hA1

section geometry

open EuclideanGeometry
open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In any triangle, the side `c = |P₀P₁|` is an SSA solution for the data `a = |P₁P₂|`, `b = |P₀P₂|` and
the angle at `P₀`, by the law of cosines. (TR-075) -/
theorem dist_mem_ssaSolutions (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (t.points 1) ∈ ssaSolutions (dist (t.points 1) (t.points 2))
      (dist (t.points 0) (t.points 2)) (∠ (t.points 1) (t.points 0) (t.points 2)) := by
  refine ⟨dist_pos.2 fun h => ?_, ?_⟩
  · have := t.independent.injective h
    simp at this
  · have := law_cos (t.points 1) (t.points 0) (t.points 2)
    rw [dist_comm (t.points 1) (t.points 0), dist_comm (t.points 2) (t.points 0)] at this
    nlinarith [this]

end geometry

end UndergradKB.Trigonometry
