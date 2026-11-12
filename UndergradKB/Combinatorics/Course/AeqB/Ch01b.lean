import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Incenter
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Totient
import UndergradKB.Combinatorics.Counting.Basic
import UndergradKB.Combinatorics.Counting.Misc
import UndergradKB.Combinatorics.AeqB.Background
import UndergradKB.Combinatorics.AeqB.Incenter
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 1: course wrappers of results proved in this library (wave 3)
-/

open Finset EuclideanGeometry

namespace UndergradKB.Combinatorics.Course.AeqB.Ch01b

/-- CO-543. A canonical form is a one-to-one description `c`, so `A = B` iff `c A = c B`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) canonical form, p. 18"]
theorem def_p18_canonical_form {α β : Type*} {c : α → β}
    (hc : UndergradKB.Combinatorics.AeqB.IsCanonicalForm c) (A B : α) :
    A = B ↔ c A = c B :=
  hc.eq_iff A B

/-- CO-544. With a normal form, equality of two objects reduces to testing whether the
difference of their names represents zero. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) normal form, p. 18"]
theorem def_p18_normal_form {G : Type*} [AddGroup G]
    (N : UndergradKB.Combinatorics.AeqB.NormalForm G) (a b : N.Name) :
    N.val a = N.val b ↔ N.isZero (N.sub a b) = true :=
  N.val_eq_iff a b

/-- CO-345. `((a+b)/2)^2 - ab = ((a-b)/2)^2`, which gives the AM-GM inequality for two numbers. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 1.3.1, p. 19"]
theorem eq_1_3_1_amgm :
    (∀ {R : Type*} [Field R] [CharZero R] (a b : R),
      ((a + b) / 2) ^ 2 - a * b = ((a - b) / 2) ^ 2) ∧
    (∀ a b : ℝ, a * b ≤ ((a + b) / 2) ^ 2) ∧
    (∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → Real.sqrt (a * b) ≤ (a + b) / 2) :=
  ⟨fun a b => sq_avg_sub_mul_eq_sq_half_diff a b, mul_le_sq_avg, sqrt_mul_le_avg⟩

/-- CO-068. The sum of the first `n` cubes is `(n(n+1)/2)^2`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 1.4.1, p. 20"]
theorem thm_1_4_1_sum_cubes (n : ℕ) : ∑ i ∈ Icc 1 n, i ^ 3 = (n * (n + 1) / 2) ^ 2 :=
  sum_cubes n

/-- CO-348. The three angle bisectors of a triangle are concurrent (the incenter). -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 1.4.2, p. 20"]
theorem thm_1_4_2_angle_bisectors_concurrent
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    ∃ I : P, I ∈ t.interior ∧ ∀ i₁ i₂ i₃ : Fin 3, i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
      ∠ (t.points i₂) (t.points i₁) I = ∠ (t.points i₂) (t.points i₁) (t.points i₃) / 2 ∧
      ∠ (t.points i₂) (t.points i₁) I = ∠ I (t.points i₁) (t.points i₃) :=
  UndergradKB.Combinatorics.AeqB.angle_bisectors_concurrent t

/-- CO-069. `∑_{i=1}^n q i = p n` for all `n` iff `p n - p (n-1) = q n` for `n ≥ 1` and `p 0 = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 21"]
theorem text_p21_sum_eq_iff_telescoping {G : Type*} [AddCommGroup G] (p q : ℕ → G) :
    (∀ n, ∑ i ∈ Icc 1 n, q i = p n) ↔ (p 0 = 0 ∧ ∀ n, 1 ≤ n → p n - p (n - 1) = q n) :=
  sum_eq_iff_telescoping p q

/-- CO-532. `arcsin x + arcsin y = arcsin (x √(1-y²) + y √(1-x²))` under the sign or size
condition on `x, y`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 1.5.1, p. 22"]
theorem ex_1_5_1_arcsin_add_arcsin {x y : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (hy1 : -1 ≤ y)
    (hy2 : y ≤ 1) (h : x * y ≤ 0 ∨ x ^ 2 + y ^ 2 ≤ 1) :
    Real.arcsin x + Real.arcsin y =
      Real.arcsin (x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2)) :=
  arcsin_add_arcsin hx1 hx2 hy1 hy2 h

/-- CO-349. `(∑ a_i)^2 = ∑ a_i^2 + 2 ∑_{i<j} a_i a_j`, i.e. `p₁² = p₂ + 2 e₂`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 23"]
theorem text_p23_sq_sum {R : Type*} [CommRing R] (a : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, a i) ^ 2 =
      ∑ i ∈ range n, a i ^ 2 + 2 * ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, a i * a j :=
  sq_sum_eq_sum_sq_add_two_mul a n

/-- CO-347. Lagrange identity; its `n = 2` case is the two-dimensional Cauchy-Schwarz inequality. -/
@[kb "petkovsekwilfzeilberger1996" "Equation 1.7.1, p. 24"]
theorem eq_1_7_1_lagrange_identity {R : Type*} [CommRing R] (a b : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, a i ^ 2) * (∑ i ∈ range n, b i ^ 2) - (∑ i ∈ range n, a i * b i) ^ 2 =
      ∑ i ∈ range n, ∑ j ∈ Ico (i + 1) n, (a i * b j - a j * b i) ^ 2 :=
  lagrange_identity a b n

end UndergradKB.Combinatorics.Course.AeqB.Ch01b
