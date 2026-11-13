import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common.Attr

/-!
# Sign diagrams (Stitz-Zeager, Precalculus, Sections 3.1 and 4.2)

The book's procedure for a sign diagram (choose one test value in each interval cut out by the zeros, and, for a
rational function, by the excluded values) rests on one fact, which the book draws from the Intermediate Value
Theorem: on an interval containing no zero (and no excluded value), the function has one constant sign. Proved
here for continuous functions on order-connected sets (intervals of every kind), then for polynomial functions
(Section 3.1, box "Steps for Constructing a Sign Diagram for a Polynomial Function") and rational functions
(Section 4.2, box "Steps for Constructing a Sign Diagram for a Rational Function").
-/

namespace UndergradKB.Precalculus

open Polynomial Set

/-- A function continuous on an interval `I` and nonzero at every point of `I` has the same sign at any two
points of `I`. -/
theorem sign_eq_of_continuousOn_ne_zero {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hf : ContinuousOn f I) (hz : ∀ x ∈ I, f x ≠ 0) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    SignType.sign (f x) = SignType.sign (f y) := by
  have hsub : uIcc x y ⊆ I := hI.uIcc_subset hx hy
  have hivt := intermediate_value_uIcc (hf.mono hsub)
  have key : ¬ (f x < 0 ∧ 0 < f y) ∧ ¬ (0 < f x ∧ f y < 0) := by
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz', hz0⟩ := hivt (Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩))
      exact hz z (hsub hz') hz0
    · rintro ⟨h1, h2⟩
      obtain ⟨z, hz', hz0⟩ := hivt (Set.mem_uIcc.2 (Or.inr ⟨h2.le, h1.le⟩))
      exact hz z (hsub hz') hz0
  have hx0 := hz x hx
  have hy0 := hz y hy
  rcases lt_or_gt_of_ne hx0 with h1 | h1 <;> rcases lt_or_gt_of_ne hy0 with h2 | h2
  · rw [sign_neg h1, sign_neg h2]
  · exact absurd ⟨h1, h2⟩ key.1
  · exact absurd ⟨h1, h2⟩ key.2
  · rw [sign_pos h1, sign_pos h2]

/-- Sign diagrams for polynomial functions (Section 3.1): a polynomial function has one constant sign on any
interval that contains none of its zeros, so the sign at one test value is the sign on the whole interval
(PC-295). -/
@[kb "stitzzeager2013" "§3.1, p. 254"]
theorem sign_diagram_polynomial (p : ℝ[X]) {I : Set ℝ} (hI : I.OrdConnected)
    (hz : ∀ x ∈ I, p.eval x ≠ 0) {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    SignType.sign (p.eval x) = SignType.sign (p.eval t) :=
  sign_eq_of_continuousOn_ne_zero hI p.continuous.continuousOn hz hx ht

/-- The same, in the form used for the diagram: if the test value `t` gives `p(t) > 0` (resp. `< 0`), then
`p(x) > 0` (resp. `< 0`) on the whole interval. -/
@[kb "stitzzeager2013" "§3.1, p. 254"]
theorem sign_diagram_polynomial_test_value (p : ℝ[X]) {I : Set ℝ} (hI : I.OrdConnected)
    (hz : ∀ x ∈ I, p.eval x ≠ 0) {t : ℝ} (ht : t ∈ I) :
    (0 < p.eval t → ∀ x ∈ I, 0 < p.eval x) ∧ (p.eval t < 0 → ∀ x ∈ I, p.eval x < 0) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := sign_diagram_polynomial p hI hz hx ht
    rw [sign_pos h, sign_eq_one_iff] at this
    exact this
  · have := sign_diagram_polynomial p hI hz hx ht
    rw [sign_neg h, sign_eq_neg_one_iff] at this
    exact this

/-- Between two consecutive zeros `a < b` of a polynomial (no zero in `(a, b)`), the polynomial has one sign. -/
@[kb "stitzzeager2013" "§3.1, p. 254"]
theorem sign_diagram_polynomial_between (p : ℝ[X]) {a b : ℝ} (hz : ∀ x ∈ Ioo a b, p.eval x ≠ 0)
    {x t : ℝ} (hx : x ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    SignType.sign (p.eval x) = SignType.sign (p.eval t) :=
  sign_diagram_polynomial p ordConnected_Ioo hz hx ht

/-- Sign diagrams for rational functions (Section 4.2): if `r(x) = p(x)/q(x)` and an interval contains no value
excluded from the domain (`q(x) = 0`) and no zero of `r`, then `r` has one constant sign on it, so the sign at one
test value is the sign on the whole interval (PC-296). -/
@[kb "stitzzeager2013" "§4.2, p. 333"]
theorem sign_diagram_rational (p q : ℝ[X]) {I : Set ℝ} (hI : I.OrdConnected)
    (hq : ∀ x ∈ I, q.eval x ≠ 0) (hz : ∀ x ∈ I, p.eval x / q.eval x ≠ 0) {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    SignType.sign (p.eval x / q.eval x) = SignType.sign (p.eval t / q.eval t) := by
  have hc : ContinuousOn (fun x => p.eval x / q.eval x) I :=
    p.continuous.continuousOn.div q.continuous.continuousOn hq
  exact sign_eq_of_continuousOn_ne_zero hI hc hz hx ht

/-- The test-value form for rational functions. -/
@[kb "stitzzeager2013" "§4.2, p. 333"]
theorem sign_diagram_rational_test_value (p q : ℝ[X]) {I : Set ℝ} (hI : I.OrdConnected)
    (hq : ∀ x ∈ I, q.eval x ≠ 0) (hz : ∀ x ∈ I, p.eval x / q.eval x ≠ 0) {t : ℝ} (ht : t ∈ I) :
    (0 < p.eval t / q.eval t → ∀ x ∈ I, 0 < p.eval x / q.eval x) ∧
      (p.eval t / q.eval t < 0 → ∀ x ∈ I, p.eval x / q.eval x < 0) := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := sign_diagram_rational p q hI hq hz hx ht
    rw [sign_pos h, sign_eq_one_iff] at this
    exact this
  · have := sign_diagram_rational p q hI hq hz hx ht
    rw [sign_neg h, sign_eq_neg_one_iff] at this
    exact this

end UndergradKB.Precalculus
