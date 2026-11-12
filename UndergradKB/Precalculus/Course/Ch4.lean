import Mathlib.Analysis.Polynomial.Basic
import UndergradKB.Common.Attr

/-! # Course layer, Chapter 4 (Stitz-Zeager): rational functions -/

namespace UndergradKB.Precalculus.Course

open Polynomial Filter Topology

/-- Theorem 4.2 (equal degrees): if `p` and `q` have the same degree with leading coefficients `a` and `b`, then
`p(x)/q(x)` tends to `a/b` as `x → ∞` and as `x → -∞`, so `y = a/b` is a horizontal asymptote (PC-076). -/
@[kb "stitzzeager2013" "Theorem 4.2, p. 320"]
theorem thm_4_2_horizontal_asymptote_equal_degree (p q : ℝ[X]) (h : p.degree = q.degree) :
    Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 (p.leadingCoeff / q.leadingCoeff)) ∧
    Tendsto (fun x => p.eval x / q.eval x) atBot (𝓝 (p.leadingCoeff / q.leadingCoeff)) :=
  ⟨p.div_tendsto_atTop_leadingCoeff_div_of_degree_eq q h,
   p.div_tendsto_atBot_leadingCoeff_div_of_degree_eq q h⟩

/-- Theorem 4.2 (smaller numerator degree): if `deg p < deg q`, then `p(x)/q(x)` tends to `0` as `x → ±∞`, so `y = 0`
is a horizontal asymptote (PC-076). -/
@[kb "stitzzeager2013" "Theorem 4.2, p. 320"]
theorem thm_4_2_horizontal_asymptote_numerator_smaller (p q : ℝ[X]) (h : p.degree < q.degree) :
    Tendsto (fun x => p.eval x / q.eval x) atTop (𝓝 0) ∧
    Tendsto (fun x => p.eval x / q.eval x) atBot (𝓝 0) :=
  ⟨p.div_tendsto_atTop_zero_of_degree_lt q h, p.div_tendsto_atBot_zero_of_degree_lt q h⟩

/-- Theorem 4.2 (larger numerator degree): if `deg p > deg q` (with `q ≠ 0`), then `|p(x)/q(x)|` grows without bound
as `x → ±∞`, so there is no horizontal asymptote (PC-076). -/
@[kb "stitzzeager2013" "Theorem 4.2, p. 320"]
theorem thm_4_2_no_horizontal_asymptote_numerator_larger (p q : ℝ[X]) (h : q.degree < p.degree) (hq : q ≠ 0) :
    Tendsto (fun x => |p.eval x / q.eval x|) atTop atTop ∧
    Tendsto (fun x => |p.eval x / q.eval x|) atBot atTop :=
  ⟨p.abs_div_tendsto_atTop_atTop_of_degree_gt q h hq, p.abs_div_tendsto_atBot_atTop_of_degree_gt q h hq⟩

end UndergradKB.Precalculus.Course
