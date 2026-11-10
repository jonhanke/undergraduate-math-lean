import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Filter Finset Topology FormalMultilinearSeries
open scoped ENNReal NNReal Nat

private theorem norm_ofScalars_real' (c : ℕ → ℝ) (n : ℕ) : ‖ofScalars ℝ c n‖ = |c n| := by
  rw [ofScalars_norm, Real.norm_eq_abs]

/-! ## Algebra of power series -/

/-- OpenStax Calculus 2:Theorem 6.2 (CA-365). Algebra of convergent power series on a common set `I`: if
`∑ c n xⁿ → f x` and `∑ d n xⁿ → g x` for `x ∈ I` (convergence of partial sums), then the sum series converges
to `f x + g x`, the series `∑ c n b x^(n+m)` converges to `b xᵐ f x`, and `∑ c n (b xᵐ)ⁿ` converges to
`f (b xᵐ)` whenever `b xᵐ ∈ I`. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.2, p. 489"]
theorem power_series_algebra {c d : ℕ → ℝ} {f g : ℝ → ℝ} {I : Set ℝ}
    (hf : ∀ x ∈ I, Tendsto (fun n => ∑ i ∈ range n, c i * x ^ i) atTop (𝓝 (f x)))
    (hg : ∀ x ∈ I, Tendsto (fun n => ∑ i ∈ range n, d i * x ^ i) atTop (𝓝 (g x))) (b : ℝ) (m : ℕ) :
    (∀ x ∈ I, Tendsto (fun n => ∑ i ∈ range n, (c i + d i) * x ^ i) atTop (𝓝 (f x + g x))) ∧
    (∀ x ∈ I, Tendsto (fun n => ∑ i ∈ range n, c i * b * x ^ (i + m)) atTop (𝓝 (b * x ^ m * f x))) ∧
    (∀ x : ℝ, b * x ^ m ∈ I →
      Tendsto (fun n => ∑ i ∈ range n, c i * (b * x ^ m) ^ i) atTop (𝓝 (f (b * x ^ m)))) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => hf _ hx⟩
  · refine ((hf x hx).add (hg x hx)).congr fun n => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine ((hf x hx).const_mul (b * x ^ m)).congr fun n => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- OpenStax Calculus 2:Theorem 6.3 (CA-366). Product of power series (Cauchy product): if `∑ a n xⁿ` and
`∑ b n xⁿ` converge absolutely, then `∑ (∑_{k ≤ n} a k b (n-k)) xⁿ` converges to the product of the two sums. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.3, p. 495"]
theorem power_series_product {a b : ℕ → ℝ} {x : ℝ} (ha : Summable fun n => |a n * x ^ n|)
    (hb : Summable fun n => |b n * x ^ n|) :
    HasSum (fun n => (∑ k ∈ range (n + 1), a k * b (n - k)) * x ^ n)
      ((∑' n, a n * x ^ n) * ∑' n, b n * x ^ n) := by
  have ha' : Summable fun n => ‖a n * x ^ n‖ := by simpa using ha
  have hb' : Summable fun n => ‖b n * x ^ n‖ := by simpa using hb
  have hs := summable_norm_sum_mul_range_of_summable_norm ha' hb'
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha' hb']
  have e : ∀ n, ∑ k ∈ range (n + 1), (a k * x ^ k) * (b (n - k) * x ^ (n - k)) =
      (∑ k ∈ range (n + 1), a k * b (n - k)) * x ^ n := fun n => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc a k * x ^ k * (b (n - k) * x ^ (n - k)) = a k * b (n - k) * (x ^ k * x ^ (n - k)) := by ring
      _ = a k * b (n - k) * x ^ n := by rw [← pow_add, Nat.add_sub_cancel' this]
  have hsum := hs.of_norm
  simp_rw [e] at hsum ⊢
  exact hsum.hasSum

/-- OpenStax Calculus 2:Theorem 6.3 (CA-366). Inside the radii of convergence of both series (`|x| < R`),
the Cauchy product of the two power series converges to the product of their sums. -/
@[kb "openstaxcalculus2016" "2:Theorem 6.3, p. 495"]
theorem power_series_product_of_lt_radius {a b : ℕ → ℝ} {x : ℝ}
    (hxa : (‖x‖₊ : ℝ≥0∞) < (ofScalars ℝ a).radius) (hxb : (‖x‖₊ : ℝ≥0∞) < (ofScalars ℝ b).radius) :
    HasSum (fun n => (∑ k ∈ range (n + 1), a k * b (n - k)) * x ^ n)
      ((∑' n, a n * x ^ n) * ∑' n, b n * x ^ n) := by
  refine power_series_product ?_ ?_
  · have := (ofScalars ℝ a).summable_norm_mul_pow hxa
    simpa [norm_ofScalars_real', abs_mul, abs_pow] using this
  · have := (ofScalars ℝ b).summable_norm_mul_pow hxb
    simpa [norm_ofScalars_real', abs_mul, abs_pow] using this

end UndergradKB.Calculus
