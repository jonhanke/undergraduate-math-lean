import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UndergradKB.Common.Attr

/-! # Calculus: arc length and surface area of revolution

OpenStax Calculus 1 §6.4 and Calculus 2 §2.4. Mathlib has no arc length of a graph, so the book's integral is the
bridging definition `arcLength`; its meaning as a supremum of inscribed polygon lengths (the book's motivation) is
proved (`arcLength_isLUB`), and so is invariance under describing the curve as `x = g(y)` (CA-264). Smoothness is
stated as `ContDiff ℝ 1` on all of `ℝ` (the book only needs it on the interval). -/

open Set Real intervalIntegral

namespace UndergradKB.Calculus

/-- Bridging definition (OpenStax Calculus 1:Theorem 6.4): the arc length of the graph of `f` over `[a, b]` is
`∫_a^b √(1 + f'(x)²) dx`. -/
noncomputable def arcLength (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, √(1 + deriv f x ^ 2)

/-- Length of the inscribed polygon of the graph of `f` with vertices at abscissae `x 0, …, x n`. -/
noncomputable def polygonLength (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, √((x (i + 1) - x i) ^ 2 + (f (x (i + 1)) - f (x i)) ^ 2)

/-- Set of lengths of inscribed polygons of the graph of `f` over `[a, b]`. -/
def polygonLengths (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {L | ∃ (n : ℕ) (x : ℕ → ℝ), Monotone x ∧ x 0 = a ∧ x n = b ∧ L = polygonLength f x n}

lemma cauchy_schwarz_sqrt (p q w : ℝ) : p + q * w ≤ √(p ^ 2 + q ^ 2) * √(1 + w ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (p * w - q)]

lemma sqrt_one_add_sq_le (s t : ℝ) : √(1 + s ^ 2) ≤ √(1 + t ^ 2) + |s - t| := by
  have hr : |t| ≤ √(1 + t ^ 2) := Real.abs_le_sqrt (by linarith)
  have hr2 : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have h1 : t * (s - t) ≤ |t| * |s - t| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |t| * |s - t| ≤ √(1 + t ^ 2) * |s - t| := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
  have h3 : |s - t| ^ 2 = (s - t) ^ 2 := sq_abs _
  nlinarith

lemma continuous_arc_integrand {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous fun t => √(1 + deriv f t ^ 2) := by
  have := hf.continuous_deriv le_rfl
  fun_prop

/-- A chord is no longer than the arc over it. -/
lemma chord_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {u v : ℝ} (huv : u ≤ v) :
    √((v - u) ^ 2 + (f v - f u) ^ 2) ≤ ∫ t in u..v, √(1 + deriv f t ^ 2) := by
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hφ := continuous_arc_integrand hf
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hy : f v - f u = ∫ t in u..v, deriv f t :=
    (integral_deriv_eq_sub (fun x _ => hdiff x) (hd.intervalIntegrable _ _)).symm
  set p := v - u with hp
  set q := f v - f u with hq
  set L := √(p ^ 2 + q ^ 2) with hL
  have hL2 : L ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (by positivity)
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hI0 : 0 ≤ ∫ t in u..v, √(1 + deriv f t ^ 2) :=
    integral_nonneg huv (fun t _ => Real.sqrt_nonneg _)
  have key : p ^ 2 + q ^ 2 = ∫ t in u..v, (p + q * deriv f t) := by
    rw [integral_add (by simp) ((hd.intervalIntegrable _ _).const_mul q), integral_const,
      integral_const_mul, ← hy]
    simp only [smul_eq_mul, ← hp]
    ring
  have hle : ∫ t in u..v, (p + q * deriv f t) ≤ ∫ t in u..v, L * √(1 + deriv f t ^ 2) :=
    integral_mono_on huv ((continuous_const.add (continuous_const.mul hd)).intervalIntegrable _ _) ((hφ.intervalIntegrable _ _).const_mul L)
      (fun t _ => cauchy_schwarz_sqrt p q (deriv f t))
  rw [integral_const_mul] at hle
  rcases hL0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hI0
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith

/-- Every inscribed polygon is no longer than the integral `∫ √(1 + f'²)`. -/
lemma polygonLength_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {x : ℕ → ℝ} (hx : Monotone x) (n : ℕ) :
    polygonLength f x n ≤ ∫ t in (x 0)..(x n), √(1 + deriv f t ^ 2) := by
  have hφ := continuous_arc_integrand hf
  rw [← sum_integral_adjacent_intervals (a := fun i => x i) (n := n)
    (fun k _ => hφ.intervalIntegrable _ _)]
  exact Finset.sum_le_sum fun i _ => chord_le hf (hx (Nat.le_succ i))

/-- OpenStax Calculus 1:Theorem 6.5 (CA-264). If `g` is a `C¹` inverse of the `C¹` function `f` with positive
derivative on `[a, b]`, the curve `x = g(y)` over `[f a, f b]` (the same curve as the graph of `f` over `[a, b]`) has
the same length `∫ √(1 + g'(y)²) dy = ∫ √(1 + f'(x)²) dx`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.5, p. 593"]
theorem arcLength_inverse {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {a b : ℝ}
    (hpos : ∀ x ∈ uIcc a b, 0 < deriv f x) (hgf : ∀ x, g (f x) = x) :
    arcLength g (f a) (f b) = arcLength f a b := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hf' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hφ := continuous_arc_integrand hg
  unfold arcLength
  rw [← integral_comp_mul_deriv (f := f) (f' := deriv f) (g := fun y => √(1 + deriv g y ^ 2))
    (fun x _ => (hdf x).hasDerivAt) hf'.continuousOn hφ]
  refine integral_congr fun x hx => ?_
  have hchain : deriv g (f x) * deriv f x = 1 := by
    have h1 := ((hdg (f x)).hasDerivAt).comp x (hdf x).hasDerivAt
    have h2 : HasDerivAt (g ∘ f) 1 x := by
      have : (g ∘ f) = id := funext hgf
      rw [this]; exact hasDerivAt_id x
    exact h1.unique h2
  have hp := hpos x hx
  have hgd : deriv g (f x) = 1 / deriv f x := by
    field_simp; linarith
  simp only [Function.comp]
  rw [hgd]
  generalize deriv f x = p at hp ⊢
  rw [show √(1 + (1 / p) ^ 2) * p = √((1 + (1 / p) ^ 2) * p ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]]
  congr 1
  field_simp
  ring

/-- On a short piece where `f'` varies by less than `ε'`, the arc exceeds the chord by at most `h ε'`. -/
lemma piece_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {u h ε' : ℝ} (hh : 0 < h)
    (hosc : ∀ s ∈ Icc u (u + h), ∀ t ∈ Icc u (u + h), |deriv f s - deriv f t| < ε') :
    ∫ t in u..(u + h), √(1 + deriv f t ^ 2) ≤
      √((u + h - u) ^ 2 + (f (u + h) - f u) ^ 2) + h * ε' := by
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hφ := continuous_arc_integrand hf
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f (deriv f) (show u < u + h by linarith)
    hf.continuous.continuousOn (fun x _ => (hdiff x).hasDerivAt)
  have hcI : c ∈ Icc u (u + h) := ⟨hc.1.le, hc.2.le⟩
  have hq : f (u + h) - f u = deriv f c * h := by
    rw [hcd, show u + h - u = h by ring]; field_simp
  have hchord : √((u + h - u) ^ 2 + (f (u + h) - f u) ^ 2) = h * √(1 + deriv f c ^ 2) := by
    rw [hq, show (u + h - u) ^ 2 + (deriv f c * h) ^ 2 = h ^ 2 * (1 + deriv f c ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hh.le]
  have hle : ∫ t in u..(u + h), √(1 + deriv f t ^ 2) ≤ ∫ t in u..(u + h), (√(1 + deriv f c ^ 2) + ε') :=
    integral_mono_on (by linarith) (hφ.intervalIntegrable _ _) (by simp)
      (fun t ht => by
        have h1 := sqrt_one_add_sq_le (deriv f t) (deriv f c)
        have h2 := hosc t ht c hcI
        linarith)
  rw [hchord]
  refine hle.trans (le_of_eq ?_)
  simp only [integral_const, smul_eq_mul]
  ring

/-- For every `ε > 0` some inscribed polygon is within `ε` of the integral `∫ √(1 + f'²)`. -/
lemma exists_polygon_close {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (x : ℕ → ℝ), Monotone x ∧ x 0 = a ∧ x n = b ∧
      (∫ t in a..b, √(1 + deriv f t ^ 2)) - ε < polygonLength f x n := by
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hφ := continuous_arc_integrand hf
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc a b) hd.continuousOn
  have hε' : 0 < ε / (2 * (b - a)) := by apply div_pos hε; linarith
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / (2 * (b - a))) hε'
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  set h := (b - a) / n with hh
  have hhpos : 0 < h := by apply div_pos <;> linarith
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  refine ⟨n, fun i => a + i * h, ?_, by simp, ?_, ?_⟩
  · intro i j hij
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only
    nlinarith
  · simp only; linarith
  · have hsplit : (∫ t in a..b, √(1 + deriv f t ^ 2)) =
        ∑ i ∈ Finset.range n, ∫ t in (a + i * h)..(a + ((i + 1 : ℕ) : ℝ) * h), √(1 + deriv f t ^ 2) := by
      have := sum_integral_adjacent_intervals (a := fun i : ℕ => a + (i : ℝ) * h) (n := n)
        (f := fun t => √(1 + deriv f t ^ 2)) (μ := MeasureTheory.volume)
        (fun k _ => hφ.intervalIntegrable _ _)
      simp only [Nat.cast_zero, zero_mul, add_zero, hnh] at this
      rw [this]
      congr 1
      ring
    have hpiece : ∀ i ∈ Finset.range n, ∫ t in (a + i * h)..(a + ((i + 1 : ℕ) : ℝ) * h),
        √(1 + deriv f t ^ 2) ≤
        √(((a + ((i + 1 : ℕ) : ℝ) * h) - (a + i * h)) ^ 2 +
          (f (a + ((i + 1 : ℕ) : ℝ) * h) - f (a + i * h)) ^ 2) + h * (ε / (2 * (b - a))) := by
      intro i hi
      have hi' : i < n := Finset.mem_range.1 hi
      have hin : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi'
      have hu : a + (i : ℝ) * h + h = a + ((i + 1 : ℕ) : ℝ) * h := by push_cast; ring
      have hmem : ∀ t ∈ Icc (a + (i : ℝ) * h) (a + (i : ℝ) * h + h), t ∈ Icc a b := by
        intro t ht
        refine ⟨by nlinarith [ht.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)], ?_⟩
        nlinarith [ht.2]
      have := piece_le hf (u := a + (i : ℝ) * h) (h := h) (ε' := ε / (2 * (b - a))) hhpos (by
        intro s hs t ht
        have := hδ' s (hmem s hs) t (hmem t ht) (by
          rw [Real.dist_eq, abs_lt]
          constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2])
        rwa [Real.dist_eq] at this)
      rw [hu] at this
      exact this
    rw [hsplit]
    have := Finset.sum_le_sum hpiece
    rw [Finset.sum_add_distrib] at this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have e : (n : ℝ) * (h * (ε / (2 * (b - a)))) = ε / 2 := by
      rw [← mul_assoc, hnh]; field_simp
    unfold polygonLength
    simp only
    linarith

/-- OpenStax Calculus 1:Theorem 6.4 (CA-263), the book's motivation made precise. For `f` with continuous derivative
on `[a, b]` (`a < b`), the integral `∫_a^b √(1 + f'²)` is the least upper bound of the lengths of the polygons
inscribed in the graph: no inscribed polygon is longer, and some are arbitrarily close. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.4, p. 591"]
theorem arcLength_isLUB {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) :
    IsLUB (polygonLengths f a b) (arcLength f a b) := by
  constructor
  · rintro L ⟨n, x, hx, h0, hn, rfl⟩
    have := polygonLength_le hf hx n
    rwa [h0, hn] at this
  · intro B hB
    by_contra hlt
    have hlt' : B < arcLength f a b := not_le.1 hlt
    obtain ⟨n, x, hx, h0, hn, hlen⟩ := exists_polygon_close hf hab (sub_pos.2 hlt')
    have := hB ⟨n, x, hx, h0, hn, rfl⟩
    rw [show arcLength f a b = ∫ x in a..b, √(1 + deriv f x ^ 2) from rfl] at hlen
    linarith

/-- OpenStax Calculus 1:Theorem 6.4 (CA-263): the arc length is the supremum of inscribed polygon lengths. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.4, p. 591"]
theorem arcLength_eq_sSup {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) :
    arcLength f a b = sSup (polygonLengths f a b) :=
  ((arcLength_isLUB hf hab).csSup_eq
    ⟨_, 1, fun i => a + i * (b - a), fun i j hij => by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      simp only
      nlinarith, by simp, by simp, rfl⟩).symm

/-- Lateral area `π r s` of a right circular cone of base radius `r` and slant height `s` (OpenStax Calculus 1:§6.4,
recalled by the book as known). -/
noncomputable def coneLateralArea (r s : ℝ) : ℝ := π * r * s

/-- OpenStax Calculus 1:§6.4 lateral area of a frustum (CA-266). A frustum with end radii `r₁ ≤ r₂` and slant
height `s` is a cone of slant `s₁ + s` and radius `r₂` with the cone of slant `s₁` and radius `r₁` cut off, the two
being similar (`r₁ (s₁ + s) = r₂ s₁`); its lateral area is `π (r₁ + r₂) s`. -/
@[kb "openstaxcalculus2016" "1:§6.4 lateral area of frustum, p. 596"]
theorem frustum_lateralArea {r₁ r₂ s₁ s : ℝ} (hsim : r₁ * (s₁ + s) = r₂ * s₁) :
    coneLateralArea r₂ (s₁ + s) - coneLateralArea r₁ s₁ = π * (r₁ + r₂) * s := by
  unfold coneLateralArea
  linear_combination (-π) * hsim

/-- Bridging definition (OpenStax Calculus 1:Theorem 6.6): surface area of the solid obtained by revolving the graph
of `f` over `[a, b]` about the `x`-axis, `2π ∫ f √(1 + f'²)`. -/
noncomputable def surfaceArea (f : ℝ → ℝ) (a b : ℝ) : ℝ := 2 * π * ∫ x in a..b, f x * √(1 + deriv f x ^ 2)

/-- OpenStax Calculus 1:Theorem 6.6 (CA-267), consistency check (the theorem itself is the definition `surfaceArea`).
Revolving `y = r x / h` over `[0, h]` gives the cone of slant height `√(h² + r²)` and lateral area `π r s`. -/
@[kb "openstaxcalculus2016" "1:Theorem 6.6, p. 597"]
theorem surfaceArea_cone {r h : ℝ} (hh : 0 < h) :
    surfaceArea (fun x => r * x / h) 0 h = coneLateralArea r (√(h ^ 2 + r ^ 2)) := by
  have hd : ∀ x : ℝ, deriv (fun x => r * x / h) x = r / h := by
    intro x
    have : HasDerivAt (fun x => r * x / h) (r / h) x := by
      simpa using ((hasDerivAt_id x).const_mul r).div_const h
    exact this.deriv
  simp only [surfaceArea, hd, coneLateralArea]
  have e1 : ∀ x : ℝ, r * x / h * √(1 + (r / h) ^ 2) = (r / h * √(1 + (r / h) ^ 2)) * x := fun x => by ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, integral_id]
  have hs : √(h ^ 2 + r ^ 2) = h * √(1 + (r / h) ^ 2) := by
    rw [show h ^ 2 + r ^ 2 = h ^ 2 * (1 + (r / h) ^ 2) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hh.le]
  rw [hs]
  field_simp
  ring

end UndergradKB.Calculus
