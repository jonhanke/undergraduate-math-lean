import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import UndergradKB.Common.Attr

/-!
# The course results of Lebl, chapters 1-4, in the book's form

Mathlib has every result of this file; the statements here are thin wrappers that restate them in the form of
J. Lebl, *Basic Analysis I* (`lebl2026`): real numbers, sequences indexed by `ℕ` with `Filter.Tendsto … atTop`,
functions on closed intervals `[a, b]` with `ContinuousOn` and `DifferentiableOn`, epsilon-delta where the book uses
it. They are the results the calculus, trigonometry and geometry courses rely on: the least-upper-bound property and
its consequences, limits of sequences, monotone convergence, Bolzano-Weierstrass, Cauchy sequences, the extreme and
intermediate value theorems, uniform continuity on `[a, b]`, Rolle, the mean value theorems and Taylor's theorem.
The proof of each names the Mathlib result it wraps.
-/

open Filter Topology Set

namespace UndergradKB.RealAnalysis

/-! ## Chapter 1: the real numbers -/

/-- Least-upper-bound property of `ℝ`: a nonempty set bounded above has a least upper bound. -/
@[kb "lebl2026" "Theorem 1.2.1, p. 29"]
theorem lub_property {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) : IsLUB S (sSup S) :=
  isLUB_csSup hne hbdd

/-- Archimedean property: for `x > 0` and any `y` there is `n ∈ ℕ` with `n x > y`. -/
@[kb "lebl2026" "Theorem 1.2.4 (i), p. 31"]
theorem archimedean {x y : ℝ} (hx : 0 < x) : ∃ n : ℕ, y < n * x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  exact ⟨n, (div_lt_iff₀ hx).1 hn⟩

/-- `ℚ` is dense in `ℝ`: between two reals there is a rational. -/
@[kb "lebl2026" "Theorem 1.2.4 (ii), p. 31"]
theorem rat_dense {x y : ℝ} (h : x < y) : ∃ r : ℚ, x < r ∧ (r : ℝ) < y :=
  exists_rat_btwn h

/-- Approximation property of the supremum: elements of `S` come within `ε` of `sup S`. -/
@[kb "lebl2026" "Proposition 1.2.8, p. 33"]
theorem exists_mem_gt_sSup_sub {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x ∧ x ≤ sSup S := by
  obtain ⟨x, hxS, hx⟩ := exists_lt_of_lt_csSup hne (show sSup S - ε < sSup S by linarith)
  exact ⟨x, hxS, hx, le_csSup hbdd hxS⟩

/-! ## Chapter 2: sequences -/

/-- A convergent sequence has a unique limit. -/
@[kb "lebl2026" "Proposition 2.1.6, p. 53"]
theorem limit_unique {x : ℕ → ℝ} {a b : ℝ} (ha : Tendsto x atTop (𝓝 a)) (hb : Tendsto x atTop (𝓝 b)) :
    a = b :=
  tendsto_nhds_unique ha hb

/-- A convergent sequence is bounded. -/
@[kb "lebl2026" "Proposition 2.1.7, p. 54"]
theorem bounded_of_convergent {x : ℕ → ℝ} {a : ℝ} (h : Tendsto x atTop (𝓝 a)) :
    ∃ B : ℝ, ∀ n, |x n| ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto x h)
  exact ⟨B, fun n => by simpa [Real.norm_eq_abs] using hB _ ⟨n, rfl⟩⟩

/-- Monotone convergence theorem, increasing case: a bounded increasing sequence converges to its supremum. -/
@[kb "lebl2026" "Theorem 2.1.10, p. 55"]
theorem monotone_convergence {x : ℕ → ℝ} (hmono : Monotone x) (hbdd : BddAbove (range x)) :
    Tendsto x atTop (𝓝 (⨆ n, x n)) :=
  tendsto_atTop_ciSup hmono hbdd

/-- Monotone convergence theorem, decreasing case: a bounded decreasing sequence converges to its infimum. -/
@[kb "lebl2026" "Theorem 2.1.10, p. 55"]
theorem antitone_convergence {x : ℕ → ℝ} (hanti : Antitone x) (hbdd : BddBelow (range x)) :
    Tendsto x atTop (𝓝 (⨅ n, x n)) :=
  tendsto_atTop_ciInf hanti hbdd

/-- Monotone convergence theorem: an increasing sequence converges iff it is bounded (above). -/
@[kb "lebl2026" "Theorem 2.1.10, p. 55"]
theorem monotone_convergent_iff_bounded {x : ℕ → ℝ} (hmono : Monotone x) :
    (∃ a, Tendsto x atTop (𝓝 a)) ↔ BddAbove (range x) :=
  ⟨fun ⟨_, h⟩ => h.bddAbove_range, fun h => ⟨_, monotone_convergence hmono h⟩⟩

/-- Squeeze lemma: if `a n ≤ x n ≤ b n` and `a, b` converge to `L`, so does `x`. -/
@[kb "lebl2026" "Lemma 2.2.1, p. 61"]
theorem squeeze {a x b : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 L))
    (hax : ∀ n, a n ≤ x n) (hxb : ∀ n, x n ≤ b n) : Tendsto x atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hax hxb

/-- Bolzano-Weierstrass: a bounded sequence of reals has a convergent subsequence. -/
@[kb "lebl2026" "Theorem 2.3.8, p. 78"]
theorem bolzano_weierstrass {x : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |x n| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a, Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, -, φ, hφ, h⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-B) B)
    (fun n => mem_Icc.2 (abs_le.1 (hB n)))
  exact ⟨φ, hφ, a, h⟩

/-- A Cauchy sequence of reals is bounded. -/
@[kb "lebl2026" "Proposition 2.4.4, p. 84"]
theorem bounded_of_cauchy {x : ℕ → ℝ} (h : CauchySeq x) : ∃ B : ℝ, ∀ n, |x n| ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 h.isBounded_range
  exact ⟨B, fun n => by simpa [Real.norm_eq_abs] using hB _ ⟨n, rfl⟩⟩

/-- Cauchy sequences of reals are exactly the convergent ones (completeness of `ℝ`). -/
@[kb "lebl2026" "Theorem 2.4.5, p. 85"]
theorem cauchy_iff_convergent {x : ℕ → ℝ} : CauchySeq x ↔ ∃ a, Tendsto x atTop (𝓝 a) :=
  ⟨cauchySeq_tendsto_of_complete, fun ⟨_, h⟩ => h.cauchySeq⟩

/-! ## Chapter 3: continuous functions on `[a, b]` -/

/-- A continuous function on `[a, b]` is bounded. -/
@[kb "lebl2026" "Lemma 3.3.1, p. 130"]
theorem bounded_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) :
    ∃ B : ℝ, ∀ x ∈ Icc a b, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (isCompact_Icc.image_of_continuousOn hf).isBounded
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB _ ⟨x, hx, rfl⟩⟩

/-- Extreme value theorem (minimum-maximum theorem): a continuous function on `[a, b]` attains an absolute
minimum and an absolute maximum. -/
@[kb "lebl2026" "Theorem 3.3.2, p. 130"]
theorem extreme_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x) ∧ (∃ d ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f d) := by
  obtain ⟨c, hc, hcmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hf
  obtain ⟨d, hd, hdmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hf
  exact ⟨⟨c, hc, fun x hx => hcmin hx⟩, ⟨d, hd, fun x hx => hdmax hx⟩⟩

/-- Bolzano's intermediate value theorem: if `f` is continuous on `[a, b]` and `y` lies strictly between `f a` and
`f b`, then `f c = y` for some `c ∈ (a, b)`. -/
@[kb "lebl2026" "Theorem 3.3.8, p. 133"]
theorem intermediate_value {f : ℝ → ℝ} {a b y : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hy : (f a < y ∧ y < f b) ∨ (f b < y ∧ y < f a)) : ∃ c ∈ Ioo a b, f c = y := by
  rcases hy with hy | hy
  · exact intermediate_value_Ioo hab.le hf hy
  · exact intermediate_value_Ioo' hab.le hf hy

/-- A continuous function on `[a, b]` is uniformly continuous (epsilon-delta form). -/
@[kb "lebl2026" "Theorem 3.4.4, p. 139"]
theorem uniformly_continuous_of_continuousOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| < δ → |f x - f y| < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  exact ⟨δ, hδ, fun x hx y hy hxy => by simpa [Real.dist_eq] using h x hx y hy (by simpa [Real.dist_eq] using hxy)⟩

/-! ## Chapter 4: the derivative -/

/-- Rolle's theorem: if `f` is continuous on `[a, b]`, differentiable on `(a, b)` and `f a = f b`, then `f' c = 0`
for some `c ∈ (a, b)`. -/
@[kb "lebl2026" "Theorem 4.2.3, p. 163"]
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) (hfab : f a = f b) : ∃ c ∈ Ioo a b, HasDerivAt f 0 c := by
  obtain ⟨c, hc, h⟩ := exists_deriv_eq_zero hab hfc hfab
  exact ⟨c, hc, h ▸ ((hfd c hc).differentiableAt (isOpen_Ioo.mem_nhds hc)).hasDerivAt⟩

/-- Mean value theorem: `f b - f a = f' c (b - a)` for some `c ∈ (a, b)`. -/
@[kb "lebl2026" "Theorem 4.2.4, p. 164"]
theorem mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, f b - f a = deriv f c * (b - a) := by
  obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope f hab hfc hfd
  refine ⟨c, hc, ?_⟩
  rw [h, div_mul_cancel₀ _ (sub_ne_zero.2 hab.ne')]

/-- Cauchy's mean value theorem: `(f b - f a) g' c = (g b - g a) f' c` for some `c ∈ (a, b)`. -/
@[kb "lebl2026" "Theorem 4.2.5, p. 165"]
theorem cauchy_mean_value {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) (hgc : ContinuousOn g (Icc a b))
    (hgd : DifferentiableOn ℝ g (Ioo a b)) :
    ∃ c ∈ Ioo a b, (f b - f a) * deriv g c = (g b - g a) * deriv f c := by
  obtain ⟨c, hc, h⟩ := exists_ratio_deriv_eq_ratio_slope f hab hfc hfd g hgc hgd
  exact ⟨c, hc, h.symm⟩

/-- Taylor's theorem with the Lagrange remainder: for `f` with `n + 1` continuous derivatives and `x₀ ≠ x`,
`f x = ∑_{k ≤ n} f^(k)(x₀) (x - x₀)^k / k! + f^(n+1)(c) (x - x₀)^(n+1) / (n+1)!` for some `c` strictly between
`x₀` and `x`. -/
@[kb "lebl2026" "Theorem 4.3.2, p. 172"]
theorem taylor {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) {x₀ x : ℝ} (hx : x₀ ≠ x) :
    ∃ c ∈ uIoo x₀ x, f x = (∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / k.factorial)
      + iteratedDeriv (n + 1) f c * (x - x₀) ^ (n + 1) / (n + 1).factorial := by
  obtain ⟨c, hc, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hf.contDiffOn
  refine ⟨c, hc, ?_⟩
  rw [← h, taylor_within_apply]
  have hsum : ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹ * (x - x₀) ^ k) •
      iteratedDerivWithin k f (uIcc x₀ x) x₀ =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / k.factorial := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (k : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by
      exact_mod_cast (Finset.mem_range.1 hk).le
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      ((hf.of_le (by exact_mod_cast hk')).contDiffAt) left_mem_uIcc, smul_eq_mul]
    ring
  rw [hsum]
  ring

end UndergradKB.RealAnalysis
