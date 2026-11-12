import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Matrix.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import UndergradKB.Common.Attr

/-!
# The Weierstrass approximation theorem and differentiation in `ℝⁿ` (Morris, section 12.1)

The real Weierstrass theorem is in Mathlib; here we add the complex-valued form, rational
coefficients, cardinality of `C[0,1]`, zero sets, and partial derivatives.
-/

namespace UndergradKB.Topology

open Set Polynomial Filter

section Complex

/-- Real polynomial viewed as a complex polynomial. -/
private theorem eval_complexify (p q : ℝ[X]) (x : ℝ) :
    ((p.map (algebraMap ℝ ℂ)) + C Complex.I * q.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
      ⟨p.eval x, q.eval x⟩ := by
  have key : ∀ r : ℝ[X], (r.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((r.eval x : ℝ) : ℂ) := by
    intro r
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) x
  apply Complex.ext
  · simp [key]
  · simp [key]

/-- Morris, Topology Without Tears, Theorem 12.1.5 (TP-332). A continuous function `[a,b] → ℂ` is
within `ε` of a complex polynomial uniformly on `[a,b]` (the real case is in Mathlib). -/
@[kb "morris2024" "Theorem 12.1.5, p. 361"]
theorem exists_complex_polynomial_near (a b : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (ε : ℝ) (hε : 0 < ε) : ∃ P : ℂ[X], ∀ x ∈ Icc a b, ‖f x - P.eval (x : ℂ)‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (f x).re)
    (Complex.continuous_re.comp_continuousOn hf) (ε / 2) (by positivity)
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (f x).im)
    (Complex.continuous_im.comp_continuousOn hf) (ε / 2) (by positivity)
  refine ⟨p.map (algebraMap ℝ ℂ) + C Complex.I * q.map (algebraMap ℝ ℂ), fun x hx => ?_⟩
  rw [eval_complexify]
  have h1 := hp x hx
  have h2 := hq x hx
  calc ‖f x - ⟨p.eval x, q.eval x⟩‖
      ≤ |(f x - ⟨p.eval x, q.eval x⟩).re| + |(f x - ⟨p.eval x, q.eval x⟩).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := by
        simp only [Complex.sub_re, Complex.sub_im]
        rw [abs_sub_comm (f x).re, abs_sub_comm (f x).im]
        exact add_lt_add h1 h2
    _ = ε := by ring

/-- Morris, Topology Without Tears, Remark 12.1.13 (TP-332). A continuous function `[a,b] → ℂ` is the
uniform limit on `[a,b]` of a sequence of polynomials. -/
@[kb "morris2024" "Remark 12.1.13, p. 367"]
theorem exists_complex_polynomial_tendstoUniformlyOn (a b : ℝ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ P : ℕ → ℂ[X], TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Icc a b) := by
  have h : ∀ n : ℕ, ∃ P : ℂ[X], ∀ x ∈ Icc a b, ‖f x - P.eval (x : ℂ)‖ < 1 / ((n : ℝ) + 1) :=
    fun n => exists_complex_polynomial_near a b f hf _ (by positivity)
  choose P hP using h
  refine ⟨P, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  rw [dist_eq_norm]
  calc ‖f x - (P n).eval (x : ℂ)‖ < 1 / ((n : ℝ) + 1) := hP n x hx
    _ ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
    _ < ε := hN

end Complex

section Rational

/-- A real polynomial is uniformly approximated on `[a,b]` by polynomials with rational
coefficients. -/
theorem exists_ratPolynomial_near_polynomial (p : ℝ[X]) (a b ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℚ[X], ∀ x ∈ Icc a b, |p.eval x - aeval x Q| < ε := by
  set d : ℕ := p.natDegree + 1 with hd
  set M : ℝ := |a| + |b| + 1 with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg a
    have := abs_nonneg b
    linarith
  have hdpos : (0 : ℝ) < d := by positivity
  have key : ∀ i, ∃ q : ℚ, |p.coeff i - q| < ε / (d * M ^ i) := by
    intro i
    have hδ : 0 < ε / (d * M ^ i) := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show p.coeff i < p.coeff i + ε / (d * M ^ i) by linarith)
    refine ⟨q, ?_⟩
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  choose q hq using key
  refine ⟨∑ i ∈ Finset.range d, C (q i) * X ^ i, fun x hx => ?_⟩
  have hxM : |x| ≤ M := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hx.1]
    · linarith [le_abs_self b, abs_nonneg a, hx.2]
  have e1 : p.eval x = ∑ i ∈ Finset.range d, p.coeff i * x ^ i := Polynomial.eval_eq_sum_range _
  have e2 : aeval x (∑ i ∈ Finset.range d, C (q i) * X ^ i) =
      ∑ i ∈ Finset.range d, (q i : ℝ) * x ^ i := by
    simp [map_sum]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range d, (p.coeff i * x ^ i - (q i : ℝ) * x ^ i)|
      ≤ ∑ i ∈ Finset.range d, |p.coeff i * x ^ i - (q i : ℝ) * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ < ∑ i ∈ Finset.range d, ε / d := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega))
        intro i _
        have hMi : 0 < M ^ i := by positivity
        calc |p.coeff i * x ^ i - (q i : ℝ) * x ^ i| = |p.coeff i - q i| * |x| ^ i := by
              rw [← sub_mul, abs_mul, abs_pow]
          _ ≤ |p.coeff i - q i| * M ^ i := by gcongr
          _ < ε / (d * M ^ i) * M ^ i := mul_lt_mul_of_pos_right (hq i) hMi
          _ = ε / d := by field_simp
    _ = ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- A function continuous on `[a,b]` is uniformly approximated there by a real polynomial with
rational coefficients. -/
theorem exists_ratPolynomial_near (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (ε : ℝ)
    (hε : 0 < ε) : ∃ Q : ℚ[X], ∀ x ∈ Icc a b, |f x - aeval x Q| < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε / 2) (by positivity)
  obtain ⟨Q, hQ⟩ := exists_ratPolynomial_near_polynomial p a b (ε / 2) (by positivity)
  refine ⟨Q, fun x hx => ?_⟩
  have h1 := hp x hx
  have h2 := hQ x hx
  calc |f x - aeval x Q| = |-(p.eval x - f x) + (p.eval x - aeval x Q)| := by ring_nf
    _ ≤ |-(p.eval x - f x)| + |p.eval x - aeval x Q| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by rw [abs_neg]; exact add_lt_add h1 h2
    _ = ε := by ring

/-- Morris, Topology Without Tears, Corollary 12.1.8 (TP-334). A continuous function `[a,b] → ℂ` is
uniformly approximated within `ε` by a polynomial whose coefficients are of the form `r + s i` with
`r, s` rational. -/
@[kb "morris2024" "Corollary 12.1.8, p. 365"]
theorem exists_ratComplexPolynomial_near (a b : ℝ) (f : ℝ → ℂ) (hf : ContinuousOn f (Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℂ[X], (∀ n, ∃ r s : ℚ, P.coeff n = r + s * Complex.I) ∧
      ∀ x ∈ Icc a b, ‖f x - P.eval (x : ℂ)‖ < ε := by
  obtain ⟨Q₁, h₁⟩ := exists_ratPolynomial_near a b (fun x => (f x).re)
    (Complex.continuous_re.comp_continuousOn hf) (ε / 2) (by positivity)
  obtain ⟨Q₂, h₂⟩ := exists_ratPolynomial_near a b (fun x => (f x).im)
    (Complex.continuous_im.comp_continuousOn hf) (ε / 2) (by positivity)
  have ev : ∀ (Q : ℚ[X]) (x : ℝ), (Q.map (algebraMap ℚ ℝ)).eval x = aeval x Q := by
    intro Q x
    rw [Polynomial.eval_map, Polynomial.aeval_def]
  refine ⟨(Q₁.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) +
    C Complex.I * (Q₂.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ), ?_, ?_⟩
  · intro n
    refine ⟨Q₁.coeff n, Q₂.coeff n, ?_⟩
    simp [Polynomial.coeff_map, mul_comm]
  · intro x hx
    rw [eval_complexify]
    have e1 := h₁ x hx
    have e2 := h₂ x hx
    rw [ev, ev]
    calc ‖f x - ⟨aeval x Q₁, aeval x Q₂⟩‖
        ≤ |(f x - ⟨aeval x Q₁, aeval x Q₂⟩).re| + |(f x - ⟨aeval x Q₁, aeval x Q₂⟩).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < ε / 2 + ε / 2 := by
          simp only [Complex.sub_re, Complex.sub_im]
          exact add_lt_add e1 e2
      _ = ε := by ring

end Rational

section CI

open ContinuousMap

/-- The continuous functions on `[a,b]` given by polynomials with rational coefficients. -/
noncomputable def ratPolynomialFunctions (a b : ℝ) : Set C(Icc a b, ℝ) :=
  range fun Q : ℚ[X] => (Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b)

/-- Polynomials with rational coefficients are dense in `C([a,b], ℝ)` for the sup metric. -/
theorem dense_ratPolynomialFunctions (a b : ℝ) : Dense (ratPolynomialFunctions a b) := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b f (r / 2) (by positivity)
  obtain ⟨Q, hQ⟩ := exists_ratPolynomial_near_polynomial p a b (r / 4) (by positivity)
  refine ⟨(Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b), ?_, ⟨Q, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 : ‖(Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b) - p.toContinuousMapOn (Icc a b)‖
      ≤ r / 4 := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    have := hQ x x.2
    rw [abs_sub_comm] at this
    simpa [Polynomial.eval_map, Polynomial.aeval_def] using this.le
  calc ‖(Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b) - f‖
      = ‖((Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b) - p.toContinuousMapOn (Icc a b)) +
          (p.toContinuousMapOn (Icc a b) - f)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(Q.map (algebraMap ℚ ℝ)).toContinuousMapOn (Icc a b) - p.toContinuousMapOn (Icc a b)‖ +
          ‖p.toContinuousMapOn (Icc a b) - f‖ := norm_add_le _ _
    _ < r := by linarith

/-- The space `C([0,1], ℝ)` has the cardinality of the continuum. -/
theorem mk_continuousMap_Icc_zero_one :
    Cardinal.mk C(Icc (0 : ℝ) 1, ℝ) = Cardinal.continuum := by
  obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq (Icc (0 : ℝ) 1)
  apply le_antisymm
  · have hinj : Function.Injective fun f : C(Icc (0 : ℝ) 1, ℝ) => fun n => f (s n) := by
      intro f g h
      have : (f : Icc (0 : ℝ) 1 → ℝ) = g :=
        hs.equalizer f.continuous g.continuous h
      exact DFunLike.coe_injective this
    refine (Cardinal.mk_le_of_injective hinj).trans (le_of_eq ?_)
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.lift_id, Cardinal.mk_real, Cardinal.mk_nat]
    exact Cardinal.continuum_power_aleph0
  · have hinj : Function.Injective fun c : ℝ => (ContinuousMap.const (Icc (0 : ℝ) 1) c) := by
      intro c d h
      exact congrFun (congrArg DFunLike.coe h) ⟨0, by simp⟩
    have := Cardinal.mk_le_of_injective hinj
    rwa [Cardinal.mk_real] at this

/-- Morris, Topology Without Tears, Proposition 12.1.9 (TP-335). In `C[0,1]` with the sup metric:
(i) polynomials are dense, (ii) polynomials with rational coefficients are dense, (iii) the space is
separable, (iv) its cardinality is `2 ^ ℵ₀ = 𝔠`. -/
@[kb "morris2024" "Proposition 12.1.9, p. 366"]
theorem continuousMap_unitInterval_polynomials :
    Dense (polynomialFunctions (Icc (0 : ℝ) 1) : Set C(Icc (0 : ℝ) 1, ℝ)) ∧
      Dense (ratPolynomialFunctions 0 1) ∧
      TopologicalSpace.SeparableSpace C(Icc (0 : ℝ) 1, ℝ) ∧
      Cardinal.mk C(Icc (0 : ℝ) 1, ℝ) = 2 ^ Cardinal.aleph0 := by
  refine ⟨?_, dense_ratPolynomialFunctions 0 1, inferInstance, ?_⟩
  · rw [dense_iff_closure_eq]
    have := polynomialFunctions_closure_eq_top (0 : ℝ) 1
    rw [← Subalgebra.topologicalClosure_coe, this]
    rfl
  · rw [Cardinal.two_power_aleph0]
    exact mk_continuousMap_Icc_zero_one

end CI

section ZeroSets

/-- Morris, Topology Without Tears, Theorem 12.1.16 (i) (TP-339). A non-constant real polynomial
has finitely many zeros. -/
@[kb "morris2024" "Theorem 12.1.16, p. 368"]
theorem finite_zeros_polynomial (p : ℝ[X]) (hp : ∃ x y, p.eval x ≠ p.eval y) :
    {x | p.eval x = 0}.Finite := by
  have : p ≠ 0 := by
    rintro rfl
    simp at hp
  exact Polynomial.finite_setOfPred_isRoot this

/-- Morris, Topology Without Tears, Theorem 12.1.16 (ii) (TP-339). The zero set of a non-constant
analytic function `ℝ → ℝ` is a discrete subspace. -/
@[kb "morris2024" "Theorem 12.1.16, p. 368"]
theorem discreteTopology_zeros_analytic {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ)
    (hnc : ∃ x y, f x ≠ f y) : DiscreteTopology {x | f x = 0} := by
  rw [discreteTopology_subtype_iff]
  intro x hx
  rw [inf_principal_eq_bot]
  rcases (hf x trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hz := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ x) h
    obtain ⟨y, z, hyz⟩ := hnc
    exact hyz ((hz (mem_univ y)).trans (hz (mem_univ z)).symm)
  · exact h

/-- Morris, Topology Without Tears, Theorem 12.1.16 (iii) (TP-339). Every closed subset of `ℝ` is
the zero set of a smooth function. -/
@[kb "morris2024" "Theorem 12.1.16, p. 368"]
theorem exists_contDiff_zeroSet_eq {Z : Set ℝ} (hZ : IsClosed Z) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ {x | f x = 0} = Z := by
  obtain ⟨f, hf, -, hz, -⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) hZ isClosed_empty (disjoint_empty Z)
  exact ⟨f, hf, by ext x; exact (hz x).symm⟩

end ZeroSets

section PartialDerivative

open scoped _root_.Topology

/-- The `i`-th partial derivative of `f : ℝⁿ → ℝ` at `r`, as the derivative along the `i`-th basis
vector (`ℝⁿ` is `Fin n → ℝ`; the notion depends only on the topology). Bridging notion for
Morris, Definition 12.1.20. -/
noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (r : Fin n → ℝ) : ℝ :=
  lineDeriv ℝ f r (Pi.single i 1)

/-- Morris, Topology Without Tears, Definition 12.1.20 (TP-342). The limit of the difference
quotient in the `i`-th coordinate exists with value `d` exactly when `d` is the `i`-th partial
derivative (as a line derivative along the `i`-th basis vector). -/
@[kb "morris2024" "Definition 12.1.20, p. 369"]
theorem hasLineDerivAt_single_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (r : Fin n → ℝ)
    (d : ℝ) :
    HasLineDerivAt ℝ f d r (Pi.single i 1) ↔
      Tendsto (fun h : ℝ => (f (Function.update r i (r i + h)) - f r) / h) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasLineDerivAt_iff_tendsto_slope_zero]
  have hu : ∀ h : ℝ, r + h • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Function.update r i (r i + h) := by
    intro h
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp only [hu, smul_eq_mul, div_eq_inv_mul]

/-- The partial derivative is the derivative of the one-variable function obtained by freezing the
other coordinates, when it exists. -/
theorem partialDeriv_eq_deriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (r : Fin n → ℝ) :
    partialDeriv f i r = deriv (fun t : ℝ => f (Function.update r i t)) (r i) := by
  have hu : ∀ h : ℝ, r + h • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Function.update r i (r i + h) := by
    intro h
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  unfold partialDeriv lineDeriv
  simp only [hu]
  rw [deriv_comp_const_add (f := fun t : ℝ => f (Function.update r i t))]
  simp

/-- Morris, Topology Without Tears, Proposition 12.1.21 (TP-343). If `f : ℝⁿ → ℝᵐ` is differentiable
at `x`, every partial derivative of every coordinate function `fⁱ` exists at `x`, and the derivative
of `f` at `x` is the `m × n` matrix of partial derivatives `(Dⱼ fⁱ (x))`. -/
@[kb "morris2024" "Proposition 12.1.21, p. 370"]
theorem fderiv_eq_matrix_partialDeriv {n m : ℕ} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x) :
    (∀ i j, HasLineDerivAt ℝ (fun y => f y i) (partialDeriv (fun y => f y i) j x) x
        (Pi.single j 1)) ∧
      (fderiv ℝ f x : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
        Matrix.toLin' (Matrix.of fun i j => partialDeriv (fun y => f y i) j x) := by
  have hcoord : ∀ i j, HasLineDerivAt ℝ (fun y => f y i) (fderiv ℝ f x (Pi.single j 1) i) x
      (Pi.single j 1) := by
    intro i j
    have h1 : HasFDerivAt (fun y => f y i)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).hasFDerivAt.comp x
        hf.hasFDerivAt
    exact h1.hasLineDerivAt (Pi.single j 1)
  have hpd : ∀ i j, partialDeriv (fun y => f y i) j x = fderiv ℝ f x (Pi.single j 1) i :=
    fun i j => (hcoord i j).lineDeriv
  refine ⟨fun i j => by rw [hpd]; exact hcoord i j, ?_⟩
  apply LinearMap.ext
  intro v
  ext i
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [ContinuousLinearMap.coe_coe, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply, hpd]
  conv_lhs => rw [hv]
  simp [map_sum, mul_comm]

end PartialDerivative

end UndergradKB.Topology
