import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import UndergradKB.Combinatorics.Analytic.WienerIkehara
import UndergradKB.Common.Attr

/-!
# The Prime Number Theorem

We prove that the number of primes up to `n`, multiplied by `log n` and divided by `n`, tends to
`1`. The route is the classical one.  The Wiener-Ikehara Tauberian theorem (vendored in
`UndergradKB.Combinatorics.Analytic.WienerIkehara`) is applied to the von Mangoldt function,
whose Dirichlet series has a simple pole of residue one at `s = 1` and extends continuously to the
closed half-plane `Re s ≥ 1` after removing that pole (this input is Mathlib's treatment of the
trivial residue class modulo one).  This gives that the Chebyshev function `ψ(x)` is asymptotic to
`x`.  Mathlib's comparison of `ψ` with the prime-sum function `θ`, and of `θ` with the prime
counting function, then transfers the statement to `π(x) log x / x → 1`.
-/

open Filter Topology Asymptotics Real

namespace UndergradKB.Combinatorics.Analytic

section Aux

/-- For the trivial modulus, the residue-class restriction of the von Mangoldt function is the
von Mangoldt function itself. -/
private lemma residueClass_one :
    ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) =
      fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n := by
  ext n
  have : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator, this]

private lemma sum_Icc_vonMangoldt (m : ℕ) :
    ∑ n ∈ Finset.Icc 0 m, ArithmeticFunction.vonMangoldt n = Chebyshev.psi m := by
  rw [Chebyshev.psi, Nat.floor_natCast, Finset.Icc_eq_cons_Ioc (Nat.zero_le m), Finset.sum_cons]
  simp

private lemma sum_range_vonMangoldt_le (n : ℕ) :
    ∑ i ∈ Finset.range n, ArithmeticFunction.vonMangoldt i ≤ (Real.log 4 + 4) * n := by
  calc ∑ i ∈ Finset.range n, ArithmeticFunction.vonMangoldt i
      ≤ ∑ i ∈ Finset.Icc 0 n, ArithmeticFunction.vonMangoldt i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
          omega
        · intros; exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi n := sum_Icc_vonMangoldt n
    _ ≤ (Real.log 4 + 4) * n := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

end Aux

/-- The Chebyshev function `ψ(x)`, the sum of the von Mangoldt function over `n ≤ x`, is
asymptotic to `x`: `ψ(x) / x → 1`. This is the form of the prime number theorem that the
Tauberian theorem delivers directly. -/
theorem chebyshev_psi_div_tendsto_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h := WienerIkehara.tendsto_sum_div
    (f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n) (C := Real.log 4 + 4) (A := 1)
    (G := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1))
    sum_range_vonMangoldt_le
    (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux _)
    (by
      have := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
        (isUnit_one (M := ZMod 1))
      rw [residueClass_one] at this
      simpa using this)
    (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg)
  refine h.congr' ?_
  filter_upwards with x
  rw [Chebyshev.psi, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp

/-- `θ(x) / x → 1`, where `θ(x)` is the sum of `log p` over primes `p ≤ x`. -/
theorem chebyshev_theta_div_tendsto_one :
    Tendsto (fun x : ℝ ↦ Chebyshev.theta x / x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - Chebyshev.theta x) * x⁻¹) atTop (𝓝 0) := by
    have hO := Chebyshev.isBigO_psi_sub_theta_sqrt.mul (isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop)
    refine hO.trans_tendsto ?_
    have : Tendsto (fun x : ℝ ↦ (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx.le).symm
    field_simp
    exact (Real.sq_sqrt hx.le).symm
  have := chebyshev_psi_div_tendsto_one.sub h1
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards with x
  simp only [div_eq_mul_inv]
  ring

/-- The prime counting function in the real variable form of the prime number theorem:
`π(⌊x⌋) · log x / x → 1`. -/
theorem prime_number_theorem_real :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
  have hO := Chebyshev.primeCounting_sub_theta_div_log_isBigO.mul
    (isBigO_refl (fun x : ℝ ↦ Real.log x / x) atTop)
  have h1 : Tendsto ((fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x) *
      (fun x : ℝ ↦ Real.log x / x)) atTop (𝓝 0) := by
    refine hO.trans_tendsto ?_
    have : Tendsto (fun x : ℝ ↦ (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    field_simp
  have := chebyshev_theta_div_tendsto_one.add h1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- CO-525. The Prime Number Theorem: `π(n) · log n / n → 1`, where `π(n)` is the number of
primes at most `n` (`Nat.primeCounting`) and `log` is the natural logarithm. Equivalently,
`π(n)` is asymptotic to `n / log n`. -/
@[kb "kellertrotter2017" "text p.89 Prime Number Theorem"]
theorem prime_number_theorem :
    Tendsto (fun n : ℕ ↦ (Nat.primeCounting n : ℝ) * Real.log n / n) atTop (𝓝 1) := by
  have := prime_number_theorem_real.comp tendsto_natCast_atTop_atTop
  refine this.congr fun n ↦ ?_
  simp

end UndergradKB.Combinatorics.Analytic
