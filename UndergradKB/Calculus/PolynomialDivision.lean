import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import UndergradKB.Common.Attr

/-! # Calculus: polynomial division and factorization over the reals

OpenStax Calculus 2 §3.4 (partial fractions). -/

open Polynomial

namespace UndergradKB.Calculus

/-- OpenStax Calculus 2:§3.4 requirement (CA-227): for real polynomials `P` and `D ≠ 0` there are `Q`, `R` with
`P = Q * D + R` and `deg R < deg D`. -/
@[kb "openstaxcalculus2016" "2:§3.4 Requirement: degree of numerator less than denominator, p. 271"]
theorem polynomial_long_division (P D : ℝ[X]) (hD : D ≠ 0) :
    ∃ Q R : ℝ[X], P = Q * D + R ∧ R.degree < D.degree :=
  ⟨P / D, P % D, by rw [mul_comm]; exact (EuclideanDomain.div_add_mod P D).symm,
    EuclideanDomain.mod_lt P hD⟩

private lemma monic_irreducible_shape {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q) :
    (∃ r : ℝ, q = X - C r) ∨ (∃ b c : ℝ, b ^ 2 - 4 * c < 0 ∧ q = X ^ 2 + C b * X + C c) := by
  have hdeg := hirr.degree_le_two
  have hpos : 0 < q.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  have hle : q.natDegree ≤ 2 := natDegree_le_iff_degree_le.2 hdeg
  have hcases : q.natDegree = 1 ∨ q.natDegree = 2 := by omega
  rcases hcases with h1 | h2
  · left
    refine ⟨-q.coeff 0, ?_⟩
    rw [hm.eq_X_add_C h1]
    simp [sub_eq_add_neg]
  · right
    have hq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      ext n
      simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
      rcases Nat.lt_or_ge n 3 with hn | hn
      · interval_cases n
        · simp
        · simp
        · have hc2 : q.coeff 2 = 1 := by
            have := hm.coeff_natDegree
            rwa [h2] at this
          simp [hc2]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega]
    refine ⟨q.coeff 1, q.coeff 0, ?_, hq⟩
    by_contra hnn
    replace hnn := not_lt.1 hnn
    set b := q.coeff 1
    set c := q.coeff 0
    have hroot : q.IsRoot ((-b + Real.sqrt (b ^ 2 - 4 * c)) / 2) := by
      rw [IsRoot, hq]
      have := Real.sq_sqrt hnn
      simp
      nlinarith
    have := degree_eq_one_of_irreducible_of_root hirr hroot
    rw [degree_eq_natDegree hirr.ne_zero, h2] at this
    norm_num at this

/-- OpenStax Calculus 2:§3.4 (CA-228): a real polynomial of positive degree is its leading coefficient times a
product of monic linear factors `x - r` and monic irreducible quadratics `x^2 + b x + c` (with `b^2 - 4c < 0`). -/
@[kb "openstaxcalculus2016" "2:§3.4 Problem-Solving Strategy (Partial Fraction Decomposition), p. 275"]
theorem real_polynomial_factorization (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ l : Multiset ℝ[X],
      (∀ q ∈ l, (∃ r : ℝ, q = X - C r) ∨
        (∃ b c : ℝ, b ^ 2 - 4 * c < 0 ∧ q = X ^ 2 + C b * X + C c)) ∧
      p = C p.leadingCoeff * l.prod := by
  refine ⟨UniqueFactorizationMonoid.normalizedFactors p, fun q hq => ?_, ?_⟩
  · have hirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hmon : q.Monic := by
      have h := UniqueFactorizationMonoid.normalize_normalized_factor q hq
      rw [← h]
      exact Polynomial.monic_normalize hirr.ne_zero
    exact monic_irreducible_shape hmon hirr
  · obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hp
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.1 u.isUnit
    have hmon : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors p, q.Monic := fun q hq => by
      have h := UniqueFactorizationMonoid.normalize_normalized_factor q hq
      rw [← h]
      exact Polynomial.monic_normalize
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
    have hprod : (UniqueFactorizationMonoid.normalizedFactors p).prod.Monic := by
      have := monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors p)
        (fun q : ℝ[X] => q) hmon
      simpa using this
    rw [← hr] at hu
    have hlc : p.leadingCoeff = r := by
      rw [← hu, leadingCoeff_mul, hprod.leadingCoeff, one_mul, leadingCoeff_C]
    rw [hlc, mul_comm]
    exact hu.symm

end UndergradKB.Calculus
