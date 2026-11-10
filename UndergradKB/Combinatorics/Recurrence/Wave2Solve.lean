import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Recurrence.General

/-!
# Solving constant-coefficient recurrences: roots, particular solutions, generating functions
(Keller–Trotter, Chapter 9)

* the root-by-root solution formula over an algebraically closed field (e.g. `ℂ`), obtained from
  the factorization of the characteristic polynomial and `solutions_general`;
* the general solution of a nonhomogeneous equation as particular plus homogeneous;
* the generating function of a solution of a constant-coefficient recurrence is a polynomial
  divided by the reversed characteristic polynomial;
* the closed form `r n = 1 + n (n+1) / 2` of the recurrence for regions cut by lines.
-/

namespace UndergradKB.Combinatorics.Recurrence

open Polynomial Finset

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- Factoring `p = ∏ (X - r_i)^(m_i)` over an algebraically closed field, with distinct roots
`r_i` and `m_i` their multiplicities. -/
lemma exists_root_factorization (p : K[X]) (hp : p.Monic) :
    ∃ (k : ℕ) (r : Fin k → K) (m : Fin k → ℕ), Function.Injective r ∧
      (∀ i, p.IsRoot (r i)) ∧ p = ∏ i, (X - C (r i)) ^ m i := by
  classical
  let s : Finset K := p.roots.toFinset
  let e : s ≃ Fin s.card := s.equivFin
  refine ⟨s.card, fun i => (e.symm i : K), fun i => p.roots.count (e.symm i : K),
    fun i j h => e.symm.injective (Subtype.ext h), fun i => ?_, ?_⟩
  · have := (e.symm i).2
    simp only [s, Multiset.mem_toFinset] at this
    exact (mem_roots'.1 this).2
  · conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
    rw [Finset.prod_multiset_map_count]
    rw [← Finset.prod_coe_sort s (fun x => (X - C x) ^ p.roots.count x)]
    exact (Equiv.prod_comp e.symm (fun x : s => (X - C (x : K)) ^ p.roots.count (x : K))).symm

/-- CO-472. Over an algebraically closed field (for instance `ℂ`) the advancement equation
`p(A) f = 0` with monic `p` and `p(0) ≠ 0` is solved by factoring `p`: with `r_1, …, r_k` the
distinct roots and `m_i` the multiplicity of `r_i`, the sequences `n^j r_i^n` (`j < m_i`) are
solutions and every solution is a linear combination of them. -/
@[kb "kellertrotter2017" "Example 9.9, p. 214"]
theorem solutions_alg_closed (p : K[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0) :
    ∃ (k : ℕ) (r : Fin k → K) (m : Fin k → ℕ), Function.Injective r ∧ (∀ i, r i ≠ 0) ∧
      (∀ i, p.IsRoot (r i)) ∧ ∀ f : ℕ → K,
        (aeval advance p : Module.End K (ℕ → K)) f = 0 ↔
          ∃ c : (i : Fin k) → Fin (m i) → K, ∀ n : ℕ,
            f n = ∑ i, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n := by
  obtain ⟨k, r, m, hinj, hroot, hfac⟩ := exists_root_factorization p hp
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i h
    have := hroot i
    rw [h, IsRoot, ← coeff_zero_eq_eval_zero] at this
    exact h0 this
  refine ⟨k, r, m, hinj, hr0, hroot, fun f => ?_⟩
  rw [hfac]
  exact solutions_general r m hinj hr0 f

/-- CO-472 (each piece solves). For a root `r` of multiplicity `m` of the characteristic
polynomial, `n ↦ n^j r^n` with `j < m` solves `p(A) f = 0`, where `(X - r)^m ∣ p`. -/
@[kb "kellertrotter2017" "Example 9.9, p. 214"]
theorem pow_mul_geom_solution (p : K[X]) (r : K) (m : ℕ) (hr : r ≠ 0) (hdvd : (X - C r) ^ m ∣ p)
    (j : ℕ) (hj : j < m) :
    (aeval advance p : Module.End K (ℕ → K)) (fun n : ℕ => (n : K) ^ j * r ^ n) = 0 := by
  obtain ⟨q, rfl⟩ := hdvd
  have key : (aeval advance ((X - C r) ^ m) : Module.End K (ℕ → K))
      (fun n : ℕ => (n : K) ^ j * r ^ n) = 0 := by
    have := (solutions_repeated_root m r hr (fun n : ℕ => (n : K) ^ j * r ^ n)).2
      ⟨fun i => if (i : ℕ) = j then 1 else 0, fun n => by
        rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]
        · simp [mul_comm]
        · intro b _ hb
          have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
          simp [this]
        · simp⟩
    exact this
  rw [mul_comm, map_mul, mul_apply_eq_comp, key, map_zero]

/-- CO-473. Nonhomogeneous equation `p(A) f = g` over an algebraically closed field: given a
particular solution `f₀`, the general solution is `f₀` plus the combination of the homogeneous
solutions `n^j r_i^n`. -/
@[kb "kellertrotter2017" "Example 9.14, p. 218"]
theorem nonhomogeneous_general_solution (p : K[X]) (hp : p.Monic) (h0 : p.coeff 0 ≠ 0)
    (g f₀ : ℕ → K) (hf₀ : (aeval advance p : Module.End K (ℕ → K)) f₀ = g) :
    ∃ (k : ℕ) (r : Fin k → K) (m : Fin k → ℕ), Function.Injective r ∧ (∀ i, r i ≠ 0) ∧
      ∀ f : ℕ → K, (aeval advance p : Module.End K (ℕ → K)) f = g ↔
        ∃ c : (i : Fin k) → Fin (m i) → K, ∀ n : ℕ,
          f n = f₀ n + ∑ i, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n := by
  obtain ⟨k, r, m, hinj, hr0, -, hsol⟩ := solutions_alg_closed p hp h0
  refine ⟨k, r, m, hinj, hr0, fun f => ?_⟩
  rw [solution_eq_particular_add_homogeneous p g f₀ hf₀ f]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨c, hc⟩ := (hsol h).1 hh
    exact ⟨c, fun n => by simp [hc n]⟩
  · rintro ⟨c, hc⟩
    refine ⟨f - f₀, (hsol _).2 ⟨c, fun n => ?_⟩, by abel⟩
    simp [hc n]

end AlgClosed

/-! ### Generating functions of recurrent sequences -/

section GeneratingFunction

variable {R : Type*} [CommRing R]

/-- CO-474. If `a` satisfies the constant-coefficient recurrence `∑_{i ≤ k} c_i a(n - i) = 0` for
all `n ≥ k`, then the generating function times the reversed characteristic polynomial
`q = ∑ c_i x^i` is a polynomial of degree `< k` (so the series is a rational function). -/
@[kb "kellertrotter2017" "Example 9.24, p. 226"]
theorem genfun_mul_reversed_isPolynomial (k : ℕ) (q : R[X]) (hq : q.natDegree ≤ k) (a : ℕ → R)
    (h : ∀ n, k ≤ n → ∑ i ∈ range (k + 1), q.coeff i * a (n - i) = 0) :
    ∃ P : R[X], P.degree < k ∧ (q : PowerSeries R) * PowerSeries.mk a = (P : PowerSeries R) := by
  have hcoeff : ∀ n, PowerSeries.coeff n ((q : PowerSeries R) * PowerSeries.mk a) =
      ∑ i ∈ range (n + 1), q.coeff i * a (n - i) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (q : PowerSeries R) * PowerSeries.coeff j (PowerSeries.mk a))]
    simp
  have hvan : ∀ n, k ≤ n → PowerSeries.coeff n ((q : PowerSeries R) * PowerSeries.mk a) = 0 := by
    intro n hn
    rw [hcoeff, ← h n hn]
    symm
    refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
    · rw [mem_range] at hi ⊢; omega
    · have : q.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by rw [mem_range] at hi; omega)
      rw [this, zero_mul]
  have hP : ∀ n, (∑ m ∈ range k, monomial m
      (PowerSeries.coeff m ((q : PowerSeries R) * PowerSeries.mk a))).coeff n =
      if n < k then PowerSeries.coeff n ((q : PowerSeries R) * PowerSeries.mk a) else 0 := by
    intro n
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp
  refine ⟨∑ m ∈ range k, monomial m (PowerSeries.coeff m ((q : PowerSeries R) * PowerSeries.mk a)),
    ?_, ?_⟩
  · rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [hP]
    simp [Nat.not_lt.2 hn]
  · ext n
    rw [Polynomial.coeff_coe, hP]
    split_ifs with hn
    · rfl
    · exact hvan n (by omega)

/-- CO-474 (converse). If `q · A(x)` is a polynomial of degree `< k` and `q` has degree `≤ k`,
then the coefficients satisfy the recurrence `∑ c_i a(n - i) = 0` for `n ≥ k`. -/
@[kb "kellertrotter2017" "Example 9.24, p. 226"]
theorem recurrence_of_genfun_mul_isPolynomial (k : ℕ) (q P : R[X]) (a : ℕ → R) (hP : P.degree < k)
    (h : (q : PowerSeries R) * PowerSeries.mk a = (P : PowerSeries R)) :
    ∀ n, k ≤ n → ∑ i ∈ range (n + 1), q.coeff i * a (n - i) = 0 := by
  intro n hn
  have h1 := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (q : PowerSeries R) * PowerSeries.coeff j (PowerSeries.mk a)),
    Polynomial.coeff_coe, coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hP (by exact_mod_cast hn))] at h1
  simpa using h1

end GeneratingFunction

/-- CO-474 (worked example). For `r₀ = 1`, `r₁ = 4` and `r_n + r_{n-1} - 6 r_{n-2} = 0`, the
solution `r_n = (6/5) 2^n - (1/5) (-3)^n` has generating function `(1 + 4x) / (1 + x - 6x²)`,
i.e. `(1 + x - 6x²) · ∑ r_n x^n = 1 + 4x`. -/
@[kb "kellertrotter2017" "Example 9.24, p. 226"]
theorem genfun_example :
    ((1 : PowerSeries ℚ) + PowerSeries.X - 6 * PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n : ℕ => (6 / 5 : ℚ) * 2 ^ n - (1 / 5) * (-3) ^ n) =
      1 + 4 * PowerSeries.X := by
  set S : PowerSeries ℚ := PowerSeries.mk (fun n : ℕ => (6 / 5 : ℚ) * 2 ^ n - (1 / 5) * (-3) ^ n)
    with hS
  have e6 : (6 : PowerSeries ℚ) = PowerSeries.C 6 := (map_ofNat PowerSeries.C 6).symm
  have e4 : (4 : PowerSeries ℚ) = PowerSeries.C 4 := (map_ofNat PowerSeries.C 4).symm
  have hL : ((1 : PowerSeries ℚ) + PowerSeries.X - 6 * PowerSeries.X ^ 2) * S =
      S + PowerSeries.X * S - PowerSeries.C 6 * (PowerSeries.X * (PowerSeries.X * S)) := by
    rw [e6]; ring
  rw [hL, e4]
  ext n
  rcases n with _ | _ | n
  · simp [hS]
    norm_num
  · simp [hS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, PowerSeries.coeff_X]
    norm_num
  · simp [hS, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, PowerSeries.coeff_X]
    ring

/-! ### Lines in the plane -/

/-- CO-214, CO-220. The recurrence part of the number of regions cut by `n` lines in general
position: from `r 0 = 1` and `r (n+1) = r n + (n+1)` one gets `2 r(n) = 2 + n(n+1)`, i.e.
`r n = 1 + n(n+1)/2`. (The geometric count of regions of a line arrangement is not formalized.) -/
@[kb "kellertrotter2017" "text, p. 210; Example 9.16, p. 220"]
theorem lines_regions_explicit (r : ℕ → ℕ) (h0 : r 0 = 1) (hs : ∀ n, r (n + 1) = r n + (n + 1)) :
    ∀ n, r n = 1 + n * (n + 1) / 2 := by
  intro n
  have key : ∀ n, 2 * r n = 2 + n * (n + 1) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [hs]; nlinarith
  have := key n
  omega

/-- CO-214 (book form of Example 1.12/3.3): from `r 1 = 2` and `r n = n + r (n-1)` (`n ≥ 2`),
`r n = 1 + n(n+1)/2` for `n ≥ 1`. -/
@[kb "kellertrotter2017" "Example 3.3, p. 67; Example 1.12, p. 36"]
theorem lines_regions_explicit' (r : ℕ → ℕ) (h1 : r 1 = 2)
    (hs : ∀ n, 2 ≤ n → r n = n + r (n - 1)) : ∀ n, 1 ≤ n → r n = 1 + n * (n + 1) / 2 := by
  intro n hn
  have key : ∀ n, 1 ≤ n → 2 * r n = 2 + n * (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [h1]
    | succ n hn ih =>
      rw [hs (n + 1) (by omega), Nat.add_sub_cancel]
      nlinarith
  have := key n hn
  omega

end UndergradKB.Combinatorics.Recurrence
