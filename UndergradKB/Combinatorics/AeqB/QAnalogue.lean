import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Combinatorics.AeqB.Zeilberger
import UndergradKB.Common.Attr

/-!
# q-analogues (Petkovsek–Wilf–Zeilberger, "A = B", §4.5, §6.5, §9.8)

* CO-376: q-proper hypergeometric terms (4.5.5) built from `Q(m, c) = (1 - cq)(1 - cq^2) ⋯ (1 - cq^m)`
  (4.5.6).
* CO-384: q-hypergeometric and bi-basic `(p,q)`-hypergeometric sequences.
* CO-429: the q-analogue of creative telescoping: when both ratios of `F` are rational functions of
  `q^n` and `q^k`, a solution of the Gosper-type equation gives `Ω(N,n) F = G(n,k+1) - G(n,k)` with
  `G = R F`, `R` rational in `q^n, q^k` (the algebra is that of `Zeilberger.zeilberger_sound`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Finset

namespace QAnalogue

variable {K : Type*} [Field K]

/-! ### CO-376 -/

/-- (4.5.6) `Q(m, c) = (1 - c q)(1 - c q^2) ⋯ (1 - c q^m)` (the q-Pochhammer symbol `(cq; q)_m`). -/
@[kb "petkovsekwilfzeilberger1996" "Equation (4.5.6), p. 81"]
def qFac (q c : K) (m : ℕ) : K := ∏ t ∈ range m, (1 - c * q ^ (t + 1))

theorem qFac_succ (q c : K) (m : ℕ) : qFac q c (m + 1) = qFac q c m * (1 - c * q ^ (m + 1)) := by
  simp [qFac, prod_range_succ]

/-- The data of a q-proper hypergeometric term (4.5.5):
`F(n,k) = ∏_s Q(a_s n + b_s k, c_s) / ∏_s Q(u_s n + v_s k, w_s) · q^{α n² + β n k + γ k² + δ k + ε n} ξ^k`
(the book's exponent `a n² + b n k + c k² + d k + e n` is written with Greek letters here). -/
structure QProperData (K : Type*) [Field K] where
  /-- number of factors in the numerator -/
  uu : ℕ
  /-- number of factors in the denominator -/
  vv : ℕ
  a : Fin uu → ℤ
  b : Fin uu → ℤ
  c : Fin uu → K
  u : Fin vv → ℤ
  v : Fin vv → ℤ
  w : Fin vv → K
  α : ℤ
  β : ℤ
  γ : ℤ
  δ : ℤ
  ε : ℤ
  ξ : K

namespace QProperData

/-- CO-376. The value of the q-proper hypergeometric term (4.5.5) at `(n, k)` (with base `q`); it is
meant at points where all arguments `a_s n + b_s k`, `u_s n + v_s k` are nonnegative
(`WellDefinedAt`). -/
@[kb "petkovsekwilfzeilberger1996" "Equation (4.5.5), p. 81"]
def eval (D : QProperData K) (q : K) (n k : ℤ) : K :=
  (∏ s, qFac q (D.c s) (D.a s * n + D.b s * k).toNat) /
      (∏ s, qFac q (D.w s) (D.u s * n + D.v s * k).toNat) *
    q ^ (D.α * n ^ 2 + D.β * n * k + D.γ * k ^ 2 + D.δ * k + D.ε * n) * D.ξ ^ k

/-- All factorial-type arguments are nonnegative at `(n, k)`. -/
def WellDefinedAt (D : QProperData K) (n k : ℤ) : Prop :=
  (∀ s, 0 ≤ D.a s * n + D.b s * k) ∧ ∀ s, 0 ≤ D.u s * n + D.v s * k

end QProperData

/-! ### CO-384 -/

/-- CO-384. A sequence `a(k)` is q-hypergeometric if `a(k+1)/a(k)` is a rational function of `q^k`
(with coefficients involving `q`): `R(q^k) a(k+1) = P(q^k) a(k)` with `R(q^k) ≠ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) q-hypergeometric, p. 196"]
def IsQHypergeometric (q : K) (a : ℕ → K) : Prop :=
  ∃ P R : Polynomial K, ∀ k : ℕ, R.eval (q ^ k) ≠ 0 ∧ R.eval (q ^ k) * a (k + 1) = P.eval (q ^ k) * a k

/-- CO-384. A sequence `a(k)` is bi-basic `(p,q)`-hypergeometric if `a(k+1)/a(k)` is a rational
function of `p^k` and `q^k` (with coefficients involving `p, q`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (unnumbered) bi-basic, p. 196"]
def IsBiBasicHypergeometric (p q : K) (a : ℕ → K) : Prop :=
  ∃ P R : MvPolynomial (Fin 2) K, ∀ k : ℕ, MvPolynomial.eval ![p ^ k, q ^ k] R ≠ 0 ∧
    MvPolynomial.eval ![p ^ k, q ^ k] R * a (k + 1) = MvPolynomial.eval ![p ^ k, q ^ k] P * a k

/-- The sequence `k ↦ Q(k, c)` is q-hypergeometric: its ratio is `1 - c q · q^k`. -/
theorem isQHypergeometric_qFac (q c : K) : IsQHypergeometric q (qFac q c) := by
  refine ⟨Polynomial.C 1 - Polynomial.C (c * q) * Polynomial.X, 1, fun k => ⟨by simp, ?_⟩⟩
  simp [qFac_succ, pow_succ]
  ring

/-- Every q-hypergeometric sequence is bi-basic `(p, q)`-hypergeometric (for any `p`). -/
theorem IsQHypergeometric.isBiBasic {q : K} {a : ℕ → K} (p : K) (h : IsQHypergeometric q a) :
    IsBiBasicHypergeometric p q a := by
  obtain ⟨P, R, hPR⟩ := h
  refine ⟨Polynomial.aeval (MvPolynomial.X 1) P, Polynomial.aeval (MvPolynomial.X 1) R, fun k => ?_⟩
  have e : ∀ S : Polynomial K, MvPolynomial.eval ![p ^ k, q ^ k] (Polynomial.aeval (MvPolynomial.X 1) S)
      = S.eval (q ^ k) := fun S => by
    induction S using Polynomial.induction_on with
    | C c => simp
    | add f g hf hg => simp only [map_add, Polynomial.eval_add, hf, hg]
    | monomial m c ih =>
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        MvPolynomial.algebraMap_eq, MvPolynomial.eval_C]
      simp
  simp only [e]
  exact hPR k

/-! ### CO-429 -/

/-- Values at `(q^n, q^k)` of a polynomial in two variables. -/
def qVal (q : K) (P : MvPolynomial (Fin 2) K) (n k : ℤ) : K := MvPolynomial.eval ![q ^ n, q ^ k] P

/-- CO-429. q-analogue of creative telescoping. Let `F(n,k)` have both ratios rational functions of
`q^n` and `q^k`: `s_2 F(n,k) = s_1 F(n-1,k)` and `r_2 F(n,k+1) = r_1 F(n,k)` with polynomials
`s_1, s_2, r_1, r_2` evaluated at `(q^n, q^k)`. If `p_1, p_2, p_3` give the canonical form (6.3.9) and
`b` solves `p_2(k) b(k+1) - p_3(k-1) b(k) = p_0(k) p_1(k)` (all at the point `(n,k)`), then the
telescoped recurrence `∑_j a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` holds with
`G(n,k) = p_3(k-1) b(k) t_k / p(k)`, at points where `s(k), p(k), p(k+1)` do not vanish. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.4), p. 126"]
theorem q_zeilberger_sound (q : K) (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 r1 r2 : MvPolynomial (Fin 2) K)
    (F : ℤ → ℤ → K)
    (hs : ∀ n k, qVal q s2 n k * F n k = qVal q s1 n k * F (n - 1) k)
    (hr : ∀ n k, qVal q r2 n k * F n (k + 1) = qVal q r1 n k * F n k)
    (p1 p2 p3 b : ℤ → ℤ → K) (n k : ℤ)
    (h9 : (qVal q r1 n k * Zeilberger.s2Prod J (qVal q s2) n k) * p1 n k * p3 n k =
      (qVal q r2 n k * Zeilberger.s2Prod J (qVal q s2) n (k + 1)) * p1 n (k + 1) * p2 n k)
    (h11 : p2 n k * b n (k + 1) - p3 n (k - 1) * b n k =
      Zeilberger.p0 J a (qVal q s1) (qVal q s2) n k * p1 n k)
    (hs0 : qVal q r2 n k * Zeilberger.s2Prod J (qVal q s2) n (k + 1) ≠ 0)
    (hp : Zeilberger.p0 J a (qVal q s1) (qVal q s2) n k * p1 n k ≠ 0)
    (hp1 : Zeilberger.p0 J a (qVal q s1) (qVal q s2) n (k + 1) * p1 n (k + 1) ≠ 0) :
    ∑ j ∈ range (J + 1), a j n * F (n + j) k =
      p3 n (k + 1 - 1) * b n (k + 1) * Zeilberger.tSeq J a F n (k + 1) /
          (Zeilberger.p0 J a (qVal q s1) (qVal q s2) n (k + 1) * p1 n (k + 1)) -
        p3 n (k - 1) * b n k * Zeilberger.tSeq J a F n k /
          (Zeilberger.p0 J a (qVal q s1) (qVal q s2) n k * p1 n k) :=
  Zeilberger.zeilberger_sound J a (qVal q s1) (qVal q s2) (qVal q r1) (qVal q r2) F hs hr
    p1 p2 p3 b n k h9 h11 hs0 hp hp1

/-- CO-429 (the certificate is a rational multiple of `F`). With the notation of
`q_zeilberger_sound`, `G(n,k) = p_3(k-1) b(k) t_k / p(k)` equals `R(n,k) F(n,k)` with
`R = p_3(k-1) b(k) / (p_1(k) ∏_{r=1}^{J} s_2(n+r,k))`, wherever `p_0(k)` and the product do not vanish:
`R` is rational in `q^n, q^k` when `p_1, p_3, b` are. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.4), p. 126"]
theorem certificate_eq_ratio_mul (J : ℕ) (a : ℕ → ℤ → K) (s1 s2 F : ℤ → ℤ → K)
    (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k) (p1 p3 b : ℤ → ℤ → K) (n k : ℤ)
    (hp0 : Zeilberger.p0 J a s1 s2 n k ≠ 0) (hprod : Zeilberger.s2Prod J s2 n k ≠ 0) :
    p3 n (k - 1) * b n k * Zeilberger.tSeq J a F n k / (Zeilberger.p0 J a s1 s2 n k * p1 n k) =
      p3 n (k - 1) * b n k / (p1 n k * Zeilberger.s2Prod J s2 n k) * F n k := by
  have h := Zeilberger.tSeq_mul_s2Prod J a s1 s2 F hs n k
  have ht : Zeilberger.tSeq J a F n k =
      Zeilberger.p0 J a s1 s2 n k * F n k / Zeilberger.s2Prod J s2 n k := by
    rw [eq_div_iff hprod, h]
  rw [ht]
  by_cases hp1 : p1 n k = 0
  · simp [hp1]
  · field_simp

end QAnalogue

end UndergradKB.Combinatorics.AeqB
