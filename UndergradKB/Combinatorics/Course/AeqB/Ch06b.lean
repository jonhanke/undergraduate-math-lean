import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Combinatorics.AeqB.Identities
import UndergradKB.Combinatorics.AeqB.Identities2
import UndergradKB.Combinatorics.AeqB.Certificates3
import UndergradKB.Combinatorics.AeqB.WZProof
import UndergradKB.Combinatorics.AeqB.Zeilberger
import UndergradKB.Combinatorics.AeqB.Telescoping2
import UndergradKB.Combinatorics.AeqB.QAnalogue
import UndergradKB.Common.Attr

/-!
# A=B, Chapter 6: course wrappers of results proved in this library (wave 3)
-/

open Finset Polynomial MeasureTheory Filter Topology
open UndergradKB.Combinatorics.AeqB

namespace UndergradKB.Combinatorics.Course.AeqB.Ch06b

/-- CO-423. For `f(n) = ∑_{0 ≤ k ≤ n/3} 2^k n/(n-k) C(n-k,2k)` one gets
`f(n) = 2^{n-1} + cos(nπ/2)` for `n ≥ 2` (from the recurrence `(N²+1)(N-2) f = 0`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.1.1, p. 114"]
theorem ex_6_1_1_monthly_sum (n : ℕ) (hn : 2 ≤ n) :
    MonthlySum.fSum n = 2 ^ (n - 1) + (MonthlySum.wSeq n : ℚ) ∧
    (MonthlySum.fSum n : ℝ) = 2 ^ (n - 1) + Real.cos (n * Real.pi / 2) :=
  ⟨MonthlySum.fSum_formula n hn, MonthlySum.fSum_formula_cos n hn⟩

/-- CO-424. (partial) Existence of creative telescoping: a nontrivial `k`-free recurrence of
two-variable shape (with finitely supported summand) yields a nontrivial telescoped recurrence
with some `G`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 6.2.1, p. 115"]
theorem thm_6_2_1_exists_nontrivial_telescoped {K : Type*} [Field K] (F : ℤ → ℤ → K)
    (hF : ∀ n, (Function.support (F n)).Finite) (J : ℕ) :
    ∀ (I : ℕ) (a : ℕ → ℕ → Polynomial K),
    (∃ i ≤ I, ∃ j ≤ J, a i j ≠ 0) →
    (∀ n k : ℤ, ∑ i ∈ range (I + 1), ∑ j ∈ range (J + 1),
      (a i j).eval (n : K) * F (n + j) (k + i) = 0) →
    ∃ c : ℕ → Polynomial K, (∃ j ≤ J, c j ≠ 0) ∧
      ∃ G : ℤ → ℤ → K, Zeilberger.IsTelescopedRecurrence J (fun j n => (c j).eval (n : K)) F G :=
  Zeilberger.exists_nontrivial_telescoped F hF J

/-- CO-425. Zeilberger's algorithm (soundness): with the data of equations (6.3.1)-(6.3.12), the
sum `∑_j a_j(n) F(n+j,k)` telescopes as `G(n,k+1) - G(n,k)` with `G = p₃(k-1) b(k) t_k / (p₀ p₁)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.3.1)-(6.3.12), p. 116-119"]
theorem text_p116_zeilberger_sound {K : Type*} [Field K] (J : ℕ) (a : ℕ → ℤ → K)
    (s1 s2 r1 r2 F : ℤ → ℤ → K)
    (hs : ∀ n k, s2 n k * F n k = s1 n k * F (n - 1) k)
    (hr : ∀ n k, r2 n k * F n (k + 1) = r1 n k * F n k)
    (p1 p2 p3 b : ℤ → ℤ → K) (n k : ℤ)
    (h9 : (r1 n k * Zeilberger.s2Prod J s2 n k) * p1 n k * p3 n k =
      (r2 n k * Zeilberger.s2Prod J s2 n (k + 1)) * p1 n (k + 1) * p2 n k)
    (h11 : p2 n k * b n (k + 1) - p3 n (k - 1) * b n k = Zeilberger.p0 J a s1 s2 n k * p1 n k)
    (hs0 : r2 n k * Zeilberger.s2Prod J s2 n (k + 1) ≠ 0)
    (hp : Zeilberger.p0 J a s1 s2 n k * p1 n k ≠ 0)
    (hp1 : Zeilberger.p0 J a s1 s2 n (k + 1) * p1 n (k + 1) ≠ 0) :
    ∑ j ∈ range (J + 1), a j n * F (n + j) k =
      p3 n (k + 1 - 1) * b n (k + 1) * Zeilberger.tSeq J a F n (k + 1) /
          (Zeilberger.p0 J a s1 s2 n (k + 1) * p1 n (k + 1)) -
        p3 n (k - 1) * b n k * Zeilberger.tSeq J a F n k /
          (Zeilberger.p0 J a s1 s2 n k * p1 n k) :=
  Zeilberger.zeilberger_sound J a s1 s2 r1 r2 F hs hr p1 p2 p3 b n k h9 h11 hs0 hp hp1

/-- CO-426. If `t_k` has Gosper-type ratio `p(k+1) p₂(k) / (p(k) p₃(k))` and `b` solves
`p₂(k) b(k+1) - p₃(k-1) b(k) = p(k)`, then `G = p₃(k-1) b(k) t_k / p(k)` telescopes:
`G(k+1) - G(k) = t_k`. -/
@[kb "petkovsekwilfzeilberger1996" "Equations (6.3.11)-(6.3.12), p. 118-119"]
theorem eq_6_3_12_gosper_step {K : Type*} [Field K] {t p p2 p3 b : ℤ → K} (k : ℤ)
    (h10 : t (k + 1) * p k * p3 k = t k * p (k + 1) * p2 k)
    (h11 : p2 k * b (k + 1) - p3 (k - 1) * b k = p k) (hp : p k ≠ 0) (hp1 : p (k + 1) ≠ 0) :
    p3 (k + 1 - 1) * b (k + 1) * t (k + 1) / p (k + 1) - p3 (k - 1) * b k * t k / p k = t k :=
  Zeilberger.gosper_step k h10 h11 hp hp1

/-- CO-427. The unknowns `a_j` and the polynomial `b` enter linearly: the equation
`p₂ b(k+1) - p₃(k-1) b(k) = p₁ ∑ a_j w_j` is the kernel of a linear map in `(a, b)`. -/
@[kb "petkovsekwilfzeilberger1996" "text after (6.3.11), p. 118"]
theorem text_p118_zeilberger_system {R : Type*} [CommRing R] (J : ℕ) (w : ℕ → R[X])
    (p1 p2 p3 : R[X]) (a : Fin (J + 1) → R) (b : R[X]) :
    Zeilberger.zeilbergerSystem J w p1 p2 p3 (a, b) = 0 ↔
      p2 * b.comp (X + 1) - p3.comp (X - 1) * b = p1 * ∑ j : Fin (J + 1), C (a j) * w j :=
  Zeilberger.zeilbergerSystem_eq_zero_iff J w p1 p2 p3 a b

/-- CO-377. `∑_k (-1)^k C(n,k) / C(x+k,k) = x/(x+n)`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.4.2, p. 120"]
theorem ex_6_4_2_kummer_sum (x : ℚ) (hx : ∀ n : ℕ, x + n ≠ 0) (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) / Ring.choose (x + (k : ℚ)) k
      = x / (x + n) :=
  kummer_sum x hx n

/-- CO-378. `∑_k (-1)^k C(n+1,k) C(2n-2k+1,n) = 1` for `n ≥ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.4.3, p. 121"]
theorem ex_6_4_3_alt_sum_choose_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ((n + 1).choose k : ℤ) * ((2 * n + 1 - 2 * k).choose n : ℤ)
      = 1 :=
  alt_sum_choose_choose n

/-- CO-428. Continuous creative telescoping: if `G(n, ·)` has derivative
`∑_j a_j(n) F(n+j, ·)` and vanishes at `±∞`, then `∑_j a_j(n) ∫ F(n+j, y) dy = 0`; the same
argument gives a differential equation for `∫ D(x, y) dy`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 122"]
theorem text_p122_continuous_telescoping :
    (∀ (J : ℕ) (a : ℕ → ℤ → ℝ) (F : ℤ → ℝ → ℝ) (G : ℤ → ℝ → ℝ) (n : ℤ),
      (∀ j ≤ J, Integrable (F (n + j))) →
      (∀ y, HasDerivAt (G n) (∑ j ∈ range (J + 1), a j n * F (n + j) y) y) →
      Tendsto (G n) atTop (𝓝 0) → Tendsto (G n) atBot (𝓝 0) →
      ∑ j ∈ range (J + 1), a j n * ∫ y, F (n + j) y = 0) ∧
    (∀ (J : ℕ) (a : ℕ → ℝ → ℝ) (D : ℕ → ℝ → ℝ → ℝ) (G : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ),
      (∀ j ≤ J, Integrable (D j x)) →
      (∀ y, HasDerivAt (G x) (∑ j ∈ range (J + 1), a j x * D j x y) y) →
      Tendsto (G x) atTop (𝓝 0) → Tendsto (G x) atBot (𝓝 0) →
      (∀ j ≤ J, iteratedDeriv j f x = ∫ y, D j x y) →
      ∑ j ∈ range (J + 1), a j x * iteratedDeriv j f x = 0) :=
  ⟨fun J a F G n hF hG hGt hGb => Continuous.integral_telescoping_recurrence J a F G n hF hG hGt hGb,
    fun J a D G f x hD hG hGt hGb hf => Continuous.integral_telescoping_ode J a D G f x hD hG hGt hGb hf⟩

/-- CO-379. `∑_k C(n,2k) C(2k,k) 4^{-k} = 2^{-(n-1)} C(2n-1,n-1)`, written with `n = m + 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.5.1), p. 123"]
theorem text_p123_sum_choose_two_mul_centralBinom_div (m : ℕ) :
    ∑ k ∈ range (m + 2), ((m + 1).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) / 4 ^ k
      = ((2 * m + 1).choose m : ℚ) / 2 ^ m :=
  sum_choose_two_mul_centralBinom_div m

/-- CO-545. Recurrences from creative telescoping or Sister Celine are self-certifying: if the
shifts of `F` are `ρ`-multiples of `F n k`, then the rational-function identity
`∑ a_{ij} ρ_{ij} = 0` implies the recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 123"]
theorem text_p123_recurrence_of_ratio_identity {K : Type*} [CommRing K] (s : Finset (ℕ × ℕ))
    (a : ℕ → ℕ → K) (F : ℤ → ℤ → K) (n k : ℤ) (ρ : ℕ → ℕ → K)
    (hρ : ∀ p ∈ s, F (n - p.2) (k - p.1) = ρ p.1 p.2 * F n k)
    (h : ∑ p ∈ s, a p.1 p.2 * ρ p.1 p.2 = 0) :
    ∑ p ∈ s, a p.1 p.2 * F (n - p.2) (k - p.1) = 0 :=
  recurrence_of_ratio_identity s a F n k ρ hρ h

/-- CO-380. `∑_k C(n+k,2k) C(2k,k) (-1)^k/(k+1)` is `1` for `n = 0` and `0` for `n ≥ 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 6.5.2, p. 125"]
theorem ex_6_5_2_sum_choose_centralBinom_alt_div (n : ℕ) :
    ∑ k ∈ range (n + 1), ((n + k).choose (2 * k) : ℚ) * ((2 * k).choose k : ℚ) * (-1) ^ k / (k + 1)
      = if n = 0 then 1 else 0 :=
  sum_choose_centralBinom_alt_div n

/-- CO-429. The `q`-analogue of Zeilberger's algorithm (soundness): for `F` with ratios rational in
`q^n, q^k`, the sum `∑_j a_j(n) F(n+j,k)` telescopes as `G(n,k+1) - G(n,k)` with `G = R F`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.4), p. 126"]
theorem eq_6_5_4_q_zeilberger_sound {K : Type*} [Field K] (q : K) (J : ℕ) (a : ℕ → ℤ → K)
    (s1 s2 r1 r2 : MvPolynomial (Fin 2) K) (F : ℤ → ℤ → K)
    (hs : ∀ n k, QAnalogue.qVal q s2 n k * F n k = QAnalogue.qVal q s1 n k * F (n - 1) k)
    (hr : ∀ n k, QAnalogue.qVal q r2 n k * F n (k + 1) = QAnalogue.qVal q r1 n k * F n k)
    (p1 p2 p3 b : ℤ → ℤ → K) (n k : ℤ)
    (h9 : (QAnalogue.qVal q r1 n k * Zeilberger.s2Prod J (QAnalogue.qVal q s2) n k) * p1 n k *
        p3 n k =
      (QAnalogue.qVal q r2 n k * Zeilberger.s2Prod J (QAnalogue.qVal q s2) n (k + 1)) *
        p1 n (k + 1) * p2 n k)
    (h11 : p2 n k * b n (k + 1) - p3 n (k - 1) * b n k =
      Zeilberger.p0 J a (QAnalogue.qVal q s1) (QAnalogue.qVal q s2) n k * p1 n k)
    (hs0 : QAnalogue.qVal q r2 n k * Zeilberger.s2Prod J (QAnalogue.qVal q s2) n (k + 1) ≠ 0)
    (hp : Zeilberger.p0 J a (QAnalogue.qVal q s1) (QAnalogue.qVal q s2) n k * p1 n k ≠ 0)
    (hp1 : Zeilberger.p0 J a (QAnalogue.qVal q s1) (QAnalogue.qVal q s2) n (k + 1) *
      p1 n (k + 1) ≠ 0) :
    ∑ j ∈ range (J + 1), a j n * F (n + j) k =
      p3 n (k + 1 - 1) * b n (k + 1) * Zeilberger.tSeq J a F n (k + 1) /
          (Zeilberger.p0 J a (QAnalogue.qVal q s1) (QAnalogue.qVal q s2) n (k + 1) *
            p1 n (k + 1)) -
        p3 n (k - 1) * b n k * Zeilberger.tSeq J a F n k /
          (Zeilberger.p0 J a (QAnalogue.qVal q s1) (QAnalogue.qVal q s2) n k * p1 n k) :=
  QAnalogue.q_zeilberger_sound q J a s1 s2 r1 r2 F hs hr p1 p2 p3 b n k h9 h11 hs0 hp hp1

/-- CO-430. Paule's symmetrization: an unrestricted sum over `k` of a finitely supported `f`
equals the sum of `(f(k) + f(-k))/2`, and likewise `∑_{k ≤ n} f k = ∑_{k ≤ n} (f k + f (n-k))/2`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 126"]
theorem text_p126_symmetrize :
    (∀ {K : Type*} [Field K] [CharZero K] (f : ℤ → K), (Function.support f).Finite →
      ∑ᶠ k : ℤ, f k = ∑ᶠ k : ℤ, (f k + f (-k)) / 2) ∧
    (∀ {K : Type*} [Field K] [CharZero K] (f : ℕ → K) (n : ℕ),
      ∑ k ∈ range (n + 1), f k = ∑ k ∈ range (n + 1), (f k + f (n - k)) / 2) :=
  ⟨fun f hf => Identities2.finsum_symmetrize f hf, fun f n => Identities2.sum_range_symmetrize f n⟩

/-- CO-382. A finite Rogers-Ramanujan-type identity in symmetrized form is certified by the
order-2 operator `A` with explicit certificates `R_L`, `R_R`: the telescoping relations
`A F_L = R_L F_L - R_L(k-1) F_L(k-1)` and the analogue for `F_R`. -/
@[kb "petkovsekwilfzeilberger1996" "Equation (6.5.7), p. 127"]
theorem eq_6_5_7_paule_certificates {K : Type*} [Field K] (q : K)
    (hP : ∀ t, 0 < t → 1 - q ^ t ≠ 0) :
    (∀ n k : ℕ, 1 ≤ k → k + 2 ≤ n →
      RogersRamanujan.applyA q (RogersRamanujan.FL q) n k =
        RogersRamanujan.RL q n k * RogersRamanujan.FL q n k -
          RogersRamanujan.RL q n (k - 1) * RogersRamanujan.FL q n (k - 1)) ∧
    ((∀ t, 1 + q ^ t ≠ 0) → ∀ n k : ℕ, 1 ≤ k → k + 2 ≤ n →
      RogersRamanujan.applyA q (RogersRamanujan.FR q) n k =
        RogersRamanujan.RR q n k * RogersRamanujan.FR q n k -
          RogersRamanujan.RR q n (k - 1) * RogersRamanujan.FR q n (k - 1)) :=
  ⟨fun n k hk hn => RogersRamanujan.paule_left q hP n k hk hn,
    fun hQ n k hk hn => RogersRamanujan.paule_right q hP hQ n k hk hn⟩

end UndergradKB.Combinatorics.Course.AeqB.Ch06b
