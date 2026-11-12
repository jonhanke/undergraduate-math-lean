import UndergradKB.Combinatorics.Counting.Bell
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Combinatorics.AeqB.Summation2
import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.ClosedForm
import UndergradKB.Combinatorics.AeqB.Holonomic
import UndergradKB.Combinatorics.AeqB.Companions
import UndergradKB.Combinatorics.AeqB.Identities2
import UndergradKB.Combinatorics.AeqB.Identities3
import UndergradKB.Combinatorics.AeqB.Identities3c
import UndergradKB.Combinatorics.AeqB.QAnalogue
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 9: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch09b

open UndergradKB.Combinatorics.AeqB

/-- CO-512. A nowhere-zero sequence `x` is annihilated by the first-order operator
`N - x(n+1)/x(n)`, which is why polynomial coefficients are needed for a meaningful theory. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 184"]
theorem text_p184_nowhere_zero_first_order {K : Type*} [Field K] (x : ℕ → K)
    (hx : ∀ n : ℕ, x n ≠ 0) (n : ℕ) : 1 * x (n + 1) + -(x (n + 1) / x n) * x n = 0 :=
  Identities3c.nowhere_zero_first_order x hx n

/-- CO-513. Every hypergeometric sequence is P-recursive (satisfies a linear recurrence with
polynomial coefficients). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
theorem def_9_2_1_hypergeometric_is_p_recursive {K : Type*} [Field K] [CharZero K] {t : ℕ → K}
    (h : IsHypergeometric t) : IsPRecursive t :=
  h.isPRecursive

/-- CO-514. Algorithm findrec: the coefficient vector of a recurrence of order `r` and degree
`D` satisfied by the first `M` terms is exactly an element of the kernel of the linear map
`findrecMap`; and the coefficients of any true recurrence lie in it. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 185"]
theorem text_p185_findrec {K : Type*} [Field K] (y : ℕ → K) (r D M : ℕ) :
    (∀ c : Fin (r + 1) → Fin (D + 1) → K, c ∈ (findrecMap y r D M).ker ↔
      ∀ m : Fin M, ∑ i : Fin (r + 1),
        Polynomial.eval ((m : ℕ) : K) (coeffPoly D (c i)) * y ((m : ℕ) + (i : ℕ)) = 0) ∧
    (∀ p : Fin (r + 1) → Polynomial K, (∀ i, (p i).natDegree ≤ D) →
      (∀ n : ℕ, ∑ i : Fin (r + 1), Polynomial.eval (n : K) (p i) * y (n + (i : ℕ)) = 0) →
      (fun (i : Fin (r + 1)) (j : Fin (D + 1)) => (p i).coeff (j : ℕ)) ∈ (findrecMap y r D M).ker) :=
  ⟨fun c => mem_ker_findrecMap_iff y r D M c, fun p hp hrec => coeffs_mem_ker_findrecMap y r D M p hp hrec⟩

/-- CO-432. If `∑_j a_j(n) F(n+j,k) = G(n,k+1) - G(n,k)` and `F`, `G` vanish at `±∞`
(with convergence), then summing over `k` gives `∑_j a_j(n) A(n+j) = 0` for `A(n) = ∑_k F(n,k)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 187"]
theorem text_p187_sum_recurrence {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] (J : ℕ) (a : ℕ → ℤ → R) (F G : ℤ → ℤ → R)
    (h : ∀ n k : ℤ, ∑ j ∈ Finset.range (J + 1), a j n * F (n + (j : ℤ)) k = G n (k + 1) - G n k)
    (n : ℤ) (hF : ∀ j ≤ J, Summable (F (n + (j : ℤ))))
    (hGt : Filter.Tendsto (G n) Filter.atTop (nhds 0))
    (hGb : Filter.Tendsto (G n) Filter.atBot (nhds 0)) :
    ∑ j ∈ Finset.range (J + 1), a j n * ∑' k : ℤ, F (n + (j : ℤ)) k = 0 :=
  tsum_recurrence J a F G h n hF hGt hGb

/-- CO-433. Elimination: if `P F = Q F = 0` and `A P + B Q = S + (K - 1) R̄` with `S` free of
`K` and `k`, then `S F = 0`, the certificate `G = -R̄ F` telescopes, and for finitely supported
`F` and `R̄ F` the sum `∑_k F(n,k)` satisfies the recurrence `S`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 187"]
theorem text_p187_elimination {K : Type*} [Field K]
    (P Q A B Rbar : Module.End K (ℤ → ℤ → K)) (J : ℕ) (s : ℕ → ℤ → K) (F : ℤ → ℤ → K)
    (hP : P F = 0) (hQ : Q F = 0)
    (h : A * P + B * Q = Holonomic.sOp J s + (Holonomic.opK K - 1) * Rbar) :
    (A * P + B * Q) F = 0 ∧
    (∀ n k : ℤ, ∑ j ∈ Finset.range (J + 1), s j n * F (n + (j : ℤ)) k =
      (-Rbar F) n (k + 1) - (-Rbar F) n k) ∧
    ((∀ n : ℤ, (Function.support (F n)).Finite) →
      (∀ n : ℤ, (Function.support (Rbar F n)).Finite) →
      ∀ n : ℤ, ∑ j ∈ Finset.range (J + 1), s j n * ∑ᶠ k : ℤ, F (n + (j : ℤ)) k = 0) :=
  Holonomic.elimination P Q A B Rbar J s F hP hQ h

/-- CO-515. The operator algebra in `n, k, N, K`: the shifts commute with each other and with
the other variable (`NK = KN`, `Nk = kN`, `nK = Kn`, `nk = kn`), while `Nn = (n+1)N` and
`Kk = (k+1)K`. -/
@[kb "petkovsekwilfzeilberger1996" "text (9.3.1-9.3.3), p. 187"]
theorem eq_9_3_1_operator_relations (K : Type*) [Field K] :
    Holonomic.opN K * Holonomic.opK K = Holonomic.opK K * Holonomic.opN K ∧
    Holonomic.opN K * Holonomic.opk K = Holonomic.opk K * Holonomic.opN K ∧
    Holonomic.opn K * Holonomic.opK K = Holonomic.opK K * Holonomic.opn K ∧
    Holonomic.opn K * Holonomic.opk K = Holonomic.opk K * Holonomic.opn K ∧
    Holonomic.opN K * Holonomic.opn K = (Holonomic.opn K + 1) * Holonomic.opN K ∧
    Holonomic.opK K * Holonomic.opk K = (Holonomic.opk K + 1) * Holonomic.opK K :=
  Holonomic.relations K

/-- CO-434. Modified elimination problem: given `P, Q`, find `A, B, C` with
`S = A P + B Q + (K - 1) C` free of `K` and `k`; then `S` gives the recurrence for the sum
(Almkvist's observation). -/
@[kb "petkovsekwilfzeilberger1996" "text (Modified elimination problem), p. 189"]
theorem def_p189_modified_elimination {K : Type*} [Field K]
    (P Q A B C : Module.End K (ℤ → ℤ → K)) (J : ℕ) (s : ℕ → ℤ → K) (F : ℤ → ℤ → K)
    (hP : P F = 0) (hQ : Q F = 0)
    (h : Holonomic.sOp J s = A * P + B * Q + (Holonomic.opK K - 1) * C) :
    (∀ n k : ℤ, ∑ j ∈ Finset.range (J + 1), s j n * F (n + (j : ℤ)) k =
      C F n (k + 1) - C F n k) ∧
    ((∀ n : ℤ, (Function.support (F n)).Finite) →
      (∀ n : ℤ, (Function.support (C F n)).Finite) →
      ∀ n : ℤ, ∑ j ∈ Finset.range (J + 1), s j n * ∑ᶠ k : ℤ, F (n + (j : ℤ)) k = 0) :=
  Holonomic.modified_elimination P Q A B C J s F hP hQ h

/-- CO-052. Chu–Vandermonde in the form `∑_k C(n,k) C(b,k) = C(n+b,b)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Chu-Vandermonde), p. 190"]
theorem text_p190_chu_vandermonde (n b : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k * b.choose k = (n + b).choose b :=
  Companions.sum_choose_mul_choose n b

/-- CO-212. The exponential generating function `T(x)` of rooted labelled trees (counted by
`n^(n-1)`) satisfies the transcendental equation `T = x e^T`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 194"]
theorem text_p194_tree_series : treeSeries = PowerSeries.X * PowerSeries.subst treeSeries (PowerSeries.exp ℚ) :=
  treeSeries_eq_X_mul_exp

/-- CO-213 (partial). The Bell numbers satisfy `B_{n+1} = ∑_k C(n,k) B_k` and have exponential
generating function `exp(e^x - 1)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 195"]
theorem text_p195_bell_numbers :
    (∀ n : ℕ, bellNumber (n + 1) = ∑ k ∈ Finset.range (n + 1), n.choose k * bellNumber k) ∧
    bellSeries = PowerSeries.subst (PowerSeries.exp ℚ - 1) (PowerSeries.exp ℚ) :=
  ⟨bellNumber_succ, bellSeries_eq_exp_exp_sub_one⟩

/-- CO-384. A q-hypergeometric sequence is bi-basic `(p, q)`-hypergeometric for every `p`
(a `q`-hypergeometric sequence has ratio rational in `q^k`, and bi-basic ones rational in
`p^k` and `q^k`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (q-hypergeometric, bi-basic), p. 196"]
theorem def_p196_q_hypergeometric_bibasic {K : Type*} [Field K] (q p : K) (a : ℕ → K)
    (h : QAnalogue.IsQHypergeometric q a) : QAnalogue.IsBiBasicHypergeometric p q a :=
  QAnalogue.IsQHypergeometric.isBiBasic p h

/-- CO-435. If `F(n,k) = -F(n, n+α-k)` for an integer `α`, then `∑_k F(n,k) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 198"]
theorem text_p198_antisymmetric_sum_vanishes {R : Type*} [Ring R] [NoZeroDivisors R] [CharZero R]
    (F : ℤ → ℤ → R) (α : ℤ) (h : ∀ n k : ℤ, F n k = -F n (n + α - k)) (n : ℤ) :
    ∑ᶠ k : ℤ, F n k = 0 :=
  finsum_eq_zero_of_reflect F α h n

/-- CO-436 (partial). Creative anti-symmetrizing: for finitely supported `F, G`, it suffices that
`∑_j s_j(n) F(n+j,k) - (G(n,k+1) - G(n,k))` be antisymmetric under `k ↦ n+α-k` to get the
recurrence `∑_j s_j(n) A(n+j) = 0` for `A(n) = ∑_k F(n,k)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 198"]
theorem text_p198_antisymmetrizing {K : Type*} [Field K] [CharZero K] (J : ℕ) (s : ℕ → ℤ → K)
    (F G : ℤ → ℤ → K) (α : ℤ) (hF : ∀ n : ℤ, (Function.support (F n)).Finite)
    (hG : ∀ n : ℤ, (Function.support (G n)).Finite)
    (h : ∀ n k : ℤ,
      ∑ j ∈ Finset.range (J + 1), s j n * F (n + (j : ℤ)) k - (G n (k + 1) - G n k) =
        -(∑ j ∈ Finset.range (J + 1), s j n * F (n + (j : ℤ)) (n + α - k) -
          (G n (n + α - k + 1) - G n (n + α - k)))) (n : ℤ) :
    ∑ j ∈ Finset.range (J + 1), s j n * ∑ᶠ k : ℤ, F (n + (j : ℤ)) k = 0 :=
  Holonomic.antisymmetrizing J s F G α hF hG h n

/-- CO-438. Symmetrizing for multisums: if the sum over permutations of the coordinates of
`P F - ∑_i Δ_i G_i` vanishes (finite supports), then the multisum satisfies the recurrence. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 198"]
theorem text_p198_symmetrizer_multisum {K : Type*} [Field K] [CharZero K] {r : ℕ} (J : ℕ)
    (s : ℕ → ℤ → K) (F : ℤ → (Fin r → ℤ) → K) (G : Fin r → ℤ → (Fin r → ℤ) → K)
    (hF : ∀ n : ℤ, (Function.support (F n)).Finite)
    (hG : ∀ (i : Fin r) (n : ℤ), (Function.support (G i n)).Finite)
    (h : ∀ (n : ℤ) (k : Fin r → ℤ), ∑ π : Equiv.Perm (Fin r),
      (∑ j ∈ Finset.range (J + 1), s j n * F (n + (j : ℤ)) (k ∘ π) -
        ∑ i : Fin r, (G i n (k ∘ π + Pi.single i 1) - G i n (k ∘ π))) = 0) (n : ℤ) :
    ∑ j ∈ Finset.range (J + 1), s j n * ∑ᶠ k : Fin r → ℤ, F (n + (j : ℤ)) k = 0 :=
  Holonomic.symmetrizer_multisum J s F G hF hG h n

/-- CO-519. The operator relations for P-Di functions: `T x = 2 x T`, `E x = x E + E`,
`E T = T E²`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 199"]
theorem text_p199_pdi_relations :
    Holonomic.opT * Holonomic.opX = (2 : ℝ) • (Holonomic.opX * Holonomic.opT) ∧
    Holonomic.opE * Holonomic.opX = Holonomic.opX * Holonomic.opE + Holonomic.opE ∧
    Holonomic.opE * Holonomic.opT = Holonomic.opT * Holonomic.opE ^ 2 :=
  Holonomic.pdi_relations

/-- CO-520. Integrals of Di-holonomic functions: if a polynomial-coefficient combination of
the shifted and doubled functions `F(2^a x + b, 2^c y + d)` vanishes, then the corresponding
combination of the integrals over `y` (scaled by `(1/2)^c`) vanishes. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 199"]
theorem text_p199_integral_annihilated (S : Finset (ℕ × ℕ × ℕ × ℕ)) (c : ℕ × ℕ × ℕ × ℕ → ℝ → ℝ)
    (F : ℝ → ℝ → ℝ)
    (hint : ∀ m ∈ S, ∀ x : ℝ, MeasureTheory.Integrable
      (fun y : ℝ => F (2 ^ m.1 * x + (m.2.1 : ℝ)) (2 ^ m.2.2.1 * y + (m.2.2.2 : ℝ)))
      MeasureTheory.volume)
    (h : ∀ x y : ℝ, ∑ m ∈ S, c m x *
      F (2 ^ m.1 * x + (m.2.1 : ℝ)) (2 ^ m.2.2.1 * y + (m.2.2.2 : ℝ)) = 0) (x : ℝ) :
    ∑ m ∈ S, c m x * (1 / 2) ^ m.2.2.1 * ∫ y : ℝ, F (2 ^ m.1 * x + (m.2.1 : ℝ)) y = 0 :=
  Holonomic.integral_annihilated S c F hint h x

/-- CO-053. Abel-type identity `∑_k C(n,k) (k+r)^(k-1) (s-k)^(n-k) = (r+s)^n / r` for `r ≠ 0`,
and its special case `∑_k C(n,k) (k+1)^(k-1) (n-k+1)^(n-k) = (n+2)^n`. -/
@[kb "petkovsekwilfzeilberger1996" "text (9.11.1, 9.11.2), p. 200"]
theorem text_p200_abel_identity :
    (∀ {K : Type*} [Field K] [CharZero K] (r s : K), r ≠ 0 → ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), (n.choose k : K) * ((k : K) + r) ^ ((k : ℤ) - 1) * (s - k) ^ (n - k) =
        (r + s) ^ n / r) ∧
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), n.choose k * (k + 1) ^ (k - 1) * (n - k + 1) ^ (n - k) =
      (n + 2) ^ n) :=
  ⟨fun r s hr n => Identities2.abel_identity r s hr n, Identities2.abel_special⟩

/-- CO-054. Euler's identity `∑_k (-1)^k C(n,k) (x-k)^n = n!`. -/
@[kb "petkovsekwilfzeilberger1996" "text (9.11.3), p. 201"]
theorem eq_9_11_3_euler_identity {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * (n.choose k : R) * (x - k) ^ n = (n.factorial : R) :=
  euler_identity n x

/-- CO-385. Pfaff–Saalschütz as a binomial-product identity (Exercise 9.14.3):
`C(a+b,a+k) C(a+c,c+k) C(b+c,b+k) = ∑_n (a+b+c-n)!/((a-n)!(b-n)!(c-n)!(n+k)!(n-k)!)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 203"]
theorem text_p203_pfaff_saalschutz (a b c k : ℕ) :
    (((a + b).choose (a + k) : ℕ) : ℚ) * (((a + c).choose (c + k) : ℕ) : ℚ) *
        (((b + c).choose (b + k) : ℕ) : ℚ) =
      ∑ n ∈ Finset.Icc k (min a (min b c)),
        ((a + b + c - n).factorial : ℚ) /
          (((a - n).factorial : ℚ) * ((b - n).factorial : ℚ) * ((c - n).factorial : ℚ) *
            ((n + k).factorial : ℚ) * ((n - k).factorial : ℚ)) :=
  Identities3.pfaff_saalschutz a b c k

end UndergradKB.Combinatorics.Course.AeqB.Ch09b
