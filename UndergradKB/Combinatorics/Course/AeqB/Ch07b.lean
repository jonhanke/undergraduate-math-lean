import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Normed.Group.Tannery
import UndergradKB.Combinatorics.AeqB.WZ
import UndergradKB.Combinatorics.AeqB.WZProof
import UndergradKB.Combinatorics.AeqB.Certificates
import UndergradKB.Combinatorics.AeqB.Certificates2
import UndergradKB.Combinatorics.AeqB.Certificates3
import UndergradKB.Combinatorics.AeqB.Certificates4
import UndergradKB.Combinatorics.AeqB.Companions
import UndergradKB.Combinatorics.AeqB.Identities
import UndergradKB.Combinatorics.AeqB.Identities2
import UndergradKB.Combinatorics.AeqB.Identities3d
import UndergradKB.Combinatorics.AeqB.PartialSumAsymptotic
import UndergradKB.Combinatorics.AeqB.Zeilberger
import UndergradKB.Combinatorics.AeqB.Gosper
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 7: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch07b

open UndergradKB.Combinatorics.AeqB

/-- CO-443. A WZ pair is a pair `(F, G)` of two-variable hypergeometric functions satisfying
`F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (7.1.2), p. 132"]
theorem eq_7_1_2_wz_pair {K : Type*} [CommRing K] (F G : ℤ → ℤ → K) :
    IsWZPair F G ↔ IsHypergeometric₂ F ∧ IsHypergeometric₂ G ∧
      ∀ n k : ℤ, F (n + 1) k - F n k = G n (k + 1) - G n k :=
  ⟨fun h => ⟨h.hyper_left, h.hyper_right, h.eq⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- CO-444. The WZ certificate of `∑_k C(n,k)^2 / C(2n,n) = 1` (with `R(n,k) = centralR n k`
from the book), in the range where the summand is supported. -/
@[kb "petkovsekwilfzeilberger1996" "Example 7.1.1, p. 132"]
theorem ex_7_1_1_central_cert (n k : ℤ) (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    centralF (n + 1) k - centralF n k =
      centralR n (k + 1) * centralF n (k + 1) - centralR n k * centralF n k :=
  central_cert n k hn hk hkn

/-- CO-445. Finding a certificate (partial): for the summand `F`, if the difference
`F(n+1,k) - F(n,k)` is hypergeometric and similar to `F(n,·)`, with Gosper data `(a,b,c)`, then
Gosper's algorithm succeeds exactly when a hypergeometric WZ mate exists, and if it fails
no hypergeometric `G` exists. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 133"]
theorem text_p133_wz_certificate_via_gosper {K : Type*} [Field K] [CharZero K]
    (F : ℕ → ℕ → K) (n : ℕ) {a b c : Polynomial K}
    (h1 : IsHypergeometric fun k : ℕ => F (n + 1) k - F n k)
    (h2 : IsSimilar (fun k : ℕ => F (n + 1) k - F n k) (F n))
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : ∀ h : ℕ, IsCoprime a (b.comp (Polynomial.X + Polynomial.C (h : K))))
    (hc' : ∀ᶠ k : ℕ in Filter.atTop,
      Polynomial.eval (k : K) (b * c) * (F (n + 1) (k + 1) - F n (k + 1)) =
        Polynomial.eval (k : K) (a * c.comp (Polynomial.X + 1)) * (F (n + 1) k - F n k)) :
    ((IsGosperSummable fun k : ℕ => F (n + 1) k - F n k) →
        IsHypergeometric (gosperOutput (fun k : ℕ => F (n + 1) k - F n k) a b c) ∧
          (∀ᶠ k : ℕ in Filter.atTop, F (n + 1) k - F n k =
            gosperOutput (fun k : ℕ => F (n + 1) k - F n k) a b c (k + 1) -
              gosperOutput (fun k : ℕ => F (n + 1) k - F n k) a b c k) ∧
          IsSimilar (gosperOutput (fun k : ℕ => F (n + 1) k - F n k) a b c) (F n)) ∧
    ((¬IsGosperSummable fun k : ℕ => F (n + 1) k - F n k) →
        ∀ G : ℕ → K, IsHypergeometric G →
          ¬∀ᶠ k : ℕ in Filter.atTop, F (n + 1) k - F n k = G (k + 1) - G k) :=
  wz_certificate_via_gosper F n h1 h2 hb hc hab hc'

/-- CO-446. Theorem 7.1.1: if `(F, G)` is a WZ pair, each `F(n,·)` is summable and
`G(n,k) → 0` as `k → ±∞`, then `∑_k F(n,k)` does not depend on `n ≥ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 7.1.1, p. 134"]
theorem thm_7_1_1_wz_constant {E : Type*} [AddCommGroup E] {F G : ℤ → ℤ → E}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    (h : WZEq F G) (hF : ∀ n : ℤ, 0 ≤ n → Summable (F n))
    (hGt : ∀ n : ℤ, 0 ≤ n → Filter.Tendsto (G n) Filter.atTop (nhds 0))
    (hGb : ∀ n : ℤ, 0 ≤ n → Filter.Tendsto (G n) Filter.atBot (nhds 0)) (n : ℤ) (hn : 0 ≤ n) :
    ∑' k : ℤ, F n k = ∑' k : ℤ, F 0 k :=
  h.tsum_const hF hGt hGb n hn

/-- CO-447. Theorem 7.1.1, companion identity: if in addition `F(n,k) → f_k` as `n → ∞`, the
series `∑_n G(n,k)` converge and `∑_{n} G(n,-L) → 0`, then `∑_{n ≥ 0} G(n,k)` equals the limit of
`∑_{-L ≤ j < k} (f_j - F(0,j))`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 7.1.1, p. 134"]
theorem thm_7_1_1_companion {E : Type*} [AddCommGroup E] {F G : ℤ → ℤ → E}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    (h : WZEq F G) (f : ℤ → E)
    (hf : ∀ k : ℤ, Filter.Tendsto (fun n : ℕ => F (n : ℤ) k) Filter.atTop (nhds (f k)))
    (hG : ∀ k : ℤ, Summable fun n : ℕ => G (n : ℤ) k)
    (hL : Filter.Tendsto (fun L : ℕ => ∑' n : ℕ, G (n : ℤ) (-(L : ℤ))) Filter.atTop (nhds 0))
    (k : ℤ) :
    Filter.Tendsto (fun L : ℕ => ∑ j ∈ Finset.Ico (-(L : ℤ)) k, (f j - F 0 j)) Filter.atTop
      (nhds (∑' n : ℕ, G (n : ℤ) k)) :=
  h.companion f hf hG hL k

/-- CO-448. Proof from a certificate: if the ratios `F(n+1,k)/F(n,k) = r₁` and
`F(n,k+1)/F(n,k) = r₂` satisfy `r₁ - 1 = R(n,k+1) r₂ - R(n,k)`, then
`F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)` with `G = R F`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 134"]
theorem text_p134_certificate_to_wz {K : Type*} [CommRing K] (F R r₁ r₂ : ℤ → ℤ → K)
    (h1 : ∀ n k : ℤ, F (n + 1) k = r₁ n k * F n k)
    (h2 : ∀ n k : ℤ, F n (k + 1) = r₂ n k * F n k)
    (h3 : ∀ n k : ℤ, r₁ n k - 1 = R n (k + 1) * r₂ n k - R n k) :
    WZEq F fun n k : ℤ => R n k * F n k :=
  wzEq_of_ratio_identity F R r₁ r₂ h1 h2 h3

/-- CO-449. Gauss's `2F1(1)` identity is certified by the rational function `gaussR`
(the book's `R(n,k) = (k+1)(k+c)/(n(n+1-c))`). -/
@[kb "petkovsekwilfzeilberger1996" "text (I), p. 136"]
theorem text_p136_I_gauss_cert (b c n k : ℤ) (hb : 1 ≤ b) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hc : n + b + 2 ≤ c) :
    gaussF b c (n + 1) k - gaussF b c n k =
      gaussR c n (k + 1) * gaussF b c n (k + 1) - gaussR c n k * gaussF b c n k :=
  gauss_cert b c n k hb hn hk hc

/-- CO-450. Kummer's `2F1(-1)` identity is certified by the rational function `kumR`. -/
@[kb "petkovsekwilfzeilberger1996" "text (II), p. 136"]
theorem text_p136_II_kummer_cert (c n k : ℤ) (hc : 1 ≤ c) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hkn : k + 1 ≤ 2 * n) :
    kumF c (n + 1) k - kumF c n k =
      kumR c n (k + 1) * kumF c n (k + 1) - kumR c n k * kumF c n k :=
  kummer_cert c n k hc hn hk hkn

/-- CO-451. Saalschütz's `3F2` identity is certified by `saalR`
(the book's `R = k(c+k-1)(a+b-c+k-n)/((b-c-n)(c-a+n)(1-k+n))`). -/
@[kb "petkovsekwilfzeilberger1996" "text (III), p. 136"]
theorem text_p136_III_saal_cert (a b c n k : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 0 ≤ n)
    (hk : 0 ≤ k) (hc : 1 ≤ c) (hkn : k + 1 ≤ n) (h1 : a + b + k + 2 ≤ n + c)
    (h2 : a + 1 ≤ n + c) (h3 : b + 1 ≤ n + c) (h4 : c + n - b ≠ 0) (h5 : c - a + n ≠ 0) :
    saalF a b c (n + 1) k - saalF a b c n k =
      saalR a b c n (k + 1) * saalF a b c n (k + 1) - saalR a b c n k * saalF a b c n k :=
  saal_cert a b c n k ha hb hn hk hc hkn h1 h2 h3 h4 h5

/-- CO-452. Dixon's identity `∑ (-1)^k C(n+b,n+k) C(n+c,c+k) C(b+c,b+k) = (n+b+c)!/(n!b!c!)`
is certified by `dixonR`. -/
@[kb "petkovsekwilfzeilberger1996" "text (IV), p. 136"]
theorem text_p136_IV_dixon_cert (b c n k : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (h1 : k ≠ n) (h2 : k ≠ n + 1) :
    dixonF b c (n + 1) k - dixonF b c n k =
      dixonR b c n (k + 1) * dixonF b c n (k + 1) - dixonR b c n k * dixonF b c n k :=
  dixon_cert b c n k hb hc hn h1 h2

/-- CO-453. Clausen's `4F3` identity is certified by the rational function `clR`
(real parameters `a, b > 0`). -/
@[kb "petkovsekwilfzeilberger1996" "text (V), p. 137"]
theorem text_p137_V_clausen_cert (a b n k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 ≤ k)
    (hkn : k + 1 ≤ n) :
    clF a b (n + 1) k - clF a b n k =
      clR a b n (k + 1) * clF a b n (k + 1) - clR a b n k * clF a b n k :=
  clausen_cert a b n k ha hb hk hkn

/-- CO-454. Dougall's `7F6` identity is certified by the rational function `dgR`. -/
@[kb "petkovsekwilfzeilberger1996" "text (VI), p. 137"]
theorem text_p137_VI_dougall_cert (a b c d : ℝ) (n k : ℕ) (h : DougallHyp a b c d n)
    (hk : k + 1 ≤ n) :
    dgF a b c d (n + 1) k - dgF a b c d n k =
      dgR a b c d (n : ℝ) ((k : ℝ) + 1) * dgF a b c d n (k + 1) -
        dgR a b c d (n : ℝ) (k : ℝ) * dgF a b c d n k :=
  dougall_wz a b c d n k h hk

/-- CO-455. Companion of `∑_k C(n,k)^2 = C(2n,n)`: for every `k ≥ 0`,
`∑_{n ≥ 0} (3n-2k+1)/(2n+1) · C(n,k)^2 / C(2n,n) = 2`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.1, p. 138"]
theorem ex_7_3_1_companion_choose_sq (k : ℕ) :
    HasSum (fun n : ℕ => (3 * (n : ℝ) - 2 * k + 1) / (2 * n + 1) * ((n.choose k : ℕ) : ℝ) ^ 2 /
      (((2 * n).choose n : ℕ) : ℝ)) 2 :=
  Companions.companion_sum_choose_sq k

/-- CO-456. The companion of the three-parameter factorial identity with certificate
`R = (k-1)/n` is Gauss's `2F1(1)` sum: for `2 ≤ k ≤ i, j`,
`∑_{r ≥ 0} (r+j-k)!(r+i-k)!/(r!(r+i+j-k)!) = (k-2)!(i-k)!(j-k)!/((i-1)!(j-1)!)`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.2, p. 139"]
theorem ex_7_3_2_gauss_companion (i j k : ℕ) (hk : 2 ≤ k) (hki : k ≤ i) (hkj : k ≤ j) :
    HasSum (fun r : ℕ => (((r + j - k).factorial * (r + i - k).factorial : ℕ) : ℝ) /
        ((r.factorial * (r + i + j - k).factorial : ℕ) : ℝ))
      ((((k - 2).factorial * (i - k).factorial * (j - k).factorial : ℕ) : ℝ) /
        (((i - 1).factorial * (j - 1).factorial : ℕ) : ℝ)) :=
  Identities3d.gauss_companion i j k hk hki hkj

/-- CO-050. Vandermonde `∑_k C(a,k) C(n,k) = C(n+a,a)`: its WZ certificate (`vandR`) and its
companion `∑_{n ≥ 0} C(n,k)/C(n+a+1,n) = (a+1)/((k+1) C(a,k+1))` for `a > k ≥ 0`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.4, p. 140"]
theorem ex_7_3_4_vandermonde_wz :
    (∀ a n k : ℤ, 0 ≤ a → 0 ≤ n → 0 ≤ k → k + 1 ≤ a → k + 1 ≤ n →
      vandF a (n + 1) k - vandF a n k =
        vandR a n (k + 1) * vandF a n (k + 1) - vandR a n k * vandF a n k) ∧
    (∀ a k : ℕ, k < a →
      HasSum (fun n : ℕ => ((n.choose k : ℕ) : ℝ) / (((n + a + 1).choose n : ℕ) : ℝ))
        (((a : ℝ) + 1) / (((k : ℝ) + 1) * ((a.choose (k + 1) : ℕ) : ℝ)))) ∧
    (∀ a n : ℕ, ∑ k ∈ Finset.range (n + 1), a.choose k * n.choose k = (n + a).choose a) :=
  ⟨vand_cert, Companions.vandermonde_companion, vandermonde_sum⟩

/-- CO-459. Duality: if `(F(n,k), G(n,k))` is a WZ pair, so is
`(G(-k-1,-n), F(-k,-n-1))`. -/
@[kb "petkovsekwilfzeilberger1996" "text (7.3.7), p. 142"]
theorem eq_7_3_7_wz_dual {K : Type*} [AddCommGroup K] {F G : ℤ → ℤ → K} (h : WZEq F G) :
    WZEq (fun n k : ℤ => G (-k - 1) (-n)) fun n k : ℤ => F (-k) (-n - 1) :=
  h.dual

/-- CO-460. The identity obtained as the dual of the sum-of-squares identity:
`∑_k (3k - 2n) C(n,k)^2 C(2k,k) = 0` for `n ≥ 0` (formalised with the square on `C(n,k)`). -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.5, p. 142"]
theorem ex_7_3_5_sum_dual_squares (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (3 * (k : ℤ) - 2 * n) * ((n.choose k : ℕ) : ℤ) ^ 2 *
      (((2 * k).choose k : ℕ) : ℤ) = 0 :=
  sum_dual_squares n

/-- CO-461. Duals of simple sums: the dual of `∑ C(n,k) = 2^n` is
`∑_k (-1)^(n+k) C(n,k) 2^k = 1`, and a dual of Vandermonde is
`∑_k (-1)^(n+k) C(n,k) C(k+b,k) = C(b,n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 143"]
theorem text_p143_dual_identities :
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) * 2 ^ k = 1) ∧
    (∀ n b : ℕ, ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k : ℤ) *
      ((k + b).choose k : ℤ) = (b.choose n : ℤ)) :=
  ⟨Identities2.dual_sum_choose, Identities2.dual_vandermonde⟩

/-- CO-462. For a WZ pair with `G(n,0) = 0`, the restricted sum is
`∑_{k=0}^n F(n,k) = F(0,0) + ∑_{j=1}^n (F(j,j) + G(j-1,j))`. -/
@[kb "petkovsekwilfzeilberger1996" "text (7.3.8), p. 143"]
theorem eq_7_3_8_restricted_sum {K : Type*} [AddCommGroup K] (F G : ℤ → ℤ → K) (h : WZEq F G)
    (h0 : ∀ n : ℕ, G (n : ℤ) 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), F (n : ℤ) (k : ℤ) =
      F 0 0 + ∑ j ∈ Finset.range n, (F ((j + 1 : ℕ) : ℤ) ((j + 1 : ℕ) : ℤ) +
        G (j : ℤ) ((j + 1 : ℕ) : ℤ)) :=
  restricted_sum_formula F G h h0 n

/-- CO-463. The partial sums of `C(3n,k)`: the closed recurrence-free form
`8^{-n} ∑_{k ≤ n} C(3n,k) = 1 + (2/3) ∑_{j=1}^n (2-j-5j²)/((3j-1)(3j-2)) 8^{-j} C(3j,j)`, and
the sum is asymptotic to twice its last term. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.6, p. 144"]
theorem ex_7_3_6_partial_choose_three :
    (∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (((3 * n).choose k : ℕ) : ℚ)) / 8 ^ n =
      1 + 2 / 3 * ∑ j ∈ Finset.range n,
        (2 - ((j : ℚ) + 1) - 5 * ((j : ℚ) + 1) ^ 2) /
          ((3 * ((j : ℚ) + 1) - 1) * (3 * ((j : ℚ) + 1) - 2)) *
          (((3 * (j + 1)).choose (j + 1) : ℕ) : ℚ) / 8 ^ (j + 1)) ∧
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (((3 * n).choose k : ℕ) : ℝ))
      (fun n : ℕ => 2 * (((3 * n).choose n : ℕ) : ℝ)) :=
  ⟨partial_choose_three, PartialSumAsymptotic.partial_sum_isEquivalent⟩

/-- CO-464. Gessel's WZ functions: for a function `F` of parameters (in an additive group `P`)
and the summation variable that is a WZ function, each parameter may be shifted by integer
multiples `n • u`, and the shifted family has a WZ mate, finite support and sum `1`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Gessel approach 2), p. 145"]
theorem text_p145_gessel_shift_param {K : Type*} [CommRing K] {P : Type*} [AddCommGroup P]
    {F : P → ℤ → K} (h : IsWZFunction F) (p u : P) :
    ∃ G : ℤ → ℤ → K, WZEq (fun n k : ℤ => F (p + n • u) k) G ∧
      (∀ n : ℤ, (Function.support fun k : ℤ => F (p + n • u) k).Finite) ∧
      ∀ n : ℤ, ∑ᶠ k : ℤ, F (p + n • u) k = 1 :=
  h.shift_param p u

/-- CO-465. Symmetries of WZ pairs: transposing, shifting, and reflecting `n` or `k` all
preserve the WZ equation. -/
@[kb "petkovsekwilfzeilberger1996" "text (Gessel approach 3-5), p. 145"]
theorem text_p145_wz_symmetries {K : Type*} [AddCommGroup K] {F G : ℤ → ℤ → K} (h : WZEq F G) :
    WZEq (fun n k : ℤ => G k n) (fun n k : ℤ => F k n) ∧
    (∀ α β : ℤ, WZEq (fun n k : ℤ => F (n + α) (k + β)) fun n k : ℤ => G (n + α) (k + β)) ∧
    WZEq (fun n k : ℤ => F (-n) k) (fun n k : ℤ => -G (-n - 1) k) ∧
    WZEq (fun n k : ℤ => F n (-k)) (fun n k : ℤ => -G n (-k + 1)) :=
  ⟨h.transpose, h.shift, h.neg_left, h.neg_right⟩

/-- CO-469. Certificate and mate for
`∑_k 2^{k+1}(k+1)(2n-k-2)! n!/((n-k-1)!(2n)!) = 1`: the mate `halfG` equals `halfR · halfF`, and
`(halfF, halfG)` satisfies the WZ equation in the supported range; also the certificate check
for the companion summand `twoF`. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.5.1, p. 148"]
theorem ex_7_5_1_half_mate :
    (∀ n k : ℤ, 0 ≤ n → 1 ≤ k → k + 1 ≤ n →
      halfF (n + 1) k - halfF n k = halfG n (k + 1) - halfG n k) ∧
    (∀ n k : ℤ, 1 ≤ k → k ≤ n → halfG n k = halfR n k * halfF n k) ∧
    (∀ n k : ℤ, 0 ≤ n → 0 ≤ k → k + 2 ≤ n →
      twoF (n + 1) k - twoF n k = twoR n (k + 1) * twoF n (k + 1) - twoR n k * twoF n k) :=
  ⟨half_mate, half_mate_eq, two_cert⟩

/-- CO-470. Companion of `∑_k k C(n+1,k) C(x,k)/((n+1) C(n+x,n+1)) = 1`: for `2 ≤ k < x`,
`∑_{n ≥ 0} C(n+1,k-1)/((n+1) C(x+n+1,x)) = x/(k(k-1)C(x,k))`, and the factorial form of it. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.5.2, p. 148"]
theorem ex_7_5_2_companion :
    (∀ x k : ℕ, 2 ≤ k → k < x →
      HasSum (fun n : ℕ => (((n + 1).choose (k - 1) : ℕ) : ℝ) /
          (((n : ℝ) + 1) * (((x + n + 1).choose x : ℕ) : ℝ)))
        ((x : ℝ) / ((k : ℝ) * ((k : ℝ) - 1) * ((x.choose k : ℕ) : ℝ)))) ∧
    (∀ x i : ℕ, i + 2 < x →
      HasSum (fun m : ℕ => (((m + i).factorial : ℕ) : ℝ) * (((m + i + 1).factorial : ℕ) : ℝ) /
          ((m.factorial : ℝ) * (((x + m + i + 1).factorial : ℕ) : ℝ)))
        ((i.factorial : ℝ) / (((i : ℝ) + 2) * ((x.choose (i + 2) : ℕ) : ℝ) *
          (((x - 1).factorial : ℕ) : ℝ)))) :=
  ⟨Identities2.companion_binomial, Identities2.companion_factorial⟩

/-- CO-471. A WZ pair is exactly the order-one case of creative telescoping: `(F, G)` satisfies the
WZ equation iff `(N - 1) F = G(k+1) - G(k)` in the sense of a telescoped recurrence of order one
with coefficients `-1, 1`. -/
@[kb "petkovsekwilfzeilberger1996" "text (7.5.2), p. 149"]
theorem eq_7_5_2_wz_iff_telescoped {K : Type*} [Field K] (F G : ℤ → ℤ → K) :
    WZEq F G ↔ Zeilberger.IsTelescopedRecurrence 1
      (fun (j : ℕ) (_ : ℤ) => if j = 0 then (-1 : K) else 1) F G :=
  Zeilberger.wzEq_iff_isTelescopedRecurrence F G

end UndergradKB.Combinatorics.Course.AeqB.Ch07b
