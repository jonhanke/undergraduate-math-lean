import UndergradKB.Combinatorics.AeqB.Database

/-!
# WZ certificates for hypergeometric identities (Petkovsek–Wilf–Zeilberger, Chapters 2 and 7)

For each summand `F(n,k)` (written with the integer factorial `fct`, so that the statements
are about genuine ratios of factorials at all arguments where those make sense) we state that the
book's certificate `R(n,k)` satisfies the Wilf–Zeilberger equation
`F(n+1,k) - F(n,k) = R(n,k+1) F(n,k+1) - R(n,k) F(n,k)`, i.e. `(F, G)` with `G = R F` is a WZ pair
(book (7.1.2)).  The hypotheses say that all the factorial arguments that occur are nonnegative
and that no denominator of `R` vanishes.  Proofs shift the factorials down to a common base
and check the resulting rational-function identity by `field_simp; ring`.
-/

namespace UndergradKB.Combinatorics.AeqB

open Finset
open scoped Nat

theorem fct_ne_zero (m : ℤ) : fct m ≠ 0 := by
  unfold fct; positivity

theorem fct_rec2 (m m' : ℤ) (h : m' = m + 1) (hm : 0 ≤ m) : fct m' = (m' : ℚ) * fct m := by
  rw [fct_rec m m' h hm, h]; push_cast; ring

theorem nz_of_int {m : ℤ} (h : m ≠ 0) : (m : ℚ) ≠ 0 := by exact_mod_cast h

/-- The summand of Gauss's `2F1(1)` identity (book p. 136 (I)), in factorial form. -/
def gaussF (b c n k : ℤ) : ℚ :=
  fct (n + k) * fct (b + k) * fct (c - n - 1) * fct (c - b - 1) /
    (fct (c + k) * fct (n - 1) * fct (c - n - b - 1) * fct (k + 1) * fct (b - 1))

/-- The certificate `R(n,k) = (k+1)(k+c) / (n(n+1-c))` of Gauss's identity. -/
def gaussR (c n k : ℤ) : ℚ := ((k : ℚ) + 1) * ((k : ℚ) + c) / ((n : ℚ) * ((n : ℚ) + 1 - c))

/-- CO-449. Gauss's `2F1(1)` identity is certified by `R(n,k) = (k+1)(k+c)/(n(n+1-c))`: the pair
`(F, R F)` satisfies the WZ equation (all factorial arguments nonnegative). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 136 (I)"]
theorem gauss_cert (b c n k : ℤ) (hb : 1 ≤ b) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hcn : n + b + 2 ≤ c) :
    gaussF b c (n + 1) k - gaussF b c n k
      = gaussR c n (k + 1) * gaussF b c n (k + 1) - gaussR c n k * gaussF b c n k := by
  unfold gaussF gaussR
  have e1 := fct_rec (n + k) (n + 1 + k) (by ring) (by omega)
  have e2' := fct_rec (c - n - 2) (c - n - 1) (by ring) (by omega)
  have e3 := fct_rec (n - 1) n (by ring) (by omega)
  have e4' := fct_rec (c - n - b - 2) (c - n - b - 1) (by ring) (by omega)
  have e5 := fct_rec (n + k) (n + (k + 1)) (by ring) (by omega)
  have e6 := fct_rec (b + k) (b + (k + 1)) (by ring) (by omega)
  have e7 := fct_rec (c + k) (c + (k + 1)) (by ring) (by omega)
  have e8 := fct_rec (k + 1) (k + 1 + 1) (by ring) (by omega)
  simp only [show c - (n + 1) - 1 = c - n - 2 by ring, show c - (n + 1) - b - 1 = c - n - b - 2 by ring,
    add_sub_cancel_right]
  rw [e1, e5, e6, e7, e8, e3, show c - n - 1 = c - n - 1 from rfl, e2', e4']
  have a1 := fct_ne_zero (n + k)
  have a2 := fct_ne_zero (b + k)
  have a3 := fct_ne_zero (c - n - 2)
  have a4 := fct_ne_zero (c - b - 1)
  have a5 := fct_ne_zero (c + k)
  have a6 := fct_ne_zero (n - 1)
  have a7 := fct_ne_zero (c - n - b - 2)
  have a8 := fct_ne_zero (k + 1)
  have a9 := fct_ne_zero (b - 1)
  have h1 : ((n : ℚ)) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h2 : ((n : ℚ) + 1 - c) ≠ 0 := by
    have : (n : ℚ) + 1 - c = ((n + 1 - c : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact_mod_cast (show n + 1 - c ≠ 0 by omega)
  have h3 : ((c : ℚ) - n - 2 + 1) ≠ 0 := by
    have : (c : ℚ) - n - 2 + 1 = ((c - n - 1 : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact_mod_cast (show c - n - 1 ≠ 0 by omega)
  have h4 : ((c : ℚ) - n - b - 2 + 1) ≠ 0 := by
    have : (c : ℚ) - n - b - 2 + 1 = ((c - n - b - 1 : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact_mod_cast (show c - n - b - 1 ≠ 0 by omega)
  have h5 : ((c : ℚ) + k + 1) ≠ 0 := by
    have : (c : ℚ) + k + 1 = ((c + k + 1 : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact_mod_cast (show c + k + 1 ≠ 0 by omega)
  have h6 : ((k : ℚ) + 1 + 1) ≠ 0 := by
    have : (k : ℚ) + 1 + 1 = ((k + 2 : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact_mod_cast (show k + 2 ≠ 0 by omega)
  push_cast
  simp only [sub_add_cancel]
  field_simp
  ring

/-- The summand of Saalschütz's identity (book p. 136 (III)), in factorial form. -/
def saalF (a b c n k : ℤ) : ℚ :=
  fct (a + k - 1) * fct (b + k - 1) * fct n * fct (n + c - a - b - k - 1) * fct (n + c - 1) /
    (fct k * fct (n - k) * fct (k + c - 1) * fct (n + c - a - 1) * fct (n + c - b - 1))

/-- The certificate for Saalschütz's identity.  Note: with the summand `saalF` as printed, the
book's `R` has the opposite sign (the printed denominator factor `b - c - n` should read
`c + n - b`); here the sign is corrected, which is what makes the equation true. -/
def saalR (a b c n k : ℤ) : ℚ :=
  (k : ℚ) * ((c : ℚ) + k - 1) * ((a : ℚ) + b - c + k - n) /
    (((c : ℚ) + n - b) * ((c : ℚ) - a + n) * (1 - k + n))

set_option maxRecDepth 100000 in
/-- CO-451. Saalschütz's `3F2` identity is certified by `R(n,k) = k(c+k-1)(a+b-c+k-n) /
((c+n-b)(c-a+n)(1-k+n))` (the book's printed `R`, with the sign of its denominator corrected). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 136 (III)"]
theorem saal_cert (a b c n k : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 0 ≤ n) (hk : 0 ≤ k)
    (hc : 1 ≤ c) (hnk : k + 1 ≤ n) (h1 : a + b + k + 2 ≤ n + c) (h2 : a + 1 ≤ n + c)
    (h3 : b + 1 ≤ n + c) (h4 : c + n - b ≠ 0) (h5 : c - a + n ≠ 0) :
    saalF a b c (n + 1) k - saalF a b c n k
      = saalR a b c n (k + 1) * saalF a b c n (k + 1) - saalR a b c n k * saalF a b c n k := by
  unfold saalF saalR
  have e1 := fct_rec2 (a + k - 1) (a + k) (by ring) (by omega)
  have e2 := fct_rec2 (b + k - 1) (b + k) (by ring) (by omega)
  have e3 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e4 := fct_rec2 (n + c - a - b - k - 2) (n + c - a - b - k - 1) (by ring) (by omega)
  have e4' := fct_rec2 (n + c - a - b - k - 1) (n + c - a - b - k) (by ring) (by omega)
  have e5 := fct_rec2 (n + c - 1) (n + c) (by ring) (by omega)
  have e6 := fct_rec2 k (k + 1) (by ring) (by omega)
  have e7 := fct_rec2 (n - k - 1) (n - k) (by ring) (by omega)
  have e7' := fct_rec2 (n - k) (n + 1 - k) (by ring) (by omega)
  have e8 := fct_rec2 (k + c - 1) (k + c) (by ring) (by omega)
  have e9 := fct_rec2 (n + c - a - 1) (n + c - a) (by ring) (by omega)
  have e10 := fct_rec2 (n + c - b - 1) (n + c - b) (by ring) (by omega)
  simp only [show n + 1 + c - a - b - k - 1 = n + c - a - b - k by ring,
    show n + 1 + c - 1 = n + c by ring, show n + 1 + c - a - 1 = n + c - a by ring,
    show n + 1 + c - b - 1 = n + c - b by ring,
    show a + (k + 1) - 1 = a + k by ring, show b + (k + 1) - 1 = b + k by ring,
    show n + c - a - b - (k + 1) - 1 = n + c - a - b - k - 2 by ring,
    show n - (k + 1) = n - k - 1 by ring, show k + 1 + c - 1 = k + c by ring]
  rw [e1, e2, e3, e4', e4, e5, e6, e7', e7, e8, e9, e10]
  have a1 := fct_ne_zero (a + k - 1)
  have a2 := fct_ne_zero (b + k - 1)
  have a3 := fct_ne_zero n
  have a4 := fct_ne_zero (n + c - a - b - k - 2)
  have a5 := fct_ne_zero (n + c - 1)
  have a6 := fct_ne_zero k
  have a7 := fct_ne_zero (n - k - 1)
  have a8 := fct_ne_zero (k + c - 1)
  have a9 := fct_ne_zero (n + c - a - 1)
  have a10 := fct_ne_zero (n + c - b - 1)
  have z1 := nz_of_int (m := n + c - a - b - k - 1) (by omega)
  have z2 := nz_of_int (m := n - k) (by omega)
  have z3 := nz_of_int (m := n + 1 - k) (by omega)
  have z4 := nz_of_int (m := k + c) (by omega)
  have z5 := nz_of_int (m := n + c - a) (by omega)
  have z6 := nz_of_int (m := n + c - b) (by omega)
  have z7 := nz_of_int (m := k + 1) (by omega)
  have z8 := nz_of_int (m := c + n - b) h4
  have z9 := nz_of_int (m := c - a + n) h5
  have z10 := nz_of_int (m := 1 - k + n) (by omega)
  have z11 := nz_of_int (m := 1 - (k + 1) + n) (by omega)
  have z12 := nz_of_int (m := n + 1) (by omega)
  have z13 := nz_of_int (m := n + c) (by omega)
  have z14 := nz_of_int (m := n + c - a - b - k) (by omega)
  have z15 := nz_of_int (m := a + k) (by omega)
  have z16 := nz_of_int (m := b + k) (by omega)
  push_cast at z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 ⊢
  field_simp
  ring

/-- The certificate `R(n,k) = (k-1)/n` of Example 2.3.2 (independent of `i` and `j`). -/
def monR (n k : ℤ) : ℚ := ((k : ℚ) - 1) / n

/-- The summand of the identity of Example 2.3.2 (an identity from the Amer. Math. Monthly). -/
def monF (i j n k : ℤ) : ℚ :=
  fct (n - i) * fct (n - j) * fct (i - 1) * fct (j - 1) /
    (fct (n - 1) * fct (k - 1) * fct (n - i - j + k) * fct (i - k) * fct (j - k))

/-- CO-442. The WZ certificate `R(n,k) = (k-1)/n` for `∑_k F(n,k) = 1`, where
`F(n,k) = (n-i)!(n-j)!(i-1)!(j-1)! / ((n-1)!(k-1)!(n-i-j+k)!(i-k)!(j-k)!)`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 2.3.2, p. 38"]
theorem mon_cert (i j n k : ℤ) (_hi : 1 ≤ i) (_hj : 1 ≤ j) (hni : i ≤ n) (hnj : j ≤ n)
    (hk : 1 ≤ k) (h1 : i + j ≤ n + k) (h2 : k + 1 ≤ i) (h3 : k + 1 ≤ j) :
    monF i j (n + 1) k - monF i j n k
      = monR n (k + 1) * monF i j n (k + 1) - monR n k * monF i j n k := by
  unfold monF monR
  have e1 := fct_rec2 (n - i) (n + 1 - i) (by ring) (by omega)
  have e2 := fct_rec2 (n - j) (n + 1 - j) (by ring) (by omega)
  have e3 := fct_rec2 (n - 1) n (by ring) (by omega)
  have e4 := fct_rec2 (n - i - j + k) (n + 1 - i - j + k) (by ring) (by omega)
  have e4' := fct_rec2 (n - i - j + k) (n - i - j + (k + 1)) (by ring) (by omega)
  have e5 := fct_rec2 (k - 1) k (by ring) (by omega)
  have e6 := fct_rec2 (i - k - 1) (i - k) (by ring) (by omega)
  have e7 := fct_rec2 (j - k - 1) (j - k) (by ring) (by omega)
  simp only [show n + 1 - 1 = n by ring, show k + 1 - 1 = k by ring,
    show i - (k + 1) = i - k - 1 by ring, show j - (k + 1) = j - k - 1 by ring]
  rw [e1, e2, e4, e4', e3, e5, e6, e7]
  have a1 := fct_ne_zero (n - i)
  have a2 := fct_ne_zero (n - j)
  have a3 := fct_ne_zero (i - 1)
  have a4 := fct_ne_zero (j - 1)
  have a5 := fct_ne_zero (n - 1)
  have a6 := fct_ne_zero (k - 1)
  have a7 := fct_ne_zero (n - i - j + k)
  have a8 := fct_ne_zero (i - k - 1)
  have a9 := fct_ne_zero (j - k - 1)
  have z1 := nz_of_int (m := n + 1 - i - j + k) (by omega)
  have z2 := nz_of_int (m := n - i - j + (k + 1)) (by omega)
  have z3 := nz_of_int (m := n) (by omega)
  have z4 := nz_of_int (m := k) (by omega)
  have z5 := nz_of_int (m := i - k) (by omega)
  have z6 := nz_of_int (m := j - k) (by omega)
  push_cast at z1 z2 z3 z4 z5 z6 ⊢
  field_simp
  ring

/-- The summand `C(n,k)^2 / C(2n,n)` in factorial form. -/
def centralF (n k : ℤ) : ℚ := fct n ^ 4 / (fct k ^ 2 * fct (n - k) ^ 2 * fct (2 * n))

/-- The certificate `R(n,k) = -k^2 (3n-2k+3) / (2 (2n+1) (n-k+1)^2)`. -/
def centralR (n k : ℤ) : ℚ :=
  -((k : ℚ) ^ 2 * (3 * n - 2 * k + 3)) / (2 * (2 * n + 1) * ((n : ℚ) - k + 1) ^ 2)

/-- CO-444. The WZ certificate for `∑_k C(n,k)^2 / C(2n,n) = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.1.1, p. 132"]
theorem central_cert (n k : ℤ) (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k + 1 ≤ n) :
    centralF (n + 1) k - centralF n k
      = centralR n (k + 1) * centralF n (k + 1) - centralR n k * centralF n k := by
  unfold centralF centralR
  have e1 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e2 := fct_rec2 (n - k) (n + 1 - k) (by ring) (by omega)
  have e3 := fct_rec2 (2 * n + 1) (2 * n + 1 + 1) (by ring) (by omega)
  have e3' := fct_rec2 (2 * n) (2 * n + 1) (by ring) (by omega)
  have e4 := fct_rec2 k (k + 1) (by ring) (by omega)
  have e5 := fct_rec2 (n - k - 1) (n - k) (by ring) (by omega)
  simp only [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, show n - (k + 1) = n - k - 1 by ring]
  rw [e1, e2, e3, e3', e4, e5]
  have a1 := fct_ne_zero n
  have a2 := fct_ne_zero k
  have a3 := fct_ne_zero (n - k - 1)
  have a4 := fct_ne_zero (2 * n)
  have z1 := nz_of_int (m := n - k) (by omega)
  have z2 := nz_of_int (m := n + 1 - k) (by omega)
  have z3 := nz_of_int (m := 2 * n + 1) (by omega)
  have z4 := nz_of_int (m := 2 * n + 1 + 1) (by omega)
  have z5 := nz_of_int (m := k + 1) (by omega)
  have z6 := nz_of_int (m := n - (k + 1) + 1) (by omega)
  have z7 := nz_of_int (m := n - k + 1) (by omega)
  push_cast at z1 z2 z3 z4 z5 z6 z7 ⊢
  field_simp
  ring

/-- The summand `C(n,k)/2^n` in factorial form.  The certificate `R = k/(2(k-n-1))` and mate
`G = -n!/(2^(n+1) (k-1)! (n-k+1)!)` printed in Example 7.5.1 belong to this summand (printed
there in place of the summand `2^(k+1)(k+1)(2n-k-2)! n!/((n-k-1)!(2n)!)`, for which they are
not a certificate; see `twoF` and `two_cert` for the latter). -/
def halfF (n k : ℤ) : ℚ := fct n / (2 ^ n * fct k * fct (n - k))

def halfG (n k : ℤ) : ℚ := -fct n / (2 ^ (n + 1) * fct (k - 1) * fct (n - k + 1))

def halfR (n k : ℤ) : ℚ := (k : ℚ) / (2 * ((k : ℚ) - n - 1))

/-- CO-469. The mate `G(n,k) = -n!/(2^(n+1)(k-1)!(n-k+1)!)` printed in Example 7.5.1 satisfies the
WZ equation for `F(n,k) = C(n,k)/2^n`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.5.1, p. 148"]
theorem half_mate (n k : ℤ) (hn : 0 ≤ n) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    halfF (n + 1) k - halfF n k = halfG n (k + 1) - halfG n k := by
  unfold halfF halfG
  have e1 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e2 := fct_rec2 (n - k) (n + 1 - k) (by ring) (by omega)
  have e3 := fct_rec2 (k - 1) k (by ring) (by omega)
  have e5' := fct_rec2 (n - k) (n - k + 1) (by ring) (by omega)
  have p1 : (2 : ℚ) ^ (n + 1) = 2 ^ n * 2 := zpow_add_one₀ (by norm_num) n
  simp only [show k + 1 - 1 = k by ring,
    show n - (k + 1) = n - k - 1 by ring, show n - k - 1 + 1 = n - k by ring, p1]
  rw [e1, e2, e3, e5']
  have a1 := fct_ne_zero n
  have a2 := fct_ne_zero (k - 1)
  have a3 := fct_ne_zero (n - k)
  have p2 : (2 : ℚ) ^ n ≠ 0 := zpow_ne_zero _ (by norm_num)
  have z1 := nz_of_int (m := n - k) (by omega)
  have z2 := nz_of_int (m := n + 1 - k) (by omega)
  have z3 := nz_of_int (m := n - k + 1) (by omega)
  have z4 := nz_of_int (m := k) (by omega)
  have z5 := nz_of_int (m := k + 1) (by omega)
  have z6 := nz_of_int (m := n + 1) (by omega)
  have z7 := nz_of_int (m := n - k) (by omega)
  push_cast at z1 z2 z3 z4 z5 z6 z7 ⊢
  field_simp
  ring

/-- CO-469. The mate is `R F` with the printed certificate `R(n,k) = k/(2(k-n-1))`. -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.5.1, p. 148"]
theorem half_mate_eq (n k : ℤ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    halfG n k = halfR n k * halfF n k := by
  unfold halfF halfG halfR
  have e3 := fct_rec2 (k - 1) k (by ring) (by omega)
  have e5' := fct_rec2 (n - k) (n - k + 1) (by ring) (by omega)
  rw [e3, e5']
  have a1 := fct_ne_zero n
  have a2 := fct_ne_zero (k - 1)
  have a3 := fct_ne_zero (n - k)
  have p2 : (2 : ℚ) ^ n ≠ 0 := zpow_ne_zero _ (by norm_num)
  have p1 : (2 : ℚ) ^ (n + 1) = 2 ^ n * 2 := zpow_add_one₀ (by norm_num) n
  have z1 := nz_of_int (m := n - k + 1) (by omega)
  have z4 := nz_of_int (m := k) (by omega)
  have z5 := nz_of_int (m := k - n - 1) (by omega)
  rw [p1]
  push_cast at z1 z4 z5 ⊢
  have : (k : ℚ) - n - 1 = -((n : ℚ) - k + 1) := by ring
  rw [this]
  field_simp

/-- The summand `2^(k+1) (k+1) (2n-k-2)! n! / ((n-k-1)! (2n)!)`. -/
def twoF (n k : ℤ) : ℚ :=
  2 ^ (k + 1) * ((k : ℚ) + 1) * fct (2 * n - k - 2) * fct n / (fct (n - k - 1) * fct (2 * n))

/-- A certificate for `twoF`: `R(n,k) = -k(2n-1-k) / (2(2n+1)(n-k))`. -/
def twoR (n k : ℤ) : ℚ := -((k : ℚ) * (2 * n - 1 - k)) / (2 * (2 * n + 1) * ((n : ℚ) - k))

/-- CO-469. A WZ certificate for the sum `∑_k 2^(k+1)(k+1)(2n-k-2)! n!/((n-k-1)!(2n)!) = 1` of
Example 7.5.1 (the certificate printed in the book does not belong to this summand, see
`half_mate`; the certificate here was found by solving for `G/F`). -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.5.1, p. 148"]
theorem two_cert (n k : ℤ) (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k + 2 ≤ n) :
    twoF (n + 1) k - twoF n k
      = twoR n (k + 1) * twoF n (k + 1) - twoR n k * twoF n k := by
  unfold twoF twoR
  have e1 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e2 := fct_rec2 (n - k - 1) (n - k) (by ring) (by omega)
  have e2' := fct_rec2 (n - k - 2) (n - k - 1) (by ring) (by omega)
  have e3 := fct_rec2 (2 * n) (2 * n + 1) (by ring) (by omega)
  have e3' := fct_rec2 (2 * n + 1) (2 * n + 1 + 1) (by ring) (by omega)
  have e4 := fct_rec2 (2 * n - k - 3) (2 * n - k - 2) (by ring) (by omega)
  have e4' := fct_rec2 (2 * n - k - 2) (2 * n - k - 1) (by ring) (by omega)
  have e4'' := fct_rec2 (2 * n - k - 1) (2 * n - k) (by ring) (by omega)
  have p1 : (2 : ℚ) ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := zpow_add_one₀ (by norm_num) (k + 1)
  simp only [show 2 * n + 1 + 1 - k - 2 = 2 * n - k by ring, show n + 1 - k - 1 = n - k by ring,
    show 2 * (n + 1) = 2 * n + 1 + 1 by ring, show 2 * n - (k + 1) - 2 = 2 * n - k - 3 by ring,
    show n - (k + 1) - 1 = n - k - 2 by ring, p1]
  rw [e1, e3', e3, e4'', e4', e4, e2, e2']
  have a1 := fct_ne_zero n
  have a2 := fct_ne_zero (n - k - 2)
  have a3 := fct_ne_zero (2 * n)
  have a4 := fct_ne_zero (2 * n - k - 3)
  have p2 : (2 : ℚ) ^ (k + 1) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have z1 := nz_of_int (m := n - k - 1) (by omega)
  have z2 := nz_of_int (m := n - k) (by omega)
  have z3 := nz_of_int (m := 2 * n + 1) (by omega)
  have z4 := nz_of_int (m := 2 * n + 1 + 1) (by omega)
  have z5 := nz_of_int (m := n - (k + 1)) (by omega)
  push_cast at z1 z2 z3 z4 z5 ⊢
  field_simp
  ring

theorem dixH_eq (b c n k : ℤ) (hk : k ≠ n + 1) :
    dixH b c n k = ((k : ℚ) + b) * ((k : ℚ) + c) / (2 * ((k : ℚ) - n - 1)) * dixT b c n k := by
  unfold dixH dixT
  have r := rf_rec (n - k) (n + 1 - k) (by ring)
  rw [r]
  have z : ((k : ℚ) - n - 1) ≠ 0 := by
    have := nz_of_int (m := k - n - 1) (by omega)
    push_cast at this; exact this
  push_cast
  generalize rf (n + k) = A1
  generalize rf (b - k) = A2
  generalize rf (c + k) = A3
  generalize rf (n + 1 - k) = A4
  generalize rf (b + k) = A5
  generalize rf (c - k) = A6
  generalize fct (n + b) = B1
  generalize fct (n + c) = B2
  generalize fct (b + c) = B3
  generalize (-1 : ℚ) ^ k = S
  have h2 : ((k : ℚ) + b) * ((k : ℚ) + c) / (2 * ((k : ℚ) - n - 1)) * ((n : ℚ) - k + 1)
      = -(((k : ℚ) + b) * ((k : ℚ) + c) / 2) := by
    field_simp
    ring
  linear_combination (-(S * B1 * B2 * B3 * (A1 * A2 * A3 * A4 * A5 * A6))) * h2

/-- Dixon's summand with the normalisation of the book,
`F(n,k) = (-1)^k C(n+b,n+k) C(n+c,c+k) C(b+c,b+k) n! b! c! / (n+b+c)!`. -/
def dixonF (b c n k : ℤ) : ℚ := dixT b c n k * (fct n * fct b * fct c / fct (n + b + c))

/-- The certificate `R(n,k) = (k+b)(k+c) / (2(k-n-1)(n+b+c+1))` for Dixon's identity. -/
def dixonR (b c n k : ℤ) : ℚ :=
  ((k : ℚ) + b) * ((k : ℚ) + c) / (2 * ((k : ℚ) - n - 1) * ((n : ℚ) + b + c + 1))

/-- CO-452. The WZ certificate `R(n,k) = (k+b)(k+c) / (2(k-n-1)(n+b+c+1))` for Dixon's identity,
valid for `k ≠ n, n+1` (where `R` is defined). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 136 (IV)"]
theorem dixon_cert (b c n k : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : 0 ≤ n) (hk1 : k ≠ n)
    (hk2 : k ≠ n + 1) :
    dixonF b c (n + 1) k - dixonF b c n k
      = dixonR b c n (k + 1) * dixonF b c n (k + 1) - dixonR b c n k * dixonF b c n k := by
  have key := dix_step b c n k hb hc hn
  rw [dixH_eq b c n (k + 1) (by omega), dixH_eq b c n k hk2] at key
  unfold dixonF dixonR
  have e1 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e2 := fct_rec2 (n + b + c) (n + 1 + b + c) (by ring) (by omega)
  simp only [show n + 1 + b + c = n + b + c + 1 by ring] at e2 ⊢
  rw [e1, e2]
  have hN : ((n : ℚ) + b + c + 1) ≠ 0 := by
    have := nz_of_int (m := n + b + c + 1) (by omega)
    push_cast at this; exact this
  have hu : ((n : ℚ) + b + c + 1) * ((n : ℚ) + b + c + 1)⁻¹ = 1 := mul_inv_cancel₀ hN
  have a := fct_ne_zero (n + b + c)
  have hq : fct (n + b + c) ≠ 0 := a
  push_cast at key ⊢
  simp only [div_eq_mul_inv, mul_inv] at key ⊢
  linear_combination ((fct n * fct b * fct c / fct (n + b + c)) * ((n : ℚ) + b + c + 1)⁻¹) * key
    + (dixT b c n k * (fct n * fct b * fct c / fct (n + b + c))) * hu


/-- The summand `C(a,k) C(n,k) / C(n+a,a)` of Vandermonde's identity, in factorial form. -/
def vandF (a n k : ℤ) : ℚ :=
  fct a ^ 2 * fct n ^ 2 / (fct k ^ 2 * fct (a - k) * fct (n - k) * fct (n + a))

/-- The certificate `R(n,k) = k^2 / ((k-1-n)(1+a+n))` of Vandermonde's identity. -/
def vandR (a n k : ℤ) : ℚ := (k : ℚ) ^ 2 / (((k : ℚ) - 1 - n) * (1 + a + n))

/-- CO-050. The WZ certificate `R(n,k) = k^2 / ((k-1-n)(1+a+n))` for the Vandermonde sum
`∑_k C(a,k) C(n,k) = C(n+a,a)` (summand normalised by `C(n+a,a)`). -/
@[kb "petkovsekwilfzeilberger1996" "Ex 7.3.4, p. 140"]
theorem vand_cert (a n k : ℤ) (ha : 0 ≤ a) (hn : 0 ≤ n) (hk : 0 ≤ k) (hka : k + 1 ≤ a)
    (hkn : k + 1 ≤ n) :
    vandF a (n + 1) k - vandF a n k
      = vandR a n (k + 1) * vandF a n (k + 1) - vandR a n k * vandF a n k := by
  unfold vandF vandR
  have e1 := fct_rec2 n (n + 1) (by ring) (by omega)
  have e2 := fct_rec2 (n - k) (n + 1 - k) (by ring) (by omega)
  have e3 := fct_rec2 (n + a) (n + 1 + a) (by ring) (by omega)
  have e4 := fct_rec2 k (k + 1) (by ring) (by omega)
  have e5 := fct_rec2 (a - k - 1) (a - k) (by ring) (by omega)
  have e6 := fct_rec2 (n - k - 1) (n - k) (by ring) (by omega)
  simp only [show a - (k + 1) = a - k - 1 by ring, show n - (k + 1) = n - k - 1 by ring]
  rw [e1, e2, e3, e4, e5, e6]
  have a1 := fct_ne_zero n
  have a2 := fct_ne_zero k
  have a3 := fct_ne_zero (a - k - 1)
  have a4 := fct_ne_zero (n - k - 1)
  have a5 := fct_ne_zero (n + a)
  have z1 := nz_of_int (m := n + 1 - k) (by omega)
  have z2 := nz_of_int (m := n - k) (by omega)
  have z3 := nz_of_int (m := n + 1 + a) (by omega)
  have z4 := nz_of_int (m := k + 1) (by omega)
  have z5 := nz_of_int (m := a - k) (by omega)
  have z6 := nz_of_int (m := k + 1 - 1 - n) (by omega)
  have z7 := nz_of_int (m := k - 1 - n) (by omega)
  have z8 := nz_of_int (m := 1 + a + n) (by omega)
  push_cast at z1 z2 z3 z4 z5 z6 z7 z8 ⊢
  field_simp
  ring

end UndergradKB.Combinatorics.AeqB
