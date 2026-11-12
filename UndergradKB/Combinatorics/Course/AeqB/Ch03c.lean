import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import UndergradKB.Combinatorics.AeqB.Example362
import UndergradKB.Combinatorics.AeqB.ClausenSum
import UndergradKB.Combinatorics.AeqB.DougallSum
import UndergradKB.Combinatorics.AeqB.DixonWellPoised
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 3: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch03c

open Finset UndergradKB.Combinatorics.AeqB

/-- CO-046. The alternating sum `∑_k (-1)^k C(2n,k) C(2k,k) C(4n-2k,2n-k)` equals `C(2n,n)^2`
(a special case of Dixon's identity). -/
@[kb "petkovsekwilfzeilberger1996" "Example 3.6.2, p. 56"]
theorem ex_3_6_2_dixon_special (n : ℕ) :
    (∑ k ∈ range (2 * n + 1), (-1 : ℤ) ^ k *
        (((2 * n).choose k * (2 * k).choose k * (4 * n - 2 * k).choose (2 * n - k) : ℕ) : ℤ))
      = (((2 * n).choose n : ℕ) : ℤ) ^ 2 :=
  example_3_6_2 n

/-- CO-365. Clausen's terminating `4F3` sum with `d = -n`, `c = 1/2-a-b-n`, `e = a+b+1/2`,
`f = 1-a-n`, `g = 1-b-n`, as a product of rising factorials. -/
@[kb "petkovsekwilfzeilberger1996" "text (V) Clausen 4F3, p. 54"]
theorem text_p54_V_clausen_4F3 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∑ k ∈ range (n + 1),
        dpoch a k * dpoch b k * dpoch (1 / 2 - a - b - n) k * dpoch (-(n : ℝ)) k /
          ((k.factorial : ℝ) * dpoch (a + b + 1 / 2) k * dpoch (1 - a - n) k *
            dpoch (1 - b - n) k)
      = dpoch (2 * a) n * dpoch (a + b) n * dpoch (2 * b) n /
          (dpoch (2 * a + 2 * b) n * dpoch a n * dpoch b n) :=
  clausen_sum a b ha hb n

/-- CO-366. Dougall's terminating well-poised balanced `7F6` sum (`1 + 2A = B + C + D + E - n`)
as a product of rising factorials. -/
@[kb "petkovsekwilfzeilberger1996" "text (VI) Dougall 7F6, p. 54"]
theorem text_p54_VI_dougall_7F6 (A B C D E : ℝ) (n : ℕ) (hE : 1 + 2 * A = B + C + D + E - n)
    (h : ∀ m ≤ n, DougallHyp (1 + 2 * A - B - C - D) (1 + A - C - D) (1 + A - B - D) A m) :
    ∑ k ∈ range (n + 1),
        dpoch A k * dpoch (1 + A / 2) k * dpoch B k * dpoch C k * dpoch D k * dpoch E k *
          dpoch (-(n : ℝ)) k /
        ((k.factorial : ℝ) * dpoch (A / 2) k * dpoch (1 + A - B) k * dpoch (1 + A - C) k *
          dpoch (1 + A - D) k * dpoch (1 + A - E) k * dpoch (1 + A + n) k)
      = dpoch (1 + A) n * dpoch (1 + A - B - C) n * dpoch (1 + A - B - D) n *
          dpoch (1 + A - C - D) n /
        (dpoch (1 + A - B) n * dpoch (1 + A - C) n * dpoch (1 + A - D) n *
          dpoch (1 + A - B - C - D) n) :=
  dougall_sum A B C D E n hE h

/-- CO-369. Dixon's identity in terminating well-poised form:
`3F2(-2n,b,c; 1-b-2n, 1-c-2n; 1) = (1)_{2n} (b)_n (c)_n (b+c)_{2n} / ((1)_n (b)_{2n} (c)_{2n} (b+c)_n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 55"]
theorem text_p55_dixon_well_poised (b c : ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < 2 * n → b + j ≠ 0) (hc : ∀ j : ℕ, j < 2 * n → c + j ≠ 0)
    (hs : ∀ j : ℕ, j < 2 * n → b + c + j ≠ 0) :
    ∑ k ∈ range (2 * n + 1),
        dpoch (-(2 * (n : ℝ))) k * dpoch b k * dpoch c k /
          (dpoch (1 - b - 2 * n) k * dpoch (1 - c - 2 * n) k * (k.factorial : ℝ)) =
      dpoch 1 (2 * n) * dpoch b n * dpoch c n * dpoch (b + c) (2 * n) /
        (dpoch 1 n * dpoch b (2 * n) * dpoch c (2 * n) * dpoch (b + c) n) :=
  dixon_well_poised b c n hb hc hs

end UndergradKB.Combinatorics.Course.AeqB.Ch03c
