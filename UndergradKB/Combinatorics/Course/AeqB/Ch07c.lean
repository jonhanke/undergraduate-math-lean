import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Pochhammer
import UndergradKB.Combinatorics.AeqB.SaalschutzCompanion
import UndergradKB.Combinatorics.AeqB.Dual
import UndergradKB.Combinatorics.AeqB.Gessel
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 7: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch07c

open Finset UndergradKB.Combinatorics.AeqB

/-- CO-457. Companion of the full Saalschütz identity: for `c > a + b` and an integer `k > 0` the
nonterminating `3F2(k, c-a-b, c+k-1; c-b+k, c-a+k; 1)` converges and is expressed through a
partial sum of Gauss's `2F1(1)` series. -/
@[kb "petkovsekwilfzeilberger1996" "Exercise 7.3.3, p. 140"]
theorem ex_7_3_3_saalschutz_companion (a b c : ℝ) (hs : 0 < c - a - b)
    (ha : ∀ n : ℕ, a ≠ -(n : ℝ)) (hb : ∀ n : ℕ, b ≠ -(n : ℝ)) (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ)) (k : ℕ) (hk : 0 < k) :
    Summable (fun m : ℕ => pFqTerm ![(k : ℝ), c - a - b, c + (k : ℝ) - 1]
        ![c - b + (k : ℝ), c - a + (k : ℝ)] (1 : ℝ) m) ∧
    ∑' m : ℕ, pFqTerm ![(k : ℝ), c - a - b, c + (k : ℝ) - 1]
        ![c - b + (k : ℝ), c - a + (k : ℝ)] (1 : ℝ) m =
      ((ascPochhammer ℝ k).eval (c - b) * (ascPochhammer ℝ k).eval (c - a) /
          ((ascPochhammer ℝ k).eval a * (ascPochhammer ℝ k).eval b)) *
        (1 - Real.Gamma (c - a) * Real.Gamma (c - b) / (Real.Gamma c * Real.Gamma (c - a - b)) *
          ∑ i ∈ range k, pFqTerm ![a, b] ![c] (1 : ℝ) i) :=
  saalschutz_companion a b c hs ha hb hc hca hcb k hk

/-- CO-458. Dual identities: replacing a numerator factorial `(an+bk+c)!` by
`(-1)^(an+bk)/(-1-an-bk-c)!` in both `F` and its mate `G` keeps a WZ pair (the replaced factor
differs by a constant, by the gamma reflection formula). -/
@[kb "petkovsekwilfzeilberger1996" "text (7.3.6), p. 141"]
theorem eq_7_3_6_dual_wz_pair (a b : ℤ) (c : ℝ) (hc : ∀ m : ℤ, c ≠ m)
    (F G H H' : ℤ → ℤ → ℝ)
    (hF : ∀ n k, F n k = Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) * H n k)
    (hG : ∀ n k, G n k = Real.Gamma (((a * n + b * k : ℤ) : ℝ) + c + 1) * H' n k)
    (hWZ : WZEq F G) :
    WZEq
      (fun n k => (-1 : ℝ) ^ (a * n + b * k) /
        Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c)) * H n k)
      (fun n k => (-1 : ℝ) ^ (a * n + b * k) /
        Real.Gamma (-(((a * n + b * k : ℤ) : ℝ) + c)) * H' n k) :=
  wzEq_dual a b c hc F G H H' hF hG hWZ

/-- CO-468. Three further Gessel identities, each certified by an explicit `R(n,k)`: a terminating
`3F2` at `3/4`, a second `3F2` at `4/3`, and a `4F3` at `2/27`, each equal to a quotient of
rising factorials. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 147"]
theorem text_p147_gessel_identities :
    (∀ (c : ℝ), NoNegInt (1 - 3 * c) → NoNegInt (c + 2 / 3) → NoNegInt (1 - c) → ∀ n : ℕ,
      ∑ k ∈ range (3 * n + 1),
          dpoch (-(3 * (n : ℝ))) k * dpoch (2 / 3 - c) k * dpoch (3 * (n : ℝ) + 2) k *
              (3 / 4) ^ k /
            ((k.factorial : ℝ) * dpoch (3 / 2) k * dpoch (1 - 3 * c) k) =
        dpoch (c + 2 / 3) n * dpoch (1 / 3) n / (dpoch (1 - c) n * dpoch (4 / 3) n)) ∧
    (∀ (b : ℝ), NoNegInt (1 / 3 - b) → NoNegInt (1 / 3 + b) → (∀ j : ℤ, 2 / 3 - b + j ≠ 0) →
      ∀ n : ℕ,
      ∑ k ∈ range (3 * n / 2 + 1),
          dpoch (-(3 * b)) k * dpoch (-(3 * (n : ℝ)) / 2) k *
              dpoch ((-(3 * (n : ℝ)) + 1) / 2) k * (4 / 3) ^ k /
            ((k.factorial : ℝ) * dpoch (-(3 * (n : ℝ))) k * dpoch (2 / 3 - b - n) k) =
        dpoch (1 / 3 - b) n / dpoch (1 / 3 + b) n) ∧
    (∀ n : ℕ,
      ∑ k ∈ range (n + 1),
          dpoch (3 / 2 + (n : ℝ) / 5) k * dpoch (2 / 3) k * dpoch (-(n : ℝ)) k *
              dpoch (2 * (n : ℝ) + 2) k * (2 / 27) ^ k /
            ((k.factorial : ℝ) * dpoch ((n : ℝ) + 11 / 6) k * dpoch (4 / 3) k *
              dpoch ((n : ℝ) / 5 + 1 / 2) k) =
        dpoch (5 / 2) n * dpoch (11 / 6) n / (dpoch (3 / 2) n * dpoch (7 / 2) n)) :=
  ⟨fun c h1 h2 h3 n => gessel_one c h1 h2 h3 n, fun b h1 h2 h3 n => gessel_two b h1 h2 h3 n,
    gessel_three⟩

end UndergradKB.Combinatorics.Course.AeqB.Ch07c
