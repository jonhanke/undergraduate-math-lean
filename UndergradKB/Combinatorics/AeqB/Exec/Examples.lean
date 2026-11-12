import UndergradKB.Combinatorics.AeqB.Exec.Celine
import UndergradKB.Combinatorics.AeqB.Exec.Operators

/-!
# The executable algorithms of "A = B" at work (wave 3)

Each statement below is proved by `decide +kernel`: the Lean kernel itself runs the algorithm
(search and certificate check) on the given input. Combined with the soundness theorems
(`zcheck_sound`, `ccheck_sound`, `wzMate_sound`, `clm_sound`) these are machine-found and
machine-checked recurrences, as the book advertises (A = B, Chapter 6: "the computer finds the
recurrence and its proof").

* Zeilberger: `∑ₖ C(n,k)` gives `f(n+1) = 2 f(n)`; `∑ₖ C(n,k)²` gives `(n+1) f(n+1) = 2(2n+1) f(n)`;
  with `#eval` (compiled code, not kernel-checked here because the kernel evaluation is slow) the
  same functions find the Franel recurrence `(n+2)² f(n+2) = (7n²+21n+16) f(n+1) + 8(n+1)² f(n)` for
  `∑ₖ C(n,k)³` (input `binomCube`) and `(n+1)² f(n+1) = 4(2n+1)² f(n)` for A = B Example 3.6.2
  (input `example362`), whose certificate was used for `Example362.lean`.
* Sister Celine: Pascal's rule for `C(n,k)`.
* WZ: the WZ mate of `C(n,k)/2ⁿ`.
* Holonomic closure: a common left multiple annihilating `2ⁿ + 3ⁿ`.
-/

namespace UndergradKB.Combinatorics.AeqB.Exec.Examples

open UndergradKB.Combinatorics.AeqB.Exec

/-- `C(n,k) = n!/(k!(n-k)!)`. -/
def binom : ZInput := ZInput.ofProper [(1, 0, 0)] [(0, 1, 0), (1, -1, 0)] 1 1

/-- `C(n,k)²`. -/
def binomSq : ZInput :=
  ZInput.ofProper [(1, 0, 0), (1, 0, 0)] [(0, 1, 0), (0, 1, 0), (1, -1, 0), (1, -1, 0)] 1 1

/-- `C(n,k)³`. -/
def binomCube : ZInput :=
  ZInput.ofProper [(1, 0, 0), (1, 0, 0), (1, 0, 0)]
    [(0, 1, 0), (0, 1, 0), (0, 1, 0), (1, -1, 0), (1, -1, 0), (1, -1, 0)] 1 1

/-- The summand of A = B Example 3.6.2: `(-1)ᵏ (2n)! (2k)! (4n-2k)! / (k!³ (2n-k)!³)`. -/
def example362 : ZInput :=
  ZInput.ofProper [(2, 0, 0), (0, 2, 0), (4, -2, 0)]
    [(0, 1, 0), (0, 1, 0), (0, 1, 0), (2, -1, 0), (2, -1, 0), (2, -1, 0)] (-1) 1

/-- The recurrence coefficients found by Zeilberger's algorithm, as lists of rational coefficients
of polynomials in `n`. -/
def zRec (I : ZInput) (Jmax Δmax : ℕ) : Option (List (List ℚ)) :=
  (zeilberger I Jmax Δmax).map fun C => C.a.map fun p => (QPoly.norm p).coeffs

/-- CO-425. Zeilberger's algorithm on `∑ₖ C(n,k)`: `2 f(n) - f(n+1) = 0`, certificate checked. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.3.1)-(6.3.12), p. 116-119"]
theorem zeilberger_binom :
    zRec binom 1 2 = some [[2], [-1]] ∧
      ((zeilberger binom 1 2).map fun C => zcheck binom C) = some true := by
  decide +kernel

/-- CO-425. Zeilberger's algorithm on `∑ₖ C(n,k)²`: `-(2n+1) f(n) + (n+1)/2 f(n+1) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text (6.3.1)-(6.3.12), p. 116-119"]
theorem zeilberger_binomSq :
    zRec binomSq 1 2 = some [[-1, -2], [1 / 2, 1 / 2]] ∧
      ((zeilberger binomSq 1 2).map fun C => zcheck binomSq C) = some true := by
  decide +kernel

/-- CO-388. Sister Celine's method on `C(n,k)` finds Pascal's rule
`-F(n,k) + F(n-1,k) + F(n-1,k-1) = 0` (coefficients `a₀₀, a₀₁, a₁₀, a₁₁`). -/
@[kb "petkovsekwilfzeilberger1996" "Sister Celine's algorithm, steps 1-5, p. 69"]
theorem celine_pascal :
    ((celine binom 1 1).map fun C => (C.I, C.J, C.a.map fun p => (QPoly.norm p).coeffs)) =
      some (1, 1, [[-1], [1], [], [1]]) := by
  decide +kernel

/-- `C(n,k)/2ⁿ`. -/
def binomHalf : ZInput := ZInput.ofProper [(1, 0, 0)] [(0, 1, 0), (1, -1, 0)] 1 (1 / 2)

/-- CO-445. The WZ mate of `F = C(n,k)/2ⁿ` is found and checked: `R(n,k) = -k/(2(n+1-k))`
(the certificate gives `R = c · k / (n+1-k)` with `c(n) = -2` as the normalizing coefficient). -/
@[kb "petkovsekwilfzeilberger1996" "text (finding the WZ certificate), p. 133-134"]
theorem wzMate_binomHalf :
    ((wzMate binomHalf 3).map fun C => (zcheck binomHalf C, C.a.map fun p => (QPoly.norm p).coeffs)) =
      some (true, [[2], [-2]]) := by
  decide +kernel

/-- `N - 2` and `N - 3`. -/
def opTwo : EOp := ⟨[⟨[-2]⟩, ⟨[1]⟩]⟩
def opThree : EOp := ⟨[⟨[-3]⟩, ⟨[1]⟩]⟩

/-- CO-513. The common left multiple of `N - 2` and `N - 3` found and checked: `N² - 5N + 6`,
which annihilates `2ⁿ + 3ⁿ` (`clm_sound`). -/
@[kb "petkovsekwilfzeilberger1996" "Definition 9.2.1, p. 184"]
theorem clm_two_three :
    ((commonLeftMultiple opTwo opThree).map fun C =>
      (clmCheck opTwo opThree C, (C.M1.mul opTwo).c.map fun p => (QPoly.norm p).coeffs)) =
      some (true, [[6], [-5], [1]]) := by
  decide +kernel

end UndergradKB.Combinatorics.AeqB.Exec.Examples
