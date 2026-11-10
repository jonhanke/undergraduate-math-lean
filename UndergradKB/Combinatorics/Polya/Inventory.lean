import Mathlib.Algebra.MvPolynomial.Eval
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Polya.CycleIndex

/-!
# The pattern inventory (Keller--Trotter, Section 15.4)

Source: Keller--Trotter, *Applied Combinatorics* (2017), p. 327.
-/

namespace UndergradKB.Combinatorics.Polya

open scoped Classical
open MulAction

attribute [local instance] arrowAction

variable (G S C : Type*) [Fintype S] [Fintype C] [Group G] [Fintype G] [MulAction G S]

/-- CO-322. The pattern inventory: the generating function of Pólya's enumeration theorem, i.e. the
sum over the orbits of colorings `S → C` of the monomial `∏_s c_{f s}` recording the color content
of a representative (colors are the variables `X c` of a polynomial ring). -/
@[kb "kellertrotter2017" "Definition (unnumbered) pattern inventory, p. 327"]
noncomputable def patternInventory : MvPolynomial C ℚ :=
  ∑ ω : orbitRel.Quotient G (S → C), ∏ s, (MvPolynomial.X (ω.out s) : MvPolynomial C ℚ)

/-- CO-322. By Pólya's enumeration theorem the pattern inventory is the cycle index with
`x_k := ∑_c c^k` substituted. -/
@[kb "kellertrotter2017" "Definition (unnumbered) pattern inventory, p. 327"]
theorem patternInventory_eq_cycleIndex :
    patternInventory G S C = MvPolynomial.aeval
      (fun k => ∑ c, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k) (cycleIndex G S) :=
  polya_enumeration

end UndergradKB.Combinatorics.Polya
