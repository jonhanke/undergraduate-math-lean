import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import UndergradKB.Combinatorics.AeqB.Symmetric
import UndergradKB.Common.Attr

/-!
# Petkovsek–Wilf–Zeilberger, "A = B", Chapter 1: course wrappers of results proved in this library (wave 4)
-/

namespace UndergradKB.Combinatorics.Course.AeqB.Ch01c

open UndergradKB.Combinatorics.AeqB

/-- CO-350. An identity among the elementary symmetric functions `e_1..e_m` and the power sums
`p_1..p_m` holds in every number of variables iff it holds in exactly `m` variables. -/
@[kb "petkovsekwilfzeilberger1996" "text (identities among symmetric functions), p. 24"]
theorem text_p24_symmetric_identity_iff (K : Type*) [CommRing K] (m : ℕ)
    (P : MvPolynomial (Fin m ⊕ Fin m) K) :
    (∀ n, symmEval K m n P = 0) ↔ symmEval K m m P = 0 :=
  symm_identity_iff K m P

end UndergradKB.Combinatorics.Course.AeqB.Ch01c
