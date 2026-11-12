import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import UndergradKB.RepresentationTheory.KostkaNumbers
import UndergradKB.RepresentationTheory.SchurPolynomials
import UndergradKB.Common.Attr

/-! # Definitions for the Frobenius character formula (Etingof et al., §4.16)

* `cyclePoly n N g`: for a permutation `g` of `Fin n` with `i_m` cycles of length `m`, the polynomial
  `∏_m (x_1^m + ⋯ + x_N^m)^{i_m}` in `N` variables over `ℂ`.
* `contingency α β`: the number of `N × N` matrices of natural numbers with row sums `α` and column sums `β`.
* `rhoExp N j = N - 1 - j`: the exponents of `ρ = (N - 1, …, 1, 0)` (`0`-based indices).
* `frobChar n N λ g`: the coefficient of `x^{λ + ρ}` in `Δ(x) · ∏_m (x_1^m + ⋯ + x_N^m)^{i_m}`, where `Δ` is the
  Vandermonde product `∏_{i<j} (x_i - x_j)`; Theorem 4.47 says that it is the character of `V_λ` at `g`.
-/

namespace UndergradKB.RepresentationTheory

open Finset

/-- The polynomial `∏_m (x_1^m + ⋯ + x_N^m)^{i_m}` attached to a permutation `g` of `Fin n` with `i_m` cycles of
length `m` (fixed points counted as cycles of length `1`). -/
noncomputable def cyclePoly (n N : ℕ) (g : Equiv.Perm (Fin n)) : MvPolynomial (Fin N) ℂ :=
  ∏ m ∈ Finset.Icc 1 n, MvPolynomial.psum (Fin N) ℂ m ^ cycleCount g m

/-- The number of `N × N` matrices with entries in `ℕ` whose row sums are `α` and column sums are `β`. -/
noncomputable def contingency {N : ℕ} (α β : Fin N → ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin N => Fintype.piFinset fun _ : Fin N => Finset.range (∑ i, α i + 1)).filter
    fun M : Fin N → Fin N → ℕ => (∀ i, ∑ j, M i j = α i) ∧ ∀ j, ∑ i, M i j = β j).card

/-- The exponents of `ρ = (N - 1, N - 2, …, 0)`, indexed from `0`. -/
def rhoExp (N : ℕ) (j : Fin N) : ℕ := (j.rev : ℕ)

/-- The exponent vector `λ + ρ` as a finitely supported function. -/
noncomputable def shiftExp {N : ℕ} (lam : Fin N → ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => lam j + rhoExp N j

/-- The class function `θ_λ(g)`: the coefficient of `x^{λ + ρ}` in `Δ(x) ∏_m (x_1^m + ⋯ + x_N^m)^{i_m}`. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
noncomputable def frobChar (n N : ℕ) (lam : Fin N → ℕ) (g : Equiv.Perm (Fin n)) : ℂ :=
  (vandermondeDelta ℂ N * cyclePoly n N g).coeff (shiftExp lam)

end UndergradKB.RepresentationTheory
