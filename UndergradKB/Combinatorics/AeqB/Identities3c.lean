import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.SolutionSpace
import UndergradKB.Common.Attr

/-!
# Annihilating operators of a sequence (A = B, §8.10 and §9.2)

The operators annihilating a sequence form a left ideal of the ring of recurrence operators
(§9.2, p. 184), and the minimal-order annihilator right-divides every annihilator (§8.10, p. 173).
-/

namespace UndergradKB.Combinatorics.AeqB.Identities3c
open UndergradKB.Combinatorics.AeqB UndergradKB.Combinatorics.AeqB.RecOp

section Ideal
variable {K : Type*} [Field K]

lemma act_seq_zero (L : RecOp K) : act L (0 : ℕ → K) = 0 := by
  funext n
  simp [act_def]

/-- CO-512. The recurrence operators (with polynomial coefficients) annihilating a given
sequence `y` form a left ideal of the ring of recurrence operators: if `L y = 0` then
`(B L) y = B (L y) = 0` for every operator `B`, and sums of annihilators annihilate. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 184"]
def annihilatorIdeal (y : ℕ → K) : Ideal (RecOp K) where
  carrier := {L | act L y = 0}
  zero_mem' := act_zero y
  add_mem' := by
    intro L M hL hM
    simp only [Set.mem_setOf_eq] at hL hM ⊢
    rw [act_add, hL, hM, add_zero]
  smul_mem' := by
    intro B L hL
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hL ⊢
    rw [act_mul, hL, act_seq_zero]

theorem mem_annihilatorIdeal {y : ℕ → K} {L : RecOp K} :
    L ∈ annihilatorIdeal y ↔ act L y = 0 := Iff.rfl

/-- CO-512. A sequence none of whose terms vanishes is annihilated by the first-order operator
`N - x(n+1)/x(n)` (whose coefficient is rational, not polynomial): this is why polynomial
coefficients are needed for a meaningful theory. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 184"]
theorem nowhere_zero_first_order (x : ℕ → K) (hx : ∀ n, x n ≠ 0) (n : ℕ) :
    (1 : K) * x (n + 1) + (-(x (n + 1) / x n)) * x n = 0 := by
  have := hx n
  field_simp
  ring

end Ideal

section MinimalOperator
variable {F : Type*} [Field F] [MulSemiringAction (Multiplicative ℕ) F]
  {V : Type*} [AddCommGroup V] [Module (SkewPolynomial F) V]

/-- CO-508. If `v` is annihilated by a nonzero operator `M` of minimal order among the nonzero
annihilators of `v`, then `M` right-divides every operator annihilating `v`: `L = Q M`.
(Stated for recurrence operators with coefficients in a field `F` with a shift action, e.g. rational
functions, acting on any module `V`, e.g. a space of sequences.  Proof as in the text: divide
`L = Q M + R` with `ord R < ord M`; then `R v = 0`, and minimality forces `R = 0`.) -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 173"]
theorem minimal_annihilator_dvd (v : V) (M : SkewPolynomial F) (hM0 : M ≠ 0) (hMv : M • v = 0)
    (hmin : ∀ L : SkewPolynomial F, L ≠ 0 → L • v = 0 → skewOrder M ≤ skewOrder L)
    (L : SkewPolynomial F) (hL : L • v = 0) : ∃ Q : SkewPolynomial F, L = Q * M := by
  obtain ⟨Q, R, hLR, hR⟩ := skew_right_division L M hM0
  have hRv : R • v = 0 := by
    have h1 : L • v = (Q * M) • v + R • v := by rw [hLR, add_smul]
    rw [mul_smul, hMv, smul_zero, zero_add, hL] at h1
    exact h1.symm
  refine ⟨Q, ?_⟩
  by_cases hR0 : R = 0
  · rw [hLR, hR0, add_zero]
  · exfalso
    have hne : R.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hR0 (SkewPolynomial.support_eq_empty.1 h)
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup R.support hne id
    have h1 : skewOrder R = m := by simpa [skewOrder] using hmeq
    have h2 := hmin R hR0 hRv
    have h3 := hR m hm
    omega

end MinimalOperator

end UndergradKB.Combinatorics.AeqB.Identities3c
