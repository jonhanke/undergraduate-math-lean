import Mathlib.Computability.Halting
import Mathlib.NumberTheory.Dioph
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad
import UndergradKB.Common

/-!
# Foundations: Matiyasevich's theorem from the DPRM theorem

Levin (Section 6.2.5, pdf p. 463) mentions, without proof, that there is no general algorithm deciding
whether a Diophantine equation has a solution (Matiyasevich's theorem, the negative answer to Hilbert's
tenth problem).

Mathlib has Diophantine sets (`Dioph`, with the hard step of Matiyasevich's proof: exponentiation is
Diophantine, `Dioph.pow_dioph`, via the Pell equation) and the undecidability of the halting problem
(`ComputablePred.halting_problem`). What it does not have is the Davis–Putnam–Robinson–Matiyasevich
(DPRM) theorem itself: every recursively enumerable set of natural numbers is Diophantine. Its missing
ingredient is Davis's bounded universal quantifier theorem (Diophantine sets are closed under bounded
universal quantification), which is what lets one encode the run of a partial recursive function by a
Diophantine condition.

This file records the DPRM theorem as the named input `DPRMTheorem` and derives from it:

* `matiyasevich_nat`: there is a polynomial `p (n, x₁, x₂, ...)` with integer coefficients such that
  no computable procedure decides, given `n`, whether `p (n, x) = 0` has a solution in natural numbers
  (the halting set is recursively enumerable, so Diophantine, but not decidable);
* `levin_s6_2_5_matiyasevich`: the same with integer unknowns, which is the book's notion of a
  Diophantine equation (only integer solutions are of interest), by Lagrange's four squares theorem.

A general algorithm for Diophantine equations would in particular decide the one-parameter family
`p (n, ·)`, so both statements say that no such algorithm exists.

Wave 5: the DPRM theorem is now proved (`UndergradKB.Foundations.dprm`, in `Hilbert10.lean`, from
Davis's bounded universal quantifier theorem in `DPRM/`), and the unconditional statement is
`levin_s6_2_5_hilbert_tenth`.
-/

namespace UndergradKB.Foundations

open Nat.Partrec (Code)
open Encodable Denumerable

/-- The Davis–Putnam–Robinson–Matiyasevich theorem, as a named input (it is not proved here and is not
in Mathlib): every recursively enumerable predicate on the natural numbers is Diophantine, that is,
for some polynomial `p` with integer coefficients, `P n` holds iff `p (n, t) = 0` for some natural
numbers `t`. -/
structure DPRMTheorem : Prop where
  re_dioph : ∀ P : ℕ → Prop, REPred P → Dioph {v : Fin 1 → ℕ | P (v 0)}

/-- The halting set, read on natural-number codes: program number `n` halts on input `0`. -/
def haltingSet (n : ℕ) : Prop := (Code.eval (ofNat Code n) 0).Dom

theorem haltingSet_re : REPred haltingSet :=
  (Code.eval_part.comp (Computable.ofNat Code) (Computable.const 0)).dom_re

theorem haltingSet_not_computable : ¬ ComputablePred haltingSet := by
  rintro ⟨inst, h⟩
  apply ComputablePred.halting_problem 0
  refine ComputablePred.of_eq (p := fun c : Code => haltingSet (encode c))
    ⟨fun c => inst (encode c), h.comp Computable.encode⟩ ?_
  intro c
  simp [haltingSet, ofNat_encode]

/-- Matiyasevich's theorem over the natural numbers, from the DPRM theorem: some one-parameter family
of Diophantine equations `p (n, t) = 0` has no algorithm deciding, given `n`, whether it is solvable
in natural numbers `t`. -/
theorem matiyasevich_nat (h : DPRMTheorem) :
    ∃ (β : Type) (p : Poly (Fin 1 ⊕ β)),
      ¬ ComputablePred fun n : ℕ => ∃ t : β → ℕ, p (Sum.elim ![n] t) = 0 := by
  obtain ⟨β, p, hp⟩ := h.re_dioph haltingSet haltingSet_re
  refine ⟨β, p, fun hc => haltingSet_not_computable (hc.of_eq fun n => ?_)⟩
  rw [show haltingSet n ↔ (![n] : Fin 1 → ℕ) ∈ {v : Fin 1 → ℕ | haltingSet (v 0)} from Iff.rfl, hp]

/-- Every polynomial function of natural-number arguments in Mathlib's sense (`IsPoly`) is the
evaluation of an integer multivariate polynomial at the arguments viewed as integers. -/
theorem exists_mvPolynomial_of_isPoly {α : Type*} {f : (α → ℕ) → ℤ} (hf : IsPoly f) :
    ∃ q : MvPolynomial α ℤ, ∀ v : α → ℕ, MvPolynomial.eval (fun i => (v i : ℤ)) q = f v := by
  induction hf with
  | proj i => exact ⟨MvPolynomial.X i, fun v => by simp⟩
  | const n => exact ⟨MvPolynomial.C n, fun v => by simp⟩
  | sub _ _ hf hg =>
    obtain ⟨q, hq⟩ := hf
    obtain ⟨r, hr⟩ := hg
    exact ⟨q - r, fun v => by simp [hq, hr]⟩
  | mul _ _ hf hg =>
    obtain ⟨q, hq⟩ := hf
    obtain ⟨r, hr⟩ := hg
    exact ⟨q * r, fun v => by simp [hq, hr]⟩

theorem eval_bind₁_int {σ τ : Type*} (f : τ → ℤ) (g : σ → MvPolynomial τ ℤ)
    (φ : MvPolynomial σ ℤ) :
    MvPolynomial.eval f (MvPolynomial.bind₁ g φ) =
      MvPolynomial.eval (fun i => MvPolynomial.eval f (g i)) φ :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℤ) f g φ

/-- The substitution of each natural-number unknown by a sum of four integer squares. -/
noncomputable def fourSquaresSubst (β : Type) : Fin 1 ⊕ β → MvPolynomial (Option (β × Fin 4)) ℤ
  | Sum.inl _ => MvPolynomial.X none
  | Sum.inr b => ∑ j : Fin 4, MvPolynomial.X (some (b, j)) ^ 2

theorem eval_fourSquaresSubst {β : Type} (n : ℕ) (z : β × Fin 4 → ℤ) (i : Fin 1 ⊕ β) :
    MvPolynomial.eval (fun o => o.elim (n : ℤ) z) (fourSquaresSubst β i) =
      Sum.elim (fun _ => (n : ℤ)) (fun b => ∑ j : Fin 4, z (b, j) ^ 2) i := by
  cases i <;> simp [fourSquaresSubst]

/-- **Matiyasevich's theorem** (Levin, Section 6.2.5), from the DPRM theorem: there is no general
algorithm deciding whether a Diophantine equation has an integer solution. Precisely, some polynomial
`q (n, z₁, z₂, ...)` with integer coefficients has no algorithm deciding, given `n`, whether
`q (n, z) = 0` has a solution in integers `z`. -/
theorem levin_s6_2_5_matiyasevich (h : DPRMTheorem) :
    ∃ (γ : Type) (q : MvPolynomial (Option γ) ℤ),
      ¬ ComputablePred fun n : ℕ => ∃ z : γ → ℤ, MvPolynomial.eval (fun o => o.elim (n : ℤ) z) q = 0 := by
  obtain ⟨β, p, hp⟩ := matiyasevich_nat h
  obtain ⟨q, hq⟩ := exists_mvPolynomial_of_isPoly p.isPoly
  refine ⟨β × Fin 4, MvPolynomial.bind₁ (fourSquaresSubst β) q, fun hc => hp (hc.of_eq fun n => ?_)⟩
  simp only [eval_bind₁_int, eval_fourSquaresSubst]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨fun b => (∑ j : Fin 4, z (b, j) ^ 2).toNat, ?_⟩
    rw [← hq, ← hz]
    refine congrArg (fun f => MvPolynomial.eval f q) (funext fun i => ?_)
    cases i with
    | inl i => simp [Fin.fin_one_eq_zero i]
    | inr b =>
      simp only [Sum.elim_inr]
      exact Int.toNat_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · rintro ⟨t, ht⟩
    choose a b c d habcd using fun x => Nat.sum_four_squares (t x)
    refine ⟨fun bj => ((![a, b, c, d] bj.2) bj.1 : ℤ), ?_⟩
    rw [← ht, ← hq]
    refine congrArg (fun f => MvPolynomial.eval f q) (funext fun i => ?_)
    cases i with
    | inl i => simp [Fin.fin_one_eq_zero i]
    | inr x =>
      simp only [Sum.elim_inr, Fin.sum_univ_four]
      rw [← habcd x]
      simp

end UndergradKB.Foundations
