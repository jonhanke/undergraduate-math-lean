import UndergradKB.Foundations.Matiyasevich
import UndergradKB.Foundations.DPRM.Partrec

/-!
# Foundations: the DPRM theorem and Hilbert's tenth problem

Levin (Section 6.2.5, pdf p. 463) mentions that there is no general algorithm deciding whether a
Diophantine equation has a solution (Matiyasevich 1970, the negative answer to Hilbert's tenth
problem). Wave 4 derived this from the Davis–Putnam–Robinson–Matiyasevich (DPRM) theorem taken as the
named input `DPRMTheorem`. Here the DPRM theorem is proved (`dprm`), so Matiyasevich's theorem holds
unconditionally (`levin_s6_2_5_hilbert_tenth`).

Ingredients, all in `UndergradKB/Foundations/DPRM/`: Mathlib's `Dioph.pow_dioph` (exponentiation is
Diophantine, via the Pell equation: the step due to Matiyasevich); binomial coefficients and factorials
are Diophantine (`Arith.lean`); Davis's bounded universal quantifier theorem (`DavisTheorem.lean`);
the graph of every partial recursive function is Diophantine (`Partrec.lean`).
-/

namespace UndergradKB.Foundations

open Dioph Vector3 Encodable

/-- **The DPRM theorem**: every recursively enumerable predicate on the natural numbers is
Diophantine: there is a polynomial `p` with integer coefficients such that `P n` holds iff
`p (n, t) = 0` for some natural numbers `t`. -/
theorem re_dioph (P : ℕ → Prop) (hP : REPred P) : Dioph {v : Fin 1 → ℕ | P (v 0)} := by
  have hG := DPRM.partrec_graph_dioph hP
  have h2 := reindex_dioph _ ([&1, &0] : Vector3 (Fin2 2) 2) hG
  have h1 := (D∃) 1 h2
  refine (reindex_dioph (Fin 1) (fun _ : Fin2 1 => (0 : Fin 1)) h1).ext fun v => ?_
  show (∃ y, y ∈ Part.bind (decode (α := ℕ) (v 0)) fun a =>
      (Part.assert (P a) fun _ => Part.some ()).map encode) ↔ P (v 0)
  simp [Part.mem_assert_iff]

/-- The DPRM theorem in the form of the named input of `Matiyasevich.lean`. -/
theorem dprm : DPRMTheorem := ⟨re_dioph⟩

/-- **Matiyasevich's theorem** (Levin, Section 6.2.5; Hilbert's tenth problem): there is no general
algorithm deciding whether a Diophantine equation has an integer solution. Precisely, some polynomial
`q (n, z₁, z₂, ...)` with integer coefficients has no algorithm deciding, given `n`, whether
`q (n, z) = 0` has a solution in integers `z`. -/
@[kb "levin2025" "Box §6.2.5 (remark), p. 463"]
theorem levin_s6_2_5_hilbert_tenth :
    ∃ (γ : Type) (q : MvPolynomial (Option γ) ℤ),
      ¬ ComputablePred fun n : ℕ => ∃ z : γ → ℤ, MvPolynomial.eval (fun o => o.elim (n : ℤ) z) q = 0 :=
  levin_s6_2_5_matiyasevich dprm

/-- Matiyasevich's theorem over the natural numbers: some one-parameter family of Diophantine
equations `p (n, t) = 0` has no algorithm deciding, given `n`, whether it has a solution in natural
numbers. -/
theorem hilbert_tenth_nat :
    ∃ (β : Type) (p : Poly (Fin 1 ⊕ β)),
      ¬ ComputablePred fun n : ℕ => ∃ t : β → ℕ, p (Sum.elim ![n] t) = 0 :=
  matiyasevich_nat dprm

end UndergradKB.Foundations
