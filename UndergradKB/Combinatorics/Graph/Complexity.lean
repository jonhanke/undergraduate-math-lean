import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Encoding
import UndergradKB.Common.Attr

/-!
# The classes P and NP (Keller–Trotter, Section 4.4)

Decision problems are predicates `L : α → Prop` on a type `α` with an encoding `ea : α → List Γ`
into strings over a finite alphabet.  Polynomial-time computability is Mathlib's
`Turing.TM2ComputableInPolyTime`.  Mathlib has neither composition of polynomial-time machines
nor a machine erasing the tail of its input, which the inclusion `P ⊆ NP` needs; we prove the
inclusion from those two facts, stated as explicit hypotheses
(`PolyTimeCompClosed`, and polynomial-time computability of the projection to the problem part).
-/

namespace UndergradKB.Combinatorics

namespace Complexity

open Turing

/-- A function between encoded types is computable in polynomial time by some TM2. -/
def PolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea eb f)

open Classical in
/-- CO-075. Class P: the decision problems `L` (on the encoded type `α`) whose characteristic
function is computable by a polynomial-time Turing machine. -/
@[kb "kellertrotter2017" "text, p. 89"]
def InP {α Γ : Type} (ea : α → List Γ) (L : α → Prop) : Prop :=
  PolyTime ea Computability.encodeBool (fun x => decide (L x))

/-- Encoding of an instance together with a binary certificate: instance symbols, a separator
(`none`), then the certificate symbols. -/
def pairEnc {α Γ : Type} (ea : α → List Γ) (q : α × List Bool) : List (Option (Γ ⊕ Bool)) :=
  (ea q.1).map (fun g => some (Sum.inl g)) ++ none :: q.2.map (fun b => some (Sum.inr b))

open Classical in
/-- CO-076. Class NP: `L` is in NP if there are a polynomial bound `p` and a relation `R`
decidable in polynomial time (on instance-with-certificate pairs) such that `L x` holds exactly
when some certificate of length at most `p(|x|)` satisfies `R`. -/
@[kb "kellertrotter2017" "text, p. 90"]
def InNP {α Γ : Type} (ea : α → List Γ) (L : α → Prop) : Prop :=
  ∃ (p : Polynomial ℕ) (R : α × List Bool → Prop),
    PolyTime (pairEnc ea) Computability.encodeBool (fun q => decide (R q)) ∧
    ∀ x, L x ↔ ∃ c : List Bool, c.length ≤ p.eval (ea x).length ∧ R (x, c)

/-- Polynomial-time computable functions are closed under composition (not in Mathlib). -/
def PolyTimeCompClosed : Prop :=
  ∀ {α β γ Γ₁ Γ₂ Γ₃ : Type} (ea : α → List Γ₁) (eb : β → List Γ₂) (ec : γ → List Γ₃)
    (f : α → β) (g : β → γ), PolyTime ea eb f → PolyTime eb ec g → PolyTime ea ec (g ∘ f)

/-- CO-077 (conditional form). `P ⊆ NP`, from closure of polynomial-time computability under
composition and polynomial-time computability of discarding the certificate. The certificate for a
yes-instance of a problem in P is the empty string. -/
@[kb "kellertrotter2017" "text, p. 90"]
theorem inP_subset_inNP {α Γ : Type} (hcomp : PolyTimeCompClosed) (ea : α → List Γ)
    (hproj : PolyTime (pairEnc ea) ea Prod.fst) (L : α → Prop) (hL : InP ea L) :
    InNP ea L := by
  classical
  refine ⟨0, fun q => L q.1, ?_, fun x => ?_⟩
  · exact hcomp (pairEnc ea) ea Computability.encodeBool Prod.fst
      (fun x => decide (L x)) hproj hL
  · exact ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩

end Complexity

end UndergradKB.Combinatorics
