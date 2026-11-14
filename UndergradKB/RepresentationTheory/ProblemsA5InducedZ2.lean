import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 4.34: representations of `A5` induced from `Z2`

Part of the decomposition of induced representations of `A5 = alternatingGroup (Fin 5)` (see
`ProblemsA5Induced.lean` for the overview); the statements are about the character of `Ind H ρ` for any
complex representation `ρ` of `H` with the given character.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-! ### `Z2` -/

section Z2

/-- The generator of `Z2`: the double transposition `(0 1)(2 3)`. -/
def a2 : A5 := classRep 1

/-- The subgroup `Z2 = {1, (0 1)(2 3)}`. -/
def H2 : Subgroup A5 := lvlSub (cycLvl a2 2) (Fin.last 2) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem hH2 : ∀ y, y ∈ H2 ↔ cycLvl a2 2 y ≠ Fin.last 2 := fun _ => Iff.rfl

theorem card_H2 : Nat.card H2 = 2 := by
  rw [H2, card_lvlSub]; decide +kernel

def n2 : Fin 5 → Fin 3 → ℕ := ![![1, 0, 0], ![0, 1, 14], ![0, 0, 20], ![0, 0, 12], ![0, 0, 12]]

theorem ind_Z2_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H2 V) (ω : ℂ) (hρ : ∀ k (hk : a2 ^ k ∈ H2), ρ.character ⟨a2 ^ k, hk⟩ = ω ^ k)
    (g : A5) : (Ind H2 ρ).character g = ![30, 2 * ω, 0, 0, 0] (cls g) := by
  rw [ind_cyclic a2 2 H2 hH2 (by decide +kernel) ρ ω hρ n2 (by decide +kernel) g, card_H2]
  generalize cls g = c
  fin_cases c <;> simp [n2, cycW, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)

/-- **Problem 4.34(a)**: the representation of `A5` induced from the trivial representation of
`Z2 = ⟨(0 1)(2 3)⟩` is `1 ⊕ 2 · (degree 4) ⊕ 3 · (degree 5) ⊕ (degree 3) ⊕ (degree 3)'`
(dimension `30`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z2_trivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H2 V) (hρ : ∀ k (hk : a2 ^ k ∈ H2), ρ.character ⟨a2 ^ k, hk⟩ = (1 : ℂ) ^ k) :
    (Ind H2 ρ).character = comb ![1, 2, 3, 1, 1] := by
  refine eq_comb_of_table _ _ (ind_Z2_values ρ 1 hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

/-- **Problem 4.34(a)**: the representation induced from the sign character (`(0 1)(2 3) ↦ -1`) of `Z2` is
`2 · (degree 4) ⊕ 2 · (degree 5) ⊕ 2 · (degree 3) ⊕ 2 · (degree 3)'`. -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z2_sign {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H2 V) (hρ : ∀ k (hk : a2 ^ k ∈ H2), ρ.character ⟨a2 ^ k, hk⟩ = (-1 : ℂ) ^ k) :
    (Ind H2 ρ).character = comb ![0, 2, 2, 2, 2] := by
  refine eq_comb_of_table _ _ (ind_Z2_values ρ (-1) hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

end Z2

end A5Induced

end UndergradKB.RepresentationTheory
