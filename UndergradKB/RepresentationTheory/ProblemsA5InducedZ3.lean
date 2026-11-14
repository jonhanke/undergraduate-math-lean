import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 4.34: representations of `A5` induced from `Z3`

Part of the decomposition of induced representations of `A5 = alternatingGroup (Fin 5)` (see
`ProblemsA5Induced.lean` for the overview); the statements are about the character of `Ind H ρ` for any
complex representation `ρ` of `H` with the given character.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-! ### `Z3` -/

section Z3

/-- The generator of `Z3`: the three-cycle `(0 1 2)` (a product of two transpositions). -/
def a3 : A5 := classRep 2

/-- The subgroup `Z3 = ⟨a3⟩`. -/
def H3 : Subgroup A5 := lvlSub (cycLvl a3 3) (Fin.last 3) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem hH3 : ∀ y, y ∈ H3 ↔ cycLvl a3 3 y ≠ Fin.last 3 := fun _ => Iff.rfl

theorem card_H3 : Nat.card H3 = 3 := by
  rw [H3, card_lvlSub]; decide +kernel

def n3 : Fin 5 → Fin 4 → ℕ :=
  ![![1, 0, 0, 0], ![0, 0, 0, 15], ![0, 1, 1, 18], ![0, 0, 0, 12], ![0, 0, 0, 12]]

theorem ind_Z3_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H3 V) (ω : ℂ) (hρ : ∀ k (hk : a3 ^ k ∈ H3), ρ.character ⟨a3 ^ k, hk⟩ = ω ^ k)
    (g : A5) : (Ind H3 ρ).character g = ![20, 0, ω + ω ^ 2, 0, 0] (cls g) := by
  rw [ind_cyclic a3 3 H3 hH3 (by decide +kernel) ρ ω hρ n3 (by decide +kernel) g, card_H3]
  generalize cls g = c
  fin_cases c <;> simp [n3, cycW, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)

/-- **Problem 4.34(b)**: the representation induced from the trivial representation of `Z3 = ⟨(0 1 2)⟩` is
`1 ⊕ 2 · (degree 4) ⊕ (degree 5) ⊕ (degree 3) ⊕ (degree 3)'` (dimension `20`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z3_trivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H3 V) (hρ : ∀ k (hk : a3 ^ k ∈ H3), ρ.character ⟨a3 ^ k, hk⟩ = (1 : ℂ) ^ k) :
    (Ind H3 ρ).character = comb ![1, 2, 1, 1, 1] := by
  refine eq_comb_of_table _ _ (ind_Z3_values ρ 1 hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

/-- **Problem 4.34(b)**: the representation induced from a nontrivial character `a3 ^ k ↦ ω ^ k`
(`ω ^ 3 = 1`, `ω ≠ 1`) of `Z3` is `(degree 4) ⊕ 2 · (degree 5) ⊕ (degree 3) ⊕ (degree 3)'`
(dimension `20`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z3_nontrivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H3 V) (ω : ℂ) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hρ : ∀ k (hk : a3 ^ k ∈ H3), ρ.character ⟨a3 ^ k, hk⟩ = ω ^ k) :
    (Ind H3 ρ).character = comb ![0, 1, 2, 1, 1] := by
  have hs : ω + ω ^ 2 = -1 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)
    linear_combination this
  refine eq_comb_of_table _ _ (ind_Z3_values ρ ω hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi, hs] <;> ring

end Z3

end A5Induced

end UndergradKB.RepresentationTheory
