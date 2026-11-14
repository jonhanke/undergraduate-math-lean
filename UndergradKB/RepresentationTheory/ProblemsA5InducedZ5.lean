import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 4.34: representations of `A5` induced from `Z5`

Part of the decomposition of induced representations of `A5 = alternatingGroup (Fin 5)` (see
`ProblemsA5Induced.lean` for the overview); the statements are about the character of `Ind H ρ` for any
complex representation `ρ` of `H` with the given character.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-! ### `Z5` -/

section Z5

/-- The subgroup `Z5 = ⟨(0 1 2 3 4)⟩`. -/
def H5' : Subgroup A5 := lvlSub (cycLvl r5 5) (Fin.last 5) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem hH5 : ∀ y, y ∈ H5' ↔ cycLvl r5 5 y ≠ Fin.last 5 := fun _ => Iff.rfl

theorem card_H5' : Nat.card H5' = 5 := by
  rw [H5', card_lvlSub]; decide +kernel

def n5 : Fin 5 → Fin 6 → ℕ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 15], ![0, 0, 0, 0, 0, 20], ![0, 1, 0, 0, 1, 10],
    ![0, 0, 1, 1, 0, 10]]

theorem ind_Z5_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H5' V) (ω : ℂ) (hρ : ∀ k (hk : r5 ^ k ∈ H5'), ρ.character ⟨r5 ^ k, hk⟩ = ω ^ k)
    (g : A5) : (Ind H5' ρ).character g = ![12, 0, 0, ω + ω ^ 4, ω ^ 2 + ω ^ 3] (cls g) := by
  rw [ind_cyclic r5 5 H5' hH5 (by decide +kernel) ρ ω hρ n5 (by decide +kernel) g, card_H5']
  generalize cls g = c
  fin_cases c <;> simp [n5, cycW, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)

/-- **Problem 4.34(c)**: the representation induced from the trivial representation of
`Z5 = ⟨(0 1 2 3 4)⟩` is `1 ⊕ (degree 5) ⊕ (degree 3) ⊕ (degree 3)'` (dimension `12`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z5_trivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H5' V) (hρ : ∀ k (hk : r5 ^ k ∈ H5'), ρ.character ⟨r5 ^ k, hk⟩ = (1 : ℂ) ^ k) :
    (Ind H5' ρ).character = comb ![1, 0, 1, 1, 1] := by
  refine eq_comb_of_table _ _ (ind_Z5_values ρ 1 hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

/-- **Problem 4.34(c)**: for a nontrivial character `r5 ^ k ↦ ω ^ k` (`ω ^ 5 = 1`, `ω ≠ 1`) of `Z5`, the induced
representation is the sum of the standard (degree 4), the degree 5 and exactly one of the two degree 3 irreducible
representations (dimension `12`); which one depends on whether `ω + ω⁴ = φ - 1` or `-φ`, so the characters
`ω` and `ω²` give the two different ones (`tab3_cases`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_Z5_nontrivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ H5' V) (ω : ℂ) (h5 : ω ^ 5 = 1) (h1 : ω ≠ 1)
    (hρ : ∀ k (hk : r5 ^ k ∈ H5'), ρ.character ⟨r5 ^ k, hk⟩ = ω ^ k) :
    (Ind H5' ρ).character = comb ![0, 1, 1, 1, 0] ∨ (Ind H5' ρ).character = comb ![0, 1, 1, 0, 1] := by
  have e1 : (ω + ω ^ 4) + (ω ^ 2 + ω ^ 3) + 1 = 0 := by linear_combination geom_five h5 h1
  have key : ∀ c, ![12, 0, 0, ω + ω ^ 4, ω ^ 2 + ω ^ 3] c = tabStd c + tabFive c + tab3 ω c := by
    intro c
    fin_cases c <;> simp [tab3, tabStd, tabFive] <;> ring
  rcases tab3_cases ω h5 h1 with ⟨hA, -⟩ | ⟨hA, -⟩
  · left
    refine eq_comb_of_table _ _ (ind_Z5_values ρ ω hρ) _ fun c => ?_
    rw [key c, hA]
    simp [tabTriv, tabM]
  · right
    refine eq_comb_of_table _ _ (ind_Z5_values ρ ω hρ) _ fun c => ?_
    rw [key c, hA]
    simp [tabTriv, tabP]

end Z5

end A5Induced

end UndergradKB.RepresentationTheory
