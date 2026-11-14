import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 4.34: representations of `A5` induced from `A4`

Part of the decomposition of induced representations of `A5 = alternatingGroup (Fin 5)` (see
`ProblemsA5Induced.lean` for the overview); the statements are about the character of `Ind H ρ` for any
complex representation `ρ` of `H` with the given character.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-! ### `A4` -/

section A4

/-- The three-cycle `(0 1 2)`, used to label the cosets of the Klein four group in `A4`. -/
def c0 : A5 := classRep 2

/-- For `y ∈ A4 = {y | y 4 = 4}`: `0` if `y` lies in the Klein four subgroup `V = {y | y² = 1}` of `A4`, `1` if
`y ∈ c0 V`, `2` if `y ∈ c0² V`; and `3` if `y ∉ A4`.  The linear characters of `A4` are `y ↦ ω ^ lvlLin y`
with `ω ^ 3 = 1`. -/
def lvlLin : A5 → Fin 4 := fun y =>
  if (y : Equiv.Perm (Fin 5)) 4 ≠ 4 then 3 else if y * y = 1 then 0
  else if (y * c0⁻¹) * (y * c0⁻¹) = 1 then 1 else 2

/-- The subgroup `A4 = {y ∈ A5 | y 4 = 4}` of `A5` (the stabilizer of the point `4`). -/
def HA : Subgroup A5 := lvlSub lvlLin 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem card_HA : Nat.card HA = 12 := by
  rw [HA, card_lvlSub]; decide +kernel

def nL : Fin 5 → Fin 4 → ℕ :=
  ![![1, 0, 0, 0], ![3, 0, 0, 12], ![0, 4, 4, 12], ![0, 0, 0, 12], ![0, 0, 0, 12]]

theorem ind_A4_lin_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HA V) (ω : ℂ)
    (hρ : ∀ y (hy : y ∈ HA), ρ.character ⟨y, hy⟩ = ω ^ (lvlLin y : ℕ)) (g : A5) :
    (Ind HA ρ).character g = ![5, 1, ω + ω ^ 2, 0, 0] (cls g) := by
  rw [ind_char_core lvlLin 3 HA (fun _ => Iff.rfl) ρ (cycW 3 ω) (by simp [cycW]) ?_ nL
    (by decide +kernel) g, card_HA]
  · generalize cls g = c
    fin_cases c <;> simp [nL, cycW, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)
  · intro y hy
    rw [hρ y hy, cycW, if_pos (Fin.val_lt_last hy)]

/-- **Problem 4.34(d)**: the representation induced from the trivial representation of `A4` is
`1 ⊕ (degree 4)` (the permutation representation on `5` points, dimension `5`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_A4_trivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HA V) (hρ : ∀ y (hy : y ∈ HA), ρ.character ⟨y, hy⟩ = 1) :
    (Ind HA ρ).character = comb ![1, 1, 0, 0, 0] := by
  refine eq_comb_of_table _ _ (ind_A4_lin_values ρ 1 (fun y hy => by simp [hρ]) ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> norm_num

/-- **Problem 4.34(d)**: the representation induced from a nontrivial linear character `y ↦ ω ^ lvlLin y`
(`ω ^ 3 = 1`, `ω ≠ 1`) of `A4` is the irreducible representation of degree `5`. -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_A4_linear {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HA V) (ω : ℂ) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (hρ : ∀ y (hy : y ∈ HA), ρ.character ⟨y, hy⟩ = ω ^ (lvlLin y : ℕ)) :
    (Ind HA ρ).character = comb ![0, 0, 1, 0, 0] := by
  have hs : ω + ω ^ 2 = -1 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h3
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)
    linear_combination this
  refine eq_comb_of_table _ _ (ind_A4_lin_values ρ ω hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi, hs] <;> norm_num

/-- Labels the elements of `A4`: `0` for `1`, `1` for the other elements of the Klein four group, `2` for the
three-cycles; and `3` for elements outside `A4`. -/
def lvl3d : A5 → Fin 4 := fun y =>
  if (y : Equiv.Perm (Fin 5)) 4 ≠ 4 then 3 else if y = 1 then 0 else if y * y = 1 then 1 else 2

def n3d : Fin 5 → Fin 4 → ℕ :=
  ![![1, 0, 0, 0], ![0, 3, 0, 12], ![0, 0, 8, 12], ![0, 0, 0, 12], ![0, 0, 0, 12]]

theorem hH3d : ∀ y, y ∈ HA ↔ lvl3d y ≠ 3 := by
  intro y
  change lvlLin y ≠ 3 ↔ lvl3d y ≠ 3
  revert y
  decide +kernel

theorem ind_A4_three_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HA V)
    (hρ : ∀ y (hy : y ∈ HA), ρ.character ⟨y, hy⟩ = if y = 1 then 3 else if y * y = 1 then -1 else 0)
    (g : A5) : (Ind HA ρ).character g = ![15, -1, 0, 0, 0] (cls g) := by
  rw [ind_char_core lvl3d 3 HA hH3d ρ (![3, -1, 0, 0] : Fin 4 → ℂ) (by simp) ?_ n3d
    (by decide +kernel) g, card_HA]
  · generalize cls g = c
    fin_cases c <;> simp [n3d, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)
  · intro y hy
    have hne : lvl3d y ≠ 3 := (hH3d y).1 hy
    rw [hρ y hy]
    unfold lvl3d at hne ⊢
    by_cases h4 : (y : Equiv.Perm (Fin 5)) 4 ≠ 4
    · simp [h4] at hne
    · by_cases h1 : y = 1 <;> by_cases h2 : y * y = 1 <;> simp [h4, h1, h2]

/-- **Problem 4.34(d)**: the representation induced from the three-dimensional irreducible representation of
`A4` (character `3, -1, 0` on `1`, the double transpositions, and the three-cycles) is
`(degree 4) ⊕ (degree 5) ⊕ (degree 3) ⊕ (degree 3)'` (dimension `15`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_A4_threeDim {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HA V)
    (hρ : ∀ y (hy : y ∈ HA), ρ.character ⟨y, hy⟩ = if y = 1 then 3 else if y * y = 1 then -1 else 0) :
    (Ind HA ρ).character = comb ![0, 1, 1, 1, 1] := by
  refine eq_comb_of_table _ _ (ind_A4_three_values ρ hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

end A4

end A5Induced

end UndergradKB.RepresentationTheory
