import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 4.34: representations of `A5` induced from the Klein four group `Z2 × Z2`

Part of the decomposition of induced representations of `A5 = alternatingGroup (Fin 5)` (see
`ProblemsA5Induced.lean` for the overview); the statements are about the character of `Ind H ρ` for any
complex representation `ρ` of `H` with the given character.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-! ### `Z2 × Z2` -/

section V4

open Equiv in
/-- The double transposition `(0 2)(1 3)`. -/
def s2 : A5 := ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

open Equiv in
/-- The double transposition `(0 3)(1 2)`. -/
def s3 : A5 := ⟨swap 0 3 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

/-- The double transposition `(0 1)(2 3)`. -/
def s1 : A5 := classRep 1

/-- Labels the elements `1, s1, s2, s3` of the Klein four group by `0, 1, 2, 3`, and everything else by `4`. -/
def lvlV : A5 → Fin 5 := fun y =>
  if y = 1 then 0 else if y = s1 then 1 else if y = s2 then 2 else if y = s3 then 3 else 4

/-- The Klein four subgroup `Z2 × Z2 = {1, (0 1)(2 3), (0 2)(1 3), (0 3)(1 2)}` of `A5`. -/
def HV : Subgroup A5 := lvlSub lvlV 4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem card_HV : Nat.card HV = 4 := by
  rw [HV, card_lvlSub]; decide +kernel

theorem lvlV_cases : ∀ y, lvlV y ≠ 4 → y = 1 ∨ y = s1 ∨ y = s2 ∨ y = s3 := by decide +kernel

theorem lvlV_vals : lvlV 1 = 0 ∧ lvlV s1 = 1 ∧ lvlV s2 = 2 ∧ lvlV s3 = 3 := by decide +kernel

theorem s_ne : s1 ≠ 1 ∧ s2 ≠ 1 ∧ s3 ≠ 1 ∧ s2 ≠ s1 ∧ s3 ≠ s1 ∧ s3 ≠ s2 := by decide +kernel

def nV : Fin 5 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 1, 1, 12], ![0, 0, 0, 0, 20], ![0, 0, 0, 0, 12], ![0, 0, 0, 0, 12]]

theorem ind_V4_values {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HV V) (e1 e2 e3 : ℂ)
    (hρ : ∀ y (hy : y ∈ HV), ρ.character ⟨y, hy⟩ =
      if y = 1 then 1 else if y = s1 then e1 else if y = s2 then e2 else e3) (g : A5) :
    (Ind HV ρ).character g = ![15, e1 + e2 + e3, 0, 0, 0] (cls g) := by
  obtain ⟨v0, v1, v2, v3⟩ := lvlV_vals
  obtain ⟨n1, n2, n3, n21, n31, n32⟩ := s_ne
  rw [ind_char_core lvlV 4 HV (fun _ => Iff.rfl) ρ (![1, e1, e2, e3, 0] : Fin 5 → ℂ) (by simp) ?_ nV
    (by decide +kernel) g, card_HV]
  · generalize cls g = c
    fin_cases c <;> simp [nV, cnt, Fin.sum_univ_succ] <;> (try ring_nf) <;> (try simp)
  · intro y hy
    rcases lvlV_cases y hy with rfl | rfl | rfl | rfl
    · simp [hρ, v0]
    · simp [hρ, v1, n1]
    · simp [hρ, v2, n2, n21]
    · simp [hρ, v3, n3, n31, n32]

/-- **Problem 4.34(e)**: the representation of `A5` induced from the trivial representation of the Klein four
subgroup `Z2 × Z2` is `1 ⊕ (degree 4) ⊕ 2 · (degree 5)` (dimension `15`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_V4_trivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HV V)
    (hρ : ∀ y (hy : y ∈ HV), ρ.character ⟨y, hy⟩ = 1) :
    (Ind HV ρ).character = comb ![1, 1, 2, 0, 0] := by
  refine eq_comb_of_table _ _ (ind_V4_values ρ 1 1 1 (fun y hy => by simp [hρ])) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> norm_num

/-- **Problem 4.34(e)**: for each of the three nontrivial characters of `Z2 × Z2` (values `±1`, equal to `1` on
exactly one of the three involutions `s1, s2, s3` and `-1` on the other two), the induced representation is
`(degree 4) ⊕ (degree 5) ⊕ (degree 3) ⊕ (degree 3)'` (dimension `15`). -/
@[kb "etingof2011" "Problem 4.34, p. 57"]
theorem ind_V4_nontrivial {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ HV V) (e1 e2 e3 : ℂ)
    (he : (e1 = 1 ∧ e2 = -1 ∧ e3 = -1) ∨ (e1 = -1 ∧ e2 = 1 ∧ e3 = -1) ∨ (e1 = -1 ∧ e2 = -1 ∧ e3 = 1))
    (hρ : ∀ y (hy : y ∈ HV), ρ.character ⟨y, hy⟩ =
      if y = 1 then 1 else if y = s1 then e1 else if y = s2 then e2 else e3) :
    (Ind HV ρ).character = comb ![0, 1, 1, 1, 1] := by
  have hs : e1 + e2 + e3 = -1 := by rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
  refine eq_comb_of_table _ _ (ind_V4_values ρ e1 e2 e3 hρ) _ fun c => ?_
  fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi, hs] <;> ring

end V4

end A5Induced

end UndergradKB.RepresentationTheory
