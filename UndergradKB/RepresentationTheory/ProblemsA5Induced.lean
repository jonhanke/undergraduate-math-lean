import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.CharacterTableA5

/-! # Problem 4.34: representations of `A5` induced from subgroups

For the subgroups `Z2`, `Z3`, `Z5`, `Z2 × Z2` and `A4` of `A5 = alternatingGroup (Fin 5)` and each irreducible
character of the subgroup, we decompose the induced representation (Mathlib's `coind`, `Ind` in
`Induced.lean`) into irreducible characters of `A5`.  The statements are about the character of
`Ind H ρ` for any complex representation `ρ` of `H` with the given character; by
`nonempty_equiv_iff_character_eq_of_charZero` this is the isomorphism class of the induced representation.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

theorem card_conj_eq : ∀ g y : A5,
    (Finset.univ.filter fun x : A5 => x * g * x⁻¹ = y).card =
      if cls y = cls g then 60 / cnt (cls g) else 0 := by
  decide +kernel

theorem sum_conj (g : A5) (f : A5 → ℂ) :
    ∑ x : A5, f (x * g * x⁻¹) =
      ∑ y : A5, (if cls y = cls g then ((60 / cnt (cls g) : ℕ) : ℂ) else 0) * f y := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : A5 => x * g * x⁻¹) (fun x => f (x * g * x⁻¹))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f y) (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, card_conj_eq, nsmul_eq_mul]
  split_ifs <;> simp

/-- The subgroup of elements `y` with `lvl y ≠ s`, given closure properties. -/
def lvlSub {q : ℕ} (lvl : A5 → Fin q) (s : Fin q) (h1 : lvl 1 ≠ s)
    (hmul : ∀ a b : A5, lvl a ≠ s → lvl b ≠ s → lvl (a * b) ≠ s)
    (hinv : ∀ a : A5, lvl a ≠ s → lvl a⁻¹ ≠ s) : Subgroup A5 where
  carrier := {y | lvl y ≠ s}
  mul_mem' := fun {a b} ha hb => hmul a b ha hb
  one_mem' := h1
  inv_mem' := fun {a} ha => hinv a ha

theorem card_lvlSub {q : ℕ} (lvl : A5 → Fin q) (s : Fin q) (h1 hmul hinv) :
    Nat.card (lvlSub lvl s h1 hmul hinv) = (Finset.univ.filter fun y => lvl y ≠ s).card := by
  classical
  rw [show Nat.card (lvlSub lvl s h1 hmul hinv) = Nat.card {y : A5 // lvl y ≠ s} from
    Nat.card_congr (Equiv.refl _), Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem ind_char_core {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] {q : ℕ}
    (lvl : A5 → Fin q) (s : Fin q) (H : Subgroup A5) (hH : ∀ y, y ∈ H ↔ lvl y ≠ s)
    (ρ : Representation ℂ H V) (w : Fin q → ℂ) (hs : w s = 0)
    (hρ : ∀ y (hy : y ∈ H), ρ.character ⟨y, hy⟩ = w (lvl y))
    (n : Fin 5 → Fin q → ℕ)
    (hn : ∀ c j, ((Finset.univ.filter fun y => cls y = c).filter fun y => lvl y = j).card = n c j)
    (g : A5) :
    (Ind H ρ).character g = (Nat.card H : ℂ)⁻¹ * ((60 / cnt (cls g) : ℕ) : ℂ) *
      ∑ j, (n (cls g) j : ℂ) * w j := by
  classical
  have : Fintype (RCosets H) := Fintype.ofFinite _
  have : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [character_Ind_averaged, invOf_eq_inv]
  have hce : ∀ y, charExt H ρ y = w (lvl y) := by
    intro y
    by_cases hy : y ∈ H
    · rw [charExt_of_mem H ρ hy, hρ y hy]
    · rw [charExt_of_not_mem H ρ hy]
      have : lvl y = s := by
        by_contra h
        exact hy ((hH y).2 h)
      rw [this, hs]
  simp_rw [hce]
  rw [sum_conj g (fun y => w (lvl y))]
  have : ∑ y : A5, (if cls y = cls g then (((60 / cnt (cls g) : ℕ)) : ℂ) else 0) * w (lvl y)
      = ((60 / cnt (cls g) : ℕ) : ℂ) * ∑ j, (n (cls g) j : ℂ) * w j := by
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum,
      ← Finset.sum_fiberwise (Finset.univ.filter fun y => cls y = cls g) lvl (fun y => w (lvl y))]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => w j) (fun y hy => by rw [(Finset.mem_filter.1 hy).2]),
      Finset.sum_const, hn, nsmul_eq_mul]
  rw [this]
  ring

/-! ### Cyclic subgroups -/

/-- The exponent `k < m` with `y = a ^ k`, or `m` if there is none. -/
def cycLvl (a : A5) (m : ℕ) (y : A5) : Fin (m + 1) :=
  ⟨(List.range m).findIdx fun k => decide (a ^ k = y), Nat.lt_succ_of_le (by
    simpa using List.findIdx_le_length (p := fun k => decide (a ^ k = y)) (xs := List.range m))⟩

/-- The weights `j ↦ ω ^ j` for `j < m`, and `0` for `j = m`. -/
noncomputable def cycW (m : ℕ) (ω : ℂ) : Fin (m + 1) → ℂ := fun j => if (j : ℕ) < m then ω ^ (j : ℕ) else 0

theorem ind_cyclic {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (a : A5) (m : ℕ) (H : Subgroup A5) (hH : ∀ y, y ∈ H ↔ cycLvl a m y ≠ Fin.last m)
    (hspec : ∀ y, cycLvl a m y ≠ Fin.last m → y = a ^ (cycLvl a m y : ℕ))
    (ρ : Representation ℂ H V) (ω : ℂ) (hρ : ∀ k (hk : a ^ k ∈ H), ρ.character ⟨a ^ k, hk⟩ = ω ^ k)
    (n : Fin 5 → Fin (m + 1) → ℕ)
    (hn : ∀ c j, ((Finset.univ.filter fun y => cls y = c).filter fun y => cycLvl a m y = j).card = n c j)
    (g : A5) :
    (Ind H ρ).character g = (Nat.card H : ℂ)⁻¹ * ((60 / cnt (cls g) : ℕ) : ℂ) *
      ∑ j, (n (cls g) j : ℂ) * cycW m ω j := by
  refine ind_char_core (cycLvl a m) (Fin.last m) H hH ρ (cycW m ω) (by simp [cycW]) ?_ n hn g
  intro y hy
  have hne := (hH y).1 hy
  have e : (⟨y, hy⟩ : H) = ⟨a ^ (cycLvl a m y : ℕ), (hspec y hne) ▸ hy⟩ := Subtype.ext (hspec y hne)
  rw [e, hρ, cycW, if_pos (Fin.val_lt_last hne)]

/-- The class function `∑ m_i χ_i` for the five irreducible characters `χ_i` of `A5` (trivial, standard of
degree 4, degree 5, and the two of degree 3), with multiplicities `m = (m₀, …, m₄)`. -/
noncomputable def comb (m : Fin 5 → ℕ) : A5 → ℂ := fun g =>
  (m 0 : ℂ) * a5Triv g + (m 1 : ℂ) * a5Std g + (m 2 : ℂ) * a5Five g + (m 3 : ℂ) * a5ThreeP g +
    (m 4 : ℂ) * a5ThreeM g

theorem eq_comb_of_table (f : A5 → ℂ) (T : Fin 5 → ℂ) (hf : ∀ g, f g = T (cls g)) (m : Fin 5 → ℕ)
    (h : ∀ c, T c = (m 0 : ℂ) * tabTriv c + (m 1 : ℂ) * tabStd c + (m 2 : ℂ) * tabFive c +
      (m 3 : ℂ) * tabP c + (m 4 : ℂ) * tabM c) : f = comb m := by
  funext g
  rw [hf, h]
  rfl

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
