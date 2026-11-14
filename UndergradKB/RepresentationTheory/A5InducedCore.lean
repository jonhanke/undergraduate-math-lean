import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.CharacterTableA5

/-! # Representations of `A5` induced from subgroups: common core

Shared tools for Problem 4.34 (and Problem 3.21): counting conjugators (`card_conj_eq`, `sum_conj`), subgroups
given by a labelling function (`lvlSub`), the character of an induced representation from a labelling
(`ind_char_core`, `ind_cyclic`), and integer combinations of the five irreducible characters of `A5` (`comb`).
Split from `ProblemsA5Induced.lean` (wave 5) so that each subgroup is a separate, smaller module.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table

namespace A5Induced

/-- The centralizer of `g` has `60 / |class of g|` elements. -/
theorem card_centralizer_eq : ∀ g : A5,
    (Finset.univ.filter fun x : A5 => x * g = g * x).card = 60 / cnt (cls g) := by
  decide +kernel

/-- Every element is conjugate to the representative of its class. -/
theorem exists_conj_rep : ∀ g : A5, ∃ x : A5, x * g * x⁻¹ = classRep (cls g) := by
  decide +kernel

/-- The number of `x` with `x g x⁻¹ = y` when `y` is in the class of `g`. -/
theorem card_conj_of_cls_eq (g y : A5) (h : cls y = cls g) :
    (Finset.univ.filter fun x : A5 => x * g * x⁻¹ = y).card = 60 / cnt (cls g) := by
  obtain ⟨x1, hx1⟩ := exists_conj_rep g
  obtain ⟨x2, hx2⟩ := exists_conj_rep y
  set z := x2⁻¹ * x1 with hz
  have hzg : z * g * z⁻¹ = y := by
    rw [h] at hx2
    rw [hz, mul_inv_rev, inv_inv]
    calc x2⁻¹ * x1 * g * (x1⁻¹ * x2) = x2⁻¹ * (x1 * g * x1⁻¹) * x2 := by group
      _ = x2⁻¹ * (x2 * y * x2⁻¹) * x2 := by rw [hx1, hx2]
      _ = y := by group
  rw [← card_centralizer_eq g]
  refine Finset.card_equiv (Equiv.mulLeft z⁻¹) fun x => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft]
  rw [← hzg]
  constructor
  · intro hx
    calc z⁻¹ * x * g = z⁻¹ * (x * g * x⁻¹) * x := by group
      _ = z⁻¹ * (z * g * z⁻¹) * x := by rw [hx]
      _ = g * (z⁻¹ * x) := by group
  · intro hx
    calc x * g * x⁻¹ = z * (z⁻¹ * x * g) * x⁻¹ := by group
      _ = z * (g * (z⁻¹ * x)) * x⁻¹ := by rw [hx]
      _ = z * g * z⁻¹ := by group

theorem cnt_mul_div : ∀ c : Fin 5, cnt c * (60 / cnt c) = 60 := by decide

/-- The number of `x` with `x g x⁻¹ = y` (wave 5: proved from the facts above instead of one enumeration of all
`60³` triples, which needed 24 GB): the fibres over the class of `g` already account for all `60` elements. -/
theorem card_conj_eq (g y : A5) :
    (Finset.univ.filter fun x : A5 => x * g * x⁻¹ = y).card =
      if cls y = cls g then 60 / cnt (cls g) else 0 := by
  split_ifs with h
  · exact card_conj_of_cls_eq g y h
  · have htot : ∑ y' : A5, (Finset.univ.filter fun x : A5 => x * g * x⁻¹ = y').card = 60 := by
      rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, card_A5]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y' => cls y' = cls g)] at htot
    have hin : ∑ y' ∈ Finset.univ.filter (fun y' => cls y' = cls g),
        (Finset.univ.filter fun x : A5 => x * g * x⁻¹ = y').card = 60 := by
      rw [Finset.sum_congr rfl (g := fun _ => 60 / cnt (cls g))
        (fun y' hy' => card_conj_of_cls_eq g y' (Finset.mem_filter.1 hy').2),
        Finset.sum_const, card_cls, smul_eq_mul, cnt_mul_div]
    rw [hin, add_eq_left, Finset.sum_eq_zero_iff] at htot
    exact htot y (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

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

end A5Induced

end UndergradKB.RepresentationTheory
