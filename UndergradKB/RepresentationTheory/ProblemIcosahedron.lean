import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.OrderOfElement
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.A5InducedCore

/-! # Problem 3.21: functions on the vertices, faces and edges of the icosahedron

The rotation group `A5` of the regular icosahedron permutes its `12` vertices, `20` faces and `30` edges, each
set transitively.  The book asks for the decomposition into irreducibles of the permutation representations on
the spaces of complex functions on these three sets.

We prove the decomposition for *every* transitive action of `A5 = alternatingGroup (Fin 5)` on a finite set `X`
with `12`, `20` or `30` elements; the vertex, face and edge sets of the icosahedron are such sets (this is the
fact the book recalls), and the answer depends only on these data.  The representation is Mathlib's permutation
representation `Representation.ofMulAction ℂ A5 X` on the free vector space `X →₀ ℂ`, which for finite `X` is
the space of complex functions on `X` (the basis vector of `x` is the indicator function of `x`).
Decompositions are stated as equalities of characters with integer combinations `comb m` of the five irreducible
characters (trivial, degree 4, degree 5, the two of degree 3); in characteristic zero the character determines
the representation up to isomorphism.

Method: the character of a permutation representation counts fixed points; for a transitive action with point
stabilizer `K`, `#fix(g) · |K| = #{a | a⁻¹ g a ∈ K}`, which is `60 / |class of g|` times the number of elements of
`K` in the class of `g`.  By orbit-stabilizer, `|K| = 60 / |X|` is the prime `5`, `3` or `2`, so `K` is cyclic and
its elements are counted class by class with `decide`.

Answers: vertices `1 ⊕ 5 ⊕ 3 ⊕ 3'`, faces `1 ⊕ 2 · 4 ⊕ 5 ⊕ 3 ⊕ 3'`, edges `1 ⊕ 2 · 4 ⊕ 3 · 5 ⊕ 3 ⊕ 3'`.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module A5Table A5Induced

namespace Icosahedron

variable {X : Type*} [MulAction A5 X] [Fintype X] [DecidableEq X]

/-- The elements of `A5` fixing `x0`, as a finite set (the point stabilizer). -/
def stabSet (x0 : X) : Finset A5 := Finset.univ.filter fun a => a • x0 = x0

/-- The points of `X` fixed by `g`. -/
def fixSet (X : Type*) [MulAction A5 X] [Fintype X] [DecidableEq X] (g : A5) : Finset X := Finset.univ.filter fun x => g • x = x

omit [Fintype X] in
theorem card_fiber (x0 : X) (b : A5) :
    (Finset.univ.filter fun a : A5 => a • x0 = b • x0).card = (stabSet x0).card := by
  refine Finset.card_equiv (Equiv.mulLeft b⁻¹) fun a => ?_
  simp [stabSet, mul_smul, inv_smul_eq_iff]

theorem card_univ_A5 : (Finset.univ : Finset A5).card = 60 := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_A5]

/-- Orbit-stabilizer for a transitive action: `|X| · |K| = 60`. -/
theorem card_mul_card_stab (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) :
    Fintype.card X * (stabSet x0).card = 60 := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset A5)) (t := (Finset.univ : Finset X))
    (f := fun a : A5 => a • x0) (fun _ _ => Finset.mem_univ _)
  rw [card_univ_A5] at this
  rw [this, Finset.sum_const_nat (m := (stabSet x0).card), Finset.card_univ]
  intro x _
  obtain ⟨b, rfl⟩ := htr x
  exact card_fiber x0 b

theorem card_fix_mul (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (g : A5) :
    (fixSet X g).card * (stabSet x0).card =
      (Finset.univ.filter fun a : A5 => g • a • x0 = a • x0).card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun a : A5 => g • a • x0 = a • x0)
    (f := fun a : A5 => a • x0) (t := fixSet X g)
    (fun a ha => by simpa [fixSet] using ha), Finset.sum_const_nat (m := (stabSet x0).card)]
  intro x hx
  obtain ⟨b, rfl⟩ := htr x
  rw [← card_fiber x0 b, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixSet] at hx ⊢
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [h]; exact hx, h⟩

theorem card_conj_eq' (g y : A5) :
    (Finset.univ.filter fun a : A5 => a⁻¹ * g * a = y).card =
      if cls y = cls g then 60 / cnt (cls g) else 0 := by
  rw [← card_conj_eq g y]
  refine Finset.card_equiv (Equiv.inv A5) fun a => ?_
  simp

/-- The fixed-point count of a transitive action, class by class. -/
theorem card_fix_mul_stab (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (g : A5) :
    (fixSet X g).card * (stabSet x0).card =
      60 / cnt (cls g) * ((stabSet x0).filter fun h => cls h = cls g).card := by
  rw [card_fix_mul x0 htr g]
  have e : (Finset.univ.filter fun a : A5 => g • a • x0 = a • x0) =
      Finset.univ.filter fun a : A5 => a⁻¹ * g * a ∈ stabSet x0 := by
    ext a
    simp [stabSet, mul_smul, inv_smul_eq_iff]
  rw [e, Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun a : A5 => a⁻¹ * g * a ∈ stabSet x0)
    (f := fun a : A5 => a⁻¹ * g * a) (t := stabSet x0)
    (fun a ha => (Finset.mem_filter.1 ha).2)]
  rw [Finset.sum_congr rfl (g := fun h => if cls h = cls g then 60 / cnt (cls g) else 0)]
  · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro h hh
    rw [Finset.filter_filter, ← card_conj_eq' g h]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h' => h'.2
    · intro h'
      exact ⟨h' ▸ hh, h'⟩

omit [Fintype X] in
/-- A stabilizer of prime order `p` consists of the powers of any of its non-identity elements, so its class
counts are those of the powers `h ^ k`, `k < p`. -/
theorem stab_cls_count (x0 : X) (p : ℕ) (hp : (stabSet x0).card = p) (hp1 : 1 < p)
    (T : Fin 5 → ℕ)
    (hT : ∀ h : A5, h ^ p = 1 → h ≠ 1 →
      ∀ c, (Finset.univ.filter fun k : Fin p => cls (h ^ (k : ℕ)) = c).card = T c)
    (hinj : ∀ h : A5, h ^ p = 1 → h ≠ 1 → Function.Injective fun k : Fin p => h ^ (k : ℕ)) (c : Fin 5) :
    ((stabSet x0).filter fun h => cls h = c).card = T c := by
  obtain ⟨h, hh, h1⟩ := Finset.exists_mem_ne (hp ▸ hp1 : 1 < (stabSet x0).card) 1
  have hK : ∀ a, a ∈ stabSet x0 ↔ a ∈ MulAction.stabilizer A5 x0 := by
    intro a; simp [stabSet]
  have hcard : Nat.card (MulAction.stabilizer A5 x0) = p := by
    rw [← hp, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => (hK a).symm)
  have hpow : h ^ p = 1 := by
    have := pow_card_eq_one' (G := MulAction.stabilizer A5 x0) (x := ⟨h, (hK h).1 hh⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  let e : Fin p ↪ A5 := ⟨fun k => h ^ (k : ℕ), hinj h hpow h1⟩
  have hsub : Finset.univ.map e ⊆ stabSet x0 := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 ha
    exact (hK _).2 (Subgroup.pow_mem _ ((hK h).1 hh) _)
  have heq : Finset.univ.map e = stabSet x0 :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hp])
  rw [← heq, Finset.filter_map, Finset.card_map]
  exact hT h hpow h1 c

theorem fix_eq_table (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (p : ℕ) (hX : Fintype.card X * p = 60)
    (hp1 : 1 < p) (T : Fin 5 → ℕ)
    (hT : ∀ h : A5, h ^ p = 1 → h ≠ 1 →
      ∀ c, (Finset.univ.filter fun k : Fin p => cls (h ^ (k : ℕ)) = c).card = T c)
    (hinj : ∀ h : A5, h ^ p = 1 → h ≠ 1 → Function.Injective fun k : Fin p => h ^ (k : ℕ)) (F : Fin 5 → ℕ)
    (hF : ∀ c, F c * p = 60 / cnt c * T c) (g : A5) :
    (fixSet X g).card = F (cls g) := by
  have hstab : (stabSet x0).card = p := by
    have h1 := card_mul_card_stab x0 htr
    have hpos : 0 < Fintype.card X := by
      rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
      · rw [h] at hX; omega
      · exact h
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hX.symm)
  have := card_fix_mul_stab x0 htr g
  rw [stab_cls_count x0 p hstab hp1 T hT hinj, hstab, ← hF] at this
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

theorem character_eq (g : A5) :
    (Representation.ofMulAction ℂ A5 X).character g = ((fixSet X g).card : ℂ) := by
  rw [character_ofMulAction]
  rfl

/-! ### Vertices: stabilizer of order `5` -/

theorem pow5_count : ∀ h : A5, h ^ 5 = 1 → h ≠ 1 →
    ∀ c, (Finset.univ.filter fun k : Fin 5 => cls (h ^ (k : ℕ)) = c).card = ![1, 0, 0, 2, 2] c := by
  decide +kernel

theorem pow5_inj : ∀ h : A5, h ^ 5 = 1 → h ≠ 1 → Function.Injective fun k : Fin 5 => h ^ (k : ℕ) := by
  decide +kernel

/-- **Problem 3.21(a)**: for a transitive action of `A5` on a set of `12` points (the vertices of the regular
icosahedron), the representation on the functions on the set is `1 ⊕ 5 ⊕ 3 ⊕ 3'`: the trivial, the
five-dimensional and both three-dimensional irreducible representations, each once. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem character_vertices (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (hX : Fintype.card X = 12) :
    (Representation.ofMulAction ℂ A5 X).character = comb ![1, 0, 1, 1, 1] := by
  refine eq_comb_of_table _ (fun c => ((![12, 0, 0, 2, 2] c : ℕ) : ℂ)) (fun g => ?_) _ fun c => ?_
  · rw [character_eq, fix_eq_table x0 htr 5 (by rw [hX]) (by norm_num) _ pow5_count pow5_inj
      ![12, 0, 0, 2, 2] (by decide) g]
  · fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

/-! ### Faces: stabilizer of order `3` -/

theorem pow3_count : ∀ h : A5, h ^ 3 = 1 → h ≠ 1 →
    ∀ c, (Finset.univ.filter fun k : Fin 3 => cls (h ^ (k : ℕ)) = c).card = ![1, 0, 2, 0, 0] c := by
  decide +kernel

theorem pow3_inj : ∀ h : A5, h ^ 3 = 1 → h ≠ 1 → Function.Injective fun k : Fin 3 => h ^ (k : ℕ) := by
  decide +kernel

/-- **Problem 3.21(b)**: for a transitive action of `A5` on a set of `20` points (the faces of the regular
icosahedron), the representation on the functions on the set is `1 ⊕ 2 · 4 ⊕ 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem character_faces (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (hX : Fintype.card X = 20) :
    (Representation.ofMulAction ℂ A5 X).character = comb ![1, 2, 1, 1, 1] := by
  refine eq_comb_of_table _ (fun c => ((![20, 0, 2, 0, 0] c : ℕ) : ℂ)) (fun g => ?_) _ fun c => ?_
  · rw [character_eq, fix_eq_table x0 htr 3 (by rw [hX]) (by norm_num) _ pow3_count pow3_inj
      ![20, 0, 2, 0, 0] (by decide) g]
  · fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

/-! ### Edges: stabilizer of order `2` -/

theorem pow2_count : ∀ h : A5, h ^ 2 = 1 → h ≠ 1 →
    ∀ c, (Finset.univ.filter fun k : Fin 2 => cls (h ^ (k : ℕ)) = c).card = ![1, 1, 0, 0, 0] c := by
  decide +kernel

theorem pow2_inj : ∀ h : A5, h ^ 2 = 1 → h ≠ 1 → Function.Injective fun k : Fin 2 => h ^ (k : ℕ) := by
  decide +kernel

/-- **Problem 3.21(b)**: for a transitive action of `A5` on a set of `30` points (the edges of the regular
icosahedron), the representation on the functions on the set is `1 ⊕ 2 · 4 ⊕ 3 · 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem character_edges (x0 : X) (htr : ∀ x : X, ∃ b : A5, b • x0 = x) (hX : Fintype.card X = 30) :
    (Representation.ofMulAction ℂ A5 X).character = comb ![1, 2, 3, 1, 1] := by
  refine eq_comb_of_table _ (fun c => ((![30, 2, 0, 0, 0] c : ℕ) : ℂ)) (fun g => ?_) _ fun c => ?_
  · rw [character_eq, fix_eq_table x0 htr 2 (by rw [hX]) (by norm_num) _ pow2_count pow2_inj
      ![30, 2, 0, 0, 0] (by decide) g]
  · fin_cases c <;> simp [tabTriv, tabStd, tabFive, tabP, tabM, phi] <;> ring

end Icosahedron

end UndergradKB.RepresentationTheory
