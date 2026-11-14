import Mathlib.NumberTheory.Dioph
import Mathlib.Data.Int.ModEq
import UndergradKB.Common

/-!
# Foundations, DPRM: elementary facts about Mathlib's polynomials `Poly`

Ingredients of Davis's bounded universal quantifier theorem:

* `poly_exists_support`: a polynomial depends on finitely many variables;
* `dioph_fintype_witness`: a Diophantine set can be written with finitely many unknowns;
* `poly_modEq`: polynomials respect congruences;
* `poly_majorant`: a polynomial is bounded in absolute value by a polynomial in bounds for its variables;
* `dioph_forall_fintype`: Diophantine sets are closed under finite intersections.
-/

namespace UndergradKB.Foundations.DPRM

open Dioph Int

local infixr:67 " ::ₒ " => Option.elim'
local infixr:65 " ⊗ " => Sum.elim

/-- A polynomial depends on finitely many variables. -/
theorem poly_exists_support {γ : Type*} (p : Poly γ) :
    ∃ s : Finset γ, ∀ w w' : γ → ℕ, (∀ i ∈ s, w i = w' i) → p w = p w' := by
  classical
  induction p using Poly.induction with
  | H1 i => exact ⟨{i}, fun w w' h => by simpa using h i (by simp)⟩
  | H2 n => exact ⟨∅, fun _ _ _ => rfl⟩
  | H3 f g hf hg =>
    obtain ⟨s, hs⟩ := hf
    obtain ⟨t, ht⟩ := hg
    refine ⟨s ∪ t, fun w w' h => ?_⟩
    simp only [Poly.sub_apply]
    rw [hs w w' fun i hi => h i (Finset.mem_union_left _ hi),
      ht w w' fun i hi => h i (Finset.mem_union_right _ hi)]
  | H4 f g hf hg =>
    obtain ⟨s, hs⟩ := hf
    obtain ⟨t, ht⟩ := hg
    refine ⟨s ∪ t, fun w w' h => ?_⟩
    simp only [Poly.mul_apply]
    rw [hs w w' fun i hi => h i (Finset.mem_union_left _ hi),
      ht w w' fun i hi => h i (Finset.mem_union_right _ hi)]

/-- A Diophantine set can be defined with finitely many unknowns. -/
theorem dioph_fintype_witness {α : Type} {S : Set (α → ℕ)} (d : Dioph S) :
    ∃ (β : Type) (_ : Fintype β) (p : Poly (α ⊕ β)), ∀ v, v ∈ S ↔ ∃ t, p (v ⊗ t) = 0 := by
  classical
  obtain ⟨β, p, hp⟩ := d
  obtain ⟨s, hs⟩ := poly_exists_support p
  let β' : Type := {b : β // Sum.inr b ∈ s}
  let g : α ⊕ β → α ⊕ Option β' := fun i =>
    Sum.elim Sum.inl (fun b => if h : Sum.inr b ∈ s then Sum.inr (some ⟨b, h⟩) else Sum.inr none) i
  have : Fintype β' := Fintype.subtype (s.preimage Sum.inr Sum.inr_injective.injOn)
    (fun b => by simp)
  refine ⟨Option β', inferInstance, p.map g, fun v => (hp v).trans ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht⟩
    refine ⟨fun o => o.elim 0 fun b => t b.1, ?_⟩
    rw [Poly.map_apply, ← ht]
    refine hs _ _ fun i hi => ?_
    rcases i with a | b
    · rfl
    · simp [g, hi]
  · rintro ⟨t, ht⟩
    refine ⟨fun b => if h : Sum.inr b ∈ s then t (some ⟨b, h⟩) else 0, ?_⟩
    rw [Poly.map_apply] at ht
    rw [← ht]
    refine hs _ _ fun i hi => ?_
    rcases i with a | b
    · rfl
    · simp [g, hi]

/-- Polynomials respect congruences. -/
theorem poly_modEq {γ : Type*} (p : Poly γ) (n : ℤ) (w w' : γ → ℕ)
    (h : ∀ i, (w i : ℤ) ≡ w' i [ZMOD n]) : p w ≡ p w' [ZMOD n] := by
  induction p using Poly.induction with
  | H1 i => simpa using h i
  | H2 c => exact Int.ModEq.refl _
  | H3 f g hf hg => simpa only [Poly.sub_apply] using hf.sub hg
  | H4 f g hf hg => simpa only [Poly.mul_apply] using hf.mul hg

/-- A polynomial is bounded, in absolute value, by a polynomial in bounds for its variables. -/
theorem poly_majorant {γ δ : Type*} (p : Poly γ) (B : γ → Poly δ) :
    ∃ M : Poly δ, ∀ (w : γ → ℕ) (z : δ → ℕ), (∀ i, (w i : ℤ) ≤ B i z) → |p w| ≤ M z := by
  induction p using Poly.induction with
  | H1 i => exact ⟨B i, fun w z h => by simpa using h i⟩
  | H2 c => exact ⟨Poly.const |c|, fun _ _ _ => by simp⟩
  | H3 f g hf hg =>
    obtain ⟨M, hM⟩ := hf
    obtain ⟨N, hN⟩ := hg
    refine ⟨M + N, fun w z h => ?_⟩
    simp only [Poly.sub_apply, Poly.add_apply]
    exact (abs_sub _ _).trans (add_le_add (hM w z h) (hN w z h))
  | H4 f g hf hg =>
    obtain ⟨M, hM⟩ := hf
    obtain ⟨N, hN⟩ := hg
    refine ⟨M * N, fun w z h => ?_⟩
    simp only [Poly.mul_apply, abs_mul]
    exact mul_le_mul (hM w z h) (hN w z h) (abs_nonneg _) ((abs_nonneg _).trans (hM w z h))

/-- Diophantine sets are closed under finite intersections. -/
theorem dioph_forall_fintype {α ι : Type} [Fintype ι] {S : ι → Set (α → ℕ)}
    (h : ∀ i, Dioph (S i)) : Dioph {v | ∀ i, v ∈ S i} := by
  classical
  have := DiophList.forall ((Finset.univ : Finset ι).toList.map S)
    (List.forall_iff_forall_mem.2 fun T hT => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hT
      exact h i)
  refine Dioph.ext this fun v => ?_
  simp [List.forall_iff_forall_mem]

end UndergradKB.Foundations.DPRM
