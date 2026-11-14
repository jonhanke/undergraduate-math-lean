import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Enumeration of discrete unbounded-above sets of reals

An infinite set of reals with only finitely many elements below each bound is enumerated by a
strictly increasing sequence tending to `+∞`.
-/

namespace UndergradKB.DifferentialEquations

open Set Filter

theorem exists_strictMono_enum {E : Set ℝ} (hinf : E.Infinite) (hfin : ∀ R : ℝ, (E ∩ Set.Iic R).Finite) :
    ∃ e : ℕ → ℝ, StrictMono e ∧ Set.range e = E ∧ Filter.Tendsto e Filter.atTop Filter.atTop := by
  have hmin : ∀ S : Set ℝ, S ⊆ E → S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
    intro S hS ⟨s0, hs0⟩
    have hT : (S ∩ Iic s0).Finite := (hfin s0).subset (fun x hx => ⟨hS hx.1, hx.2⟩)
    obtain ⟨a, ha, hmin⟩ := Set.exists_min_image (S ∩ Iic s0) id hT ⟨s0, hs0, Set.mem_Iic.2 le_rfl⟩
    refine ⟨a, ha.1, fun x hx => ?_⟩
    by_cases h : x ≤ s0
    · exact hmin x ⟨hx, h⟩
    · exact ha.2.trans (not_le.1 h).le
  have h0 : ∃ m ∈ E, ∀ x ∈ E, m ≤ x := hmin E subset_rfl hinf.nonempty
  have hg : ∀ y : ℝ, ∃ m, m ∈ E ∧ y < m ∧ ∀ x ∈ E, y < x → m ≤ x := by
    intro y
    have hne : ({x | x ∈ E ∧ y < x} : Set ℝ).Nonempty := by
      by_contra hne
      refine hinf ((hfin y).subset fun x hx => ⟨hx, not_lt.1 fun h => hne ⟨x, hx, h⟩⟩)
    obtain ⟨m, hm, hmm⟩ := hmin {x | x ∈ E ∧ y < x} (fun x hx => hx.1) hne
    exact ⟨m, hm.1, hm.2, fun x hx hyx => hmm x ⟨hx, hyx⟩⟩
  choose g hgE hgy hgmin using hg
  obtain ⟨m0, hm0E, hm0⟩ := h0
  let e : ℕ → ℝ := fun n => Nat.rec m0 (fun _ y => g y) n
  have heS : ∀ n, e (n + 1) = g (e n) := fun n => rfl
  have heE : ∀ n, e n ∈ E := by
    intro n
    induction n with
    | zero => exact hm0E
    | succ n _ => rw [heS]; exact hgE _
  have hsm : StrictMono e := strictMono_nat_of_lt_succ fun n => by rw [heS]; exact hgy _
  refine ⟨e, hsm, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨n, rfl⟩; exact heE n
    · intro x hx
      by_contra hxn
      have hlt : ∀ n, e n < x := by
        intro n
        induction n with
        | zero => exact lt_of_le_of_ne (hm0 x hx) (fun h => hxn ⟨0, h⟩)
        | succ n ih =>
          rw [heS]
          exact lt_of_le_of_ne (hgmin _ x hx ih) (fun h => hxn ⟨n + 1, by rw [heS]; exact h⟩)
      have : (Set.range e).Finite :=
        (hfin x).subset (by rintro _ ⟨n, rfl⟩; exact ⟨heE n, (hlt n).le⟩)
      exact (Set.infinite_range_of_injective hsm.injective) this
  · rw [Filter.tendsto_atTop_atTop]
    intro R
    have hf : {n | e n ≤ R}.Finite :=
      ((hfin R).preimage (hsm.injective.injOn (s := e ⁻¹' (E ∩ Iic R)))).subset
        (fun n hn => ⟨heE n, hn⟩)
    obtain ⟨N, hN⟩ := Set.Finite.bddAbove hf
    refine ⟨N + 1, fun a ha => ?_⟩
    by_contra h
    have := hN (show a ∈ {n | e n ≤ R} from (not_le.1 h).le)
    omega

end UndergradKB.DifferentialEquations
