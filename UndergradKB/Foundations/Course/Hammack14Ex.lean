import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Int
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 14, worked examples
-/

namespace UndergradKB.Foundations.Course

/-- Hammack Example 14.1: negation is a bijection from `{0, ..., 5}` onto `{-5, ..., 0}`, so the two sets have
the same cardinality. -/
@[kb "hammack2018" "Example 14.1, p. 282"]
theorem hammack_ex_14_1_negation_bijection :
    Set.BijOn (fun n : ℤ => -n) (Set.Icc 0 5) (Set.Icc (-5) 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨h1, h2⟩ := hn
    exact ⟨by simp only; omega, by simp only; omega⟩
  · intro a _ b _ h
    simpa using h
  · intro b hb
    obtain ⟨h1, h2⟩ := hb
    exact ⟨-b, ⟨by omega, by omega⟩, by simp⟩

/-- Hammack Example 14.5: `n ↦ 2n` is a bijection from `ℤ` to the even integers, so the even integers have
cardinality `ℵ₀`. -/
@[kb "hammack2018" "Example 14.5, p. 287"]
theorem hammack_ex_14_5_even_integers_countable :
    Cardinal.mk {x : ℤ // Even x} = Cardinal.aleph0 := by
  have e : ℤ ≃ {x : ℤ // Even x} :=
    Equiv.ofBijective (fun n => (⟨2 * n, ⟨n, by ring⟩⟩ : {x : ℤ // Even x}))
      ⟨fun a b h => by
        have := congrArg Subtype.val h
        simp only at this
        omega,
       fun ⟨x, k, hk⟩ => ⟨k, by apply Subtype.ext; simp only; omega⟩⟩
  rw [← Cardinal.mk_congr e]
  exact Cardinal.mk_int

end UndergradKB.Foundations.Course
