import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Involutions
open Equiv Finset
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The finset of involutions (permutations `σ` with `σ * σ = 1`) of a finite type. -/
def invs (α : Type*) [Fintype α] [DecidableEq α] : Finset (Perm α) :=
  univ.filter fun σ => σ * σ = 1

/-- The number of involutions of a finite type. -/
def invCount (α : Type*) [Fintype α] [DecidableEq α] : ℕ := (invs α).card

lemma mem_invs {σ : Perm α} : σ ∈ invs α ↔ σ * σ = 1 := by simp [invs]

lemma permCongr_inv (e : α ≃ β) {σ : Perm α} (h : σ * σ = 1) :
    e.permCongr σ * e.permCongr σ = 1 := by
  refine Equiv.ext fun x => ?_
  have := congrArg (fun f : Perm α => f (e.symm x)) h
  simpa [Equiv.permCongr_apply] using congrArg e this

lemma invCount_congr (e : α ≃ β) : invCount α = invCount β := by
  unfold invCount
  refine Finset.card_nbij' (fun σ => e.permCongr σ) (fun σ => e.symm.permCongr σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_coe, mem_invs] at hσ ⊢
    exact permCongr_inv e hσ
  · intro σ hσ
    simp only [mem_coe, mem_invs] at hσ ⊢
    exact permCongr_inv e.symm hσ
  · intro σ _
    ext x; simp [Equiv.permCongr_apply]
  · intro σ _
    ext x; simp [Equiv.permCongr_apply]

lemma invCount_congr_card (h : Fintype.card α = Fintype.card β) : invCount α = invCount β :=
  invCount_congr (Fintype.equivOfCardEq h)

/-- Involutions of `Option α` given by a pair `(a, τ)`: the value at `none` and the rest. -/
lemma inv_none_iff (τ : Perm α) :
    (Perm.decomposeOption.symm ((none : Option α), τ)) * (Perm.decomposeOption.symm ((none : Option α), τ)) = 1
      ↔ τ * τ = 1 := by
  simp only [Perm.decomposeOption_symm_apply, swap_self]
  constructor
  · intro h; refine Equiv.ext fun c => ?_
    have := congrArg (fun f : Perm (Option α) => f (some c)) h
    simpa using this
  · intro h; refine Equiv.ext fun x => ?_
    cases x with
    | none => simp
    | some c =>
      have := congrArg (fun f : Perm α => f c) h
      simpa using this

lemma inv_some_iff (b : α) (τ : Perm α) :
    (Perm.decomposeOption.symm (some b, τ)) * (Perm.decomposeOption.symm (some b, τ)) = 1
      ↔ τ b = b ∧ τ * τ = 1 := by
  simp only [Perm.decomposeOption_symm_apply]
  constructor
  · intro h
    have h0 := congrArg (fun f : Perm (Option α) => f none) h
    have hb : τ b = b := by
      by_contra hne
      simp [swap_apply_def, hne] at h0
    refine ⟨hb, ?_⟩
    refine Equiv.ext fun c => ?_
    have h1 := congrArg (fun f : Perm (Option α) => f (some c)) h
    by_cases hc : τ c = b
    · have : c = b := τ.injective (hc.trans hb.symm)
      subst this
      simp [hb]
    · by_cases hc2 : τ (τ c) = b
      · exact absurd (τ.injective (hc2.trans hb.symm)) hc
      · simpa [swap_apply_def, hc, hc2] using h1
  · rintro ⟨hb, h⟩
    refine Equiv.ext fun x => ?_
    cases x with
    | none => simp [swap_apply_def, hb]
    | some c =>
      have h1 := congrArg (fun f : Perm α => f c) h
      simp only [Perm.coe_mul, Function.comp_apply, Perm.one_apply] at h1
      by_cases hc : τ c = b
      · have : c = b := τ.injective (hc.trans hb.symm)
        subst this
        simp [swap_apply_def, hb]
      · have hc2 : τ (τ c) ≠ b := fun h' => hc (τ.injective (h'.trans hb.symm))
        have hcb : c ≠ b := fun e => hc (e ▸ hb)
        simp [swap_apply_def, hc, hcb, h1]

/-- Involutions of `α` fixing `b` correspond to involutions of `{x // x ≠ b}`. -/
lemma fix_count (b : α) :
    ((invs α).filter (fun τ => τ b = b)).card = invCount {x : α // x ≠ b} := by
  unfold invCount
  symm
  refine Finset.card_bij (fun f _ => Perm.ofSubtype f) ?_ ?_ ?_
  · intro f hf
    rw [mem_invs] at hf
    simp only [mem_filter, mem_invs]
    refine ⟨?_, ?_⟩
    · rw [← map_mul, hf, map_one]
    · exact Perm.ofSubtype_apply_of_not_mem f (by simp)
  · intro f _ g _ h
    exact Perm.ofSubtype_injective h
  · intro τ hτ
    simp only [mem_filter, mem_invs] at hτ
    obtain ⟨h1, h2⟩ := hτ
    have hp : ∀ x, (τ x ≠ b) ↔ (x ≠ b) := by
      intro x
      constructor
      · intro hx e; subst e; exact hx h2
      · intro hx e; exact hx (τ.injective (e.trans h2.symm))
    have hq : ∀ x, τ x ≠ x → x ≠ b := by
      intro x hx e; subst e; exact hx h2
    have hs := Perm.ofSubtype_subtypePerm (p := fun x => x ≠ b) (f := τ) hp hq
    refine ⟨τ.subtypePerm hp, ?_, hs⟩
    rw [mem_invs]
    apply Perm.ofSubtype_injective (p := fun x => x ≠ b)
    rw [map_mul, hs, map_one]
    exact h1

/-- Recursion for the number of involutions of `Option α`. -/
lemma invCount_option :
    invCount (Option α) = invCount α + ∑ b : α, ((invs α).filter fun τ => τ b = b).card := by
  classical
  have h1 : invCount (Option α) = (univ.filter fun p : Option α × Perm α =>
      match p.1 with
      | none => p.2 * p.2 = 1
      | some b => p.2 b = b ∧ p.2 * p.2 = 1).card := by
    unfold invCount
    refine Finset.card_equiv Perm.decomposeOption ?_
    intro σ
    obtain ⟨⟨a, τ⟩, hσ⟩ : ∃ p, σ = Perm.decomposeOption.symm p :=
      ⟨Perm.decomposeOption σ, by simp⟩
    subst hσ
    rw [mem_invs]
    simp only [Equiv.apply_symm_apply, mem_filter, mem_univ, true_and]
    cases a with
    | none => exact inv_none_iff τ
    | some b => exact inv_some_iff b τ
  rw [h1, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_option]
  congr 1
  · rw [invCount, invs, Finset.card_filter]
    exact Finset.sum_congr rfl fun τ _ => by congr
  · refine sum_congr rfl fun b _ => ?_
    simp only
    rw [invs, Finset.filter_filter, Finset.card_filter]
    simp [and_comm]

end

/-- The number of involutions of an `n`-element set (permutations `σ` of `Fin n` with
`σ * σ = 1`). -/
def involutionNumber (n : ℕ) : ℕ := invCount (Fin n)

/-- CO-494 (recurrence part). The number `y(n)` of involutions of an `n`-set satisfies
`y(n) = y(n-1) + (n-1) y(n-2)` (here indexed as `y(n+2) = y(n+1) + (n+1) y(n)`). The claim that
this recurrence has no hypergeometric solution is not formalized. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.3, p. 165"]
theorem involutionNumber_rec (n : ℕ) :
    involutionNumber (n + 2) = involutionNumber (n + 1) + (n + 1) * involutionNumber n := by
  unfold involutionNumber
  rw [invCount_congr (finSuccEquiv (n + 1)), invCount_option]
  congr 1
  have h : ∀ b : Fin (n + 1),
      ((invs (Fin (n + 1))).filter fun τ => τ b = b).card = invCount (Fin n) := by
    intro b
    rw [fix_count]
    refine invCount_congr_card ?_
    simp [Fintype.card_subtype_compl]
  simp [h]

end UndergradKB.Combinatorics.AeqB.Involutions
