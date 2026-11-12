import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UndergradKB.Common

/-! # Logic: quantifiers, equivalences and rules of inference

Results of Hammack, *Book of Proof*, Chapter 2, and Levin, *Discrete Mathematics*, Section 1.3, that Mathlib has
only implicitly (as core logic or a one-line term) or not at all: the order of quantifiers, distributing `∀`
over `∨`, the rules of inference, the validity of deduction rules checked by truth tables, and `∀ → ∃` on a
nonempty domain. Statements are the books' propositional and predicate forms; a "deduction rule is valid" is
read as: for every truth assignment of the letters, the premises imply the conclusion.
-/

namespace UndergradKB.Foundations

/-! ## Biconditional (FO-041) -/

/-- FO-041. `P ⇔ Q` means `(P ⇒ Q) ∧ (Q ⇒ P)`, and also `(P ∧ Q) ∨ (¬P ∧ ¬Q)`. -/
@[kb "hammack2018" "Def §2.4, p. 58", kb "levin2025" "Sec 1.2.3, p. 58"]
theorem iff_iff_imp_and_imp_and_or (P Q : Prop) :
    ((P ↔ Q) ↔ (P → Q) ∧ (Q → P)) ∧ ((P ↔ Q) ↔ (P ∧ Q) ∨ (¬P ∧ ¬Q)) :=
  ⟨iff_def, iff_iff_and_or_not_and_not⟩

/-! ## Order of quantifiers (FO-052) -/

/-- FO-052, valid direction: `∃ y ∀ x, P(x,y)` implies `∀ x ∃ y, P(x,y)`. -/
@[kb "levin2025" "Example 1.3.14, p. 74"]
theorem forall_exists_of_exists_forall {α β : Sort*} (P : α → β → Prop) :
    (∃ y, ∀ x, P x y) → ∀ x, ∃ y, P x y :=
  fun ⟨y, hy⟩ x => ⟨y, hy x⟩

/-- FO-052, Hammack's counterexample: every real number has a real cube root, but no real number is a cube root of
every real number. -/
@[kb "hammack2018" "Example 2.7, p. 67"]
theorem cube_root_quantifier_order :
    (∀ x : ℝ, ∃ y : ℝ, y ^ 3 = x) ∧ ¬ ∃ y : ℝ, ∀ x : ℝ, y ^ 3 = x := by
  refine ⟨fun x => ?_, fun ⟨y, hy⟩ => ?_⟩
  · rcases le_total 0 x with hx | hx
    · refine ⟨x ^ ((1 : ℝ) / 3), ?_⟩
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      norm_num
    · refine ⟨-(-x) ^ ((1 : ℝ) / 3), ?_⟩
      have h0 : 0 ≤ -x := by linarith
      rw [neg_pow, ← Real.rpow_natCast ((-x) ^ ((1 : ℝ) / 3)), ← Real.rpow_mul h0]
      norm_num
  · have h0 := hy 0
    have h1 := hy 1
    rw [h0] at h1
    exact zero_ne_one h1

/-- FO-052, Levin's counterexample: every natural number has a larger one, but no natural number is larger than
all of them. So `∀ x ∃ y` does not imply `∃ y ∀ x`. -/
@[kb "levin2025" "Example 1.3.14, p. 74"]
theorem lt_quantifier_order :
    (∀ x : ℕ, ∃ y : ℕ, x < y) ∧ ¬ ∃ y : ℕ, ∀ x : ℕ, x < y :=
  ⟨fun x => ⟨x + 1, Nat.lt_succ_self x⟩, fun ⟨y, hy⟩ => lt_irrefl y (hy y)⟩

/-! ## Distributing `∀` over `∨` (FO-053) -/

/-- FO-053, valid direction: if everything is a `P`-thing or everything is a `Q`-thing, then everything is a
`P`-thing or a `Q`-thing. -/
@[kb "levin2025" "Example 1.3.13, p. 73"]
theorem forall_or_of_or_forall {α : Sort*} (P Q : α → Prop) :
    ((∀ x, P x) ∨ (∀ x, Q x)) → ∀ x, P x ∨ Q x := by
  rintro (h | h) x
  · exact Or.inl (h x)
  · exact Or.inr (h x)

/-- FO-053, Levin's counterexample: every integer is even or odd, but neither are all integers even nor are all
integers odd. -/
@[kb "levin2025" "Example 1.3.13, p. 73"]
theorem even_or_odd_not_distrib :
    (∀ n : ℤ, Even n ∨ Odd n) ∧ ¬ ((∀ n : ℤ, Even n) ∨ (∀ n : ℤ, Odd n)) := by
  refine ⟨Int.even_or_odd, ?_⟩
  rintro (h | h)
  · exact Int.not_even_one (h 1)
  · exact Int.not_odd_zero (h 0)

/-! ## Rules of inference (FO-058) -/

/-- FO-058. The rules of inference: modus ponens, modus tollens, disjunctive syllogism (elimination),
conjunction introduction and elimination, and disjunction introduction. -/
@[kb "hammack2018" "Sec 2.11, p. 75", kb "levin2025" "Sec 1.3.5, p. 75"]
theorem rules_of_inference (P Q : Prop) :
    (P → (P → Q) → Q) ∧ ((P → Q) → ¬Q → ¬P) ∧ (P ∨ Q → ¬P → Q) ∧ (P → Q → P ∧ Q) ∧
      (P ∧ Q → P) ∧ (P → P ∨ Q) :=
  ⟨fun p h => h p, fun h => mt h, fun h np => h.resolve_left np, And.intro, And.left, Or.inl⟩

/-! ## Deduction rules checked by truth tables (FO-059) -/

/-- FO-059 (Levin Example 1.3.15). From `P → Q` and `¬P → Q` conclude `Q`: valid for every truth assignment. -/
@[kb "levin2025" "Example 1.3.15, p. 75"]
theorem deduction_cases (P Q : Bool) (h₁ : P = true → Q = true) (h₂ : P = false → Q = true) : Q = true := by
  cases P
  · exact h₂ rfl
  · exact h₁ rfl

/-- FO-059 (Levin Example 1.3.16, valid part). From `P → R`, `Q → R` and `P ∨ Q` conclude `R` (proof by cases). -/
@[kb "levin2025" "Sec 1.3.5, p. 76"]
theorem deduction_or_elim (P Q R : Prop) (h₁ : P → R) (h₂ : Q → R) (h : P ∨ Q) : R :=
  h.elim h₁ h₂

/-- FO-059 (Levin Example 1.3.16). From `P → R`, `Q → R` and `R` one cannot conclude `P ∨ Q`: the truth assignment
`P, Q` false and `R` true makes every premise true and the conclusion false. -/
@[kb "levin2025" "Example 1.3.16, p. 76"]
theorem deduction_converse_or_invalid :
    ¬ ∀ P Q R : Bool, (P = true → R = true) → (Q = true → R = true) → R = true →
      (P = true ∨ Q = true) := by
  intro h
  simpa using h false false true

/-! ## Universal implies existential on a nonempty domain (FO-060) -/

/-- FO-060. If everything in a nonempty domain has property `P`, then something has property `P`. -/
@[kb "levin2025" "Sec 1.3.5, p. 77"]
theorem exists_of_forall {α : Sort*} [Nonempty α] (P : α → Prop) (h : ∀ x, P x) : ∃ x, P x :=
  let ⟨a⟩ := ‹Nonempty α›
  ⟨a, h a⟩

/-- FO-060. The nonemptiness of the domain is needed: over an empty domain every universal statement is true and
every existential statement false. -/
@[kb "levin2025" "Sec 1.3.5, p. 77"]
theorem forall_not_imp_exists_of_isEmpty {α : Sort*} [IsEmpty α] (P : α → Prop) :
    (∀ x, P x) ∧ ¬ ∃ x, P x :=
  ⟨fun x => isEmptyElim x, fun ⟨x, _⟩ => isEmptyElim x⟩

/-! ## Quantified statements and negation (FO-055, FO-144) -/

/-- FO-055. "For all `x ∈ X`, `Q(x)`" means "for all `x`, `x ∈ X ⇒ Q(x)`"; and "every `P`-thing is a `Q`-thing" is
`∀ x, P(x) ⇒ Q(x)`, the inclusion `{x | P x} ⊆ {x | Q x}`; dually "some `P`-thing is a `Q`-thing" is
`∃ x, P(x) ∧ Q(x)`. -/
@[kb "hammack2018" "Fact 2.2, p. 70", kb "levin2025" "Sec 1.1.3, p. 44"]
theorem bounded_quantifiers {α : Type*} (X : Set α) (P Q : α → Prop) :
    ((∀ x ∈ X, Q x) ↔ ∀ x, x ∈ X → Q x) ∧ ({x | P x} ⊆ {x | Q x} ↔ ∀ x, P x → Q x) ∧
      ((∃ x ∈ {x | P x}, Q x) ↔ ∃ x, P x ∧ Q x) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- FO-144. To disprove a statement prove its negation: the negation of `∀ x, P x` is `∃ x, ¬P x`, of `∃ x, P x` is
`∀ x, ¬P x`, and of `P ⇒ Q` is `P ∧ ¬Q`. -/
@[kb "hammack2018" "Prop §9.1, p. 187", kb "levin2025" "Ex 1.4.15, p. 92"]
theorem negation_rules {α : Sort*} (P : α → Prop) (A B : Prop) :
    (¬ (∀ x, P x) ↔ ∃ x, ¬ P x) ∧ (¬ (∃ x, P x) ↔ ∀ x, ¬ P x) ∧ (¬ (A → B) ↔ A ∧ ¬ B) :=
  ⟨not_forall, not_exists, Classical.not_imp⟩

end UndergradKB.Foundations
