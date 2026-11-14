import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Filter
import Mathlib.Algebra.Order.Group.Int
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 11, worked examples (wave 4)

The four equivalence relations `R₁, ..., R₄` of Figure 11.2 on `A = {-1, 1, 2, 3, 4}`, as finite sets of pairs.
-/

namespace UndergradKB.Foundations.Course

/-- The base set `A = {-1, 1, 2, 3, 4}` of Figure 11.2. -/
def hammackFig112A : Finset ℤ := {-1, 1, 2, 3, 4}

/-- Figure 11.2, `R₁`: equality on `A`. -/
def hammackFig112R1 : Finset (ℤ × ℤ) := {(-1, -1), (1, 1), (2, 2), (3, 3), (4, 4)}

/-- Figure 11.2, `R₂`: same parity. -/
def hammackFig112R2 : Finset (ℤ × ℤ) :=
  {(-1, -1), (1, 1), (2, 2), (3, 3), (4, 4), (-1, 1), (1, -1), (-1, 3), (3, -1), (1, 3), (3, 1), (2, 4), (4, 2)}

/-- Figure 11.2, `R₃`: same sign. -/
def hammackFig112R3 : Finset (ℤ × ℤ) :=
  {(-1, -1), (1, 1), (2, 2), (3, 3), (4, 4), (1, 2), (2, 1), (1, 3), (3, 1), (1, 4), (4, 1), (3, 4), (4, 3),
    (2, 3), (3, 2), (2, 4), (4, 2)}

/-- Figure 11.2, `R₄`: same parity and same sign. -/
def hammackFig112R4 : Finset (ℤ × ℤ) :=
  {(-1, -1), (1, 1), (2, 2), (3, 3), (4, 4), (1, 3), (3, 1), (2, 4), (4, 2)}

/-- The equivalence class `[a]` of `a` in `A` under the pair set `R`. -/
def hammackClass (R : Finset (ℤ × ℤ)) (a : ℤ) : Finset ℤ :=
  hammackFig112A.filter (fun x => (x, a) ∈ R)

/-- `R` is reflexive, symmetric and transitive on `A`. -/
def hammackIsEquivOnA (R : Finset (ℤ × ℤ)) : Prop :=
  (∀ a ∈ hammackFig112A, (a, a) ∈ R) ∧ (∀ a ∈ hammackFig112A, ∀ b ∈ hammackFig112A, (a, b) ∈ R → (b, a) ∈ R) ∧
    (∀ a ∈ hammackFig112A, ∀ b ∈ hammackFig112A, ∀ c ∈ hammackFig112A, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R)

instance (R : Finset (ℤ × ℤ)) : Decidable (hammackIsEquivOnA R) := by
  unfold hammackIsEquivOnA; infer_instance

/-- The classes of `R` form a partition of `A`: they are nonempty, any two are equal or disjoint, and they cover `A`. -/
def hammackClassesPartition (R : Finset (ℤ × ℤ)) : Prop :=
  (∀ a ∈ hammackFig112A, (hammackClass R a).Nonempty) ∧
    (∀ a ∈ hammackFig112A, ∀ b ∈ hammackFig112A, hammackClass R a = hammackClass R b ∨
      Disjoint (hammackClass R a) (hammackClass R b)) ∧
    hammackFig112A.biUnion (hammackClass R) = hammackFig112A

instance (R : Finset (ℤ × ℤ)) : Decidable (hammackClassesPartition R) := by
  unfold hammackClassesPartition; infer_instance

/-- Hammack Example 11.11: `R₄` (same parity and sign) is an equivalence relation on `A` with exactly three classes,
`[-1] = {-1}`, `[1] = [3] = {1, 3}` and `[2] = [4] = {2, 4}`. -/
@[kb "hammack2018" "Example 11.11, p. 223"]
theorem hammack_ex_11_11_R4_classes :
    hammackIsEquivOnA hammackFig112R4 ∧
    hammackClass hammackFig112R4 (-1) = {-1} ∧
    hammackClass hammackFig112R4 1 = {1, 3} ∧ hammackClass hammackFig112R4 3 = {1, 3} ∧
    hammackClass hammackFig112R4 2 = {2, 4} ∧ hammackClass hammackFig112R4 4 = {2, 4} ∧
    (hammackFig112A.image (hammackClass hammackFig112R4)).card = 3 := by
  decide +kernel

/-- Hammack Example 11.15: for each of `R₁, ..., R₄` of Figure 11.2 the equivalence classes form a partition of `A`;
the resulting partitions are `{{-1},{1},{2},{3},{4}}`, `{{-1,1,3},{2,4}}`, `{{-1},{1,2,3,4}}` and
`{{-1},{1,3},{2,4}}`. -/
@[kb "hammack2018" "Example 11.15, p. 228"]
theorem hammack_ex_11_15_classes_partition :
    (hammackIsEquivOnA hammackFig112R1 ∧ hammackClassesPartition hammackFig112R1 ∧
      hammackFig112A.image (hammackClass hammackFig112R1) = {{-1}, {1}, {2}, {3}, {4}}) ∧
    (hammackIsEquivOnA hammackFig112R2 ∧ hammackClassesPartition hammackFig112R2 ∧
      hammackFig112A.image (hammackClass hammackFig112R2) = {{-1, 1, 3}, {2, 4}}) ∧
    (hammackIsEquivOnA hammackFig112R3 ∧ hammackClassesPartition hammackFig112R3 ∧
      hammackFig112A.image (hammackClass hammackFig112R3) = {{-1}, {1, 2, 3, 4}}) ∧
    (hammackIsEquivOnA hammackFig112R4 ∧ hammackClassesPartition hammackFig112R4 ∧
      hammackFig112A.image (hammackClass hammackFig112R4) = {{-1}, {1, 3}, {2, 4}}) := by
  decide +kernel

end UndergradKB.Foundations.Course
