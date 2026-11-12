import Mathlib.Basic.Rel
import Mathlib.Order.Setoid.Partition
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import UndergradKB.Common

/-!
# Course layer: Hammack, Book of Proof, Chapter 11 (relations)

Thin theorems in the book's terms for the "Relations and functions" rows of the Foundations checklist that are
already in Mathlib and belong to Hammack's chapter on relations.
-/

namespace UndergradKB.Foundations.Course

/-- FO-062. A relation from `A` to `B` is a subset of `A × B`. -/
@[kb "hammack2018" "Def 11.1, p. 214", kb "hammack2018" "Def 11.7, p. 233", kb "levin2025" "Def 2.6.3, p. 186"]
theorem hammack_def_11_1_relation_is_subset (A B : Type*) : SetRel A B = Set (A × B) :=
  rfl

/-- FO-063. Reflexive, symmetric and transitive, spelled out as quantified statements. -/
@[kb "hammack2018" "Def 11.2, p. 217", kb "levin2025" "Def 2.6.10, p. 190"]
theorem hammack_def_11_2_refl_symm_trans {A : Type*} (R : A → A → Prop) :
    (Std.Refl R ↔ ∀ x, R x x) ∧ (Std.Symm R ↔ ∀ x y, R x y → R y x) ∧
      (IsTrans A R ↔ ∀ x y z, R x y → R y z → R x z) :=
  ⟨⟨fun h x => h.refl x, fun h => ⟨h⟩⟩, ⟨fun h x y => h.symm x y, fun h => ⟨h⟩⟩,
    ⟨fun h x y z => h.trans x y z, fun h => ⟨h⟩⟩⟩

/-- FO-064. Congruence mod `n` is reflexive, symmetric and transitive on the integers, and
`a ≡ b (mod n)` means `n ∣ b - a`. -/
@[kb "hammack2018" "Prop §11.2, p. 220", kb "levin2025" "Example 2.6.16, p. 193"]
theorem hammack_s11_2_modEq_equivalence (n : ℤ) :
    (∀ a : ℤ, a ≡ a [ZMOD n]) ∧ (∀ a b : ℤ, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]) ∧
      (∀ a b c : ℤ, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n]) ∧
      (∀ a b : ℤ, a ≡ b [ZMOD n] ↔ n ∣ b - a) :=
  ⟨fun a => Int.ModEq.refl a, fun _ _ h => h.symm, fun _ _ _ h₁ h₂ => h₁.trans h₂,
    fun _ _ => Int.modEq_iff_dvd⟩

/-- FO-065. An equivalence relation is one that is reflexive, symmetric and transitive. -/
@[kb "hammack2018" "Def 11.3, p. 222", kb "levin2025" "Def 2.6.14, p. 193"]
theorem hammack_def_11_3_equivalence {A : Type*} (R : A → A → Prop) :
    Equivalence R ↔ (∀ x, R x x) ∧ (∀ x y, R x y → R y x) ∧ (∀ x y z, R x y → R y z → R x z) :=
  ⟨fun h => ⟨h.refl, fun _ _ => h.symm, fun _ _ _ => h.trans⟩,
    fun h => ⟨h.1, fun {x y} => h.2.1 x y, fun {x y z} => h.2.2 x y z⟩⟩

/-- FO-066. The equivalence class of `a` is the set of elements related to `a`, and it is one of the classes
of the relation. -/
@[kb "hammack2018" "Def 11.4, p. 223", kb "levin2025" "Def 2.6.18, p. 194"]
theorem hammack_def_11_4_class_mem {A : Type*} (r : Setoid A) (a : A) :
    {x | r x a} ∈ r.classes :=
  Setoid.mem_classes r a

/-- FO-069. A partition has nonempty blocks that cover the set and are pairwise disjoint. -/
@[kb "hammack2018" "Def 11.5, p. 228", kb "levin2025" "Def 2.6.21, p. 196"]
theorem hammack_def_11_5_partition {A : Type*} (P : Set (Set A)) (h : Setoid.IsPartition P) :
    ∅ ∉ P ∧ ⋃₀ P = Set.univ ∧ P.PairwiseDisjoint id :=
  ⟨h.1, h.sUnion_eq_univ, h.pairwiseDisjoint⟩

/-- FO-070. The equivalence classes of an equivalence relation form a partition of the set. -/
@[kb "hammack2018" "Thm 11.2, p. 228", kb "levin2025" "Thm 2.6.24, p. 197"]
theorem hammack_thm_11_2_classes_partition {A : Type*} (r : Setoid A) :
    Setoid.IsPartition r.classes :=
  Setoid.isPartition_classes r

/-- FO-071. A partition gives an equivalence relation ("same block") whose classes are the blocks, and the
two constructions undo each other. -/
@[kb "hammack2018" "Prop §11.4, p. 229", kb "levin2025" "Thm 2.6.24, p. 197"]
theorem hammack_s11_4_partition_equivalence {A : Type*} :
    (∀ (P : Set (Set A)) (h : Setoid.IsPartition P), (Setoid.mkClasses P h.2).classes = P) ∧
      (∀ r : Setoid A, Setoid.mkClasses r.classes Setoid.classes_eqv_classes = r) :=
  ⟨fun P h => Setoid.classes_mkClasses P h, fun r => Setoid.mkClasses_classes r⟩

/-- FO-072. `ℤ_n` has `n` elements, and two integers give the same class iff they are congruent mod `n`;
the arithmetic of classes is computed on representatives. -/
@[kb "hammack2018" "Def 11.6, p. 231"]
theorem hammack_def_11_6_zmod (n : ℕ) [NeZero n] (a b : ℤ) :
    Fintype.card (ZMod n) = n ∧ (((a : ZMod n) = (b : ZMod n)) ↔ a ≡ b [ZMOD n]) ∧
      ((a + b : ℤ) : ZMod n) = (a : ZMod n) + (b : ZMod n) ∧
      ((a * b : ℤ) : ZMod n) = (a : ZMod n) * (b : ZMod n) :=
  ⟨ZMod.card n, ZMod.intCast_eq_intCast_iff a b n, Int.cast_add a b, Int.cast_mul a b⟩

/-- FO-073. Addition and multiplication of congruence classes are well defined. -/
@[kb "hammack2018" "Prop §11.5, p. 232"]
theorem hammack_s11_5_modEq_add_mul {n a a' b b' : ℤ} (ha : a ≡ a' [ZMOD n]) (hb : b ≡ b' [ZMOD n]) :
    a + b ≡ a' + b' [ZMOD n] ∧ a * b ≡ a' * b' [ZMOD n] :=
  ⟨ha.add hb, ha.mul hb⟩

end UndergradKB.Foundations.Course
