import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Set.Countable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.WellFounded
import UndergradKB.Common.Attr

/-!
# Course layer: Morris, Appendix 1 (infinite sets)

Thin wrappers of Mathlib results in the terms of Morris, *Topology Without Tears*.
-/

open Cardinal Set
open scoped Cardinal Polynomial

namespace UndergradKB.Topology.Course

universe u

/-- Morris, Topology Without Tears, Definition A1.1.1 (TP-377). Two sets are equipotent (there is
a bijection between them) exactly when they have the same cardinal. -/
@[kb "morris2024" "Definition A1.1.1, p. 394"]
theorem morris_A1_1_1 (α β : Type u) : Nonempty (α ≃ β) ↔ #α = #β :=
  Cardinal.eq.symm

/-- Morris, Topology Without Tears, Proposition A1.1.2 (TP-378). Equipotence is reflexive,
symmetric and transitive. -/
@[kb "morris2024" "Proposition A1.1.2, p. 394"]
theorem morris_A1_1_2 :
    (∀ α : Type u, Nonempty (α ≃ α)) ∧ (∀ α β : Type u, Nonempty (α ≃ β) → Nonempty (β ≃ α)) ∧
      (∀ α β γ : Type u, Nonempty (α ≃ β) → Nonempty (β ≃ γ) → Nonempty (α ≃ γ)) :=
  ⟨fun _ => ⟨Equiv.refl _⟩, fun _ _ ⟨e⟩ => ⟨e.symm⟩, fun _ _ _ ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Morris, Topology Without Tears, Proposition A1.1.3 (TP-379). The initial segments `{1..n}`
and `{1..m}` are equipotent exactly when `n = m`. -/
@[kb "morris2024" "Proposition A1.1.3, p. 394"]
theorem morris_A1_1_3 (n m : ℕ) : Nonempty (Fin n ≃ Fin m) ↔ n = m :=
  Fin.equiv_iff_eq

/-- Morris, Topology Without Tears, Definition A1.1.4 (TP-380). A set is finite when it is
equipotent to some initial segment `{1..n}`, and infinite otherwise. -/
@[kb "morris2024" "Definition A1.1.4, p. 395"]
theorem morris_A1_1_4 (α : Type u) :
    (Finite α ↔ ∃ n : ℕ, Nonempty (α ≃ Fin n)) ∧ (Infinite α ↔ ¬ ∃ n : ℕ, Nonempty (α ≃ Fin n)) :=
  ⟨finite_iff_exists_equiv_fin, by rw [← finite_iff_exists_equiv_fin]; exact not_finite_iff_infinite.symm⟩

/-- Morris, Topology Without Tears, Definition A1.1.5 (TP-381). A set is countably infinite iff it
is equipotent to `ℕ`; it is countable iff finite or countably infinite; uncountable otherwise. -/
@[kb "morris2024" "Definition A1.1.5, p. 395"]
theorem morris_A1_1_5 (α : Type u) :
    (Nonempty (α ≃ ℕ) ↔ Countable α ∧ Infinite α) ∧ (Countable α ↔ Finite α ∨ Nonempty (α ≃ ℕ)) ∧
      (Uncountable α ↔ ¬ Countable α) := by
  refine ⟨?_, ?_, not_countable_iff.symm⟩
  · rw [← nonempty_denumerable_iff]
    exact ⟨fun ⟨e⟩ => ⟨Denumerable.mk' e⟩, fun ⟨d⟩ => ⟨d.eqv⟩⟩
  · constructor
    · intro h
      by_cases hf : Finite α
      · exact Or.inl hf
      · have : Infinite α := not_finite_iff_infinite.mp hf
        exact Or.inr ⟨(nonempty_denumerable α).some.eqv⟩
    · rintro (h | h)
      · infer_instance
      · obtain ⟨e⟩ := h
        exact e.injective.countable

/-- Morris, Topology Without Tears, Proposition A1.1.10 (TP-382). A set equipotent to a countable
set is countable. -/
@[kb "morris2024" "Proposition A1.1.10, p. 396"]
theorem morris_A1_1_10 {α β : Type u} [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.injective.countable

/-- Morris, Topology Without Tears, Proposition A1.1.11 (TP-383). Every subset of a countable set
is countable. -/
@[kb "morris2024" "Proposition A1.1.11, p. 397"]
theorem morris_A1_1_11 {α : Type u} {s t : Set α} (hs : s.Countable) (h : t ⊆ s) : t.Countable :=
  hs.mono h

/-- Morris, Topology Without Tears, Corollary A1.1.12 (TP-383). Every subset of `ℤ` is
countable. -/
@[kb "morris2024" "Corollary A1.1.12, p. 397"]
theorem morris_A1_1_12 (s : Set ℤ) : s.Countable :=
  s.to_countable

/-- Morris, Topology Without Tears, Proposition A1.1.15 (TP-384). A countable union of countable
sets is countable. -/
@[kb "morris2024" "Proposition A1.1.15, p. 398"]
theorem morris_A1_1_15 {α : Type u} (A : ℕ → Set α) (h : ∀ n, (A n).Countable) :
    (⋃ n, A n).Countable :=
  countable_iUnion h

/-- Morris, Topology Without Tears, Proposition A1.1.16 (TP-385). The product of two countable
sets is countable. -/
@[kb "morris2024" "Proposition A1.1.16, p. 398"]
theorem morris_A1_1_16 {α β : Type u} {s : Set α} {t : Set β} (hs : s.Countable)
    (ht : t.Countable) : (s ×ˢ t).Countable :=
  hs.prod ht

/-- Morris, Topology Without Tears, Corollary A1.1.17 (TP-385). A finite product of countable
sets is countable. -/
@[kb "morris2024" "Corollary A1.1.17, p. 398"]
theorem morris_A1_1_17 {α : Type u} (n : ℕ) (s : Fin n → Set α) (hs : ∀ i, (s i).Countable) :
    {f : Fin n → α | ∀ i, f i ∈ s i}.Countable :=
  countable_pi hs

/-- Morris, Topology Without Tears, Theorem A1.1.19 (TP-386). The rationals are countably
infinite. -/
@[kb "morris2024" "Theorem A1.1.19, p. 399"]
theorem morris_A1_1_19 : Countable ℚ ∧ Infinite ℚ ∧ Nonempty (ℚ ≃ ℕ) :=
  ⟨inferInstance, inferInstance, ⟨(nonempty_denumerable ℚ).some.eqv⟩⟩

/-- Morris, Topology Without Tears, Corollary A1.1.20 (TP-386). Every set of rationals is
countable. -/
@[kb "morris2024" "Corollary A1.1.20, p. 399"]
theorem morris_A1_1_20 (s : Set ℚ) : s.Countable :=
  s.to_countable

/-- Morris, Topology Without Tears, Definition A1.1.21 (TP-387). A real number is algebraic if it
is a root of a nonzero integer polynomial, and transcendental otherwise. -/
@[kb "morris2024" "Definition A1.1.21, p. 399"]
theorem morris_A1_1_21 (x : ℝ) :
    IsAlgebraic ℤ x ↔ ∃ p : ℤ[X], p ≠ 0 ∧ Polynomial.aeval x p = 0 :=
  Iff.rfl

/-- Morris, Topology Without Tears, Definition A1.1.21 (TP-387), transcendental part. -/
@[kb "morris2024" "Definition A1.1.21, p. 399"]
theorem morris_A1_1_21_b (x : ℝ) : Transcendental ℤ x ↔ ¬ IsAlgebraic ℤ x :=
  Iff.rfl

/-- Morris, Topology Without Tears, Theorem A1.1.26 (TP-388). The set of algebraic real numbers
is countably infinite. -/
@[kb "morris2024" "Theorem A1.1.26, p. 401"]
theorem morris_A1_1_26 :
    {x : ℝ | IsAlgebraic ℤ x}.Countable ∧ {x : ℝ | IsAlgebraic ℤ x}.Infinite := by
  refine ⟨Algebraic.countable ℤ ℝ, ?_⟩
  refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono ?_
  rintro _ ⟨n, rfl⟩
  exact isAlgebraic_natCast n

/-- Morris, Topology Without Tears, Corollary A1.1.27 (TP-388). Every set of algebraic numbers is
countable. -/
@[kb "morris2024" "Corollary A1.1.27, p. 401"]
theorem morris_A1_1_27 (s : Set ℝ) (h : ∀ x ∈ s, IsAlgebraic ℤ x) : s.Countable :=
  (Algebraic.countable ℤ ℝ).mono (fun x hx => h x hx)

/-- Morris, Topology Without Tears, Proposition A1.1.28 (TP-389). The image of a countable set
under a map is countable, and the domain of an injection into a countable set is countable. -/
@[kb "morris2024" "Proposition A1.1.28, p. 402"]
theorem morris_A1_1_28 {α β : Type u} (f : α → β) (s : Set α) (hs : s.Countable) :
    (f '' s).Countable :=
  hs.image f

/-- Morris, Topology Without Tears, Proposition A1.1.28 (TP-389), injective part. -/
@[kb "morris2024" "Proposition A1.1.28, p. 402"]
theorem morris_A1_1_28_b {α β : Type u} [Countable β] (f : α → β) (hf : Function.Injective f) :
    Countable α :=
  hf.countable

/-- Morris, Topology Without Tears, Proposition A1.1.29 (TP-390). The set of finite subsets of a
countable set is countable. -/
@[kb "morris2024" "Proposition A1.1.29, p. 402"]
theorem morris_A1_1_29 (α : Type u) [Countable α] : {s : Set α | s.Finite}.Countable :=
  Set.Countable.ofPred_finite

/-- Morris, Topology Without Tears, Theorem A1.1.31 (TP-392). Cantor: no map from `S` to its power
set is surjective. -/
@[kb "morris2024" "Theorem A1.1.31, p. 402"]
theorem morris_A1_1_31 {S : Type u} (f : S → Set S) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- Morris, Topology Without Tears, Theorem A1.2.6 (TP-392). Cantor, cardinal form:
`card S < card P(S)`. -/
@[kb "morris2024" "Theorem A1.2.6, p. 408"]
theorem morris_A1_2_6 (S : Type u) : #S < #(Set S) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

/-- Morris, Topology Without Tears, Lemma A1.1.32 (TP-393). Every set is equipotent to a subset of
its power set, via singletons. -/
@[kb "morris2024" "Lemma A1.1.32, p. 403"]
theorem morris_A1_1_32 (S : Type u) :
    Function.Injective (fun a : S => ({a} : Set S)) ∧ #S ≤ #(Set S) :=
  ⟨Set.singleton_injective, Cardinal.mk_le_of_injective Set.singleton_injective⟩

/-- Morris, Topology Without Tears, Lemma A1.1.34 (TP-395). The half-open unit interval is
uncountable. -/
@[kb "morris2024" "Lemma A1.1.34, p. 404"]
theorem morris_A1_1_34 : ¬ (Set.Ico (0 : ℝ) 1).Countable := by
  intro h
  have h1 := Cardinal.mk_Ico_real (zero_lt_one' ℝ)
  have h2 := Cardinal.le_aleph0_iff_set_countable.mpr h
  rw [h1] at h2
  exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr h2)

/-- Morris, Topology Without Tears, Theorem A1.1.35 (TP-395). The set of real numbers is
uncountable. -/
@[kb "morris2024" "Theorem A1.1.35, p. 404"]
theorem morris_A1_1_35 : ¬ (Set.univ : Set ℝ).Countable :=
  not_countable_real

/-- Morris, Topology Without Tears, Theorem A1.2.1 (TP-398). Cantor-Schroeder-Bernstein: injections
`S → T` and `T → S` give a bijection. -/
@[kb "morris2024" "Theorem A1.2.1, p. 406"]
theorem morris_A1_2_1 {S T : Type u} {f : S → T} {g : T → S} (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : S → T, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf hg

/-- Morris, Topology Without Tears, Theorem A1.2.7 (TP-398). For cardinals, `m ≤ n` and `n ≤ m`
imply `m = n`. -/
@[kb "morris2024" "Theorem A1.2.7, p. 408"]
theorem morris_A1_2_7 {m n : Cardinal.{u}} (h₁ : m ≤ n) (h₂ : n ≤ m) : m = n :=
  le_antisymm h₁ h₂

/-- Morris, Topology Without Tears, Definition A1.2.3 (TP-400). The cardinality of `ℝ` is the
continuum `c`. -/
@[kb "morris2024" "Definition A1.2.3, p. 407"]
theorem morris_A1_2_3 : #ℝ = 𝔠 :=
  Cardinal.mk_real

/-- Morris, Topology Without Tears, Definition A1.2.4 (TP-401). `card A ≤ card B` iff there is an
injection from `A` into `B`. -/
@[kb "morris2024" "Definition A1.2.4, p. 407"]
theorem morris_A1_2_4 (α β : Type u) : #α ≤ #β ↔ ∃ f : α → β, Function.Injective f := by
  rw [Cardinal.le_def]
  exact ⟨fun ⟨f⟩ => ⟨f, f.injective⟩, fun ⟨f, hf⟩ => ⟨⟨f, hf⟩⟩⟩

/-- Morris, Topology Without Tears, Proposition A1.2.5 (TP-402). `ℵ₀ < c`. -/
@[kb "morris2024" "Proposition A1.2.5, p. 408"]
theorem morris_A1_2_5 : ℵ₀ < 𝔠 :=
  Cardinal.aleph0_lt_continuum

/-- Morris, Topology Without Tears, Definition A1.2.10 (TP-404). The cardinality of the power set
of `S` is `2 ^ card S`. -/
@[kb "morris2024" "Definition A1.2.10, p. 408"]
theorem morris_A1_2_10 (S : Type u) : #(Set S) = 2 ^ #S :=
  Cardinal.mk_set

/-- Morris, Topology Without Tears, Definition A1.3.1 (TP-407). The sum of cardinals is the
cardinal of the disjoint union. -/
@[kb "morris2024" "Definition A1.3.1, p. 410"]
theorem morris_A1_3_1 (α β : Type u) : #α + #β = #(α ⊕ β) :=
  by rw [Cardinal.mk_sum]; simp

/-- Morris, Topology Without Tears, Propositions A1.3.3 and A1.3.4 (TP-408). Cardinal addition is
associative, commutative, has unit `0` and is monotone. -/
@[kb "morris2024" "Proposition A1.3.3, p. 411"]
theorem morris_A1_3_3 :
    (∀ a b c : Cardinal.{u}, a + b + c = a + (b + c)) ∧ (∀ a b : Cardinal.{u}, a + b = b + a) ∧
      (∀ a : Cardinal.{u}, a + 0 = a) ∧
      (∀ a b c d : Cardinal.{u}, a ≤ b → c ≤ d → a + c ≤ b + d) :=
  ⟨add_assoc, add_comm, add_zero, fun _ _ _ _ => add_le_add⟩

/-- Morris, Topology Without Tears, Definition A1.3.5 (TP-409). The product of cardinals is the
cardinal of the cartesian product. -/
@[kb "morris2024" "Definition A1.3.5, p. 412"]
theorem morris_A1_3_5 (α β : Type u) : #α * #β = #(α × β) :=
  by rw [Cardinal.mk_prod]; simp

/-- Morris, Topology Without Tears, Propositions A1.3.6 and A1.3.7 (TP-410). Cardinal
multiplication is associative, commutative, distributes over addition and is monotone. -/
@[kb "morris2024" "Proposition A1.3.6, p. 412"]
theorem morris_A1_3_6 :
    (∀ a b c : Cardinal.{u}, a * b * c = a * (b * c)) ∧ (∀ a b : Cardinal.{u}, a * b = b * a) ∧
      (∀ a b c : Cardinal.{u}, a * (b + c) = a * b + a * c) ∧
      (∀ a b c d : Cardinal.{u}, a ≤ b → c ≤ d → a * c ≤ b * d) :=
  ⟨mul_assoc, mul_comm, mul_add, fun _ _ _ _ => mul_le_mul'⟩

/-- Morris, Topology Without Tears, Definition A1.3.8 (TP-411). `β ^ α` is the cardinal of the set
of functions from `A` to `B` when `α = card A`, `β = card B`. -/
@[kb "morris2024" "Definition A1.3.8, p. 413"]
theorem morris_A1_3_8 (A B : Type u) : #B ^ #A = #(A → B) :=
  Cardinal.power_def B A

/-- Morris, Topology Without Tears, Proposition A1.3.9 (TP-412). Laws of exponents for
cardinals. -/
@[kb "morris2024" "Proposition A1.3.9, p. 413"]
theorem morris_A1_3_9 :
    (∀ a b c : Cardinal.{u}, a ^ (b + c) = a ^ b * a ^ c) ∧
      (∀ a b c : Cardinal.{u}, (a ^ b) ^ c = a ^ (b * c)) ∧
      (∀ a b c : Cardinal.{u}, (a * b) ^ c = a ^ c * b ^ c) :=
  ⟨Cardinal.power_add, fun _ _ _ => (Cardinal.power_mul).symm, fun _ _ _ => Cardinal.mul_power⟩

/-- Morris, Topology Without Tears, Lemma A1.3.10 (TP-413). `ℵ₀ ^ ℵ₀ = c`. -/
@[kb "morris2024" "Lemma A1.3.10, p. 414"]
theorem morris_A1_3_10 : ℵ₀ ^ ℵ₀ = 𝔠 :=
  Cardinal.aleph0_power_aleph0

/-- Morris, Topology Without Tears, Theorem A1.3.11 (TP-414). `2 ^ ℵ₀ = c`. -/
@[kb "morris2024" "Theorem A1.3.11, p. 415"]
theorem morris_A1_3_11 : (2 : Cardinal.{0}) ^ ℵ₀ = 𝔠 :=
  Cardinal.two_power_aleph0

/-- Morris, Topology Without Tears, Definition A1.4.2 (TP-417). A linearly ordered set is
well-ordered iff every nonempty subset has a least element. -/
@[kb "morris2024" "Definition A1.4.2, p. 416"]
theorem morris_A1_4_2 (α : Type u) [LinearOrder α] :
    WellFoundedLT α ↔ ∀ s : Set α, s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
  constructor
  · intro h s hs
    obtain ⟨a, ha, hmin⟩ := (wellFounded_lt (α := α)).has_min s hs
    exact ⟨a, ha, fun b hb => not_lt.mp (hmin b hb)⟩
  · intro h
    have hwf : WellFounded ((· < ·) : α → α → Prop) :=
      WellFounded.wellFounded_iff_has_min.mpr fun s hs => by
        obtain ⟨a, ha, hmin⟩ := h s hs
        exact ⟨a, ha, fun b hb => not_lt.mpr (hmin b hb)⟩
    exact hwf

/-- Morris, Topology Without Tears, Theorem A1.4.4 (TP-418). Well-ordering theorem: every set
admits a well-ordering. -/
@[kb "morris2024" "Theorem A1.4.4, p. 417"]
theorem morris_A1_4_4 (α : Type u) : ∃ r : α → α → Prop, IsWellOrder α r :=
  ⟨WellOrderingRel, inferInstance⟩

/-- Morris, Topology Without Tears, Proposition A1.4.6 (TP-419). Order isomorphism is reflexive,
symmetric and transitive. -/
@[kb "morris2024" "Proposition A1.4.6, p. 418"]
theorem morris_A1_4_6 :
    (∀ (α : Type u) [LE α], Nonempty (α ≃o α)) ∧
      (∀ (α β : Type u) [LE α] [LE β], Nonempty (α ≃o β) → Nonempty (β ≃o α)) ∧
      (∀ (α β γ : Type u) [LE α] [LE β] [LE γ],
        Nonempty (α ≃o β) → Nonempty (β ≃o γ) → Nonempty (α ≃o γ)) :=
  ⟨fun _ _ => ⟨OrderIso.refl _⟩, fun _ _ _ _ ⟨e⟩ => ⟨e.symm⟩,
    fun _ _ _ _ _ _ ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Morris, Topology Without Tears, Proposition A1.4.18 (TP-424). Trichotomy: for ordinals exactly
one of `α < β`, `α = β`, `β < α` holds. -/
@[kb "morris2024" "Proposition A1.4.18, p. 421"]
theorem morris_A1_4_18 (a b : Ordinal.{u}) :
    (a < b ∨ a = b ∨ b < a) ∧ ¬ (a < b ∧ a = b) ∧ ¬ (a = b ∧ b < a) ∧ ¬ (a < b ∧ b < a) :=
  ⟨lt_trichotomy a b, fun h => (ne_of_lt h.1) h.2, fun h => (ne_of_gt h.2) h.1,
    fun h => lt_asymm h.1 h.2⟩

/-- Morris, Topology Without Tears, Proposition A1.4.22 (TP-427). For every (small) set of
ordinals there is an ordinal larger than all of them. -/
@[kb "morris2024" "Proposition A1.4.22, p. 422"]
theorem morris_A1_4_22 (s : Set Ordinal.{u}) [Small.{u} s] : ∃ b : Ordinal.{u}, ∀ a ∈ s, a < b := by
  obtain ⟨c, hc⟩ := Ordinal.bddAbove_of_small (s := s)
  exact ⟨Order.succ c, fun a ha => lt_of_le_of_lt (hc ha) (Order.lt_succ c)⟩

/-- Morris, Topology Without Tears, Theorem A1.4.27 (TP-429). Transfinite induction over the
ordinals. -/
@[kb "morris2024" "Theorem A1.4.27, p. 423"]
theorem morris_A1_4_27 (P : Ordinal.{u} → Prop) (h : ∀ a, (∀ b < a, P b) → P a) : ∀ a, P a :=
  fun a => WellFoundedLT.induction a h

/-- Morris, Topology Without Tears, Proposition A1.4.28 (TP-430). Ordinal exponentiation:
`α^(β+1) = α^β · α`, and at a limit ordinal `β` the power `α^β` is the supremum of the earlier
powers. -/
@[kb "morris2024" "Proposition A1.4.28, p. 423"]
theorem morris_A1_4_28 :
    (∀ a b : Ordinal.{u}, a ^ (b + 1) = a ^ b * a) ∧
      (∀ a b : Ordinal.{u}, a ≠ 0 → Order.IsSuccLimit b → a ^ b = ⨆ x : Set.Iio b, a ^ x.1) :=
  ⟨Ordinal.opow_add_one, fun _ _ ha hb => Ordinal.opow_limit ha hb⟩

end UndergradKB.Topology.Course
