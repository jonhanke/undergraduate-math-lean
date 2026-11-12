import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.AlgebraicCard
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.ZFC.Ordinal
import UndergradKB.Common.Attr

/-!
# Infinite sets, cardinals and ordinals (Morris, Appendix 1)

Uncountability of power sets, irrationals and transcendentals; cardinality of intervals and the plane;
`α ^ ℵ₀ = 𝔠`; and the book's ordinal statements read through Mathlib's `Ordinal` and `ZFSet.IsOrdinal`.
-/

namespace UndergradKB.Topology

open Cardinal Set

universe u

/-- Morris, Topology Without Tears, Proposition A1.1.33 (TP-394). The power set of an infinite set is
uncountable. -/
@[kb "morris2024" "Proposition A1.1.33, p. 403"]
theorem uncountable_set_of_infinite {S : Type u} [Infinite S] : Uncountable (Set S) := by
  rw [← not_countable_iff]
  intro h
  have h1 : #(Set S) ≤ ℵ₀ := mk_le_aleph0_iff.2 h
  have h2 : ℵ₀ ≤ #S := infinite_iff.1 inferInstance
  have h3 : #S < #(Set S) := by rw [mk_set]; exact cantor _
  exact absurd (h3.trans_le (h1.trans h2)) (lt_irrefl _)

/-- Morris, Topology Without Tears, Proposition A1.1.33 (TP-394). The set of all subsets of an infinite
set `S` is uncountable (set form). -/
@[kb "morris2024" "Proposition A1.1.33, p. 403"]
theorem not_countable_powerset_of_infinite {α : Type u} {S : Set α} (hS : S.Infinite) :
    ¬ (𝒫 S).Countable := by
  intro h
  have : Infinite S := hS.to_subtype
  have : Countable (Set S) := by
    have e : Set S ≃ 𝒫 S :=
      { toFun := fun T => ⟨(↑) '' T, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩
        invFun := fun T => ((↑) : S → α) ⁻¹' T.1
        left_inv := fun T => Set.preimage_image_eq _ Subtype.coe_injective
        right_inv := fun T => by
          apply Subtype.ext
          simp only
          rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
          exact Set.inter_eq_left.2 T.2 }
    exact (e.countable_iff).2 h.to_subtype
  exact not_countable_iff.2 uncountable_set_of_infinite this

/-- Morris, Topology Without Tears, Corollary A1.1.36 (TP-396). The set of irrational numbers is
uncountable. -/
@[kb "morris2024" "Corollary A1.1.36, p. 405"]
theorem not_countable_irrational : ¬ {x : ℝ | Irrational x}.Countable := by
  intro h
  have h2 : (Set.univ : Set ℝ).Countable := by
    have : (Set.univ : Set ℝ) = {x : ℝ | Irrational x} ∪ Set.range ((↑) : ℚ → ℝ) := by
      ext x
      by_cases h : x ∈ Set.range ((↑) : ℚ → ℝ)
      · exact ⟨fun _ => Or.inr h, fun _ => trivial⟩
      · exact ⟨fun _ => Or.inl h, fun _ => trivial⟩
    rw [this]
    exact h.union (Set.countable_range _)
  exact not_countable_real h2

/-- Morris, Topology Without Tears, Corollary A1.1.37 (TP-397). The set of transcendental real numbers
(not roots of a nonzero integer polynomial) is uncountable. -/
@[kb "morris2024" "Corollary A1.1.37, p. 405"]
theorem not_countable_transcendental : ¬ {x : ℝ | Transcendental ℤ x}.Countable := by
  intro h
  have h2 : (Set.univ : Set ℝ).Countable := by
    have : (Set.univ : Set ℝ) = {x : ℝ | Transcendental ℤ x} ∪ {x : ℝ | IsAlgebraic ℤ x} := by
      ext x
      by_cases h : IsAlgebraic ℤ x <;> simp [Transcendental, h]
    rw [this]
    exact h.union (Algebraic.countable ℤ ℝ)
  exact not_countable_real h2

/-- Morris, Topology Without Tears, Corollary A1.2.9 (TP-403). There is no largest cardinal number. -/
@[kb "morris2024" "Corollary A1.2.9, p. 408"]
theorem no_largest_cardinal : ¬ ∃ a : Cardinal.{u}, ∀ b : Cardinal.{u}, b ≤ a := by
  rintro ⟨a, ha⟩
  exact absurd (cantor a) (not_lt.2 (ha _))

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). An open bounded nondegenerate interval is
equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Ioo_real {a b : ℝ} (h : a < b) : Nonempty (Ioo a b ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Ioo_real h).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). A closed bounded nondegenerate interval is
equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Icc_real {a b : ℝ} (h : a < b) : Nonempty (Icc a b ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Icc_real h).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). A half-open interval `[a, b)` is
equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Ico_real {a b : ℝ} (h : a < b) : Nonempty (Ico a b ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Ico_real h).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). A half-open interval `(a, b]` is
equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Ioc_real {a b : ℝ} (h : a < b) : Nonempty (Ioc a b ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Ioc_real h).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). An open ray `(a, ∞)` is equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Ioi_real (a : ℝ) : Nonempty (Ioi a ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Ioi_real a).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). An open ray `(-∞, a)` is equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Iio_real (a : ℝ) : Nonempty (Iio a ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Iio_real a).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). A closed ray `[a, ∞)` is equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Ici_real (a : ℝ) : Nonempty (Ici a ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Ici_real a).trans mk_real.symm)

/-- Morris, Topology Without Tears, Lemma A1.2.11 (TP-405). A closed ray `(-∞, a]` is equipotent to `ℝ`. -/
@[kb "morris2024" "Lemma A1.2.11, p. 409"]
theorem nonempty_equiv_Iic_real (a : ℝ) : Nonempty (Iic a ≃ ℝ) :=
  Cardinal.eq.1 ((mk_Iic_real a).trans mk_real.symm)

/-- Morris, Topology Without Tears, Proposition A1.2.12 (TP-405). Any subset of `ℝ` containing an open
interval `(a, b)` with `a < b` has cardinality `𝔠`. -/
@[kb "morris2024" "Proposition A1.2.12, p. 410"]
theorem mk_eq_continuum_of_Ioo_subset {a b : ℝ} {S : Set ℝ} (h : a < b) (hS : Ioo a b ⊆ S) :
    #S = 𝔠 := by
  refine le_antisymm ?_ ?_
  · calc #S ≤ #ℝ := mk_set_le S
      _ = 𝔠 := mk_real
  · calc 𝔠 = #(Ioo a b) := (mk_Ioo_real h).symm
      _ ≤ #S := mk_le_mk_of_subset hS

/-- Morris, Topology Without Tears, Proposition A1.2.13 (TP-406). The Euclidean plane `ℝ × ℝ` has
cardinality `𝔠`. -/
@[kb "morris2024" "Proposition A1.2.13, p. 410"]
theorem mk_real_prod_real : #(ℝ × ℝ) = 𝔠 := by
  rw [mk_prod, mk_real]
  simp [continuum_mul_self]

/-- Morris, Topology Without Tears, Proposition A1.2.13 (TP-406). `ℝ × ℝ` is equipotent to `ℝ`. -/
@[kb "morris2024" "Proposition A1.2.13, p. 410"]
theorem nonempty_equiv_real_prod_real : Nonempty ((ℝ × ℝ) ≃ ℝ) :=
  Cardinal.eq.1 (mk_real_prod_real.trans mk_real.symm)

/-- Morris, Topology Without Tears, Corollary A1.3.12 (TP-415). If `2 ≤ α ≤ 𝔠` then `α ^ ℵ₀ = 𝔠`. -/
@[kb "morris2024" "Corollary A1.3.12, p. 416"]
theorem power_aleph0_eq_continuum {α : Cardinal.{0}} (h2 : 2 ≤ α) (hc : α ≤ 𝔠) : α ^ ℵ₀ = 𝔠 := by
  refine le_antisymm ?_ ?_
  · calc α ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ := power_le_power_right hc
      _ = 𝔠 := continuum_power_aleph0
  · calc 𝔠 = 2 ^ ℵ₀ := two_power_aleph0.symm
      _ ≤ α ^ ℵ₀ := power_le_power_right h2

/-! ### Ordinals -/

open Ordinal in
/-- Morris, Topology Without Tears, Definition A1.4.8 (TP-420). Mathlib's von Neumann form: the ordinal
`o` as a set of ZF sets is the set of the sets of the smaller ordinals, and it is a `ZFSet.IsOrdinal`
(a transitive set well-ordered by membership). -/
@[kb "morris2024" "Definition A1.4.8, p. 419"]
theorem toZFSet_isOrdinal_and_mem (o : Ordinal.{u}) :
    o.toZFSet.IsOrdinal ∧ ∀ x : ZFSet.{u}, x ∈ o.toZFSet ↔ ∃ a < o, a.toZFSet = x :=
  ⟨ZFSet.isOrdinal_toZFSet o, fun _ => Ordinal.mem_toZFSet_iff⟩

/-- Morris, Topology Without Tears, Proposition A1.4.9 (TP-420). A von Neumann ordinal is well ordered
by membership. -/
@[kb "morris2024" "Proposition A1.4.9, p. 419"]
theorem isWellOrder_mem_of_isOrdinal {x : ZFSet.{u}} (h : x.IsOrdinal) :
    IsWellOrder _ (Subrel (· ∈ ·) (· ∈ x)) :=
  h.isWellOrder

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). Elements of ordinals are ordinals. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem isOrdinal_of_mem_isOrdinal {x y : ZFSet.{u}} (hx : x.IsOrdinal) (hy : y ∈ x) :
    y.IsOrdinal :=
  hx.mem hy

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). Any two ordinals are comparable:
`x ∈ y`, `x = y` or `y ∈ x`. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem ordinals_comparable {x y : ZFSet.{u}} (hx : x.IsOrdinal) (hy : y.IsOrdinal) :
    x ∈ y ∨ x = y ∨ y ∈ x :=
  ZFSet.IsOrdinal.mem_trichotomous hx hy

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). The union of a set of ordinals is an
ordinal. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem isOrdinal_sUnion_of_forall {S : ZFSet.{u}} (h : ∀ x ∈ S, x.IsOrdinal) :
    (ZFSet.sUnion S).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isOrdinal]
  refine ⟨ZFSet.IsTransitive.sUnion' (fun y hy => (h y hy).isTransitive), ?_⟩
  intro y hy
  rw [ZFSet.mem_sUnion] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  exact (h z hz).mem hyz

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). Isomorphic well-orders have the same
order type, that is, they determine the same ordinal (Mathlib's `Ordinal.type`); and every well-order
is isomorphic to the ordinal `Ordinal.type r`, namely the well-order on the initial segment of smaller
ordinals. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem type_eq_iff_nonempty_relIso {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] :
    Ordinal.type r = Ordinal.type s ↔ Nonempty (r ≃r s) :=
  Ordinal.type_eq

/-- Morris, Topology Without Tears, Proposition A1.4.12 (TP-421). Every well-order is isomorphic to the
well-order of the smaller ordinals below its type. -/
@[kb "morris2024" "Proposition A1.4.12, p. 420"]
theorem nonempty_relIso_Iio_type {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    Nonempty (r ≃r ((· < ·) : Set.Iio (Ordinal.type r) → Set.Iio (Ordinal.type r) → Prop)) :=
  ⟨(Ordinal.enum r).symm⟩

/-- Morris, Topology Without Tears, Proposition A1.4.21 (TP-426). The supremum of a (small) set of
ordinals is an upper bound and is below every upper bound. -/
@[kb "morris2024" "Proposition A1.4.21, p. 422"]
theorem isLUB_sSup_ordinal (s : Set Ordinal.{u}) [Small.{u} s] : IsLUB s (sSup s) :=
  isLUB_csSup' Ordinal.bddAbove_of_small

/-- Morris, Topology Without Tears, Proposition A1.4.21 (TP-426). In von Neumann form, the union of a set
of ordinals is an upper bound for it with respect to inclusion, and is included in every set that
includes all of them. -/
@[kb "morris2024" "Proposition A1.4.21, p. 422"]
theorem sUnion_isLeast_upperBound {S : ZFSet.{u}} (h : ∀ x ∈ S, x.IsOrdinal) :
    (ZFSet.sUnion S).IsOrdinal ∧ (∀ x ∈ S, x ⊆ ZFSet.sUnion S) ∧
      ∀ z : ZFSet.{u}, (∀ x ∈ S, x ⊆ z) → ZFSet.sUnion S ⊆ z := by
  refine ⟨isOrdinal_sUnion_of_forall h, ?_, ?_⟩
  · intro x hx y hy
    exact ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩
  · intro z hz y hy
    obtain ⟨x, hx, hyx⟩ := ZFSet.mem_sUnion.1 hy
    exact hz x hx hyx

/-- Morris, Topology Without Tears, Definition A1.4.25 (TP-428). Mathlib defines ordinal exponentiation
by recursion; its defining equations are the book's characterisation: `α ^ 0 = 1`, `α ^ (β + 1) =
α ^ β * α`, and at a limit `β` the power is the supremum of the earlier powers. -/
@[kb "morris2024" "Definition A1.4.25, p. 423"]
theorem ordinal_opow_equations (a : Ordinal.{u}) (ha : a ≠ 0) :
    a ^ (0 : Ordinal) = 1 ∧ (∀ b : Ordinal, a ^ (b + 1) = a ^ b * a) ∧
      ∀ b : Ordinal, Order.IsSuccLimit b → a ^ b = ⨆ x : Set.Iio b, a ^ x.1 :=
  ⟨Ordinal.opow_zero a, fun b => Ordinal.opow_add_one a b, fun _ hb => Ordinal.opow_limit ha hb⟩

end UndergradKB.Topology
