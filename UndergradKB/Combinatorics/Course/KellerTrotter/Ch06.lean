import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Extension.Linear
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 6 (Partially Ordered Sets): thin course wrappers
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter

/-- CO-155. The cover graph of a poset contains no triangle. -/
@[kb "kellertrotter2017" "text (triangle is not a cover graph), p. 145"]
theorem text_p145_cover_graph_triangle_free (P : Type*) [PartialOrder P] :
    (SimpleGraph.hasse P).CliqueFree 3 :=
  SimpleGraph.cliqueFree_hasse_three

/-- CO-164. Every poset has a linear extension: a linear order on the same set containing
the given order. -/
@[kb "kellertrotter2017" "Discussion 6.24, p. 149"]
theorem disc_6_24 (P : Type*) [PartialOrder P] :
    ∃ s : P → P → Prop, IsLinearOrder P s ∧ (· ≤ ·) ≤ s :=
  extend_partialOrder (· ≤ ·)

/-! ### Definitions of Sections 6.1--6.4 in the book's terms -/

section Definitions

variable {P Q : Type*} [PartialOrder P] [PartialOrder Q]

/-- CO-133. A partial order is reflexive, antisymmetric and transitive. -/
@[kb "kellertrotter2017" "Definition (unnumbered) poset, p. 138"]
theorem def_p138_poset (x y z : P) :
    x ≤ x ∧ (x ≤ y → y ≤ x → x = y) ∧ (x ≤ y → y ≤ z → x ≤ z) :=
  ⟨le_refl x, fun h1 h2 => le_antisymm h1 h2, fun h1 h2 => le_trans h1 h2⟩

/-- CO-134. `y` covers `x` when `x < y` and no `z` lies strictly between them. -/
@[kb "kellertrotter2017" "Definition (unnumbered) cover, p. 139"]
theorem def_p139_cover (x y : P) : x ⋖ y ↔ x < y ∧ ∀ z, ¬ (x < z ∧ z < y) :=
  ⟨fun h => ⟨h.lt, fun _ hz => h.2 hz.1 hz.2⟩, fun h => ⟨h.1, fun z h1 h2 => h.2 z ⟨h1, h2⟩⟩⟩

/-- CO-135. In the cover graph two points are adjacent when one covers the other. -/
@[kb "kellertrotter2017" "Definition (unnumbered) cover graph, p. 139"]
theorem def_p139_cover_graph (x y : P) : (SimpleGraph.hasse P).Adj x y ↔ x ⋖ y ∨ y ⋖ x :=
  SimpleGraph.hasse_adj

/-- CO-137. In a total (linear) order any two elements are comparable. -/
@[kb "kellertrotter2017" "Definition (unnumbered) total order, p. 140"]
theorem def_p140_total_order {L : Type*} [LinearOrder L] (x y : L) : x ≤ y ∨ y ≤ x :=
  le_total x y

/-- CO-141. A subposet carries the restricted order: for points of a subset `S`,
`x ≤ y` in the subposet exactly when `x ≤ y` in `P`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) subposet, p. 142"]
theorem def_p142_subposet (S : Set P) (x y : S) : x ≤ y ↔ (x : P) ≤ y :=
  Iff.rfl

/-- CO-142. A chain is a set any two distinct points of which are comparable. -/
@[kb "kellertrotter2017" "Definition (unnumbered) chain, p. 142"]
theorem def_p142_chain (S : Set P) :
    IsChain (· ≤ ·) S ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ≤ y ∨ y ≤ x :=
  Iff.rfl

/-- CO-143. An antichain is a set any two distinct points of which are incomparable. -/
@[kb "kellertrotter2017" "Definition (unnumbered) antichain, p. 142"]
theorem def_p142_antichain (S : Set P) :
    IsAntichain (· ≤ ·) S ↔ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ x ≤ y :=
  Iff.rfl

/-- CO-146. An isomorphism of posets is an order-preserving and order-reflecting bijection. -/
@[kb "kellertrotter2017" "Definition (unnumbered) isomorphism, p. 143"]
theorem def_p143_isomorphism (f : P ≃o Q) :
    Function.Bijective f ∧ ∀ x y, f x ≤ f y ↔ x ≤ y :=
  ⟨f.bijective, fun _ _ => f.le_iff_le⟩

/-- CO-147. Automorphisms of a poset (isomorphisms onto itself) compose, and each has an inverse
automorphism. -/
@[kb "kellertrotter2017" "Definition (unnumbered) automorphism, p. 143"]
theorem def_p143_automorphism (f g : P ≃o P) (x : P) :
    (f.trans g) x = g (f x) ∧ f.symm (f x) = x :=
  ⟨rfl, f.symm_apply_apply x⟩

/-- CO-148. An embedding of `P` in `Q` is an isomorphism of `P` onto a subposet of `Q`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) embedding, p. 143"]
theorem def_p143_embedding (f : P ↪o Q) :
    ∃ g : P ≃o Set.range f, ∀ x, (g x : Q) = f x :=
  ⟨f.orderIso, fun _ => rfl⟩

/-- CO-158. A point is minimal if no point is below it, and maximal if no point is above it. -/
@[kb "kellertrotter2017" "Definition (unnumbered) minimal point, p. 146"]
theorem def_p146_minimal_maximal (x : P) :
    (IsMin x ↔ ∀ y, ¬ y < x) ∧ (IsMax x ↔ ∀ y, ¬ x < y) :=
  ⟨isMin_iff_forall_not_lt, isMax_iff_forall_not_lt⟩

/-- CO-163. A linear extension of a poset: a linear order in which `x < y` in `P` implies
`x < y` there (Mathlib's `LinearExtension P`, a linear order on `P` with `toLinearExtension`
order preserving). -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear extension, p. 149"]
theorem def_p149_linear_extension (x y : P) (h : x ≤ y) :
    toLinearExtension x ≤ (toLinearExtension y : LinearExtension P) :=
  toLinearExtension.monotone h

end Definitions

end UndergradKB.Combinatorics.Course.KellerTrotter
