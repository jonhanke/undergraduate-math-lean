import UndergradKB.RepresentationTheory.GabrielOrbits
import UndergradKB.RepresentationTheory.GabrielFiniteClasses
import UndergradKB.RepresentationTheory.GabrielTitsForm
import UndergradKB.Common.Attr

/-! # Gabriel's theorem, both directions (Etingof et al., Theorem 1.2, Problem 5.4, Theorem 5.23)

For a finite quiver `Q` on `Fin n` (finitely many arrows between any two vertices) over an infinite field `k`:

* `titsForm_pos_of_isFiniteType` (Problem 5.4(a)): if `Q` is of finite type then `q(d) > 0` for every nonzero
  dimension vector `d`. Otherwise `Rep(d)` would be a finite union of orbits (`IsFiniteType.exists_finite_orbits`:
  every representation is a sum of the finitely many indecomposables), which `exists_not_equiv` rules out.
* `isDynkin_of_isFiniteType` (Problem 5.4(b), (c)): a connected quiver of finite type has no loops, at most one arrow
  between two vertices, and its underlying graph is a Dynkin diagram.
* `gabriel_iff` (Theorem 1.2): a connected finite quiver is of finite type if and only if it has no loops, no
  multiple arrows (in either direction) and its underlying graph is a Dynkin diagram (`A_n`, `D_n`, `E_6`, `E_7`,
  `E_8` by `classification_dynkin`). The "if" direction is `gabriel_finiteType` (Theorem 5.23) and holds over every
  field.

The book works over an algebraically closed field; the "only if" direction here needs only an infinite field.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open Roots QRep

universe u a

variable {k : Type u} [Field k] {n : ℕ} [Q : Quiver.{a} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

/-- **Etingof et al., Problem 5.4(a)**: over an infinite field, a quiver of finite type has `q(d) > 0` for every
nonzero dimension vector `d`. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem titsForm_pos_of_isFiniteType [Infinite k] (h : IsFiniteType Q k) (d : Fin n → ℕ) (hd : d ≠ 0) :
    0 < titsForm (fun i => (d i : ℤ)) := by
  by_contra hq
  push Not at hq
  obtain ⟨m, xs, hxs⟩ := h.exists_finite_orbits d
  obtain ⟨y, hy⟩ := exists_not_equiv (k := k) hd hq xs
  obtain ⟨t, ht⟩ := hxs y
  exact hy t ht

/-- **Etingof et al., Problem 5.4** (the "only if" direction of Gabriel's theorem): over an infinite field, a
connected quiver of finite type has no loops, at most one arrow between any two vertices (counting both
directions), and its underlying graph is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem isDynkin_of_isFiniteType [Infinite k] (hc : (underlyingGraph Q).Connected) (h : IsFiniteType Q k) :
    (∀ i : Fin n, IsEmpty (i ⟶ i)) ∧ (∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) ∧
      IsDynkin (underlyingGraph Q) :=
  isDynkin_of_titsForm_pos hc fun d hd => titsForm_pos_of_isFiniteType h d hd

/-- The "if" direction (Theorem 5.23, over any field): an orientation of a Dynkin diagram is of finite type. -/
theorem isFiniteType_of_isDynkin (hl : ∀ i : Fin n, IsEmpty (i ⟶ i))
    (h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) (hD : IsDynkin (underlyingGraph Q)) :
    IsFiniteType Q k := by
  obtain ⟨M, hfin, hM, huniq⟩ :=
    gabriel_finiteType (k := k) (underlyingGraph Q) hD (isOrientation_of_card_le hl h1)
  refine ⟨_, hfin, M, fun β => (hM β).1, fun V hVf hV => ?_⟩
  haveI := hVf
  obtain ⟨β, hβ, -⟩ := huniq V hV
  exact ⟨β, hβ⟩

/-- **Gabriel's theorem (Etingof et al., Theorem 1.2)**: over an infinite field, a connected finite quiver has
finitely many indecomposable representations up to isomorphism if and only if it has no loops, at most one arrow
between any two vertices, and its underlying graph is a Dynkin diagram (one of `A_n`, `D_n`, `E_6`, `E_7`, `E_8`,
`classification_dynkin`); this does not depend on the orientation. -/
@[kb "etingof2011" "Theorem 1.2, p. 6"]
theorem gabriel_iff [Infinite k] (hc : (underlyingGraph Q).Connected) :
    IsFiniteType Q k ↔ (∀ i : Fin n, IsEmpty (i ⟶ i)) ∧ (∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) ∧
      IsDynkin (underlyingGraph Q) :=
  ⟨isDynkin_of_isFiniteType hc, fun ⟨hl, h1, hD⟩ => isFiniteType_of_isDynkin hl h1 hD⟩

end UndergradKB.RepresentationTheory.Gabriel
