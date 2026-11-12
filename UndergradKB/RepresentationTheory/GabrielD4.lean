import UndergradKB.RepresentationTheory.GabrielTheorem
import UndergradKB.RepresentationTheory.DynkinForms
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Card
import UndergradKB.Common.Attr

/-! # The quiver `D_4` with subspace orientation (Etingof et al., Examples 5.10 and 5.38)

Mathlib's matrix `CartanMatrix.D 4` has its branch vertex at index `1`: the vertices `0`, `2`, `3` are the three
outer vertices, each joined only to vertex `1`.  The subspace orientation `d4Quiver` of this graph has exactly one
arrow from each outer vertex into the centre `1`.

* `d4Quiver_isOrientation`: `d4Quiver` is an orientation of the graph of `CartanMatrix.D 4`, a Dynkin diagram.
* `d4_form`: the quadratic form of the graph in closed form.
* `d4_positiveRoots_ncard`: the graph has exactly `12` positive roots.
* `d4_twelve_indecomposables` (Example 5.10): over any field there are exactly `12` isomorphism classes of
  finite-dimensional indecomposable representations of `d4Quiver`.
* `d4_isPositiveRoot_central`, `d4_central_indecomposable` (Example 5.38): the vector with coordinate `2` at the
  centre and `1` at the outer vertices is a positive root; there is a finite-dimensional indecomposable
  representation with this dimension vector and it is unique up to isomorphism.

Not formalized here: the concrete realisation of the representation of Example 5.38 as three distinct lines in
`k²` is not done on the vertex type `Fin 4` (an equivalent model on a custom vertex type exists in
`QuiverA3.lean`); transporting its indecomposability to `Fin 4` is missing.
-/

namespace UndergradKB.RepresentationTheory.GabrielD4

open Roots Gabriel QRep

/-- The graph `D_4`: the graph of Mathlib's Cartan matrix `CartanMatrix.D 4`; vertex `1` is the branch vertex. -/
abbrev d4Graph : SimpleGraph (Fin 4) := graphOfCartan (CartanMatrix.D 4)

/-- The subspace orientation of `D_4`: one arrow from each outer vertex (`0`, `2`, `3`) into the centre `1`
(a local instance). -/
local instance d4Quiver : Quiver.{0} (Fin 4) := ⟨fun i j => PLift (i ≠ 1 ∧ j = 1)⟩

theorem d4_matrix : CartanMatrix.D 4 = !![2, -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] := by
  decide

theorem d4_adj (x y : Fin 4) : d4Graph.Adj x y ↔ (x ≠ 1 ∧ y = 1) ∨ (y ≠ 1 ∧ x = 1) := by
  revert x y
  decide

theorem d4_arr (x y : Fin 4) : arr d4Quiver x y ↔ (x ≠ 1 ∧ y = 1) :=
  ⟨fun ⟨e⟩ => e.down, fun h => ⟨⟨h⟩⟩⟩

/-- The subspace orientation is an orientation of the graph `D_4`. -/
theorem d4Quiver_isOrientation : IsOrientation d4Graph d4Quiver where
  sub x y := ⟨fun a b => by cases a; cases b; rfl⟩
  adj x y h := by
    rw [d4_arr] at h
    exact (d4_adj x y).2 (Or.inl h)
  adj' x y h := by
    rw [d4_adj] at h
    rcases h with h | h
    · exact Or.inl ((d4_arr x y).2 h)
    · exact Or.inr ((d4_arr y x).2 h)
  asymm x y h h' := by
    rw [d4_arr] at h h'
    exact h.1 h'.2

theorem d4_isDynkin : IsDynkin d4Graph := isDynkin_D 1

/-- The quadratic form of `D_4` in closed form; vertex `1` is the centre. -/
theorem d4_form (β : Fin 4 → ℤ) :
    form d4Graph β β = 2 * (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2 + β 3 ^ 2) - 2 * β 1 * (β 0 + β 2 + β 3) := by
  have hM : ∀ i j, cartanMatrix d4Graph i j =
      !![(2 : ℤ), -1, 0, 0; -1, 2, -1, -1; 0, -1, 2, 0; 0, -1, 0, 2] i j := by
    intro i j
    rw [cartanMatrix_D_eq, d4_matrix]
  simp only [form_eq_sum, Fin.sum_univ_four, hM]
  simp
  ring

/-- Every positive root of `D_4` has all coordinates at most `2`. -/
theorem d4_root_le_two {β : Fin 4 → ℤ} (h : IsPositiveRoot d4Graph β) (i : Fin 4) : β i ≤ 2 := by
  have h2 : form d4Graph β β = 2 := h.1
  rw [d4_form] at h2
  have h0 := h.2 0
  have h1 := h.2 1
  have h2' := h.2 2
  have h3 := h.2 3
  have s0 := sq_nonneg (2 * β 0 - β 1)
  have s2 := sq_nonneg (2 * β 2 - β 1)
  have s3 := sq_nonneg (2 * β 3 - β 1)
  have s1 := sq_nonneg (β 1)
  have e1 : β 1 ≤ 2 := by nlinarith
  have e0 : β 0 ≤ 2 := by nlinarith
  have e2 : β 2 ≤ 2 := by nlinarith
  have e3 : β 3 ≤ 2 := by nlinarith
  fin_cases i <;> assumption

/-- The finite set of candidate coordinate vectors satisfying the closed form of `B(β, β) = 2`. -/
def d4Candidates : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (0 : ℤ) 2).filter fun β =>
    2 * (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2 + β 3 ^ 2) - 2 * β 1 * (β 0 + β 2 + β 3) = 2

theorem d4Candidates_card : d4Candidates.card = 12 := by
  decide

theorem d4_isPositiveRoot_iff (β : Fin 4 → ℤ) : IsPositiveRoot d4Graph β ↔ β ∈ d4Candidates := by
  constructor
  · intro h
    have h2 : form d4Graph β β = 2 := h.1
    rw [d4_form] at h2
    simp only [d4Candidates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
    exact ⟨fun i => ⟨h.2 i, d4_root_le_two h i⟩, h2⟩
  · intro h
    simp only [d4Candidates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at h
    refine ⟨?_, fun i => (h.1 i).1⟩
    show form d4Graph β β = 2
    rw [d4_form]
    exact h.2

/-- The graph `D_4` has exactly `12` positive roots. -/
theorem d4_positiveRoots_ncard : {β : Fin 4 → ℤ | IsPositiveRoot d4Graph β}.ncard = 12 := by
  have : {β : Fin 4 → ℤ | IsPositiveRoot d4Graph β} = ↑d4Candidates := by
    ext β
    exact d4_isPositiveRoot_iff β
  rw [this, Set.ncard_coe_finset, d4Candidates_card]

theorem d4_positiveRoots_equiv : Nonempty (Fin 12 ≃ {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β}) := by
  have h : Nat.card {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β} = 12 := by
    rw [← d4_positiveRoots_ncard, ← Nat.card_coe_set_eq]
    rfl
  have hf : Finite {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β} :=
    Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have := Fintype.ofFinite {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β}
  exact ⟨(Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact h)).symm⟩

universe u w

/-- **Example 5.10.** Over any field `k`, the quiver `D_4` with the subspace orientation (three arrows into the
central vertex) has exactly `12` isomorphism classes of finite-dimensional indecomposable representations: there
is a family `M : Fin 12 → QRep` of finite-dimensional indecomposable representations such that every
finite-dimensional indecomposable representation is isomorphic to exactly one `M i`. -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem d4_twelve_indecomposables (k : Type u) [Field k] :
    ∃ M : Fin 12 → QRep.{u, 0, u, 0} k (Fin 4),
      (∀ i, (∀ j, Module.Finite k ((M i).obj j)) ∧ (M i).IsIndecomposable) ∧
      ∀ (V : QRep.{u, 0, w, 0} k (Fin 4)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
        ∃! i, V.Isomorphic (M i) := by
  obtain ⟨e⟩ := d4_positiveRoots_equiv
  have key : ∃ M : {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β} → QRep.{u, 0, u, 0} k (Fin 4),
      Finite {β : Fin 4 → ℤ // IsPositiveRoot d4Graph β} ∧
      (∀ β, (∀ j, Module.Finite k ((M β).obj j)) ∧ (M β).IsIndecomposable ∧ (M β).dimZ = β.1) ∧
      ∀ (V : QRep.{u, 0, w, 0} k (Fin 4)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
        ∃! β, V.Isomorphic (M β) :=
    gabriel_finiteType d4Graph d4_isDynkin d4Quiver_isOrientation
  obtain ⟨M, -, hM, hV⟩ := key
  refine ⟨fun i => M (e i), fun i => ⟨(hM (e i)).1, (hM (e i)).2.1⟩, fun V _ hVi => ?_⟩
  obtain ⟨β, hβ, huniq⟩ := hV V hVi
  refine ⟨e.symm β, by simpa using hβ, fun i hi => ?_⟩
  have := huniq (e i) hi
  rw [← this]
  simp

/-- The dimension vector of Example 5.38: dimension `2` at the centre `1` and `1` at the three outer vertices. -/
def d4Central : Fin 4 → ℤ := ![1, 2, 1, 1]

/-- The vector `α_0 + α_2 + α_3 + 2 α_1` is a positive root of `D_4`. -/
theorem d4_isPositiveRoot_central : IsPositiveRoot d4Graph d4Central := by
  refine ⟨?_, fun i => by fin_cases i <;> simp [d4Central]⟩
  show form d4Graph d4Central d4Central = 2
  rw [d4_form]
  simp [d4Central]

/-- **Example 5.38.** For `D_4` oriented towards the centre, there is a finite-dimensional indecomposable
representation with dimension vector `(1, 2, 1, 1)` (dimension `2` at the centre, `1` at each outer vertex), and
any two finite-dimensional indecomposable representations with this dimension vector are isomorphic. -/
@[kb "etingof2011" "Example 5.38, p. 96"]
theorem d4_central_indecomposable (k : Type u) [Field k] :
    (∃ V : QRep.{u, 0, u, 0} k (Fin 4), (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧
      V.dimZ = d4Central) ∧
    ∀ (V V' : QRep.{u, 0, u, 0} k (Fin 4)) [∀ j, Module.Finite k (V.obj j)]
      [∀ j, Module.Finite k (V'.obj j)], V.IsIndecomposable → V'.IsIndecomposable →
      V.dimZ = d4Central → V'.dimZ = d4Central → V.Isomorphic V' := by
  refine ⟨exists_indecomposable_of_isPositiveRoot d4Graph d4_isDynkin.2 d4Quiver_isOrientation
    d4_isPositiveRoot_central, fun V V' _ _ hV hV' h h' => ?_⟩
  exact isomorphic_of_dimVec_eq d4Graph d4_isDynkin.2 d4Quiver_isOrientation V V' hV hV'
    (dimZ_injective (h.trans h'.symm))

end UndergradKB.RepresentationTheory.GabrielD4
