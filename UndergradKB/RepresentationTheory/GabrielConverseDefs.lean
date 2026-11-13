import UndergradKB.RepresentationTheory.GabrielTheorem
import UndergradKB.Common.Attr

/-! # Definitions for the converse of Gabriel's theorem (Etingof et al., Problem 5.4)

For a quiver `Q` on `Fin n` with finitely many arrows between any two vertices:

* `titsForm`: the quadratic form `q(x) = ∑_i x_i² - ∑_{arrows i → j} x_i x_j` of Problem 5.4 (the book writes it
  with the symmetric edge counts `b_ij`; a loop at `i` contributes `-x_i²`). For a dimension vector `d`,
  `q(d) = dim ∏ GL(d_i) - dim Rep(d)`.
* `MatRep k d`: representations on the coordinate spaces `k^{d_i}`, given by one matrix per arrow;
  `MatRep.toQRep` is the corresponding `QRep`, and `MatRep.Equiv x y` says that `x` and `y` lie in the same orbit
  of `∏ GL(d_i)` (`y_a g_i = g_j x_a` with invertible `g_i`).
* `IsFiniteType k Q`: finitely many indecomposable finite-dimensional representations up to isomorphism.
* `underlyingGraph Q`: the simple graph joining distinct vertices with an arrow between them.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open Roots QRep

noncomputable section

universe u a

variable {n : ℕ} [Q : Quiver.{a} (Fin n)]

/-- The quadratic form of Problem 5.4: `q(x) = ∑_i x_i² - ∑_{arrows i → j} x_i x_j`. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
def titsForm [∀ i j : Fin n, Fintype (i ⟶ j)] (x : Fin n → ℤ) : ℤ :=
  ∑ i, x i ^ 2 - ∑ i, ∑ j, (Fintype.card (i ⟶ j) : ℤ) * x i * x j

variable (k : Type u) [Field k]

/-- Representations of `Q` on the spaces `k^{d_i}`: one `d_j × d_i` matrix for each arrow `i → j`. -/
abbrev MatRep (d : Fin n → ℕ) : Type (max u a) := ∀ i j : Fin n, (i ⟶ j) → Matrix (Fin (d j)) (Fin (d i)) k

variable {k}

/-- The quiver representation given by a tuple of matrices. -/
def MatRep.toQRep {d : Fin n → ℕ} (x : MatRep k d) : QRep.{u, 0, u, a} k (Fin n) where
  obj i := Fin (d i) → k
  map {i j} e := Matrix.toLin' (x i j e)

/-- `x` and `y` lie in the same orbit of `∏_i GL(d_i)`: `y_a g_i = g_j x_a` for invertible matrices `g_i`. -/
def MatRep.Equiv {d : Fin n → ℕ} (x y : MatRep k d) : Prop :=
  ∃ g : ∀ i, Matrix (Fin (d i)) (Fin (d i)) k, (∀ i, IsUnit (g i)) ∧ ∀ i j (e : i ⟶ j), y i j e * g i = g j * x i j e

variable (k Q) in
/-- **Etingof et al., Problem 5.4**: the quiver is of finite type if it has finitely many indecomposable
finite-dimensional representations up to isomorphism. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
def IsFiniteType : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (W : ι → QRep.{u, 0, u, a} k (Fin n)), (∀ m j, Module.Finite k ((W m).obj j)) ∧
    ∀ V : QRep.{u, 0, u, a} k (Fin n), (∀ j, Module.Finite k (V.obj j)) → V.IsIndecomposable →
      ∃ m, V.Isomorphic (W m)

variable (Q) in
/-- The underlying simple graph of the quiver: distinct vertices are adjacent when an arrow joins them. -/
def underlyingGraph : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (Nonempty (i ⟶ j) ∨ Nonempty (j ⟶ i))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end

end UndergradKB.RepresentationTheory.Gabriel
