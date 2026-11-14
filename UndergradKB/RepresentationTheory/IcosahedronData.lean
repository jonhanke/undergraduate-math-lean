import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr

/-! # The regular icosahedron: exact coordinates

The regular icosahedron with edge length `2` has as vertices the twelve cyclic permutations of `(0, ±1, ±φ)`,
where `φ = (1 + √5)/2` is the golden ratio (`φ² = φ + 1`).  Every coordinate, every inner product of two
vertices, and every entry of a rotation of the icosahedron (times `2`) has the form `a + b φ` with integers
`a, b`.  We compute with such numbers exactly, as pairs of integers (`GInt`), and transfer to real numbers
with `GInt.toReal`, which is injective because `φ` is irrational.  This file holds the data: the twelve
vertices, the adjacency of vertices (inner product `φ`, i.e. distance `2`), three rotation matrices (orders
`2`, `3`, `5`), and the transfer lemmas for sums, products, inner products, matrix-vector products and
determinants.

Data computed by a Python script (not included; Lean checks the result).
-/

namespace UndergradKB.RepresentationTheory.Icosahedron

open Real Matrix

/-- Numbers `a + b φ` with integer `a`, `b`, where `φ` is the golden ratio. -/
structure GInt where
  a : ℤ
  b : ℤ
deriving DecidableEq

namespace GInt

instance : Add GInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg GInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub GInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
/-- Multiplication, using `φ² = φ + 1`. -/
instance : Mul GInt := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩
instance : Zero GInt := ⟨⟨0, 0⟩⟩

@[simp] theorem add_a (x y : GInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : GInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : GInt) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : GInt) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : GInt) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : GInt) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : GInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : GInt) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

/-- The real number `a + b φ`. -/
noncomputable def toReal (x : GInt) : ℝ := x.a + x.b * goldenRatio

theorem toReal_add (x y : GInt) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, add_a, add_b]; push_cast; ring

theorem toReal_neg (x : GInt) : (-x).toReal = -x.toReal := by
  simp only [toReal, neg_a, neg_b]; push_cast; ring

theorem toReal_sub (x y : GInt) : (x - y).toReal = x.toReal - y.toReal := by
  simp only [toReal, sub_a, sub_b]; push_cast; ring

theorem toReal_mul (x y : GInt) : (x * y).toReal = x.toReal * y.toReal := by
  simp only [toReal, mul_a, mul_b]; push_cast
  linear_combination (-(x.b : ℝ) * y.b) * goldenRatio_sq

theorem toReal_mk (a b : ℤ) : (⟨a, b⟩ : GInt).toReal = a + b * goldenRatio := rfl

theorem toReal_zero : (0 : GInt).toReal = 0 := by simp [toReal, show (0 : GInt) = ⟨0, 0⟩ from rfl]

theorem toReal_injective : Function.Injective toReal := by
  intro x y h
  have h' : ((x.a - y.a : ℤ) : ℝ) + ((x.b - y.b : ℤ) : ℝ) * goldenRatio = 0 := by
    simp only [toReal] at h; push_cast; linarith
  have hb : x.b - y.b = 0 := by
    by_contra hb
    exact ((goldenRatio_irrational.intCast_mul hb).intCast_add (x.a - y.a)).ne_zero h'
  have ha : x.a - y.a = 0 := by
    rw [hb] at h'; simp at h'; exact_mod_cast h'
  cases x; cases y; simp only [GInt.mk.injEq] at *; omega

end GInt

/-- Vectors with coordinates `a + b φ`. -/
abbrev GVec := Fin 3 → GInt
/-- `3 × 3` matrices with entries `a + b φ`. -/
abbrev GMat := Fin 3 → Fin 3 → GInt

/-- Inner product of exact vectors. -/
def gdot (u v : GVec) : GInt := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Matrix-vector product of exact matrices and vectors. -/
def gmv (M : GMat) (v : GVec) : GVec := fun i => gdot (M i) v

/-- Matrix product of exact matrices. -/
def gmm (M N : GMat) : GMat := fun i j => gdot (M i) fun k => N k j

/-- Determinant of an exact matrix (expansion along the first row). -/
def gdet (M : GMat) : GInt :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1) - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0) +
    M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

/-- Transpose of an exact matrix. -/
def gtr (M : GMat) : GMat := fun i j => M j i

/-- The real vector of an exact vector. -/
noncomputable def rvec (v : GVec) : Fin 3 → ℝ := fun i => (v i).toReal

/-- The real matrix of an exact matrix. -/
noncomputable def rmat (M : GMat) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (M i j).toReal

theorem rvec_injective : Function.Injective rvec := by
  intro u v h
  funext i
  exact GInt.toReal_injective (congrFun h i)

theorem dot_rvec (u v : GVec) : rvec u ⬝ᵥ rvec v = (gdot u v).toReal := by
  simp only [dotProduct, Fin.sum_univ_three, rvec, gdot, GInt.toReal_add, GInt.toReal_mul]

theorem mulVec_rvec (M : GMat) (v : GVec) : rmat M *ᵥ rvec v = rvec (gmv M v) := by
  funext i
  simp only [Matrix.mulVec, rmat, rvec, gmv, ← dot_rvec]
  rfl

theorem mul_rmat (M N : GMat) : rmat M * rmat N = rmat (gmm M N) := by
  ext i j
  simp only [Matrix.mul_apply, rmat, Matrix.of_apply, gmm, gdot, Fin.sum_univ_three, GInt.toReal_add,
    GInt.toReal_mul]

theorem transpose_rmat (M : GMat) : (rmat M)ᵀ = rmat (gtr M) := by
  ext i j; rfl

theorem det_rmat (M : GMat) : (rmat M).det = (gdet M).toReal := by
  rw [Matrix.det_fin_three]
  simp only [rmat, Matrix.of_apply, gdet, GInt.toReal_add, GInt.toReal_sub, GInt.toReal_mul]
  ring

/-! ### Vertices and adjacency -/

/-- The twelve vertices, the cyclic permutations of `(0, ±1, ±φ)`. -/
def gvtx : Fin 12 → GVec :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩],
    ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

/-- The vertices of the regular icosahedron, as points of `ℝ³`. -/
noncomputable def vtx (i : Fin 12) : Fin 3 → ℝ := rvec (gvtx i)

theorem gvtx_injective : Function.Injective gvtx := by decide

theorem vtx_injective : Function.Injective vtx := rvec_injective.comp gvtx_injective

/-- Two vertices are adjacent (joined by an edge) when their inner product is `φ`; equivalently their
distance is `2` (`gdist_eq_four_iff`). -/
def Adj (i j : Fin 12) : Prop := gdot (gvtx i) (gvtx j) = ⟨0, 1⟩

instance : DecidableRel Adj := fun i j => inferInstanceAs (Decidable (gdot (gvtx i) (gvtx j) = ⟨0, 1⟩))

/-- Squared distance of exact vectors. -/
def gsq (u v : GVec) : GInt := gdot (u - v) (u - v)

theorem gsq_eq_four_iff : ∀ i j : Fin 12, gsq (gvtx i) (gvtx j) = ⟨4, 0⟩ ↔ Adj i j := by decide

/-- Squared Euclidean distance in `ℝ³`. -/
def sqDist (v w : Fin 3 → ℝ) : ℝ := (v - w) ⬝ᵥ (v - w)

theorem rvec_sub (u v : GVec) : rvec (u - v) = rvec u - rvec v := by
  funext i; simp [rvec, GInt.toReal_sub]

theorem sqDist_vtx (i j : Fin 12) : sqDist (vtx i) (vtx j) = (gsq (gvtx i) (gvtx j)).toReal := by
  rw [sqDist, vtx, vtx, ← rvec_sub, dot_rvec, gsq]

/-- Two vertices are at distance `2` exactly when they are adjacent. -/
theorem sqDist_vtx_eq_four_iff (i j : Fin 12) : sqDist (vtx i) (vtx j) = 4 ↔ Adj i j := by
  rw [sqDist_vtx, ← gsq_eq_four_iff]
  constructor
  · intro h; apply GInt.toReal_injective; rw [h, GInt.toReal_mk]; simp
  · intro h; rw [h, GInt.toReal_mk]; simp

/-! ### Three rotations (matrices times `2`) -/

/-- Twice the half-turn `diag(1, -1, -1)` about the first axis. -/
def gR2 : GMat := ![![⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩]]
/-- Twice the rotation of order `3` permuting the coordinates cyclically. -/
def gR3 : GMat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩]]
/-- Twice a rotation of order `5` about the vertex `vtx 0`. -/
def gR5 : GMat := ![![⟨-1, 1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩]]

/-- Twice the identity matrix, scaled: `4 · 1`. -/
def gFour : GMat := fun i j => if i = j then ⟨4, 0⟩ else ⟨0, 0⟩

theorem gR2_orth : gmm (gtr gR2) gR2 = gFour := by decide
theorem gR3_orth : gmm (gtr gR3) gR3 = gFour := by decide
theorem gR5_orth : gmm (gtr gR5) gR5 = gFour := by decide
theorem gR2_det : gdet gR2 = ⟨8, 0⟩ := by decide
theorem gR3_det : gdet gR3 = ⟨8, 0⟩ := by decide
theorem gR5_det : gdet gR5 = ⟨8, 0⟩ := by decide

/-- The matrix whose columns are the vertices `i, j, k`. -/
def gcols (i j k : Fin 12) : GMat := fun r c => gvtx (![i, j, k] c) r

theorem gdet_cols_012 : gdet (gcols 0 1 2) = ⟨2, 2⟩ := by decide
theorem gdet_cols_016 : gdet (gcols 0 1 6) = ⟨-2, -2⟩ := by decide

/-- The common neighbours of the vertices `0` and `1` are `2` and `6`. -/
theorem common_nbr_01 : ∀ k : Fin 12, Adj k 0 → Adj k 1 → k = 2 ∨ k = 6 := by decide

end UndergradKB.RepresentationTheory.Icosahedron
