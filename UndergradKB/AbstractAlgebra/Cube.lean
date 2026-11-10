import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.IntervalCases
import UndergradKB.Common.Attr

/-!
# The rotation group of the cube

Model: the cube is `[-1,1]^3` with vertex set `{±1}^3`.  Its group of rotations is the group of
integer `3 × 3` matrices `A` with `A * Aᵀ = 1` and `det A = 1`, that is Mathlib's
`Matrix.specialOrthogonalGroup (Fin 3) ℤ` (an integer orthogonal matrix is automatically a signed
permutation matrix, hence preserves the vertex set).

The four long diagonals are the vertex pairs `{v, -v}`; they are indexed by `Fin 4` through the
representatives `vtx k` with first coordinate `1`.  The action of a rotation on the diagonals gives
a homomorphism `cubeToPerm` to `Equiv.Perm (Fin 4)`, which is bijective (Judson–Beezer, Prop. 5.2.8
and Thm. 5.2.9): the rotation group has 24 elements and is isomorphic to `S₄`.
-/

namespace UndergradKB.AbstractAlgebra

open Matrix

/-- The rotation group of the cube `[-1,1]^3`: integer orthogonal matrices of determinant `1`. -/
abbrev CubeRotations : Type := ↥(Matrix.specialOrthogonalGroup (Fin 3) ℤ)

namespace Cube

/-- The vertex predicate: all coordinates are `±1`. -/
def IsV (w : Fin 3 → ℤ) : Prop := ∀ i, w i = 1 ∨ w i = -1

/-- Representatives (with first coordinate `1`) of the four long diagonals. -/
def vtx : Fin 4 → Fin 3 → ℤ := ![![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1]]

/-- Index of the diagonal through a vertex. -/
def idx (w : Fin 3 → ℤ) : Fin 4 :=
  (if w 0 * w 1 = 1 then 0 else 2) + (if w 0 * w 2 = 1 then 0 else 1)

lemma vtx_isV (k : Fin 4) : IsV (vtx k) := by
  intro i
  fin_cases k <;> fin_cases i <;> simp [vtx]

lemma idx_vtx (k : Fin 4) : idx (vtx k) = k := by
  fin_cases k <;> simp [idx, vtx]

lemma idx_smul (s : ℤ) (hs : s = 1 ∨ s = -1) (w : Fin 3 → ℤ) : idx (s • w) = idx w := by
  rcases hs with rfl | rfl <;> simp [idx]

lemma vertex_eq {w : Fin 3 → ℤ} (hw : IsV w) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ w = s • vtx (idx w) := by
  refine ⟨w 0, hw 0, ?_⟩
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  funext i
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    fin_cases i <;> simp [idx, vtx, h0, h1, h2]

lemma aux (a b c x y z : ℤ) (h : a * a + b * b + c * c = 1) (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (hz : z = 1 ∨ z = -1) :
    a * x + b * y + c * z = 1 ∨ a * x + b * y + c * z = -1 := by
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [mul_self_nonneg b, mul_self_nonneg c]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [mul_self_nonneg a, mul_self_nonneg c]
  have hc : -1 ≤ c ∧ c ≤ 1 := by constructor <;> nlinarith [mul_self_nonneg a, mul_self_nonneg b]
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> omega

lemma rowsq (A : CubeRotations) (i : Fin 3) :
    A.1 i 0 * A.1 i 0 + A.1 i 1 * A.1 i 1 + A.1 i 2 * A.1 i 2 = 1 := by
  have h := A.2
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff] at h
  have := congrFun (congrFun h.1 i) i
  simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply] using this

lemma mulVec_isV (A : CubeRotations) {w : Fin 3 → ℤ} (hw : IsV w) : IsV (A.1 *ᵥ w) := by
  intro i
  have := aux (A.1 i 0) (A.1 i 1) (A.1 i 2) (w 0) (w 1) (w 2) (rowsq A i) (hw 0) (hw 1) (hw 2)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this

/-- The action of the rotation group on the four diagonals. -/
instance : MulAction CubeRotations (Fin 4) where
  smul A k := idx (A.1 *ᵥ vtx k)
  one_smul k := by
    show idx ((1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ vtx k) = k
    simpa using idx_vtx k
  mul_smul A B k := by
    show idx (((A * B : CubeRotations) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ vtx k) =
      idx (A.1 *ᵥ vtx (idx (B.1 *ᵥ vtx k)))
    obtain ⟨s, hs, e⟩ := vertex_eq (mulVec_isV B (vtx_isV k))
    have : ((A * B : CubeRotations) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ vtx k =
        s • (A.1 *ᵥ vtx (idx (B.1 *ᵥ vtx k))) := by
      rw [← Matrix.mulVec_smul, ← e]
      exact (Matrix.mulVec_mulVec _ _ _).symm
    rw [this, idx_smul s hs]

lemma smul_def (A : CubeRotations) (k : Fin 4) : A • k = idx (A.1 *ᵥ vtx k) := rfl

/-- The homomorphism from the cube rotations to the permutations of the four diagonals. -/
def cubeToPerm : CubeRotations →* Equiv.Perm (Fin 4) := MulAction.toPermHom CubeRotations (Fin 4)

lemma cubeToPerm_apply (A : CubeRotations) (k : Fin 4) : cubeToPerm A k = idx (A.1 *ᵥ vtx k) := rfl

lemma cubeToPerm_injective : Function.Injective cubeToPerm := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hk : ∀ k, A • k = k := fun k => by
    have : cubeToPerm A k = k := by rw [hA]; rfl
    exact this
  have key : ∀ k : Fin 4, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ A.1 *ᵥ vtx k = s • vtx k := by
    intro k
    obtain ⟨s, hs, e⟩ := vertex_eq (mulVec_isV A (vtx_isV k))
    refine ⟨s, hs, ?_⟩
    have := hk k
    rw [smul_def] at this
    rw [this] at e
    exact e
  obtain ⟨s0, hs0, e0⟩ := key 0
  obtain ⟨s1, hs1, e1⟩ := key 1
  obtain ⟨s2, hs2, e2⟩ := key 2
  obtain ⟨s3, hs3, e3⟩ := key 3
  have f0 : ∀ i, (A.1 *ᵥ vtx 0) i = (s0 • vtx 0) i := fun i => by rw [e0]
  have f1 : ∀ i, (A.1 *ᵥ vtx 1) i = (s1 • vtx 1) i := fun i => by rw [e1]
  have f2 : ∀ i, (A.1 *ᵥ vtx 2) i = (s2 • vtx 2) i := fun i => by rw [e2]
  have f3 : ∀ i, (A.1 *ᵥ vtx 3) i = (s3 • vtx 3) i := fun i => by rw [e3]
  have a0 := f0 0
  have a1 := f0 1
  have a2 := f0 2
  have b0 := f1 0
  have b1 := f1 1
  have b2 := f1 2
  have c0 := f2 0
  have c1 := f2 1
  have c2 := f2 2
  have d0 := f3 0
  have d1 := f3 1
  have d2 := f3 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, vtx] at a0 a1 a2 b0 b1 b2 c0 c1 c2 d0 d1 d2
  have hd := A.2
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hd
  have hdet := hd.2
  rw [Matrix.det_fin_three] at hdet
  have goal : A.1 0 0 = A.1 1 1 ∧ A.1 1 1 = A.1 2 2 ∧ A.1 0 1 = 0 ∧ A.1 0 2 = 0 ∧ A.1 1 0 = 0 ∧
      A.1 1 2 = 0 ∧ A.1 2 0 = 0 ∧ A.1 2 1 = 0 ∧ (A.1 0 0 = 1 ∨ A.1 0 0 = -1) := by
    rcases hs0 with rfl | rfl <;> rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      rcases hs3 with rfl | rfl <;> omega
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := goal
  rw [g3, g4, g5, g6, g7, g8] at hdet
  have hone : A.1 0 0 = 1 := by
    rcases g9 with h | h
    · exact h
    · have e1 : A.1 1 1 = -1 := by omega
      have e2 : A.1 2 2 = -1 := by omega
      rw [h, e1, e2] at hdet
      norm_num at hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- Quarter turn about the third coordinate axis. -/
def rotZ : CubeRotations :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
    · simp [Matrix.det_fin_three]⟩

/-- Half turn about an axis through midpoints of opposite edges. -/
def rotE : CubeRotations :=
  ⟨!![-1, 0, 0; 0, 0, 1; 0, 1, 0], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
    · simp [Matrix.det_fin_three]⟩

lemma cubeToPerm_rotZ : cubeToPerm rotZ = c[0, 3, 1, 2] := by
  ext k
  fin_cases k <;>
    simp [cubeToPerm_apply, rotZ, idx, vtx, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    decide

lemma cubeToPerm_rotE : cubeToPerm rotE = Equiv.swap 0 3 := by
  ext k
  fin_cases k <;>
    simp [cubeToPerm_apply, rotE, idx, vtx, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    decide

lemma cubeToPerm_surjective : Function.Surjective cubeToPerm := by
  have hcyc : (c[0, 3, 1, 2] : Equiv.Perm (Fin 4)).IsCycle :=
    List.isCycle_formPerm (l := [0, 3, 1, 2]) (by decide) (by decide)
  have hsupp : (c[0, 3, 1, 2] : Equiv.Perm (Fin 4)).support = Finset.univ := by decide
  have h := Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp 0
  have h3 : (c[0, 3, 1, 2] : Equiv.Perm (Fin 4)) 0 = 3 := by decide
  rw [h3] at h
  have hle : Subgroup.closure ({c[0, 3, 1, 2], Equiv.swap 0 3} : Set (Equiv.Perm (Fin 4))) ≤
      cubeToPerm.range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨rotZ, cubeToPerm_rotZ⟩
    · exact ⟨rotE, cubeToPerm_rotE⟩
  rw [h] at hle
  intro σ
  exact hle (Subgroup.mem_top σ)

lemma cubeToPerm_bijective : Function.Bijective cubeToPerm :=
  ⟨cubeToPerm_injective, cubeToPerm_surjective⟩

end Cube

open Cube in
/-- AA-077. The cube rotation group is isomorphic to `S₄`, via its action on the four long
diagonals. -/
@[kb "judson2026" "Theorem 5.2.9, p. 83"]
noncomputable def cubeRotationsEquivPerm : CubeRotations ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective cubeToPerm cubeToPerm_bijective

open Cube in
/-- AA-077. The group of rotations of the cube has 24 elements. -/
@[kb "judson2026" "Proposition 5.2.8, p. 83"]
theorem card_cubeRotations : Nat.card CubeRotations = 24 := by
  rw [Nat.card_congr cubeRotationsEquivPerm.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm]
  rfl

end UndergradKB.AbstractAlgebra
