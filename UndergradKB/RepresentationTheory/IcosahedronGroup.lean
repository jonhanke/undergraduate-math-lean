import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.IndexNormal
import UndergradKB.RepresentationTheory.IcosahedronData
import UndergradKB.RepresentationTheory.CharacterTableA5

/-! # The rotation group of the regular icosahedron is `A5`

The rotation group of the regular icosahedron is the group of rotations of `ℝ³` (orthogonal matrices of
determinant `1`) mapping its vertex set onto itself.  We prove that it is isomorphic to the alternating group
`A5 = alternatingGroup (Fin 5)` (`rotEquiv`), the fact recalled in Problem 3.21.

Method.
* Each rotation permutes the twelve vertices (`permHom`), preserving inner products, hence adjacency; a
  rotation is determined by its values on three vertices spanning `ℝ³`, so `permHom` is injective, and a
  rotation fixing the adjacent vertices `0` and `1` is the identity (it fixes or swaps their two common
  neighbours `2`, `6`; swapping would make its determinant `-1`).
* `A5` acts on the twelve vertices through conjugation of the labels `lab i ∈ A5` (`psi`); the label of a
  vertex is the image in `A5` of the rotation by `2π/5` about it, `A5` being seen as the group of even
  permutations of the five inscribed octahedral frames (computed in a Python script (not included; Lean checks the result), used here
  only as data).
* Three explicit rotations of orders `2`, `3`, `5` act on vertices as `psi` of elements of `A5`; the elements of
  `A5` so realized form a subgroup of order divisible by `30`, hence all of `A5` (a subgroup of index `2` would
  be normal, and `A5` is simple).  Conversely every rotation agrees with some `psi g` on the directed edge
  `(0, 1)` (`A5` is transitive on directed edges), hence equals it.
-/

namespace UndergradKB.RepresentationTheory.Icosahedron

open Matrix Equiv A5Table

/-! ### `A5` acting on vertex labels -/

theorem mem_alt {σ : Perm (Fin 5)} (h : Perm.sign σ = 1) : σ ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]; exact h

/-- The label of each vertex: an element of order `5` of `A5` (one conjugacy class of `12` elements). -/
def lab : Fin 12 → A5 :=
  ![⟨swap 0 1 * swap 1 4 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 4 * swap 1 3 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 3 * swap 1 2 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 1 * swap 1 3 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 3 * swap 1 2 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 2 * swap 1 2 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 2 * swap 1 4 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 4 * swap 1 4 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 3 * swap 1 3 * swap 2 4 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 2 * swap 1 4 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩,
    ⟨swap 0 4 * swap 1 3 * swap 2 3 * swap 3 4, mem_alt (by decide)⟩]

/-- The index of a label (`0` if `x` is not a label). -/
def idx (x : A5) : Fin 12 := ((List.finRange 12).find? fun j => decide (lab j = x)).getD 0

/-- The action of `A5` on vertices, by conjugating labels. -/
def psiFun (g : A5) (i : Fin 12) : Fin 12 := idx (g * lab i * g⁻¹)

theorem lab_psiFun : ∀ g : A5, ∀ i : Fin 12, lab (psiFun g i) = g * lab i * g⁻¹ := by decide +kernel

theorem lab_injective : Function.Injective lab := by decide +kernel

theorem psiFun_mul (g h : A5) (i : Fin 12) : psiFun (g * h) i = psiFun g (psiFun h i) := by
  apply lab_injective
  rw [lab_psiFun, lab_psiFun, lab_psiFun]; group

theorem psiFun_one (i : Fin 12) : psiFun 1 i = i := by
  apply lab_injective; rw [lab_psiFun]; group

/-- `A5` acting on the twelve vertices. -/
def psi : A5 →* Perm (Fin 12) where
  toFun g :=
    { toFun := psiFun g
      invFun := psiFun g⁻¹
      left_inv := fun i => by rw [← psiFun_mul, inv_mul_cancel, psiFun_one]
      right_inv := fun i => by rw [← psiFun_mul, mul_inv_cancel, psiFun_one] }
  map_one' := by ext i; exact congrArg Fin.val (psiFun_one i)
  map_mul' g h := by ext i; exact congrArg Fin.val (psiFun_mul g h i)

@[simp] theorem psi_apply (g : A5) (i : Fin 12) : psi g i = psiFun g i := rfl

theorem psiFun_eq_id : ∀ g : A5, (∀ i, psiFun g i = i) → g = 1 := by decide +kernel

theorem psi_injective : Function.Injective psi := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact psiFun_eq_id g fun i => by simpa using congrArg (fun σ : Perm (Fin 12) => σ i) hg

/-- `A5` is transitive on directed edges. -/
theorem psi_directed : ∀ i j : Fin 12, Adj i j → ∃ g : A5, psiFun g 0 = i ∧ psiFun g 1 = j := by
  decide +kernel

/-! ### The rotation group -/

/-- The rotations of `ℝ³`: orthogonal `3 × 3` real matrices of determinant `1`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- The vertex set of the regular icosahedron. -/
noncomputable def vertexSet : Set (Fin 3 → ℝ) := Set.range vtx

theorem star_eq_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) : star A = Aᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem SO3.transpose_mul_self (A : SO3) : (A : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * A = 1 := by
  rw [← star_eq_transpose]; exact (Matrix.mem_unitaryGroup_iff'.1 A.2.1)

theorem SO3.det_eq_one (A : SO3) : (A : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := A.2.2

theorem SO3.coe_inv (A : SO3) : ((A⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = (A : Matrix _ _ ℝ)ᵀ := by
  rw [← star_eq_transpose]; rfl

/-- Rotations preserve inner products. -/
theorem SO3.dot_mulVec (A : SO3) (v w : Fin 3 → ℝ) :
    ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) ⬝ᵥ ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, SO3.transpose_mul_self, one_mulVec]

/-- The **rotation group of the regular icosahedron**: rotations mapping its vertex set onto itself. -/
def rotGroup : Subgroup SO3 where
  carrier := {A | (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet}
  one_mem' := by
    show (fun v => (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet
    simp
  mul_mem' {A B} hA hB := by
    change (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet at hA
    change (fun v => (B : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet at hB
    change (fun v => ((A : Matrix (Fin 3) (Fin 3) ℝ) * (B : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ v) ''
      vertexSet = vertexSet
    simp_rw [← mulVec_mulVec]
    rw [← Set.image_image (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v), hB, hA]
  inv_mem' {A} hA := by
    change (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet at hA
    change (fun v => ((A⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet
    rw [SO3.coe_inv]
    conv_lhs => rw [← hA]
    rw [Set.image_image]
    simp_rw [mulVec_mulVec, SO3.transpose_mul_self, one_mulVec, Set.image_id']

/-- The matrix of an element of the rotation group. -/
abbrev mat (A : rotGroup) : Matrix (Fin 3) (Fin 3) ℝ := ((A : SO3) : Matrix (Fin 3) (Fin 3) ℝ)

theorem mat_mul (A B : rotGroup) : mat (A * B) = mat A * mat B := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem exists_vtx (A : rotGroup) (i : Fin 12) : ∃ j, mat A *ᵥ vtx i = vtx j := by
  have h : mat A *ᵥ vtx i ∈ (fun v => mat A *ᵥ v) '' vertexSet := ⟨vtx i, ⟨i, rfl⟩, rfl⟩
  rw [A.2] at h
  obtain ⟨j, hj⟩ := h
  exact ⟨j, hj.symm⟩

/-- The vertex to which a rotation sends vertex `i`. -/
noncomputable def vmap (A : rotGroup) (i : Fin 12) : Fin 12 := (exists_vtx A i).choose

theorem mat_vtx (A : rotGroup) (i : Fin 12) : mat A *ᵥ vtx i = vtx (vmap A i) :=
  (exists_vtx A i).choose_spec

theorem vmap_mul (A B : rotGroup) (i : Fin 12) : vmap (A * B) i = vmap A (vmap B i) := by
  apply vtx_injective
  rw [← mat_vtx, ← mat_vtx, ← mat_vtx, mat_mul, ← mulVec_mulVec]

theorem vmap_one (i : Fin 12) : vmap 1 i = i := by
  apply vtx_injective; rw [← mat_vtx, mat_one, one_mulVec]

/-- The rotation group acting on the twelve vertices. -/
noncomputable def permHom : rotGroup →* Perm (Fin 12) where
  toFun A :=
    { toFun := vmap A
      invFun := vmap A⁻¹
      left_inv := fun i => by rw [← vmap_mul, inv_mul_cancel, vmap_one]
      right_inv := fun i => by rw [← vmap_mul, mul_inv_cancel, vmap_one] }
  map_one' := by ext i; exact congrArg Fin.val (vmap_one i)
  map_mul' A B := by ext i; exact congrArg Fin.val (vmap_mul A B i)

@[simp] theorem permHom_apply (A : rotGroup) (i : Fin 12) : permHom A i = vmap A i := rfl

theorem gdot_vmap (A : rotGroup) (i j : Fin 12) :
    gdot (gvtx (vmap A i)) (gvtx (vmap A j)) = gdot (gvtx i) (gvtx j) := by
  apply GInt.toReal_injective
  rw [← dot_rvec, ← dot_rvec]
  change vtx (vmap A i) ⬝ᵥ vtx (vmap A j) = vtx i ⬝ᵥ vtx j
  rw [← mat_vtx, ← mat_vtx]
  exact SO3.dot_mulVec _ _ _

/-- Rotations preserve adjacency. -/
theorem adj_vmap (A : rotGroup) {i j : Fin 12} (h : Adj i j) : Adj (vmap A i) (vmap A j) := by
  unfold Adj at h ⊢; rw [gdot_vmap]; exact h

/-! ### A rotation is determined on three vertices -/

theorem mul_gcols (A : Matrix (Fin 3) (Fin 3) ℝ) (i j k : Fin 12) :
    A * rmat (gcols i j k) = Matrix.of fun r c => (A *ᵥ vtx (![i, j, k] c)) r := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, rmat, gcols, vtx, rvec]

theorem det_gcols_012 : IsUnit (rmat (gcols 0 1 2)).det := by
  rw [det_rmat, gdet_cols_012, GInt.toReal_mk]
  have := Real.goldenRatio_pos
  exact isUnit_iff_ne_zero.2 (by push_cast; positivity)

theorem eq_of_vtx_012 (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ c : Fin 3, A *ᵥ vtx (![0, 1, 2] c) = B *ᵥ vtx (![0, 1, 2] c)) : A = B := by
  have hC : A * rmat (gcols 0 1 2) = B * rmat (gcols 0 1 2) := by
    rw [mul_gcols, mul_gcols]; ext r c; rw [Matrix.of_apply, Matrix.of_apply, h c]
  calc A = A * rmat (gcols 0 1 2) * (rmat (gcols 0 1 2))⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ det_gcols_012, Matrix.mul_one]
    _ = B := by rw [hC, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ det_gcols_012, Matrix.mul_one]

theorem adj_01 : Adj 0 1 := by decide
theorem adj_20 : Adj 2 0 := by decide
theorem adj_21 : Adj 2 1 := by decide

/-- A rotation of the icosahedron fixing the adjacent vertices `0` and `1` is the identity. -/
theorem eq_one_of_fix_01 (A : rotGroup) (h0 : vmap A 0 = 0) (h1 : vmap A 1 = 1) : A = 1 := by
  have h2 : vmap A 2 = 2 ∨ vmap A 2 = 6 := by
    apply common_nbr_01
    · have := adj_vmap A adj_20; rwa [h0] at this
    · have := adj_vmap A adj_21; rwa [h1] at this
  rcases h2 with h2 | h2
  · have : mat A = 1 := by
      apply eq_of_vtx_012
      intro c
      fin_cases c <;> simp [mat_vtx, h0, h1, h2]
    exact Subtype.ext (Subtype.ext this)
  · exfalso
    have hC : mat A * rmat (gcols 0 1 2) = rmat (gcols 0 1 6) := by
      rw [mul_gcols, ← Matrix.one_mul (rmat (gcols 0 1 6)), mul_gcols]
      ext r c
      fin_cases c <;> simp [mat_vtx, h0, h1, h2]
    have hd := congrArg Matrix.det hC
    rw [Matrix.det_mul, SO3.det_eq_one, one_mul, det_rmat, det_rmat, gdet_cols_012, gdet_cols_016] at hd
    exact absurd (GInt.toReal_injective hd) (by decide)

theorem permHom_injective : Function.Injective permHom := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply eq_one_of_fix_01
  · simpa using congrArg (fun σ : Perm (Fin 12) => σ 0) hA
  · simpa using congrArg (fun σ : Perm (Fin 12) => σ 1) hA

/-! ### Three rotations -/

/-- The rotation with twice its matrix equal to `N`, when it maps every vertex `i` to `σ i`. -/
theorem mem_rotGroup_of_perm (A : SO3) (σ : Perm (Fin 12))
    (h : ∀ i, (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vtx i = vtx (σ i)) : A ∈ rotGroup := by
  show (fun v => (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' vertexSet = vertexSet
  ext v
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨σ i, (h i).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨vtx (σ.symm j), ⟨_, rfl⟩, (h _).trans (by rw [Equiv.apply_symm_apply])⟩

theorem rmat_gFour : rmat gFour = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat, gFour, GInt.toReal_mk]

theorem half_mem_SO3 (N : GMat) (hN : gmm (gtr N) N = gFour) (hd : gdet N = ⟨8, 0⟩) :
    (1 / 2 : ℝ) • rmat N ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_transpose, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, transpose_rmat, mul_rmat, hN, rmat_gFour, smul_smul, smul_smul]
    norm_num
  · rw [Matrix.det_smul, det_rmat, hd, GInt.toReal_mk]
    norm_num

/-- Twice a vector. -/
def gtwo (v : GVec) : GVec := fun r => v r + v r

theorem rvec_gtwo (v : GVec) : rvec (gtwo v) = (2 : ℝ) • rvec v := by
  funext r; simp [rvec, gtwo, GInt.toReal_add]; ring

theorem half_mulVec_vtx (N : GMat) (i j : Fin 12) (h : gmv N (gvtx i) = gtwo (gvtx j)) :
    ((1 / 2 : ℝ) • rmat N) *ᵥ vtx i = vtx j := by
  rw [Matrix.smul_mulVec, vtx, mulVec_rvec, h, rvec_gtwo, smul_smul]
  norm_num; rfl

/-- The elements of `A5` realized by the three rotations. -/
def g2 : A5 := ⟨swap 0 2 * swap 1 4, mem_alt (by decide)⟩
def g3 : A5 := ⟨swap 0 2 * swap 1 2, mem_alt (by decide)⟩
def g5 : A5 := lab 0

theorem gR2_act : ∀ i, gmv gR2 (gvtx i) = gtwo (gvtx (psiFun g2 i)) := by decide +kernel
theorem gR3_act : ∀ i, gmv gR3 (gvtx i) = gtwo (gvtx (psiFun g3 i)) := by decide +kernel
theorem gR5_act : ∀ i, gmv gR5 (gvtx i) = gtwo (gvtx (psiFun g5 i)) := by decide +kernel

/-- An element `g` of `A5` is realized when some rotation acts on vertices as `psi g`. -/
theorem realized (N : GMat) (hN : gmm (gtr N) N = gFour) (hd : gdet N = ⟨8, 0⟩) (g : A5)
    (h : ∀ i, gmv N (gvtx i) = gtwo (gvtx (psiFun g i))) : ∃ A : rotGroup, permHom A = psi g := by
  let B : SO3 := ⟨_, half_mem_SO3 N hN hd⟩
  have hB : ∀ i, (B : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vtx i = vtx (psi g i) :=
    fun i => half_mulVec_vtx N i _ (h i)
  refine ⟨⟨B, mem_rotGroup_of_perm B (psi g) hB⟩, ?_⟩
  ext i
  simp only [permHom_apply]
  congr 1
  apply vtx_injective
  rw [← mat_vtx]
  exact hB i

/-! ### Every element of `A5` is realized -/

theorem orderOf_g2 : orderOf g2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_g3 : orderOf g3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_g5 : orderOf g5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- The elements of `A5` acting on the vertices as some rotation does. -/
noncomputable def realizedSub : Subgroup A5 := (permHom.range).comap psi

theorem dvd_card_realized {g : A5} (hg : g ∈ realizedSub) : orderOf g ∣ Nat.card realizedSub := by
  have := orderOf_dvd_natCard (⟨g, hg⟩ : realizedSub)
  rwa [Subgroup.orderOf_mk] at this

theorem realizedSub_eq_top : realizedSub = ⊤ := by
  have m2 : g2 ∈ realizedSub := by
    obtain ⟨A, hA⟩ := realized gR2 gR2_orth gR2_det g2 gR2_act; exact ⟨A, hA⟩
  have m3 : g3 ∈ realizedSub := by
    obtain ⟨A, hA⟩ := realized gR3 gR3_orth gR3_det g3 gR3_act; exact ⟨A, hA⟩
  have m5 : g5 ∈ realizedSub := by
    obtain ⟨A, hA⟩ := realized gR5 gR5_orth gR5_det g5 gR5_act; exact ⟨A, hA⟩
  have d2 := dvd_card_realized m2
  have d3 := dvd_card_realized m3
  have d5 := dvd_card_realized m5
  rw [orderOf_g2] at d2; rw [orderOf_g3] at d3; rw [orderOf_g5] at d5
  have d30 : 30 ∣ Nat.card realizedSub := by
    have d6 : 6 ∣ Nat.card realizedSub := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 d3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d6 d5
  have d60 : Nat.card realizedSub ∣ 60 := card_A5 ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := d30
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact absurd (hk ▸ d60) (by norm_num)
  have hk2 : k ≤ 2 := by
    have := Nat.le_of_dvd (by norm_num) d60; omega
  obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
  · exfalso
    have hidx : realizedSub.index = 2 := by
      have := realizedSub.card_mul_index
      rw [hk, card_A5] at this; omega
    have hn := Subgroup.normal_of_index_eq_two hidx
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hk; omega
    · rw [h, Subgroup.card_top, card_A5] at hk; omega
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hk, card_A5])

theorem exists_realized (g : A5) : ∃ A : rotGroup, permHom A = psi g := by
  have : g ∈ realizedSub := realizedSub_eq_top ▸ Subgroup.mem_top g
  exact this

theorem range_eq : psi.range = permHom.range := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨A, hA⟩ := exists_realized g
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    obtain ⟨g, hg0, hg1⟩ := psi_directed _ _ (adj_vmap A adj_01)
    obtain ⟨B, hB⟩ := exists_realized g
    have : B⁻¹ * A = 1 := by
      apply eq_one_of_fix_01
      · rw [vmap_mul]
        have : vmap B 0 = vmap A 0 := by rw [← permHom_apply, hB]; exact hg0
        rw [← this, ← vmap_mul, inv_mul_cancel, vmap_one]
      · rw [vmap_mul]
        have : vmap B 1 = vmap A 1 := by rw [← permHom_apply, hB]; exact hg1
        rw [← this, ← vmap_mul, inv_mul_cancel, vmap_one]
    rw [inv_mul_eq_one] at this
    exact ⟨g, by rw [← hB, this]⟩

/-- **The rotation group of the regular icosahedron is isomorphic to `A5`.** -/
noncomputable def rotEquiv : A5 ≃* rotGroup :=
  (MonoidHom.ofInjective psi_injective).trans
    ((MulEquiv.subgroupCongr range_eq).trans (MonoidHom.ofInjective permHom_injective).symm)

theorem permHom_rotEquiv (g : A5) : permHom (rotEquiv g) = psi g := by
  have := MonoidHom.ofInjective_apply permHom_injective (x := rotEquiv g)
  have h2 : MonoidHom.ofInjective permHom_injective (rotEquiv g) =
      MulEquiv.subgroupCongr range_eq (MonoidHom.ofInjective psi_injective g) := by
    simp [rotEquiv]
  rw [h2] at this
  rw [← this]
  rfl

theorem vmap_rotEquiv (g : A5) (i : Fin 12) : vmap (rotEquiv g) i = psiFun g i := by
  rw [← permHom_apply, permHom_rotEquiv, psi_apply]

/-- The rotation group of the regular icosahedron is isomorphic to `A5` (the fact recalled in Problem 3.21). -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem rotGroup_iso_A5 : Nonempty (rotGroup ≃* alternatingGroup (Fin 5)) := ⟨rotEquiv.symm⟩

end UndergradKB.RepresentationTheory.Icosahedron
