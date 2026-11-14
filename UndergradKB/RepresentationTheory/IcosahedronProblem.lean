import Mathlib.Data.Set.Card
import UndergradKB.RepresentationTheory.IcosahedronGroup
import UndergradKB.RepresentationTheory.ProblemIcosahedron

/-! # Problem 3.21 for the geometric icosahedron

The rotation group `rotGroup` of the regular icosahedron (rotations of `ℝ³` mapping its vertex set onto itself)
acts on its `12` vertices, its `30` edges and its `20` faces.  An edge is recorded as the set of its two
endpoints and a face as the set of its three corners: a set of `2` (resp. `3`) vertices at mutual distance `2`
(the edge length).  For the icosahedron every such triple of vertices spans a face (there are `20` of them).

We prove that the rotation group acts transitively on each of the three sets and, with the isomorphism
`rotEquiv : A5 ≃* rotGroup` of `IcosahedronGroup.lean`, deduce from `ProblemIcosahedron.lean` the
decompositions asked in Problem 3.21: the characters of the permutation representations on the complex
functions on vertices, edges and faces are `1 + 5 + 3 + 3'`, `1 + 2·4 + 3·5 + 3 + 3'` and `1 + 2·4 + 5 + 3 + 3'`.
-/

namespace UndergradKB.RepresentationTheory.Icosahedron

open Matrix Equiv A5Table A5Induced Representation

theorem mat_mem (A : rotGroup) {v : Fin 3 → ℝ} (hv : v ∈ vertexSet) : mat A *ᵥ v ∈ vertexSet := by
  have hA : (fun v => mat A *ᵥ v) '' vertexSet = vertexSet := A.2
  rw [← hA]; exact ⟨v, hv, rfl⟩

theorem mat_injective (A : rotGroup) : Function.Injective fun v : Fin 3 → ℝ => mat A *ᵥ v := by
  intro v w h
  have h' := congrArg (fun u => (mat A)ᵀ *ᵥ u) h
  simpa only [mulVec_mulVec, SO3.transpose_mul_self, one_mulVec] using h'

theorem sqDist_mat (A : rotGroup) (v w : Fin 3 → ℝ) : sqDist (mat A *ᵥ v) (mat A *ᵥ w) = sqDist v w := by
  unfold sqDist; rw [← mulVec_sub]; exact SO3.dot_mulVec _ _ _

/-! ### Vertices -/

/-- The vertices of the regular icosahedron, as a type. -/
abbrev Vert : Type := ↥vertexSet

instance : MulAction rotGroup Vert where
  smul A v := ⟨mat A *ᵥ v.1, mat_mem A v.2⟩
  one_smul v := Subtype.ext (one_mulVec v.1)
  mul_smul A B v := Subtype.ext (mulVec_mulVec v.1 (mat A) (mat B)).symm

theorem coe_smul_vert (A : rotGroup) (v : Vert) : ((A • v : Vert) : Fin 3 → ℝ) = mat A *ᵥ v.1 := rfl

instance : Finite Vert := Set.finite_range vtx |>.to_subtype

noncomputable instance : Fintype Vert := Fintype.ofFinite _

noncomputable instance : DecidableEq Vert := Classical.decEq _

theorem card_vert : Fintype.card Vert = 12 := by
  rw [Fintype.card_eq_nat_card]
  exact (Nat.card_range_of_injective vtx_injective).trans (by simp)

/-- The vertex `vtx 0` as an element of `Vert`. -/
noncomputable def vert0 : Vert := ⟨vtx 0, 0, rfl⟩

theorem mat_vtx_rotEquiv (g : A5) (i : Fin 12) : mat (rotEquiv g) *ᵥ vtx i = vtx (psiFun g i) := by
  rw [mat_vtx, vmap_rotEquiv]

theorem psi_transitive : ∀ i : Fin 12, ∃ g : A5, psiFun g 0 = i := by decide +kernel

/-- The rotation group acts transitively on the vertices. -/
theorem transitive_vert (v : Vert) : ∃ g : A5, rotEquiv g • vert0 = v := by
  obtain ⟨_, i, rfl⟩ := v
  obtain ⟨g, hg⟩ := psi_transitive i
  exact ⟨g, Subtype.ext (by rw [coe_smul_vert, vert0, mat_vtx_rotEquiv, hg])⟩

/-! ### Edges and faces -/

/-- A set of `k` vertices at mutual distance `2`: an edge for `k = 2`, a face for `k = 3`. -/
def IsCell (k : ℕ) (s : Set (Fin 3 → ℝ)) : Prop :=
  s ⊆ vertexSet ∧ s.ncard = k ∧ s.Pairwise fun v w => sqDist v w = 4

/-- The cells of size `k`. -/
abbrev Cell (k : ℕ) : Type := {s : Set (Fin 3 → ℝ) // IsCell k s}

/-- The edges of the regular icosahedron, each recorded by its two endpoints. -/
abbrev Edge : Type := Cell 2

/-- The faces of the regular icosahedron, each recorded by its three corners. -/
abbrev Face : Type := Cell 3

theorem isCell_image (A : rotGroup) {k : ℕ} {s : Set (Fin 3 → ℝ)} (hs : IsCell k s) :
    IsCell k ((fun v => mat A *ᵥ v) '' s) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact mat_mem A (hs.1 hv)
  · rw [Set.ncard_image_of_injective _ (mat_injective A)]; exact hs.2.1
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hne
    rw [sqDist_mat]
    exact hs.2.2 hv hw fun h => hne (by rw [h])

instance (k : ℕ) : MulAction rotGroup (Cell k) where
  smul A s := ⟨(fun v => mat A *ᵥ v) '' s.1, isCell_image A s.2⟩
  one_smul s := Subtype.ext (by
    change (fun v => (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) '' s.1 = s.1
    simp)
  mul_smul A B s := Subtype.ext (by
    change (fun v => (mat A * mat B) *ᵥ v) '' s.1 = (fun v => mat A *ᵥ v) '' ((fun v => mat B *ᵥ v) '' s.1)
    rw [Set.image_image]; simp_rw [mulVec_mulVec])

theorem coe_smul_cell (A : rotGroup) {k : ℕ} (s : Cell k) :
    ((A • s : Cell k) : Set (Fin 3 → ℝ)) = (fun v => mat A *ᵥ v) '' s.1 := rfl

/-! ### Counting edges and faces -/

/-- The sets of `k` mutually adjacent vertex indices. -/
def cellFinset (k : ℕ) : Finset (Finset (Fin 12)) :=
  (Finset.univ.powersetCard k).filter fun t => ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Adj i j

theorem card_cellFinset_two : (cellFinset 2).card = 30 := by decide +kernel

theorem card_cellFinset_three : (cellFinset 3).card = 20 := by decide +kernel

theorem isCell_of_mem {k : ℕ} {t : Finset (Fin 12)} (ht : t ∈ cellFinset k) :
    IsCell k (vtx '' (t : Set (Fin 12))) := by
  simp only [cellFinset, Finset.mem_filter, Finset.mem_powersetCard] at ht
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rw [Set.ncard_image_of_injective _ vtx_injective, Set.ncard_coe_finset]; exact ht.1.2
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
    rw [sqDist_vtx_eq_four_iff]
    exact ht.2 i hi j hj fun h => hne (by rw [h])

/-- The cell of a set of mutually adjacent vertex indices. -/
noncomputable def cellOf (k : ℕ) (t : {t // t ∈ cellFinset k}) : Cell k := ⟨_, isCell_of_mem t.2⟩

theorem cellOf_injective (k : ℕ) : Function.Injective (cellOf k) := by
  intro t u h
  have h' := congrArg Subtype.val h
  simp only [cellOf] at h'
  exact Subtype.ext (Finset.coe_injective (Set.image_injective.2 vtx_injective h'))

theorem cellOf_surjective (k : ℕ) : Function.Surjective (cellOf k) := by
  classical
  rintro ⟨s, hsub, hcard, hpair⟩
  let t : Finset (Fin 12) := Finset.univ.filter fun i => vtx i ∈ s
  have hst : vtx '' (t : Set (Fin 12)) = s := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩; simpa [t] using hi
    · intro hv
      obtain ⟨i, rfl⟩ := hsub hv
      exact ⟨i, by simpa [t] using hv, rfl⟩
  have ht : t ∈ cellFinset k := by
    simp only [cellFinset, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [← hcard, ← hst, Set.ncard_image_of_injective _ vtx_injective, Set.ncard_coe_finset]
    · intro i hi j hj hij
      rw [← sqDist_vtx_eq_four_iff]
      exact hpair (by simpa [t] using hi) (by simpa [t] using hj) (fun h => hij (vtx_injective h))
  exact ⟨⟨t, ht⟩, Subtype.ext hst⟩

instance (k : ℕ) : Finite (Cell k) := Finite.of_surjective _ (cellOf_surjective k)

noncomputable instance (k : ℕ) : Fintype (Cell k) := Fintype.ofFinite _

noncomputable instance (k : ℕ) : DecidableEq (Cell k) := Classical.decEq _

theorem card_cell (k : ℕ) : Fintype.card (Cell k) = (cellFinset k).card := by
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.ofBijective _ ⟨cellOf_injective k, cellOf_surjective k⟩),
    Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The regular icosahedron has `30` edges. -/
theorem card_edge : Fintype.card Edge = 30 := by rw [card_cell, card_cellFinset_two]

/-- The regular icosahedron has `20` faces. -/
theorem card_face : Fintype.card Face = 20 := by rw [card_cell, card_cellFinset_three]

/-! ### Transitivity on edges and faces -/

theorem vtx_of_mem {s : Set (Fin 3 → ℝ)} (hs : s ⊆ vertexSet) {v : Fin 3 → ℝ} (hv : v ∈ s) :
    ∃ i, vtx i = v := hs hv

/-- The edge from `vtx 0` to `vtx 1`. -/
noncomputable def edge0 : Edge :=
  cellOf 2 ⟨{0, 1}, by decide⟩

theorem edge0_val : (edge0 : Set (Fin 3 → ℝ)) = {vtx 0, vtx 1} := by
  simp [edge0, cellOf]

/-- The rotation group acts transitively on the edges. -/
theorem transitive_edge (e : Edge) : ∃ g : A5, rotEquiv g • edge0 = e := by
  obtain ⟨s, hsub, hcard, hpair⟩ := e
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 hcard
  obtain ⟨i, rfl⟩ := vtx_of_mem hsub (Set.mem_insert _ _)
  obtain ⟨j, rfl⟩ := vtx_of_mem hsub (Set.mem_insert_of_mem _ rfl)
  have hij : Adj i j := (sqDist_vtx_eq_four_iff i j).1
    (hpair (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) hxy)
  obtain ⟨g, hg0, hg1⟩ := psi_directed i j hij
  refine ⟨g, Subtype.ext ?_⟩
  rw [coe_smul_cell, edge0_val, Set.image_pair, mat_vtx_rotEquiv, mat_vtx_rotEquiv, hg0, hg1]

/-- The face with corners `vtx 0`, `vtx 1`, `vtx 2`. -/
noncomputable def face0 : Face :=
  cellOf 3 ⟨{0, 1, 2}, by decide⟩

theorem face0_val : (face0 : Set (Fin 3 → ℝ)) = {vtx 0, vtx 1, vtx 2} := by
  simp [face0, cellOf, Set.image_insert_eq, Set.image_singleton]

theorem psi_faces : ∀ a b c : Fin 12, Adj a b → Adj a c → Adj b c → ∃ g : A5,
    (psiFun g 0 = a ∧ psiFun g 1 = b ∧ psiFun g 2 = c) ∨
      (psiFun g 0 = a ∧ psiFun g 1 = c ∧ psiFun g 2 = b) := by
  decide +kernel

/-- The rotation group acts transitively on the faces. -/
theorem transitive_face (f : Face) : ∃ g : A5, rotEquiv g • face0 = f := by
  obtain ⟨s, hsub, hcard, hpair⟩ := f
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.1 hcard
  have mx : x ∈ ({x, y, z} : Set (Fin 3 → ℝ)) := by simp
  have my : y ∈ ({x, y, z} : Set (Fin 3 → ℝ)) := by simp
  have mz : z ∈ ({x, y, z} : Set (Fin 3 → ℝ)) := by simp
  obtain ⟨a, rfl⟩ := vtx_of_mem hsub mx
  obtain ⟨b, rfl⟩ := vtx_of_mem hsub my
  obtain ⟨c, rfl⟩ := vtx_of_mem hsub mz
  have hab := (sqDist_vtx_eq_four_iff a b).1 (hpair mx my hxy)
  have hac := (sqDist_vtx_eq_four_iff a c).1 (hpair mx mz hxz)
  have hbc := (sqDist_vtx_eq_four_iff b c).1 (hpair my mz hyz)
  obtain ⟨g, hg⟩ := psi_faces a b c hab hac hbc
  refine ⟨g, Subtype.ext ?_⟩
  rw [coe_smul_cell, face0_val, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    mat_vtx_rotEquiv, mat_vtx_rotEquiv, mat_vtx_rotEquiv]
  rcases hg with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · rw [h0, h1, h2]
  · rw [h0, h1, h2, Set.pair_comm]

/-! ### The decompositions -/

/-- Transport a character identity from `A5` to the rotation group. -/
theorem character_transport {X : Type*} [MulAction rotGroup X] [Fintype X] [DecidableEq X] (x0 : X)
    (htr : ∀ x : X, ∃ g : A5, rotEquiv g • x0 = x) (m : Fin 5 → ℕ)
    (hA5 : ∀ [MulAction A5 X], (∀ x : X, ∃ b : A5, b • x0 = x) →
      (Representation.ofMulAction ℂ A5 X).character = comb m) :
    (Representation.ofMulAction ℂ rotGroup X).character = fun A => comb m (rotEquiv.symm A) := by
  let : MulAction A5 X := MulAction.compHom X rotEquiv.toMonoidHom
  have h := hA5 htr
  funext A
  rw [← h, character_ofMulAction, character_ofMulAction]
  congr 3
  funext x
  change _ = (rotEquiv (rotEquiv.symm A) • x = x)
  rw [MulEquiv.apply_symm_apply]

/-- **Problem 3.21 (vertices)**: the rotation group of the regular icosahedron (isomorphic to `A5` by
`rotEquiv`) acting on the complex functions on the `12` vertices: the character is that of
`1 ⊕ 5 ⊕ 3 ⊕ 3'` (trivial, five-dimensional, both three-dimensional irreducible representations). -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem etingof_3_21_vertices :
    (Representation.ofMulAction ℂ rotGroup Vert).character =
      fun A => comb ![1, 0, 1, 1, 1] (rotEquiv.symm A) :=
  character_transport vert0 transitive_vert _ fun htr => character_vertices vert0 htr card_vert

/-- **Problem 3.21 (faces)**: on the complex functions on the `20` faces the character is that of
`1 ⊕ 2 · 4 ⊕ 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem etingof_3_21_faces :
    (Representation.ofMulAction ℂ rotGroup Face).character =
      fun A => comb ![1, 2, 1, 1, 1] (rotEquiv.symm A) :=
  character_transport face0 transitive_face _ fun htr => character_faces face0 htr card_face

/-- **Problem 3.21 (edges)**: on the complex functions on the `30` edges the character is that of
`1 ⊕ 2 · 4 ⊕ 3 · 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
theorem etingof_3_21_edges :
    (Representation.ofMulAction ℂ rotGroup Edge).character =
      fun A => comb ![1, 2, 3, 1, 1] (rotEquiv.symm A) :=
  character_transport edge0 transitive_edge _ fun htr => character_edges edge0 htr card_edge

end UndergradKB.RepresentationTheory.Icosahedron
