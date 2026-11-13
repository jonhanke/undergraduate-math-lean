import Mathlib.Analysis.Fourier.ZMod
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.Trace
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.AbelianCharacters
import UndergradKB.RepresentationTheory.CharacterTableA5
import UndergradKB.RepresentationTheory.CharactersChapter4
import UndergradKB.RepresentationTheory.VirtualCharacters
import UndergradKB.RepresentationTheory.LittleGroupTheorem

/-! # Problems on irreducible representations of finite groups (Etingof et al., Problems 3.17 (a), 3.18, 3.22)

Generic tools.

* `mem_irrChars_of_hermitianPairing`: the character of a representation whose character has Hermitian norm `1`
  is an irreducible character.
* `irrChars_eq_of_sum_sq`: a finite family of irreducible characters whose squared dimensions add up to `|G|` is
  the whole set of irreducible characters (so completeness only needs a dimension count).

Problem 3.17 (a), dihedral group of order `2N` (`DihedralGroup N`, `N ≥ 1`): the two-dimensional representation
`dihRep j` with its character `dihChar j`, irreducible when `2j ≠ 0` (`isIrreducible_dihRep`), the linear
characters `dihLinHom`, and the complete lists `irrChars_dihedral_odd` and `irrChars_dihedral_even`, with the
dimension counts `dihedral_counts_odd` (2 of dimension 1, `(N-1)/2` of dimension 2) and `dihedral_counts_even`
(4 of dimension 1, `N/2 - 1` of dimension 2).

Problem 3.22, the group `AffGrp F` of maps `x ↦ ax + b` over a finite field: `irrChars_affine` (the `q - 1`
characters of `F^×` pulled back along `(a, b) ↦ a`, plus the character `stdChar` of degree `q - 1`),
`card_irrChars_affine` and `exists_irrRep_affine_dim`.

Problem 3.18, the Heisenberg group `Heis p` over `ZMod p`: the representations `heisRep z hz` on functions on
`ZMod p`, `isIrreducible_heisRep_iff` (irreducible iff `z ≠ 1`), `character_rep_one` (decomposition of `R_1` at the
level of characters), `exists_linHom_eq` (the one-dimensional characters), and `irrChars_heis` (the full list).

Differences from the book: statements about classification are made for the set of irreducible characters
`irrChars ℂ G` (equivalently, isomorphism classes of irreducible representations).  The dihedral group is given by
Mathlib's `DihedralGroup N` with the two-dimensional representations written as explicit complex matrices
`diag(ζ^j, ζ^{-j})` and the swap, `ζ = exp(2πi/N)` realised through `ZMod.stdAddChar`.  The affine group and the
Heisenberg group are defined as structures (pairs, resp. triples) with the matrix multiplication rule; for the
Heisenberg group `Heis.toMatrix` is a multiplicative injective map to `3 × 3` matrices.  For Problem 3.22 the
`(q-1)`-dimensional representation is described through its character (permutation character minus the trivial one,
shown irreducible by the norm criterion), not as the space of zero-sum functions; tensor products are not treated.
For Problem 3.18, uniqueness of `R_z` (part (a)) and the explicit decomposition of `R_1` into lines are not
formalized; `R_1` is compared with the sum of the `p` linear characters `a ↦ linHom a 0` through characters only.
Problem 3.17 (b) is not treated.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Representation Module
open scoped ComplexConjugate

section Generic

/-- Complex-valued group orders are invertible (local convenience instance). -/
noncomputable local instance (priority := low) invertibleCardComplex {G : Type*} [Finite G] [Group G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- The character of a representation with Hermitian norm `1` is an irreducible character. -/
theorem mem_irrChars_of_hermitianPairing {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : hermitianPairing ρ.character ρ.character = 1) : ρ.character ∈ irrChars ℂ G := by
  have := isIrreducible_of_hermitianPairing_self_eq_one ρ h
  exact ⟨{ V := V, ρ := ρ }, rfl⟩

/-- A finite set of irreducible characters whose values at `1` have squares adding up to `|G|` is the set of all
irreducible characters. -/
theorem irrChars_eq_of_sum_sq {G : Type} [Group G] [Fintype G] (S : Finset (G → ℂ))
    (hS : ∀ χ ∈ S, χ ∈ irrChars ℂ G) (hsum : ∑ χ ∈ S, χ 1 ^ 2 = Nat.card G) :
    irrChars ℂ G = ↑S := by
  classical
  have hfin : (irrChars ℂ G).Finite := irrChars_finite
  have hST : S ⊆ hfin.toFinset := fun x hx => hfin.mem_toFinset.mpr (hS x hx)
  have hT : ∑ χ ∈ hfin.toFinset, χ 1 ^ 2 = Nat.card G := by
    rw [Finset.sum_subtype hfin.toFinset (p := fun x => x ∈ irrChars ℂ G)
      (fun x => hfin.mem_toFinset) (fun χ : G → ℂ => χ 1 ^ 2)]
    exact sum_irrChars_one_sq (k := ℂ) (G := G)
  have hdiff : ∑ χ ∈ hfin.toFinset \ S, χ 1 ^ 2 = 0 := by
    have := Finset.sum_sdiff hST (f := fun χ : G → ℂ => χ 1 ^ 2)
    rw [hT, hsum] at this
    linear_combination this
  have hpos : ∀ χ ∈ hfin.toFinset \ S, 0 < (χ 1 ^ 2).re := by
    intro χ hχ
    obtain ⟨X, hX⟩ := hfin.mem_toFinset.mp (Finset.mem_sdiff.mp hχ).1
    have h1 : χ 1 = (finrank ℂ X.V : ℂ) := by rw [← hX]; exact char_one X.ρ
    have h2 : (finrank ℂ X.V : ℂ) ≠ 0 := finrank_ne_zero_of_isIrreducible (ρ := X.ρ)
    have h3 : 0 < finrank ℂ X.V := Nat.pos_of_ne_zero (by exact_mod_cast h2)
    rw [h1, ← Nat.cast_pow, Complex.natCast_re]
    exact_mod_cast pow_pos h3 2
  have hempty : hfin.toFinset \ S = ∅ := by
    by_contra hne
    have hre := congrArg Complex.re hdiff
    rw [Complex.re_sum, Complex.zero_re] at hre
    have := Finset.sum_pos hpos (Finset.nonempty_iff_ne_empty.mpr hne)
    linarith
  ext x
  constructor
  · intro hx
    have : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx
    by_contra hxS
    have : x ∈ hfin.toFinset \ S := Finset.mem_sdiff.mpr ⟨this, hxS⟩
    rw [hempty] at this
    simp at this
  · intro hx
    exact hS x hx

end Generic

section Dihedral

open DihedralGroup

variable {N : ℕ} [NeZero N]

/-- The standard additive character `j ↦ exp(2πi j/N)` of `ZMod N`. -/
noncomputable def ee : AddChar (ZMod N) ℂ := ZMod.stdAddChar

lemma ee_mul_neg (x : ZMod N) : ee x * ee (-x) = 1 := by
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

lemma ee_ne_zero (x : ZMod N) : ee x ≠ 0 := left_ne_zero_of_mul_eq_one (ee_mul_neg x)

lemma ee_neg (x : ZMod N) : ee (-x) = (ee x)⁻¹ := AddChar.map_neg_eq_inv _ _

lemma conj_ee (x : ZMod N) : conj (ee x) = (ee x)⁻¹ := by
  have h : ee x = ((ZMod.toCircle x : Circle) : ℂ) := rfl
  rw [h, ← Circle.coe_inv_eq_conj]
  simp

lemma ee_eq_one_iff (x : ZMod N) : ee x = 1 ↔ x = 0 := by
  rw [← AddChar.map_zero_eq_one (ψ := (ee : AddChar (ZMod N) ℂ))]
  exact (ZMod.injective_stdAddChar (N := N)).eq_iff

lemma sum_ee_mul (b : ZMod N) : ∑ x : ZMod N, ee (x * b) = if b = 0 then (N : ℂ) else 0 := by
  classical
  have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod N) ℂ)) b (ZMod.isPrimitive_stdAddChar N)
  simpa [ee, ZMod.card] using this

/-- Sum over the dihedral group as a sum over rotations and reflections. -/
lemma sum_dihedral {M : Type*} [AddCommMonoid M] (f : DihedralGroup N → M) :
    ∑ g, f g = ∑ i : ZMod N, f (r i) + ∑ i : ZMod N, f (sr i) := by
  rw [Fintype.sum_equiv (DihedralGroup.equivSum) f
    (fun s => Sum.elim (fun i => f (r i)) (fun i => f (sr i)) s) (by intro g; cases g <;> rfl),
    Fintype.sum_sum_type]
  rfl

/-- The matrix of the group element in the two-dimensional representation of index `j`: rotation `r i` acts by
`diag(ζ^{ji}, ζ^{-ji})`, and the reflection `sr i` as the swap composed with that diagonal matrix. -/
noncomputable def dihMat (j : ZMod N) : DihedralGroup N → Matrix (Fin 2) (Fin 2) ℂ
  | r i => !![ee (j * i), 0; 0, (ee (j * i))⁻¹]
  | sr i => !![0, (ee (j * i))⁻¹; ee (j * i), 0]

lemma dihMat_mul (j : ZMod N) (g h : DihedralGroup N) : dihMat j (g * h) = dihMat j g * dihMat j h := by
  have e1 := ee_ne_zero (N := N)
  cases g with
  | r i =>
    cases h with
    | r k =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [dihMat, r_mul_r, mul_add, AddChar.map_add_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    | sr k =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [dihMat, r_mul_sr, mul_sub, AddChar.map_sub_eq_div, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp [e1]
  | sr i =>
    cases h with
    | r k =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [dihMat, sr_mul_r, mul_add, AddChar.map_add_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    | sr k =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [dihMat, sr_mul_sr, mul_sub, AddChar.map_sub_eq_div, Matrix.mul_apply, Fin.sum_univ_two] <;>
        field_simp [e1]

lemma dihMat_one (j : ZMod N) : dihMat j 1 = 1 := by
  rw [one_def]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [dihMat]

/-- The two-dimensional representation `ρ_j` of the dihedral group on `ℂ²`. -/
noncomputable def dihRep (j : ZMod N) : Representation ℂ (DihedralGroup N) (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (dihMat j g)
  map_one' := by rw [dihMat_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [dihMat_mul, Matrix.toLin'_mul]; rfl

/-- The character of `ρ_j`. -/
lemma character_dihRep (j : ZMod N) (g : DihedralGroup N) :
    (dihRep j).character g = match g with
      | r i => ee (j * i) + (ee (j * i))⁻¹
      | sr _ => 0 := by
  show LinearMap.trace ℂ _ (Matrix.toLin' (dihMat j g)) = _
  rw [Matrix.trace_toLin'_eq]
  cases g <;> simp [dihMat, Matrix.trace, Fin.sum_univ_two]

/-- The class function `θ_j`, the character of `ρ_j`. -/
noncomputable def dihChar (j : ZMod N) : DihedralGroup N → ℂ
  | r i => ee (j * i) + (ee (j * i))⁻¹
  | sr _ => 0

lemma character_dihRep_eq (j : ZMod N) : (dihRep j).character = dihChar j := by
  funext g
  rw [character_dihRep]
  cases g <;> rfl

lemma dihChar_one (j : ZMod N) : dihChar j 1 = 2 := by
  rw [one_def]
  simp [dihChar]
  norm_num

/-- The character `θ_j` has Hermitian norm `1` as soon as `2j ≠ 0`. -/
lemma hermitianPairing_dihChar (j : ZMod N) (hj : j + j ≠ 0) :
    hermitianPairing (dihChar j) (dihChar j) = 1 := by
  have hcard : (Nat.card (DihedralGroup N) : ℂ) = 2 * N := by
    rw [DihedralGroup.nat_card]; push_cast; ring
  have key : ∀ i : ZMod N, dihChar j (r i) * conj (dihChar j (r i)) =
      ee (i * (j + j)) + 2 + ee (i * (-(j + j))) := by
    intro i
    have h1 : ee (i * (j + j)) = ee (j * i) * ee (j * i) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    have h2 : ee (i * (-(j + j))) = (ee (j * i))⁻¹ * (ee (j * i))⁻¹ := by
      rw [show i * (-(j + j)) = -(j * i) + -(j * i) by ring, AddChar.map_add_eq_mul, ee_neg]
    have h3 := ee_ne_zero (j * i)
    simp only [dihChar, map_add, map_inv₀, conj_ee, inv_inv, h1, h2]
    field_simp
    ring
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold hermitianPairing
  rw [sum_dihedral]
  simp only [key]
  simp only [dihChar, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ee_mul, sum_ee_mul, if_neg hj,
    if_neg (neg_ne_zero.mpr hj)]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hcard]
  field_simp
  ring

/-- For `2j ≠ 0` the representation `ρ_j` is irreducible. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem isIrreducible_dihRep (j : ZMod N) (hj : j + j ≠ 0) : IsIrreducible (dihRep j) := by
  apply isIrreducible_of_hermitianPairing_self_eq_one
  rw [character_dihRep_eq]
  exact hermitianPairing_dihChar j hj

theorem dihChar_mem_irrChars (j : ZMod N) (hj : j + j ≠ 0) :
    dihChar j ∈ irrChars ℂ (DihedralGroup N) := by
  rw [← character_dihRep_eq]
  apply mem_irrChars_of_hermitianPairing
  rw [character_dihRep_eq]
  exact hermitianPairing_dihChar j hj

/-- A linear character of the dihedral group: the rotation `r i` goes to `ζ^{mi}` (with `2m = 0`, so this is `±1`)
and the reflection `sr i` goes to `b ζ^{mi}` for a sign `b`. -/
noncomputable def dihLinHom (m : ZMod N) (hm : m + m = 0) (b : ℂ) (hb : b * b = 1) :
    DihedralGroup N →* ℂ where
  toFun
    | r i => ee (m * i)
    | sr i => b * ee (m * i)
  map_one' := by rw [one_def]; simp
  map_mul' g h := by
    have hsq : ∀ i : ZMod N, ee (m * i) * ee (m * i) = 1 := by
      intro i
      rw [← AddChar.map_add_eq_mul, show m * i + m * i = (m + m) * i by ring, hm, zero_mul,
        AddChar.map_zero_eq_one]
    have hinv : ∀ i : ZMod N, (ee (m * i))⁻¹ = ee (m * i) := fun i => inv_eq_of_mul_eq_one_right (hsq i)
    cases g with
    | r i =>
      cases h with
      | r k => simp [r_mul_r, mul_add, AddChar.map_add_eq_mul]
      | sr k =>
        simp only [r_mul_sr, mul_sub, AddChar.map_sub_eq_div, div_eq_mul_inv, hinv]
        ring
    | sr i =>
      cases h with
      | r k => simp [sr_mul_r, mul_add, AddChar.map_add_eq_mul]; ring
      | sr k =>
        simp only [sr_mul_sr, mul_sub, AddChar.map_sub_eq_div, div_eq_mul_inv, hinv]
        linear_combination (-(ee (m * i) * ee (m * k))) * hb

lemma dihLinHom_r (m : ZMod N) (hm : m + m = 0) (b : ℂ) (hb : b * b = 1) (i : ZMod N) :
    dihLinHom m hm b hb (r i) = ee (m * i) := rfl

lemma dihLinHom_sr (m : ZMod N) (hm : m + m = 0) (b : ℂ) (hb : b * b = 1) (i : ZMod N) :
    dihLinHom m hm b hb (sr i) = b * ee (m * i) := rfl

/-- Every homomorphism to `ℂ` of a finite group is an irreducible character (one-dimensional representation). -/
theorem hom_mem_irrChars {G : Type} [Group G] [Fintype G] (φ : G →* ℂ) :
    (φ : G → ℂ) ∈ irrChars ℂ G := by
  have hirr := isIrreducible_of_finrank_eq_one (lineRep' φ) (Module.finrank_self ℂ)
  refine ⟨@IrrRep.mk ℂ G _ _ ℂ _ _ _ (lineRep' φ) hirr, ?_⟩
  funext g
  exact character_lineRep' φ g

lemma natCast_add_natCast_ne_zero {j : ℕ} (h0 : 0 < j) (h2 : 2 * j < N) :
    (j : ZMod N) + (j : ZMod N) ≠ 0 := by
  intro h
  have h' : ((2 * j : ℕ) : ZMod N) = 0 := by push_cast; rw [two_mul]; exact h
  have := (ZMod.natCast_eq_zero_iff _ _).mp h'
  have := Nat.le_of_dvd (by omega) this
  omega

/-- The characters `θ_j` for `0 < j`, `2j < N` are pairwise distinct. -/
lemma dihChar_natCast_injective {j k : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hk0 : 0 < k) (hk : 2 * k < N)
    (h : dihChar (j : ZMod N) = dihChar (k : ZMod N)) : j = k := by
  have h1 := congrFun h (r 1)
  simp only [dihChar, mul_one] at h1
  have hx := ee_ne_zero (j : ZMod N)
  have hy := ee_ne_zero (k : ZMod N)
  have h2 : (ee (j : ZMod N) - ee (k : ZMod N)) * (ee (j : ZMod N) * ee (k : ZMod N) - 1) = 0 := by
    field_simp at h1
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have h4 : ee (j : ZMod N) = ee (k : ZMod N) := sub_eq_zero.mp h3
    have h5 : (j : ZMod N) = (k : ZMod N) := (ZMod.injective_stdAddChar (N := N)) h4
    have h6 := (ZMod.natCast_eq_natCast_iff' j k N).mp h5
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h6
  · have h4 : ee ((j : ZMod N) + (k : ZMod N)) = 1 := by
      rw [AddChar.map_add_eq_mul]; exact sub_eq_zero.mp h3
    have h5 : ((j + k : ℕ) : ZMod N) = 0 := by
      push_cast; exact (ee_eq_one_iff _).mp h4
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp h5)
    omega

/-- The two-dimensional irreducible characters `θ_j`, `0 < j`, `2j < N`. -/
noncomputable def dihTwoDimChars (N : ℕ) [NeZero N] : Finset (DihedralGroup N → ℂ) :=
  (Finset.Ioo 0 ((N + 1) / 2)).image fun j : ℕ => dihChar (j : ZMod N)

lemma mem_dihTwoDimChars {χ : DihedralGroup N → ℂ} :
    χ ∈ dihTwoDimChars N ↔ ∃ j : ℕ, 0 < j ∧ 2 * j < N ∧ χ = dihChar (j : ZMod N) := by
  unfold dihTwoDimChars
  simp only [Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩; exact ⟨j, h1, by omega, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩; exact ⟨j, ⟨h1, by omega⟩, rfl⟩

lemma card_dihTwoDimChars : (dihTwoDimChars N).card = (N + 1) / 2 - 1 := by
  unfold dihTwoDimChars
  rw [Finset.card_image_of_injOn, Nat.card_Ioo]
  · omega
  · intro j hj k hk h
    simp only [Finset.coe_Ioo, Set.mem_Ioo] at hj hk
    exact dihChar_natCast_injective (by omega) (by omega) (by omega) (by omega) h

lemma dihTwoDimChars_mem_irrChars {χ : DihedralGroup N → ℂ} (h : χ ∈ dihTwoDimChars N) :
    χ ∈ irrChars ℂ (DihedralGroup N) := by
  obtain ⟨j, h0, h2, rfl⟩ := mem_dihTwoDimChars.mp h
  exact dihChar_mem_irrChars _ (natCast_add_natCast_ne_zero h0 h2)

lemma dihTwoDimChars_one {χ : DihedralGroup N → ℂ} (h : χ ∈ dihTwoDimChars N) : χ 1 = 2 := by
  obtain ⟨j, -, -, rfl⟩ := mem_dihTwoDimChars.mp h
  exact dihChar_one _

/-- Completion: if `A` is a finite set of distinct one-dimensional irreducible characters with `a` elements and
`a + 4 ((N+1)/2 - 1) = 2N`, then together with the two-dimensional ones they exhaust the irreducible characters. -/
theorem irrChars_dihedral_of_linear (A : Finset (DihedralGroup N → ℂ))
    (hA : ∀ χ ∈ A, χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1)
    (hcount : A.card + 4 * ((N + 1) / 2 - 1) = 2 * N) :
    irrChars ℂ (DihedralGroup N) = ↑(A ∪ dihTwoDimChars N) := by
  have hdisj : Disjoint A (dihTwoDimChars N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hA x hx).2
    have h2 := dihTwoDimChars_one hx'
    rw [h1] at h2
    norm_num at h2
  apply irrChars_eq_of_sum_sq
  · intro χ hχ
    rcases Finset.mem_union.mp hχ with h | h
    · exact (hA χ h).1
    · exact dihTwoDimChars_mem_irrChars h
  · rw [Finset.sum_union hdisj,
      Finset.sum_congr rfl (fun x hx => by rw [(hA x hx).2]),
      Finset.sum_congr (s₂ := dihTwoDimChars N) rfl (fun x hx => by rw [dihTwoDimChars_one hx])]
    simp only [Finset.sum_const, nsmul_eq_mul, card_dihTwoDimChars, DihedralGroup.nat_card]
    generalize (N + 1) / 2 - 1 = k at hcount ⊢
    have : ((A.card + 4 * k : ℕ) : ℂ) = ((2 * N : ℕ) : ℂ) := by rw [hcount]
    push_cast at this ⊢
    linear_combination this

/-- Dimension counts for a decomposition `irrChars = A ∪ B` into one-dimensional and two-dimensional characters. -/
lemma dihedral_counts_of_eq (A : Finset (DihedralGroup N → ℂ))
    (hA : ∀ χ ∈ A, χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1)
    (heq : irrChars ℂ (DihedralGroup N) = ↑(A ∪ dihTwoDimChars N)) :
    (∀ χ ∈ irrChars ℂ (DihedralGroup N), χ 1 = 1 ∨ χ 1 = 2) ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1}.ncard = A.card ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 2}.ncard = (N + 1) / 2 - 1 := by
  have h12 : (1 : ℂ) ≠ 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    rw [heq] at hχ
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hχ) with h | h
    · exact Or.inl (hA χ h).2
    · exact Or.inr (dihTwoDimChars_one h)
  · have : {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1} = ↑A := by
      ext χ
      simp only [Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨h, h1⟩
        rw [heq] at h
        rcases Finset.mem_union.mp (Finset.mem_coe.mp h) with h | h
        · exact h
        · exact absurd (h1.symm.trans (dihTwoDimChars_one h)) h12
      · intro h
        exact hA χ h
    rw [this, Set.ncard_coe_finset]
  · have : {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 2} = ↑(dihTwoDimChars N) := by
      ext χ
      simp only [Set.mem_setOf_eq, Finset.mem_coe]
      constructor
      · rintro ⟨h, h1⟩
        rw [heq] at h
        rcases Finset.mem_union.mp (Finset.mem_coe.mp h) with h | h
        · exact absurd ((hA χ h).2.symm.trans h1) h12
        · exact h
      · intro h
        exact ⟨dihTwoDimChars_mem_irrChars h, dihTwoDimChars_one h⟩
    rw [this, Set.ncard_coe_finset, card_dihTwoDimChars]

/-- The sign `±1` as a complex number. -/
def signC (s : Bool) : ℂ := if s then -1 else 1

lemma signC_mul_self (s : Bool) : signC s * signC s = 1 := by cases s <;> simp [signC]

/-- The linear characters of the dihedral group with a given `m` (`2m = 0`) and sign. -/
noncomputable def dihLinChar (m : ZMod N) (hm : m + m = 0) (s : Bool) : DihedralGroup N → ℂ :=
  ⇑(dihLinHom m hm (signC s) (signC_mul_self s))

lemma dihLinChar_mem (m : ZMod N) (hm : m + m = 0) (s : Bool) :
    dihLinChar m hm s ∈ irrChars ℂ (DihedralGroup N) := hom_mem_irrChars _

lemma dihLinChar_one (m : ZMod N) (hm : m + m = 0) (s : Bool) : dihLinChar m hm s 1 = 1 :=
  map_one (dihLinHom m hm (signC s) (signC_mul_self s))

lemma dihLinChar_inj {m m' : ZMod N} {hm : m + m = 0} {hm' : m' + m' = 0} {s s' : Bool}
    (h : dihLinChar m hm s = dihLinChar m' hm' s') : m = m' ∧ s = s' := by
  have h1 := congrFun h (r 1)
  have h2 := congrFun h (sr 0)
  simp only [dihLinChar, dihLinHom_r, dihLinHom_sr, mul_one, mul_zero, AddChar.map_zero_eq_one] at h1 h2
  refine ⟨(ZMod.injective_stdAddChar (N := N)) h1, ?_⟩
  cases s <;> cases s' <;> first | rfl | (exfalso; revert h2; norm_num [signC])

/-- **Problem 3.17 (a), `N` odd.**  The irreducible characters of the dihedral group of order `2N` are the two
linear characters (trivial and the sign `r ↦ 1`, `sr ↦ -1`) and the `(N-1)/2` characters `θ_j` of the
two-dimensional representations `ρ_j`, `0 < j < N/2`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem irrChars_dihedral_odd (hN : Odd N) :
    irrChars ℂ (DihedralGroup N) =
      ↑(Finset.univ.image (fun s : Bool => dihLinChar (0 : ZMod N) (add_zero 0) s) ∪ dihTwoDimChars N) := by
  have hinj : Function.Injective (fun s : Bool => dihLinChar (0 : ZMod N) (add_zero 0) s) :=
    fun s s' h => (dihLinChar_inj h).2
  apply irrChars_dihedral_of_linear
  · intro χ hχ
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hχ
    exact ⟨dihLinChar_mem _ _ _, dihLinChar_one _ _ _⟩
  · rw [Finset.card_image_of_injective _ hinj]
    obtain ⟨k, hk⟩ := hN
    simp only [Finset.card_univ, Fintype.card_bool]
    omega

/-- Counts for `N` odd: two irreducible representations of dimension one, `(N-1)/2` of dimension two, no others. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem dihedral_counts_odd (hN : Odd N) :
    (∀ χ ∈ irrChars ℂ (DihedralGroup N), χ 1 = 1 ∨ χ 1 = 2) ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1}.ncard = 2 ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 2}.ncard = (N - 1) / 2 := by
  have hinj : Function.Injective (fun s : Bool => dihLinChar (0 : ZMod N) (add_zero 0) s) :=
    fun s s' h => (dihLinChar_inj h).2
  have hA : ∀ χ ∈ Finset.univ.image (fun s : Bool => dihLinChar (0 : ZMod N) (add_zero 0) s),
      χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1 := by
    intro χ hχ
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hχ
    exact ⟨dihLinChar_mem _ _ _, dihLinChar_one _ _ _⟩
  obtain ⟨h1, h2, h3⟩ := dihedral_counts_of_eq _ hA (irrChars_dihedral_odd hN)
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, Finset.card_image_of_injective _ hinj]; simp
  · rw [h3]; omega

/-- Half of an even `N` as an element of `ZMod N`. -/
def halfN (N : ℕ) : ZMod N := ((N / 2 : ℕ) : ZMod N)

lemma halfN_add_halfN (hN : Even N) : halfN N + halfN N = 0 := by
  have : ((N / 2 + N / 2 : ℕ) : ZMod N) = 0 := by
    rw [(ZMod.natCast_eq_zero_iff _ _)]
    obtain ⟨k, hk⟩ := hN
    exact ⟨1, by omega⟩
  rw [halfN, ← Nat.cast_add]
  exact this

lemma halfN_ne_zero (hN : Even N) : halfN N ≠ 0 := by
  intro h
  have := Nat.le_of_dvd (by obtain ⟨k, hk⟩ := hN; have := NeZero.ne N; omega)
    ((ZMod.natCast_eq_zero_iff _ _).mp h)
  obtain ⟨k, hk⟩ := hN
  have := NeZero.ne N
  omega

/-- The two values of `m` with `2m = 0` for even `N`. -/
def evenM (N : ℕ) (t : Bool) : ZMod N := if t then halfN N else 0

lemma evenM_add (hN : Even N) (t : Bool) : evenM N t + evenM N t = 0 := by
  cases t
  · simp [evenM]
  · simpa [evenM] using halfN_add_halfN hN

/-- The four linear characters for even `N`. -/
noncomputable def dihLinEven (hN : Even N) (p : Bool × Bool) : DihedralGroup N → ℂ :=
  dihLinChar (evenM N p.1) (evenM_add hN p.1) p.2

lemma dihLinEven_injective (hN : Even N) : Function.Injective (dihLinEven hN) := by
  rintro ⟨t, s⟩ ⟨t', s'⟩ h
  obtain ⟨h1, h2⟩ := dihLinChar_inj h
  have : t = t' := by
    have hne := halfN_ne_zero hN
    cases t <;> cases t' <;> simp_all [evenM]
  subst this
  subst h2
  rfl

/-- **Problem 3.17 (a), `N` even.**  The irreducible characters of the dihedral group of order `2N` are four
linear characters (the rotation `r` goes to `±1`, the reflection `s` goes to `±1`) and the `N/2 - 1` characters
`θ_j` of the two-dimensional representations, `0 < j < N/2`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem irrChars_dihedral_even (hN : Even N) :
    irrChars ℂ (DihedralGroup N) = ↑(Finset.univ.image (dihLinEven hN) ∪ dihTwoDimChars N) := by
  apply irrChars_dihedral_of_linear
  · intro χ hχ
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hχ
    exact ⟨dihLinChar_mem _ _ _, dihLinChar_one _ _ _⟩
  · rw [Finset.card_image_of_injective _ (dihLinEven_injective hN)]
    obtain ⟨k, hk⟩ := hN
    have := NeZero.ne N
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    omega

/-- Counts for `N` even: four irreducible representations of dimension one, `N/2 - 1` of dimension two. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem dihedral_counts_even (hN : Even N) :
    (∀ χ ∈ irrChars ℂ (DihedralGroup N), χ 1 = 1 ∨ χ 1 = 2) ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1}.ncard = 4 ∧
    {χ | χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 2}.ncard = N / 2 - 1 := by
  have hA : ∀ χ ∈ Finset.univ.image (dihLinEven hN),
      χ ∈ irrChars ℂ (DihedralGroup N) ∧ χ 1 = 1 := by
    intro χ hχ
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hχ
    exact ⟨dihLinChar_mem _ _ _, dihLinChar_one _ _ _⟩
  obtain ⟨h1, h2, h3⟩ := dihedral_counts_of_eq _ hA (irrChars_dihedral_even hN)
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, Finset.card_image_of_injective _ (dihLinEven_injective hN)]; simp
  · rw [h3]; obtain ⟨k, hk⟩ := hN; omega

end Dihedral

section Affine

/-- The group of maps `x ↦ a x + b` of a field `F`, with `a ≠ 0`; the pair `(a, b)` stands for this map. -/
@[ext]
structure AffGrp (F : Type) [Field F] where
  /-- The (nonzero) slope. -/
  a : Fˣ
  /-- The translation part. -/
  b : F

namespace AffGrp

variable {F : Type} [Field F]

instance : Mul (AffGrp F) := ⟨fun x y => ⟨x.a * y.a, x.a * y.b + x.b⟩⟩
instance : One (AffGrp F) := ⟨⟨1, 0⟩⟩
instance : Inv (AffGrp F) := ⟨fun x => ⟨x.a⁻¹, -(x.a⁻¹ * x.b)⟩⟩

@[simp] lemma mul_a (x y : AffGrp F) : (x * y).a = x.a * y.a := rfl
@[simp] lemma mul_b (x y : AffGrp F) : (x * y).b = x.a * y.b + x.b := rfl
@[simp] lemma one_a : (1 : AffGrp F).a = 1 := rfl
@[simp] lemma one_b : (1 : AffGrp F).b = 0 := rfl
@[simp] lemma inv_a (x : AffGrp F) : (x⁻¹).a = x.a⁻¹ := rfl
@[simp] lemma inv_b (x : AffGrp F) : (x⁻¹).b = -(x.a⁻¹ * x.b) := rfl

instance : Group (AffGrp F) where
  mul_assoc x y z := by ext <;> simp [mul_assoc] ; ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp

/-- The slope of the affine map as a homomorphism to `Fˣ`. -/
def slope : AffGrp F →* Fˣ where
  toFun x := x.a
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The group acts on the field by affine maps. -/
instance : MulAction (AffGrp F) F where
  smul g x := g.a * x + g.b
  one_smul x := by simp [HSMul.hSMul, SMul.smul]
  mul_smul g h x := by simp [HSMul.hSMul, SMul.smul]; ring

lemma smul_def (g : AffGrp F) (x : F) : g • x = g.a * x + g.b := rfl

/-- The equivalence with pairs. -/
def equivProd : AffGrp F ≃ Fˣ × F where
  toFun g := (g.a, g.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype F] [DecidableEq F]

instance : Fintype (AffGrp F) := Fintype.ofEquiv _ equivProd.symm

lemma sum_aff {M : Type*} [AddCommMonoid M] (f : AffGrp F → M) :
    ∑ g, f g = ∑ a : Fˣ, ∑ b : F, f ⟨a, b⟩ := by
  rw [← Fintype.sum_prod_type' (f := fun a b => f ⟨a, b⟩)]
  exact Fintype.sum_equiv equivProd _ _ (fun g => rfl)

lemma card_aff : Nat.card (AffGrp F) = (Fintype.card F - 1) * Fintype.card F := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_units]

/-- The linear character of the affine group attached to a character `ψ` of the multiplicative group of the
field: `(a, b) ↦ ψ(a)`. -/
noncomputable def linHom (ψ : Fˣ →* ℂˣ) : AffGrp F →* ℂ :=
  (Units.coeHom ℂ).comp (ψ.comp slope)

lemma linHom_apply (ψ : Fˣ →* ℂˣ) (g : AffGrp F) : linHom ψ g = (ψ g.a : ℂ) := rfl

lemma linHom_injective : Function.Injective fun ψ : Fˣ →* ℂˣ => (⇑(linHom ψ) : AffGrp F → ℂ) := by
  intro ψ ψ' h
  ext a
  have := congrFun h ⟨a, 0⟩
  simp only [linHom_apply] at this
  exact_mod_cast this

open scoped Classical in
/-- The character `ζ` with values `q - 1` at the identity, `-1` at the nontrivial translations and `0` at all
elements with `a ≠ 1`; it is the character of the space of functions on `F` with sum zero. -/
noncomputable def stdChar (F : Type) [Field F] [Fintype F] : AffGrp F → ℂ := fun g =>
  if g.a = 1 then (if g.b = 0 then (Fintype.card F : ℂ) - 1 else -1) else 0

lemma card_fixed (g : AffGrp F) :
    ((Finset.univ.filter fun x : F => g • x = x).card : ℂ) - 1 = stdChar F g := by
  unfold stdChar
  by_cases ha : g.a = 1
  · by_cases hb : g.b = 0
    · have : (Finset.univ.filter fun x : F => g • x = x) = Finset.univ := by
        ext x; simp [smul_def, ha, hb]
      simp [this, ha, hb]
    · have : (Finset.univ.filter fun x : F => g • x = x) = ∅ := by
        ext x; simp [smul_def, ha, hb]
      simp [this, ha, hb]
  · have h1 : (g.a : F) - 1 ≠ 0 := by
      intro h
      apply ha
      ext
      simpa [sub_eq_zero] using h
    have : (Finset.univ.filter fun x : F => g • x = x) = {g.b / (1 - g.a)} := by
      have h2 : (1 : F) - g.a ≠ 0 := by
        intro h; apply h1; linear_combination -h
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, smul_def]
      constructor
      · intro h
        field_simp
        linear_combination -h
      · rintro rfl
        field_simp
        ring
    simp [this, ha]

lemma stdChar_inv (g : AffGrp F) : stdChar F g⁻¹ = stdChar F g := by
  unfold stdChar
  by_cases ha : g.a = 1
  · by_cases hb : g.b = 0 <;> simp [ha, hb]
  · simp [ha]

lemma stdChar_mem_virtualChars : stdChar F ∈ virtualChars ℂ (AffGrp F) := by
  have h1 := S4Table.character_mem_virtualChars (Representation.ofMulAction ℂ (AffGrp F) F)
  have h2 := S4Table.character_mem_virtualChars (lineRep' (1 : AffGrp F →* ℂ))
  have := Submodule.sub_mem _ h1 h2
  convert this using 1
  funext g
  rw [Pi.sub_apply, A5Table.character_ofMulAction, character_lineRep', ← card_fixed]
  simp

lemma stdChar_one : stdChar F 1 = (Fintype.card F : ℂ) - 1 := by
  simp [stdChar]

lemma pairing_stdChar [Invertible (Nat.card (AffGrp F) : ℂ)] (hF : 2 ≤ Fintype.card F) :
    pairing (stdChar F) (stdChar F) = 1 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Fintype.card F = n + 2 := ⟨Fintype.card F - 2, by omega⟩
  have hq : (Fintype.card F : ℂ) - 1 = ((n + 1 : ℕ) : ℂ) := by rw [hn]; push_cast; ring
  have hq1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcard : (Nat.card (AffGrp F) : ℂ) = ((n + 1 : ℕ) : ℂ) * (Fintype.card F : ℂ) := by
    rw [card_aff, hn]; push_cast; ring
  have key : ∀ (a : Fˣ) (b : F), stdChar F ⟨a, b⟩ * stdChar F ⟨a, b⟩⁻¹ =
      if a = 1 then (if b = 0 then ((Fintype.card F : ℂ) - 1) ^ 2 else 1) else 0 := by
    intro a b
    rw [stdChar_inv]
    by_cases ha : a = 1
    · by_cases hb : b = 0 <;> simp [stdChar, ha, hb, sq]
    · simp [stdChar, ha]
  rw [pairing_apply, sum_aff]
  simp only [key]
  rw [Finset.sum_eq_single (1 : Fˣ)]
  · have : ∀ b : F, (if b = 0 then ((Fintype.card F : ℂ) - 1) ^ 2 else 1) =
        1 + if b = 0 then ((Fintype.card F : ℂ) - 1) ^ 2 - 1 else 0 := by
      intro b; split_ifs <;> ring
    simp only [if_true, this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, nsmul_eq_mul, mul_one]
    rw [hcard, hq]
    field_simp
    push_cast [hn]
    ring
  · intro a _ ha
    simp [ha]
  · simp

open scoped ComplexOrder in
lemma stdChar_mem_irrChars (hF : 2 ≤ Fintype.card F) : stdChar F ∈ irrChars ℂ (AffGrp F) := by
  have : Invertible (Nat.card (AffGrp F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine mem_irrChars_of_pairing_eq_one stdChar_mem_virtualChars (pairing_stdChar hF) ?_
  rw [stdChar_one, show (Fintype.card F : ℂ) - 1 = ((Fintype.card F - 1 : ℕ) : ℂ) by
    rw [Nat.cast_sub (by omega)]; simp]
  exact_mod_cast (by omega : 0 < Fintype.card F - 1)

lemma linHom_one (ψ : Fˣ →* ℂˣ) : linHom ψ (1 : AffGrp F) = 1 := map_one _

/-- **Problem 3.22.**  The irreducible characters of the group `x ↦ ax + b` over a finite field `F_q`: the `q - 1`
characters `(a, b) ↦ ψ(a)` for `ψ` a character of `F_q^×`, together with one more character `stdChar`, of degree
`q - 1` (that of the representation on functions with zero sum). -/
@[kb "etingof2011" "Problem 3.22, p. 44"]
theorem irrChars_affine (hF : 2 ≤ Fintype.card F) :
    irrChars ℂ (AffGrp F) =
      Set.range (fun ψ : Fˣ →* ℂˣ => (⇑(linHom ψ) : AffGrp F → ℂ)) ∪ {stdChar F} := by
  classical
  haveI : Finite (Fˣ →* ℂˣ) := Nat.finite_of_card_ne_zero (by
    rw [nat_card_monoidHom_units_complex]; exact Nat.card_pos.ne')
  letI : Fintype (Fˣ →* ℂˣ) := Fintype.ofFinite _
  have hdual : Fintype.card (Fˣ →* ℂˣ) = Fintype.card F - 1 := by
    rw [← Nat.card_eq_fintype_card, nat_card_monoidHom_units_complex, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have hdisj : Disjoint (Finset.univ.image fun ψ : Fˣ →* ℂˣ => (⇑(linHom ψ) : AffGrp F → ℂ))
      {stdChar F} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    obtain ⟨ψ, -, hψ⟩ := Finset.mem_image.mp h
    have h1 := congrFun hψ ⟨1, 1⟩
    simp only [linHom_apply, stdChar] at h1
    simp at h1
    norm_num at h1
  have hS := irrChars_eq_of_sum_sq (G := AffGrp F)
    (Finset.univ.image (fun ψ : Fˣ →* ℂˣ => (⇑(linHom ψ) : AffGrp F → ℂ)) ∪ {stdChar F})
    (by
      intro χ hχ
      rcases Finset.mem_union.mp hχ with h | h
      · obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.mp h
        exact hom_mem_irrChars _
      · rw [Finset.mem_singleton.mp h]; exact stdChar_mem_irrChars hF)
    (by
      rw [Finset.sum_union hdisj, Finset.sum_image (fun ψ _ ψ' _ h => linHom_injective h),
        Finset.sum_singleton]
      simp only [linHom_one, one_pow, Finset.sum_const, Finset.card_univ, hdual, stdChar_one,
        nsmul_eq_mul, mul_one, card_aff]
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Fintype.card F = n + 2 := ⟨Fintype.card F - 2, by omega⟩
      rw [hn]
      push_cast [Nat.add_sub_cancel]
      ring_nf)
  rw [hS]
  simp [Set.union_comm]

/-- **Problem 3.22, counts.**  There are exactly `q` irreducible representations. -/
@[kb "etingof2011" "Problem 3.22, p. 44"]
theorem card_irrChars_affine (hF : 2 ≤ Fintype.card F) :
    Nat.card (irrChars ℂ (AffGrp F)) = Fintype.card F := by
  classical
  haveI : Finite (Fˣ →* ℂˣ) := Nat.finite_of_card_ne_zero (by
    rw [nat_card_monoidHom_units_complex]; exact Nat.card_pos.ne')
  have hdisj : Disjoint (Set.range (fun ψ : Fˣ →* ℂˣ => (⇑(linHom ψ) : AffGrp F → ℂ)))
      {stdChar F} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨ψ, hψ⟩
    have h1 := congrFun hψ ⟨1, 1⟩
    simp only [linHom_apply, stdChar] at h1
    simp at h1
    norm_num at h1
  rw [Nat.card_coe_set_eq, irrChars_affine hF, Set.ncard_union_eq hdisj (Set.finite_range _)
    (Set.finite_singleton _), Set.ncard_singleton, ← Set.image_univ,
    Set.ncard_image_of_injective _ linHom_injective, Set.ncard_univ, nat_card_monoidHom_units_complex,
    Nat.card_eq_fintype_card, Fintype.card_units]
  omega

/-- **Problem 3.22, dimensions.**  There is an irreducible representation of dimension `q - 1` with character
`stdChar`; all other irreducible representations are one-dimensional. -/
@[kb "etingof2011" "Problem 3.22, p. 44"]
theorem exists_irrRep_affine_dim (hF : 2 ≤ Fintype.card F) :
    ∃ X : IrrRep ℂ (AffGrp F), X.ρ.character = stdChar F ∧ Module.finrank ℂ X.V = Fintype.card F - 1 := by
  obtain ⟨X, hX⟩ := stdChar_mem_irrChars hF
  refine ⟨X, hX, ?_⟩
  have h1 := char_one X.ρ
  have hX' : X.ρ.character = stdChar F := hX
  rw [hX', stdChar_one] at h1
  have : ((Module.finrank ℂ X.V : ℕ) : ℂ) = ((Fintype.card F - 1 : ℕ) : ℂ) := by
    rw [← h1, Nat.cast_sub (by omega)]; simp
  exact_mod_cast this

end AffGrp

end Affine

section Heisenberg

/-- The Heisenberg group of upper unitriangular `3 × 3` matrices over `ZMod p`: the triple `(x, y, w)` stands for
the matrix `[[1, x, w], [0, 1, y], [0, 0, 1]]`. -/
@[ext]
structure Heis (p : ℕ) where
  /-- The entry in position `(1,2)`. -/
  x : ZMod p
  /-- The entry in position `(2,3)`. -/
  y : ZMod p
  /-- The corner entry in position `(1,3)`. -/
  w : ZMod p

namespace Heis

variable {p : ℕ}

instance : Mul (Heis p) := ⟨fun g h => ⟨g.x + h.x, g.y + h.y, g.w + h.w + g.x * h.y⟩⟩
instance : One (Heis p) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis p) := ⟨fun g => ⟨-g.x, -g.y, -g.w + g.x * g.y⟩⟩

@[simp] lemma mul_x (g h : Heis p) : (g * h).x = g.x + h.x := rfl
@[simp] lemma mul_y (g h : Heis p) : (g * h).y = g.y + h.y := rfl
@[simp] lemma mul_w (g h : Heis p) : (g * h).w = g.w + h.w + g.x * h.y := rfl
@[simp] lemma one_x : (1 : Heis p).x = 0 := rfl
@[simp] lemma one_y : (1 : Heis p).y = 0 := rfl
@[simp] lemma one_w : (1 : Heis p).w = 0 := rfl
@[simp] lemma inv_x (g : Heis p) : (g⁻¹).x = -g.x := rfl
@[simp] lemma inv_y (g : Heis p) : (g⁻¹).y = -g.y := rfl
@[simp] lemma inv_w (g : Heis p) : (g⁻¹).w = -g.w + g.x * g.y := rfl

instance : Group (Heis p) where
  mul_assoc g h k := by ext <;> simp <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp <;> ring

/-- The matrix of an element of the Heisenberg group. -/
def toMatrix (g : Heis p) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![1, g.x, g.w; 0, 1, g.y; 0, 0, 1]

lemma toMatrix_mul (g h : Heis p) : toMatrix (g * h) = toMatrix g * toMatrix h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

lemma toMatrix_injective : Function.Injective (toMatrix : Heis p → Matrix (Fin 3) (Fin 3) (ZMod p)) := by
  intro g h hgh
  have h1 := congrFun (congrFun hgh 0) 1
  have h2 := congrFun (congrFun hgh 1) 2
  have h3 := congrFun (congrFun hgh 0) 2
  simp [toMatrix] at h1 h2 h3
  ext <;> assumption

/-- Every upper unitriangular matrix is the matrix of an element of the group. -/
lemma exists_toMatrix_eq (M : Matrix (Fin 3) (Fin 3) (ZMod p))
    (h : M = !![1, M 0 1, M 0 2; 0, 1, M 1 2; 0, 0, 1]) : ∃ g : Heis p, toMatrix g = M :=
  ⟨⟨M 0 1, M 1 2, M 0 2⟩, h.symm⟩

variable [NeZero p]

def equivProd : Heis p ≃ ZMod p × ZMod p × ZMod p where
  toFun g := (g.x, g.y, g.w)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Heis p) := Fintype.ofEquiv _ equivProd.symm

lemma sum_heis {M : Type*} [AddCommMonoid M] (f : Heis p → M) :
    ∑ g, f g = ∑ x : ZMod p, ∑ y : ZMod p, ∑ w : ZMod p, f ⟨x, y, w⟩ := by
  rw [Fintype.sum_equiv equivProd f (fun t => f ⟨t.1, t.2.1, t.2.2⟩) (fun g => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

lemma card_heis : Nat.card (Heis p) = p ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

/-- The representation `R_ψ` of the Heisenberg group on functions `ZMod p → ℂ`, for `ψ` an additive character:
`(x, y, w)` sends `f` to `t ↦ ψ(y t - w) f(t - x)`.  For `ψ(s) = z^s` this is the book's representation: the matrix
with `x = 1` shifts the argument and the matrix with `y = 1` multiplies by `z^t`. -/
noncomputable def repMap (ψ : AddChar (ZMod p) ℂ) (g : Heis p) : Module.End ℂ (ZMod p → ℂ) where
  toFun f t := ψ (g.y * t - g.w) * f (t - g.x)
  map_add' := by intros; ext; simp [mul_add]
  map_smul' := by intros; ext; simp; ring

lemma repMap_apply (ψ : AddChar (ZMod p) ℂ) (g : Heis p) (f : ZMod p → ℂ) (t : ZMod p) :
    repMap ψ g f t = ψ (g.y * t - g.w) * f (t - g.x) := rfl

/-- The representation `R_ψ` of the Heisenberg group on functions `ZMod p → ℂ`. -/
noncomputable def rep (ψ : AddChar (ZMod p) ℂ) : Representation ℂ (Heis p) (ZMod p → ℂ) where
  toFun := repMap ψ
  map_one' := by
    refine LinearMap.ext fun f => funext fun t => ?_
    simp [repMap_apply]
  map_mul' g h := by
    refine LinearMap.ext fun f => funext fun t => ?_
    show repMap ψ (g * h) f t = repMap ψ g (repMap ψ h f) t
    simp only [repMap_apply, mul_x, mul_y, mul_w]
    have e1 : (g.y + h.y) * t - (g.w + h.w + g.x * h.y) =
        g.y * t - g.w + (h.y * (t - g.x) - h.w) := by ring
    have e2 : t - (g.x + h.x) = t - g.x - h.x := by ring
    rw [e1, e2, AddChar.map_add_eq_mul, mul_assoc]

lemma character_rep_aux (ψ : AddChar (ZMod p) ℂ) (g : Heis p) :
    (rep ψ).character g = if g.x = 0 then ∑ s : ZMod p, ψ (g.y * s - g.w) else 0 := by
  classical
  rw [Representation.character]
  show LinearMap.trace ℂ _ (repMap ψ g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod p))]
  simp [Matrix.trace, Matrix.diag, repMap_apply, Pi.single_apply]

end Heis

section HeisPrime

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

namespace Heis

/-- The character of `R_ψ` for a nontrivial additive character `ψ`: it is supported on the centre. -/
noncomputable def repChar (ψ : AddChar (ZMod p) ℂ) (g : Heis p) : ℂ :=
  if g.x = 0 ∧ g.y = 0 then (p : ℂ) * ψ (-g.w) else 0

lemma character_rep (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    (rep ψ).character = repChar ψ := by
  funext g
  rw [character_rep_aux]
  unfold repChar
  by_cases hx : g.x = 0
  · by_cases hy : g.y = 0
    · simp [hx, hy, sub_eq_add_neg]
    · have h0 : ∑ s : ZMod p, ψ (g.y * s) = 0 := by
        rw [Fintype.sum_equiv (Equiv.mulLeft₀ g.y hy) (fun s => ψ (g.y * s)) (fun s => ψ s)
          (fun s => rfl)]
        exact AddChar.sum_eq_zero_of_ne_one hψ
      have : ∑ s : ZMod p, ψ (g.y * s - g.w) = ψ (-g.w) * ∑ s : ZMod p, ψ (g.y * s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      simp [hx, hy, this, h0]
  · simp [hx]

lemma repChar_one (ψ : AddChar (ZMod p) ℂ) : repChar ψ 1 = p := by
  simp [repChar]

lemma hermitianPairing_repChar (ψ : AddChar (ZMod p) ℂ) :
    hermitianPairing (repChar ψ) (repChar ψ) = 1 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have key : ∀ x y w : ZMod p, repChar ψ ⟨x, y, w⟩ * conj (repChar ψ ⟨x, y, w⟩) =
      if x = 0 then (if y = 0 then (p : ℂ) ^ 2 else 0) else 0 := by
    intro x y w
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · have : ψ (-w) * conj (ψ (-w)) = 1 := by
          rw [← AddChar.map_neg_eq_conj, neg_neg, ← AddChar.map_add_eq_mul, neg_add_cancel,
            AddChar.map_zero_eq_one]
        simp only [repChar, hx, hy, and_self, if_true, map_mul, Complex.conj_natCast]
        linear_combination (p : ℂ) ^ 2 * this
      · simp [repChar, hx, hy]
    · simp [repChar, hx]
  unfold hermitianPairing
  rw [sum_heis]
  simp only [key]
  rw [Finset.sum_eq_single (0 : ZMod p) (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single (0 : ZMod p) (fun y _ hy => by simp [hy]) (by simp)]
  simp only [if_true, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, card_heis]
  push_cast
  field_simp

/-- For a nontrivial additive character `ψ`, the representation `R_ψ` is irreducible. -/
theorem isIrreducible_rep (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) : IsIrreducible (rep ψ) := by
  apply isIrreducible_of_hermitianPairing_self_eq_one
  rw [character_rep ψ hψ]
  exact hermitianPairing_repChar ψ

/-- The characters `(x, y, w) ↦ exp(2πi (a x + b y)/p)`. -/
noncomputable def linHom (a b : ZMod p) : Heis p →* ℂ where
  toFun g := ee (a * g.x + b * g.y)
  map_one' := by simp
  map_mul' g h := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [mul_x, mul_y]
    ring

lemma linHom_apply (a b : ZMod p) (g : Heis p) : linHom a b g = ee (a * g.x + b * g.y) := rfl

lemma linHom_injective : Function.Injective fun q : ZMod p × ZMod p => (⇑(linHom q.1 q.2) : Heis p → ℂ) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 := congrFun h ⟨1, 0, 0⟩
  have h2 := congrFun h ⟨0, 1, 0⟩
  simp only [linHom_apply, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  have e1 := (ZMod.injective_stdAddChar (N := p)) h1
  have e2 := (ZMod.injective_stdAddChar (N := p)) h2
  rw [e1, e2]

/-- The additive character `s ↦ exp(2πi k s/p)`. -/
noncomputable def psi (k : ZMod p) : AddChar (ZMod p) ℂ := (ee : AddChar (ZMod p) ℂ).mulShift k

lemma psi_apply (k s : ZMod p) : psi k s = ee (k * s) := AddChar.mulShift_apply

lemma psi_ne_one {k : ZMod p} (hk : k ≠ 0) : psi k ≠ 1 := by
  intro h
  have := congrArg (fun χ : AddChar (ZMod p) ℂ => χ 1) h
  simp only [psi_apply, mul_one] at this
  exact hk ((ee_eq_one_iff k).mp (by simpa using this))

lemma repChar_psi_injective {k k' : ZMod p} (h : repChar (psi k) = repChar (psi k')) : k = k' := by
  have h1 := congrFun h ⟨0, 0, 1⟩
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  simp only [repChar, and_self, if_true, psi_apply] at h1
  have h2 := mul_left_cancel₀ hp h1
  have := (ZMod.injective_stdAddChar (N := p)) h2
  simpa using this

/-- **Problem 3.18 (d).**  The irreducible characters of the Heisenberg group over `F_p` are the `p²` linear
characters `linHom a b` and the `p - 1` characters `repChar (psi k)`, `k ≠ 0`, of the representations `R_z`
(`z = exp(2πi k/p)`), which have dimension `p`. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
theorem irrChars_heis :
    irrChars ℂ (Heis p) =
      Set.range (fun q : ZMod p × ZMod p => (⇑(linHom q.1 q.2) : Heis p → ℂ)) ∪
        (fun k : ZMod p => repChar (psi k)) '' {k | k ≠ 0} := by
  classical
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hp1' : (1 : ℂ) ≠ p := by
    intro h; have : (1 : ℕ) = p := by exact_mod_cast h
    omega
  have hdisj : Disjoint (Finset.univ.image fun q : ZMod p × ZMod p => (⇑(linHom q.1 q.2) : Heis p → ℂ))
      ((Finset.univ.filter fun k : ZMod p => k ≠ 0).image fun k => repChar (psi k)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hx'
    have h1 := congrFun hk 1
    rw [repChar_one] at h1
    simp only [linHom_apply, one_x, one_y, mul_zero, add_zero, AddChar.map_zero_eq_one] at h1
    exact hp1' h1.symm
  have hS := irrChars_eq_of_sum_sq (G := Heis p)
    (Finset.univ.image (fun q : ZMod p × ZMod p => (⇑(linHom q.1 q.2) : Heis p → ℂ)) ∪
      (Finset.univ.filter fun k : ZMod p => k ≠ 0).image fun k => repChar (psi k))
    (by
      intro χ hχ
      rcases Finset.mem_union.mp hχ with h | h
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp h
        exact hom_mem_irrChars _
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
        have hk' : k ≠ 0 := (Finset.mem_filter.mp hk).2
        have := isIrreducible_rep (psi k) (psi_ne_one hk')
        exact ⟨{ V := ZMod p → ℂ, ρ := rep (psi k) }, character_rep _ (psi_ne_one hk')⟩)
    (by
      rw [Finset.sum_union hdisj, Finset.sum_image (fun q _ q' _ h => linHom_injective h),
        Finset.sum_image (fun k _ k' _ h => repChar_psi_injective h)]
      simp only [map_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
        nsmul_eq_mul, repChar_one, card_heis]
      have hc : (Finset.univ.filter fun k : ZMod p => k ≠ 0).card = p - 1 := by
        rw [Finset.filter_ne' Finset.univ (0 : ZMod p), Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card]
      rw [hc]
      obtain ⟨m, hm⟩ : ∃ m : ℕ, p = m + 2 := ⟨p - 2, by omega⟩
      rw [hm]
      push_cast [Nat.add_sub_cancel]
      ring_nf)
  rw [hS]
  ext χ
  simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
    Set.mem_range, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]

/-- The book's representation `R_z`, for a complex number `z` with `z^p = 1`:
`(x, y, w) ↦ (f ↦ (t ↦ z^{y t - w} f(t - x)))`. -/
noncomputable def heisRep (z : ℂ) (hz : z ^ p = 1) : Representation ℂ (Heis p) (ZMod p → ℂ) :=
  rep (AddChar.zmodChar p hz)

/-- On the generators of the book, `R_z` shifts the argument for the matrix with entry `x = 1` and multiplies
by `z^t` for the matrix with entry `y = 1` (here `t` is read through its representative in `[0,p)`). -/
lemma heisRep_generators (z : ℂ) (hz : z ^ p = 1) (f : ZMod p → ℂ) (t : ZMod p) :
    heisRep z hz ⟨1, 0, 0⟩ f t = f (t - 1) ∧ heisRep z hz ⟨0, 1, 0⟩ f t = z ^ t.val * f t := by
  constructor
  · simp [heisRep, rep, repMap_apply]
  · simp [heisRep, rep, repMap_apply, AddChar.zmodChar_apply]

lemma zmodChar_ne_one {z : ℂ} (hz : z ^ p = 1) (h1 : z ≠ 1) : AddChar.zmodChar p hz ≠ 1 := by
  intro h
  have h2 : AddChar.zmodChar p hz 1 = (1 : AddChar (ZMod p) ℂ) 1 := by rw [h]
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rw [AddChar.zmodChar_apply, ZMod.val_one p] at h2
  exact h1 (by simpa using h2)

lemma zmodChar_eq_one {hz : (1 : ℂ) ^ p = 1} : AddChar.zmodChar p hz = 1 := by
  ext s
  simp [AddChar.zmodChar_apply]

/-- The trivial-parameter representation `R_1` (shifts only) has the constants as a proper nonzero
subrepresentation, so it is not irreducible. -/
lemma not_isIrreducible_rep_one : ¬ IsIrreducible (rep (1 : AddChar (ZMod p) ℂ)) := by
  intro hirr
  have hp1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  let S : Subrepresentation (rep (1 : AddChar (ZMod p) ℂ)) :=
    { toSubmodule := Submodule.span ℂ {fun _ : ZMod p => (1 : ℂ)}
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
        refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
        funext t
        show _ = repMap 1 g (c • fun _ => (1 : ℂ)) t
        simp [repMap_apply] }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · have hmem : (fun _ : ZMod p => (1 : ℂ)) ∈ S.toSubmodule :=
      Submodule.subset_span (Set.mem_singleton _)
    have := congrArg Subrepresentation.toSubmodule h
    rw [this] at hmem
    have h0 := congrFun (Submodule.mem_bot ℂ |>.mp hmem) 0
    simp at h0
  · have hmem : (Pi.single 0 1 : ZMod p → ℂ) ∈ S.toSubmodule := by
      have := congrArg Subrepresentation.toSubmodule h
      rw [this]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [Pi.single_apply, hp1] at h0 h1
    rw [h0] at h1
    simp at h1

/-- **Problem 3.18 (b).**  `R_z` is irreducible if and only if `z ≠ 1`. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
theorem isIrreducible_heisRep_iff (z : ℂ) (hz : z ^ p = 1) :
    IsIrreducible (heisRep z hz) ↔ z ≠ 1 := by
  constructor
  · intro h hz1
    subst hz1
    exact not_isIrreducible_rep_one (by simpa [heisRep, zmodChar_eq_one] using h)
  · intro h
    exact isIrreducible_rep _ (zmodChar_ne_one hz h)

/-- **Problem 3.18 (c).**  Every one-dimensional character of the Heisenberg group is one of the `p²` characters
`linHom a b`; they are pairwise distinct. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
theorem exists_linHom_eq (φ : Heis p →* ℂ) : ∃ a b : ZMod p, ⇑φ = ⇑(linHom a b) := by
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hmem := hom_mem_irrChars φ
  rw [irrChars_heis] at hmem
  rcases hmem with ⟨q, hq⟩ | ⟨k, hk, hk'⟩
  · exact ⟨q.1, q.2, hq.symm⟩
  · exfalso
    have h1 : repChar (psi k) 1 = φ 1 := congrFun hk' 1
    rw [repChar_one, map_one] at h1
    have : (p : ℕ) = 1 := by exact_mod_cast h1
    omega

/-- **Problem 3.18 (c), decomposition of `R_1`.**  The character of `R_1` is the sum of the `p` linear characters
`linHom a 0`, which are pairwise distinct. -/
@[kb "etingof2011" "Problem 3.18, p. 43"]
theorem character_rep_one :
    (rep (1 : AddChar (ZMod p) ℂ)).character = ∑ a : ZMod p, (⇑(linHom a 0) : Heis p → ℂ) := by
  funext g
  rw [character_rep_aux, Finset.sum_apply]
  simp only [linHom_apply, zero_mul, add_zero, AddChar.one_apply, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one]
  by_cases hx : g.x = 0
  · simp [hx]
  · have := sum_ee_mul (N := p) g.x
    simp only [mul_comm _ g.x] at *
    simp [hx, this]

end Heis

end HeisPrime

end Heisenberg

end UndergradKB.RepresentationTheory
