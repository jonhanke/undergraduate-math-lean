import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Trace
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.ComplexCharacters
import UndergradKB.RepresentationTheory.VirtualCharacters
import UndergradKB.RepresentationTheory.CharactersChapter4

/-! # Character tables of small groups (Etingof et al., Example 3.15)

The character table of `S4` (the table of `Q8` is `irrChars_q8` in `CharactersChapter4.lean`).

The five classes of `S4` are determined by the number `f` of fixed points together with the sign `ε`: the identity
(`f = 4`), transpositions (`f = 2`), double transpositions (`f = 0`, `ε = 1`), three-cycles (`f = 1`) and four-cycles
(`f = 0`, `ε = -1`).  The irreducible characters are the trivial character, the sign, the standard character `f - 1`,
its twist `(f - 1) ε`, and the two-dimensional character (values `2, 0, 2, -1, 0` on the classes in the order above).

Strategy: all five class functions are shown to be integer combinations of characters of explicit representations
(trivial, sign, the permutation representation and its tensor products), hence virtual characters; each has norm one
and positive value at `1`, hence is irreducible (Lemma 4.27); they are pairwise distinct, and `S4` has exactly five
irreducible characters (the number of partitions of `4`).
-/

namespace UndergradKB.RepresentationTheory

open Representation Module Equiv

namespace S4Table

/-- The number of fixed points of a permutation of `{0,1,2,3}`. -/
def fixZ (g : Perm (Fin 4)) : ℤ := ((Finset.univ.filter fun x => g x = x).card : ℤ)

/-- The sign of a permutation of `{0,1,2,3}`, as an integer. -/
def signZ (g : Perm (Fin 4)) : ℤ := ((Perm.sign g : ℤˣ) : ℤ)

/-- The values of the two-dimensional character of `S4`, read off from fixed points and sign. -/
def twoZ (g : Perm (Fin 4)) : ℤ :=
  if fixZ g = 4 ∨ (fixZ g = 0 ∧ signZ g = 1) then 2 else if fixZ g = 1 then -1 else 0

/-- The integer-valued characters of `S4`, indexed by `Fin 5`: trivial, sign, standard, standard twisted by the sign,
and the two-dimensional character. -/
def chiZ : Fin 5 → Perm (Fin 4) → ℤ
  | 0 => fun _ => 1
  | 1 => signZ
  | 2 => fun g => fixZ g - 1
  | 3 => fun g => (fixZ g - 1) * signZ g
  | 4 => twoZ

/-- The trivial character of `S4`. -/
def s4Triv : Perm (Fin 4) → ℂ := fun g => (chiZ 0 g : ℂ)
/-- The sign character of `S4`. -/
def s4Sign : Perm (Fin 4) → ℂ := fun g => (chiZ 1 g : ℂ)
/-- The character of the standard three-dimensional representation of `S4`: number of fixed points minus one. -/
def s4Std : Perm (Fin 4) → ℂ := fun g => (chiZ 2 g : ℂ)
/-- The character of the standard representation tensored with the sign. -/
def s4StdSign : Perm (Fin 4) → ℂ := fun g => (chiZ 3 g : ℂ)
/-- The character of the two-dimensional representation of `S4` (through `S4 → S3`). -/
def s4Two : Perm (Fin 4) → ℂ := fun g => (chiZ 4 g : ℂ)

/-- The five characters as a family indexed by `Fin 5`. -/
def s4Chi (i : Fin 5) : Perm (Fin 4) → ℂ := fun g => (chiZ i g : ℂ)

noncomputable instance : Invertible (Nat.card (Perm (Fin 4)) : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

theorem card_perm_four : Nat.card (Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-! ### Characters of explicit representations -/

/-- The sign as a homomorphism to `ℂ`. -/
def signHom : Perm (Fin 4) →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Perm.sign)

/-- The permutation representation of `S4` on `ℂ^4`. -/
noncomputable abbrev permRep : Representation ℂ (Perm (Fin 4)) (MonoidAlgebra ℂ (Fin 4)) :=
  Representation.ofMulAction ℂ (Perm (Fin 4)) (Fin 4)

theorem character_permRep (g : Perm (Fin 4)) : permRep.character g = (fixZ g : ℂ) := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ
    (MonoidAlgebra.basis (Fin 4) ℂ), fixZ]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Representation.ofMulAction_single,
    MonoidAlgebra.basis, Finsupp.single_apply]

/-- The character of any finite-dimensional complex representation of a finite group is a virtual character. -/
theorem character_mem_virtualChars {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : ρ.character ∈ virtualChars ℂ G := by
  classical
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := eq_sum_pairing_smul (character_mem_classFunctions ρ)
  rw [h]
  refine Submodule.sum_mem _ fun χ _ => ?_
  obtain ⟨X, hX⟩ := χ.2
  have hp : pairing ρ.character (χ : G → ℂ) = (finrank ℂ (IntertwiningMap X.ρ ρ) : ℂ) := by
    rw [← hX, ← hermitianPairing_character]
    exact hermitianPairing_character_eq_finrank ρ X.ρ
  rw [hp, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem (Submodule.subset_span χ.2) _

theorem fixC_mem : (fun g => (fixZ g : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)) := by
  have := character_mem_virtualChars permRep
  rwa [show permRep.character = fun g => (fixZ g : ℂ) from funext character_permRep] at this

theorem one_mem : (fun _ : Perm (Fin 4) => (1 : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)) := by
  have := character_mem_virtualChars (lineRep' (1 : Perm (Fin 4) →* ℂ))
  rwa [show (lineRep' (1 : Perm (Fin 4) →* ℂ)).character = fun _ => (1 : ℂ) from
    funext fun g => character_lineRep' _ g] at this

theorem signC_mem : (fun g => (signZ g : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)) := by
  have := character_mem_virtualChars (lineRep' signHom)
  rwa [show (lineRep' signHom).character = fun g => (signZ g : ℂ) from
    funext fun g => by rw [character_lineRep']; rfl] at this

theorem fixSq_mem : (fun g => (fixZ g : ℂ) * (fixZ g : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)) := by
  have := character_mem_virtualChars (V := TensorProduct ℂ (MonoidAlgebra ℂ (Fin 4)) (MonoidAlgebra ℂ (Fin 4)))
    (permRep.tprod permRep)
  rwa [Representation.char_tensor, show permRep.character = fun g => (fixZ g : ℂ) from
    funext character_permRep] at this

theorem fixSign_mem : (fun g => (fixZ g : ℂ) * (signZ g : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)) := by
  have := character_mem_virtualChars (V := TensorProduct ℂ (MonoidAlgebra ℂ (Fin 4)) ℂ)
    (permRep.tprod (lineRep' signHom))
  rwa [Representation.char_tensor, show permRep.character = fun g => (fixZ g : ℂ) from
    funext character_permRep, show (lineRep' signHom).character = fun g => (signZ g : ℂ) from
    funext fun g => by rw [character_lineRep']; rfl] at this

theorem twoZ_eq (g : Perm (Fin 4)) :
    twoZ g = 1 + signZ g - 3 * fixZ g - fixZ g * signZ g + fixZ g * fixZ g := by
  revert g
  decide

open scoped ComplexOrder in
/-- A class function that is an integer-valued virtual character with norm `1` and value `> 0` at `1` is
irreducible. -/
theorem mem_irrChars_of_int (z : Perm (Fin 4) → ℤ)
    (hV : (fun g => (z g : ℂ)) ∈ virtualChars ℂ (Perm (Fin 4)))
    (hn : ∑ g, z g * z g⁻¹ = 24) (hpos : 0 < z 1) : (fun g => (z g : ℂ)) ∈ irrChars ℂ (Perm (Fin 4)) := by
  refine mem_irrChars_of_pairing_eq_one hV ?_ ?_
  · rw [pairing_apply, card_perm_four]
    have : ∑ g, (z g : ℂ) * (z g⁻¹ : ℂ) = 24 := by exact_mod_cast hn
    rw [this]
    norm_num
  · show (0 : ℂ) < ((z 1 : ℤ) : ℂ)
    exact_mod_cast hpos

theorem chiZ_mem_irrChars (i : Fin 5) : s4Chi i ∈ irrChars ℂ (Perm (Fin 4)) := by
  have hone := one_mem
  have hsign := signC_mem
  have hfix := fixC_mem
  have hsq := fixSq_mem
  have hfs := fixSign_mem
  apply mem_irrChars_of_int (chiZ i)
  · fin_cases i
    · simpa [chiZ] using hone
    · simpa [chiZ] using hsign
    · have := Submodule.sub_mem _ hfix hone
      convert this using 1
      funext g
      simp [chiZ]
    · have := Submodule.sub_mem _ hfs hsign
      convert this using 1
      funext g
      simp [chiZ]
      ring
    · have := Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ hone hsign)
        (Submodule.smul_mem _ (3 : ℤ) hfix)) hfs) hsq
      convert this using 1
      funext g
      simp [chiZ, twoZ_eq]
  · revert i
    decide
  · revert i
    decide

theorem s4Chi_injective : Function.Injective s4Chi := by
  intro i j h
  have h1 := Int.cast_injective (α := ℂ) (congrFun h 1)
  have h2 := Int.cast_injective (α := ℂ) (congrFun h (swap 0 1))
  have key : ∀ i j : Fin 5, chiZ i 1 = chiZ j 1 → chiZ i (swap 0 1) = chiZ j (swap 0 1) → i = j := by
    decide
  exact key i j h1 h2

/-- Representatives of the five conjugacy classes of `S4`: identity, transposition, double transposition,
three-cycle, four-cycle. -/
def classRep : Fin 5 → Perm (Fin 4)
  | 0 => 1
  | 1 => swap 0 1
  | 2 => swap 0 1 * swap 2 3
  | 3 => swap 0 1 * swap 1 2
  | 4 => swap 0 1 * swap 1 2 * swap 2 3

theorem exists_conj_classRep : ∀ g : Perm (Fin 4), ∃ i : Fin 5, ∃ c : Perm (Fin 4), c * g * c⁻¹ = classRep i := by
  decide

theorem ncard_irrChars_s4_le : (irrChars ℂ (Perm (Fin 4))).ncard ≤ 5 := by
  rw [← Nat.card_coe_set_eq, card_irrChars (k := ℂ) (G := Perm (Fin 4))]
  have hsurj : Function.Surjective fun i : Fin 5 => ConjClasses.mk (classRep i) := by
    intro x
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
    obtain ⟨i, c, hc⟩ := exists_conj_classRep g
    refine ⟨i, ?_⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, ← hc]
    exact (isConj_iff.mpr ⟨c, rfl⟩).symm
  simpa using Nat.card_le_card_of_surjective _ hsurj

end S4Table

open S4Table in
/-- **Etingof et al., Example 3.15** (character table of `S4`): the irreducible complex characters of the symmetric
group on four letters are exactly the trivial character, the sign, the standard character (fixed points minus one),
the standard character twisted by the sign, and the two-dimensional character. They are given in terms of the
number `f` of fixed points and the sign `ε` (see the module docstring for the correspondence with cycle types):
`1`, `ε`, `f - 1`, `(f - 1) ε` and `twoZ`, which is `2` on the identity and the double transpositions, `-1` on the
three-cycles and `0` on transpositions and four-cycles. -/
@[kb "etingof2011" "Example 3.15, p. 41"]
theorem irrChars_perm_four :
    irrChars ℂ (Perm (Fin 4)) = {s4Triv, s4Sign, s4Std, s4StdSign, s4Two} := by
  have hsub : Set.range s4Chi ⊆ irrChars ℂ (Perm (Fin 4)) := by
    rintro _ ⟨i, rfl⟩
    exact chiZ_mem_irrChars i
  have hrange : Set.range s4Chi = {s4Triv, s4Sign, s4Std, s4StdSign, s4Two} := by
    ext f
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
  rw [← hrange]
  symm
  refine Set.eq_of_subset_of_ncard_le hsub ?_ irrChars_finite
  refine ncard_irrChars_s4_le.trans ?_
  rw [← Set.image_univ, Set.ncard_image_of_injective _ s4Chi_injective, Set.ncard_univ]
  simp

end UndergradKB.RepresentationTheory
