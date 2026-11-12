import Mathlib.Analysis.Complex.Polynomial.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.Artin
import UndergradKB.RepresentationTheory.AbelianCharacters
import UndergradKB.RepresentationTheory.LittleGroupTheorem

/-! # Exhaustion in the little group method (Etingof et al., Theorem 4.75)

* `exists_equiv_of_sum_finrank_sq`: a family of pairwise non-isomorphic irreducible complex representations of a
  finite group whose squared dimensions add up to the group order contains every irreducible representation.
* `DualChar`: the dual of `A` with the action of `G` (`(g x)(a) = x (g⁻¹ a)`), whose stabilizers are `stabChar`.
* `exists_equiv_littleInd`: every irreducible representation of `A ⋊ G` is isomorphic to some `V_(O,U)`.
-/

set_option linter.unusedSectionVars false

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

section General

variable {Γ : Type v} [Group Γ] [Fintype Γ]

/-- The dimension (as a natural number) of a chosen irreducible representation with character `χ`. -/
noncomputable def irrCharDim (χ : irrChars ℂ Γ) : ℕ := finrank ℂ χ.2.choose.V

lemma irrChar_spec (χ : irrChars ℂ Γ) : χ.2.choose.ρ.character = (χ : Γ → ℂ) := χ.2.choose_spec

lemma irrChar_one (χ : irrChars ℂ Γ) : (χ : Γ → ℂ) 1 = (irrCharDim χ : ℂ) := by
  rw [← irrChar_spec χ, char_one]
  rfl

/-- The squares of the dimensions of the irreducible representations of `Γ` (one for each irreducible
character) add up to the order of `Γ`. -/
theorem sum_irrCharDim_sq : ∑ χ : irrChars ℂ Γ, irrCharDim χ ^ 2 = Nat.card Γ := by
  have h := sum_irrChars_one_sq (k := ℂ) (G := Γ)
  simp only [irrChar_one] at h
  exact_mod_cast h

theorem irrCharDim_pos (χ : irrChars ℂ Γ) : 0 < irrCharDim χ := by
  have := finrank_ne_zero_of_isIrreducible (k := ℂ) (ρ := χ.2.choose.ρ)
  exact Nat.pos_of_ne_zero (by exact_mod_cast this)

/-- A family of pairwise non-isomorphic irreducible representations of a finite group whose dimensions
squared add up to the order of the group contains every irreducible representation up to isomorphism. -/
theorem exists_equiv_of_sum_finrank_sq {ι : Type*} [Fintype ι] (X : ι → IrrRep ℂ Γ)
    (hinj : ∀ i j, Nonempty (Representation.Equiv (X i).ρ (X j).ρ) → i = j)
    (hsum : ∑ i, finrank ℂ (X i).V ^ 2 = Nat.card Γ) (Y : IrrRep ℂ Γ) :
    ∃ i, Nonempty (Representation.Equiv Y.ρ (X i).ρ) := by
  classical
  by_contra hno
  push Not at hno
  let e : ι → irrChars ℂ Γ := fun i => ⟨(X i).ρ.character, X i, rfl⟩
  have he : Function.Injective e := fun i j h =>
    hinj i j ((nonempty_equiv_iff_character_eq _ _).mpr (congrArg Subtype.val h))
  have hdim : ∀ i, irrCharDim (e i) = finrank ℂ (X i).V := by
    intro i
    have h1 := irrChar_one (e i)
    have h2 : ((e i : irrChars ℂ Γ) : Γ → ℂ) 1 = (finrank ℂ (X i).V : ℂ) := char_one _
    exact_mod_cast h1.symm.trans h2
  let χY : irrChars ℂ Γ := ⟨Y.ρ.character, Y, rfl⟩
  have hY : χY ∉ Finset.univ.image e := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    obtain ⟨f⟩ := (nonempty_equiv_iff_character_eq _ _).mpr (congrArg Subtype.val hi)
    exact (hno i).false f.symm
  have hlt := Finset.sum_lt_sum_of_subset (f := fun χ : irrChars ℂ Γ => irrCharDim χ ^ 2)
    (Finset.subset_univ (Finset.univ.image e)) (Finset.mem_univ χY) hY
    (pow_pos (irrCharDim_pos χY) 2) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_image (fun i _ j _ h => he h), sum_irrCharDim_sq] at hlt
  simp only [hdim] at hlt
  omega

end General

section Little

variable {A : Type u} {G : Type v} [CommGroup A] [Group G]

/-- The dual of `A` (its characters `A →* ℂˣ`), as a type carrying the action of `G` through `φ`. -/
def DualChar (_φ : G →* MulAut A) : Type u := A →* ℂˣ

namespace DualChar

variable {φ : G →* MulAut A}

/-- The underlying character. -/
def toHom (x : DualChar φ) : A →* ℂˣ := x

/-- A character viewed as an element of the dual with its `G`-action. -/
def ofHom (φ : G →* MulAut A) (x : A →* ℂˣ) : DualChar φ := x

lemma ext {x y : DualChar φ} (h : x.toHom = y.toHom) : x = y := h

/-- `(g x)(a) = x (g⁻¹ a)`. -/
instance : SMul G (DualChar φ) := ⟨fun g x => ofHom φ (x.toHom.comp (φ g⁻¹).toMonoidHom)⟩

lemma toHom_smul (g : G) (x : DualChar φ) (a : A) : (g • x).toHom a = x.toHom (φ g⁻¹ a) := rfl

lemma apply_inv_apply (g : G) (a : A) : φ g⁻¹ (φ g a) = a := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

lemma apply_apply_inv (g : G) (a : A) : φ g (φ g⁻¹ a) = a := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

instance : MulAction G (DualChar φ) where
  one_smul x := ext (MonoidHom.ext fun a => by rw [toHom_smul]; simp)
  mul_smul g h x := ext (MonoidHom.ext fun a => by
    simp only [toHom_smul, mul_inv_rev, map_mul, MulAut.mul_apply])

/-- The stabilizer of a character under the action on the dual is the group `G_x` used in the little group
method. -/
lemma stabilizer_eq (y : DualChar φ) : MulAction.stabilizer G y = stabChar φ y.toHom := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_stabChar]
  constructor
  · intro h a
    have := congrArg (fun z : DualChar φ => z.toHom (φ g a)) h
    simp only [toHom_smul, apply_inv_apply] at this
    exact this.symm
  · intro h
    refine ext (MonoidHom.ext fun a => ?_)
    rw [toHom_smul]
    have := h (φ g⁻¹ a)
    rw [apply_apply_inv] at this
    exact this.symm

lemma exists_forall_ne_of_not_mem_orbit {y y' : DualChar φ} (h : y' ∉ MulAction.orbit G y) (g : G) :
    ∃ a, y'.toHom a ≠ y.toHom (φ g a) := by
  by_contra hc
  push Not at hc
  apply h
  refine ⟨g⁻¹, ext (MonoidHom.ext fun a => ?_)⟩
  rw [toHom_smul, inv_inv]
  exact (hc a).symm

/-- Orbit-stabilizer for the action on the dual. -/
lemma card_orbit_mul_card_stabChar (y : DualChar φ) :
    Nat.card (MulAction.orbit G y) * Nat.card (stabChar φ y.toHom) = Nat.card G := by
  rw [← stabilizer_eq y, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G y)

instance [Finite A] : Finite (DualChar φ) := by
  have : Nat.card (A →* ℂˣ) ≠ 0 := by
    rw [nat_card_monoidHom_units_complex]
    exact Nat.card_pos.ne'
  exact Nat.finite_of_card_ne_zero this

noncomputable instance fintypeOrbitQuot [Finite A] :
    Fintype (MulAction.orbitRel.Quotient G (DualChar φ)) := Fintype.ofFinite _

/-- The orbits of `G` on the dual of `A` partition it: the orbit sizes add up to `|A|`. -/
theorem sum_card_orbit [Finite A] :
    ∑ ω : MulAction.orbitRel.Quotient G (DualChar φ), Nat.card (MulAction.orbit G ω.out) = Nat.card A := by
  rw [← nat_card_monoidHom_units_complex A]
  have h1 : Nat.card (A →* ℂˣ) = Nat.card (DualChar φ) := rfl
  rw [h1, Nat.card_congr (MulAction.selfEquivSigmaOrbits G (DualChar φ)), Nat.card_sigma]

end DualChar

open DualChar

noncomputable instance fintypeStabChar [Finite G] {φ : G →* MulAut A} (x : A →* ℂˣ) :
    Fintype (stabChar φ x) := Fintype.ofFinite _

section Counting

variable [Fintype A] [Fintype G] (φ : G →* MulAut A)

lemma index_littleSub_mul_card (x : A →* ℂˣ) :
    (littleSub φ x).index * Nat.card (stabChar φ x) = Nat.card G := by
  have h := Subgroup.card_mul_index (littleSub φ x)
  rw [card_littleSub, card_semidirectProduct] at h
  have hA : 0 < Nat.card A := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hA ?_
  rw [← h]
  ring

lemma index_littleSub_eq_card_orbit (y : DualChar φ) :
    (littleSub φ y.toHom).index = Nat.card (MulAction.orbit G y) := by
  have hH : 0 < Nat.card (stabChar φ y.toHom) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hH ?_
  rw [index_littleSub_mul_card, card_orbit_mul_card_stabChar]

lemma sum_index_littleSub :
    ∑ ω : MulAction.orbitRel.Quotient G (DualChar φ), (littleSub φ ω.out.toHom).index = Nat.card A := by
  rw [← sum_card_orbit (φ := φ)]
  exact Finset.sum_congr rfl fun ω _ => index_littleSub_eq_card_orbit φ ω.out

/-- The little group representation `V_(O,U)`, packaged as an irreducible representation of `A ⋊ G`. -/
noncomputable def littleIrr (x : A →* ℂˣ) (U : IrrRep ℂ (stabChar φ x)) : IrrRep ℂ (A ⋊[φ] G) :=
  haveI : IsIrreducible (Ind (littleSub φ x) (littleRep φ x U.ρ)) := isIrreducible_littleInd φ x U.ρ
  haveI : FiniteDimensional ℂ (coindV (littleSub φ x).subtype (littleRep φ x U.ρ)) :=
    haveI : Finite (RCosets (littleSub φ x)) := inferInstance
    Module.Finite.equiv (indEquivPi (littleSub φ x) (littleRep φ x U.ρ)).symm
  { V := coindV (littleSub φ x).subtype (littleRep φ x U.ρ)
    ρ := Ind (littleSub φ x) (littleRep φ x U.ρ) }

/-- The index set of the representations `V_(O,U)`: an orbit `O` (with chosen representative) together with an
irreducible character of the stabilizer of the representative. -/
abbrev LittleIdx : Type (max u v) :=
  Σ ω : MulAction.orbitRel.Quotient G (DualChar φ), irrChars ℂ (stabChar φ ω.out.toHom)

/-- The family of representations `V_(O,U)` of `A ⋊ G`. -/
noncomputable def littleFamily (i : LittleIdx φ) : IrrRep ℂ (A ⋊[φ] G) :=
  littleIrr φ i.1.out.toHom i.2.2.choose

theorem littleFamily_injective (i j : LittleIdx φ)
    (h : Nonempty (Representation.Equiv (littleFamily φ i).ρ (littleFamily φ j).ρ)) : i = j := by
  obtain ⟨e⟩ := h
  obtain ⟨ω, χ⟩ := i
  obtain ⟨ω', χ'⟩ := j
  by_cases hω : ω = ω'
  · subst hω
    have hχ : χ = χ' := by
      by_contra hne
      have hU : IsEmpty (Representation.Equiv χ.2.choose.ρ χ'.2.choose.ρ) :=
        ⟨fun f => hne (Subtype.ext
          ((irrChar_spec χ).symm.trans ((char_iso f).trans (irrChar_spec χ'))))⟩
      exact (isEmpty_equiv_littleInd φ ω.out.toHom χ.2.choose.ρ χ'.2.choose.ρ hU).false e
    subst hχ
    rfl
  · exfalso
    have hnot : ω'.out ∉ MulAction.orbit G ω.out := by
      intro hmem
      apply hω
      have h1 : ω'.out ∈ ω.orbit := by
        rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
        exact hmem
      have h2 := MulAction.orbitRel.Quotient.mem_orbit.mp h1
      rw [Quotient.out_eq'] at h2
      exact h2.symm
    exact (isEmpty_equiv_littleInd_of_not_mem_orbit φ ω.out.toHom χ.2.choose.ρ ω'.out.toHom
      χ'.2.choose.ρ (exists_forall_ne_of_not_mem_orbit hnot)).false e

theorem sum_finrank_sq_littleFamily :
    ∑ i : LittleIdx φ, finrank ℂ (littleFamily φ i).V ^ 2 = Nat.card (A ⋊[φ] G) := by
  have hfin : ∀ i : LittleIdx φ, finrank ℂ (littleFamily φ i).V =
      irrCharDim i.2 * (littleSub φ i.1.out.toHom).index :=
    fun i => finrank_Ind (littleSub φ i.1.out.toHom) (littleRep φ i.1.out.toHom i.2.2.choose.ρ)
  simp only [hfin]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  have hsq : ∀ ω : MulAction.orbitRel.Quotient G (DualChar φ),
      ∑ χ : irrChars ℂ (stabChar φ ω.out.toHom), (irrCharDim χ * (littleSub φ ω.out.toHom).index) ^ 2 =
        (littleSub φ ω.out.toHom).index * Nat.card G := by
    intro ω
    simp_rw [mul_pow]
    rw [← Finset.sum_mul, sum_irrCharDim_sq, ← index_littleSub_mul_card φ ω.out.toHom]
    ring
  simp only [hsq]
  rw [← Finset.sum_mul, sum_index_littleSub, card_semidirectProduct]

/-- **Etingof et al., Theorem 4.75 (exhaustion)**: every irreducible complex representation of `A ⋊ G`, for `A`
finite abelian and `G` finite, is isomorphic to a representation `V_(O,U)`, that is to the induced representation
from `A ⋊ G_x` of `x ⊗ U` for some character `x` of `A` and irreducible representation `U` of the stabilizer
`G_x`. -/
@[kb "etingof2011" "Theorem 4.75, p. 76"]
theorem exists_equiv_littleInd (Y : IrrRep ℂ (A ⋊[φ] G)) :
    ∃ (x : A →* ℂˣ) (U : IrrRep ℂ (stabChar φ x)),
      Nonempty (Representation.Equiv Y.ρ (Ind (littleSub φ x) (littleRep φ x U.ρ))) := by
  obtain ⟨i, hi⟩ := exists_equiv_of_sum_finrank_sq (littleFamily φ) (littleFamily_injective φ)
    (sum_finrank_sq_littleFamily φ) Y
  exact ⟨_, _, hi⟩

end Counting

end Little

end UndergradKB.RepresentationTheory
