import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Group.ConjFinite
import UndergradKB.RepresentationTheory.SymmetricGroup
import UndergradKB.RepresentationTheory.SymmetricGroupSpecht
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.Common.Attr

/-! # Specht modules (Etingof et al., §4.12-4.13)

For a Young diagram `λ` with `n` boxes and a filling `T : λ ≃ Fin n`, the Young symmetrizer `c_T = a_T b_T` of
`ℂ[S_n]` generates the left ideal `V_λ = ℂ[S_n] c_T` (a Specht module).

* `isSimpleModule_span_youngSymmetrizer` (Theorem 4.36, irreducibility): `V_λ` is a simple `ℂ[S_n]`-module.
* `isEmpty_linearEquiv_span_youngSymmetrizerN` (Theorem 4.36, non-isomorphism): for diagrams `λ ≠ μ` with `n`
  boxes, `V_λ` and `V_μ` are not isomorphic.
* `exists_equiv_spechtModule` (Corollary 4.38 in the form: the `V_λ` exhaust the irreducible representations):
  every irreducible representation of `S_n` over `ℂ` is isomorphic to some `V_λ`; combined with the above, the
  irreducible representations of `S_n` are in bijection with the partitions of `n`
  (`card_irrChars_symm_eq_card_partition`).
-/

namespace UndergradKB.RepresentationTheory

open Finset

/-! ### The symmetrizer attached to a filling by `Fin n` -/

/-- The Young symmetrizer `a_T b_T` of a filling `T : λ ≃ Fin n` (for arbitrary `n`). -/
noncomputable def youngSymmetrizerN {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  rowSumN T * colSumN T

lemma youngSymmetrizerN_eq {mu : YoungDiagram} (T : YoungTableau mu) :
    youngSymmetrizerN T = youngSymmetrizer T := rfl

lemma card_eq_of_equiv {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) : la.card = n := by
  have h1 : Nat.card la = n := by
    rw [Nat.card_congr T, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← h1]
  exact (Nat.card_eq_finsetCard la.cells).symm

lemma youngSymmetrizer_ne_zero {mu : YoungDiagram} (T : YoungTableau mu) : youngSymmetrizer T ≠ 0 := by
  intro h
  have := coeff_one_youngSymmetrizer T
  rw [h] at this
  simp at this

/-- `c x c` is a scalar multiple of `c`. -/
lemma youngSymmetrizer_mul_mul_self {mu : YoungDiagram} (T : YoungTableau mu)
    (y : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))) :
    ∃ s : ℂ, youngSymmetrizer T * y * youngSymmetrizer T = s • youngSymmetrizer T := by
  obtain ⟨ℓ, hℓ⟩ := rowSum_mul_mul_colSum T
  refine ⟨ℓ (colSum T * y * rowSum T), ?_⟩
  rw [← hℓ]
  simp only [youngSymmetrizer, mul_assoc]

/-! ### Theorem 4.36: irreducibility -/

/-- If a left ideal `U` inside `ℂ[S_n] c` contains an element `u` with `c u ≠ 0`, then `U = ℂ[S_n] c`. -/
lemma eq_span_of_exists_mul_ne_zero {mu : YoungDiagram} (T : YoungTableau mu)
    {U : Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)))}
    (hU : U ≤ Ideal.span {youngSymmetrizer T})
    (h : ∃ u ∈ U, youngSymmetrizer T * u ≠ 0) : U = Ideal.span {youngSymmetrizer T} := by
  obtain ⟨u, huU, hne⟩ := h
  refine le_antisymm hU ?_
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 (hU huU)
  obtain ⟨s, hs⟩ := youngSymmetrizer_mul_mul_self T y
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hne
    rw [← mul_assoc, hs, zero_smul]
  have h1 : youngSymmetrizer T * (y * youngSymmetrizer T) ∈ U := U.mul_mem_left _ huU
  rw [← mul_assoc, hs] at h1
  rw [Ideal.span_singleton_le_iff_mem]
  have h2 := U.mul_mem_left (algebraMap ℂ _ s⁻¹) h1
  rwa [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

/-- **Theorem 4.36 (irreducibility).** The left ideal `V_λ = ℂ[S_n] c_λ` is an irreducible (simple)
`ℂ[S_n]`-module. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem isSimpleModule_span_youngSymmetrizer {mu : YoungDiagram} (T : YoungTableau mu) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)))
      (Ideal.span {youngSymmetrizer T}) := by
  classical
  set A := MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))
  set c := youngSymmetrizer T with hc
  have hcne : c ≠ 0 := youngSymmetrizer_ne_zero T
  have hcc : c * c ≠ 0 := by
    obtain ⟨hdim, hk⟩ := youngSymmetrizer_mul_self T
    rw [hk]
    refine smul_ne_zero (div_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.2 hdim)) hcne
  have hcV : c ∈ Ideal.span {c} := Ideal.subset_span rfl
  have : NeZero (Nat.card (Equiv.Perm (Fin mu.card)) : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero⟩
  rw [isSimpleModule_iff_isAtom]
  refine ⟨?_, fun W hW => ?_⟩
  · intro h
    rw [h] at hcV
    exact hcne (by simpa using hcV)
  · obtain ⟨W'', hW''⟩ := exists_isCompl W
    have hWV : W ≤ Ideal.span {c} := hW.le
    set W' := W'' ⊓ Ideal.span {c} with hW'
    have hsup : W ⊔ W' = Ideal.span {c} := by
      rw [hW', ← sup_inf_assoc_of_le W'' hWV, hW''.sup_eq_top, top_inf_eq]
    by_cases h1 : ∃ u ∈ W, c * u ≠ 0
    · exact absurd (eq_span_of_exists_mul_ne_zero T hWV h1) hW.ne
    · by_cases h2 : ∃ u ∈ W', c * u ≠ 0
      · have := eq_span_of_exists_mul_ne_zero T inf_le_right h2
        rw [eq_bot_iff]
        intro w hw
        have hw' : w ∈ W'' := by
          have hmem : w ∈ W'' ⊓ Ideal.span {youngSymmetrizer T} := by rw [this]; exact hWV hw
          exact hmem.1
        have hw0 : w ∈ W ⊓ W'' := ⟨hw, hw'⟩
        rw [hW''.inf_eq_bot] at hw0
        exact hw0
      · push Not at h1 h2
        exfalso
        rw [← hsup] at hcV
        obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 hcV
        apply hcc
        conv_lhs => rhs; rw [← hsum]
        rw [mul_add, h1 w hw, h2 w' hw', add_zero]

/-! ### Theorem 4.36: non-isomorphism -/

/-- If `λ` is lexicographically larger than `μ`, then `V_λ` and `V_μ` are not isomorphic as modules over the
group algebra. -/
theorem isEmpty_linearEquiv_of_lex {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n) (Tm : mu ≃ Fin n)
    (hlex : ∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k) :
    IsEmpty (Ideal.span {youngSymmetrizerN Tl} ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN Tm}) := by
  have hn := card_eq_of_equiv Tl
  subst hn
  refine ⟨fun φ => ?_⟩
  set c := youngSymmetrizer Tl with hc
  have hcne : c ≠ 0 := youngSymmetrizer_ne_zero Tl
  obtain ⟨hdim, hk⟩ := youngSymmetrizer_mul_self Tl
  set k : ℂ := (la.card.factorial : ℂ) / (Module.finrank ℂ
    ((Ideal.span {youngSymmetrizer Tl}).restrictScalars ℂ) : ℂ) with hkdef
  have hk0 : k ≠ 0 := div_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.2 hdim)
  let c' : Ideal.span {youngSymmetrizerN Tl} := ⟨c, Ideal.subset_span rfl⟩
  have h1 : c • c' = (algebraMap ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin la.card))) k) • c' := by
    apply Subtype.ext
    show c * c = algebraMap ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin la.card))) k * c
    rw [hk, Algebra.smul_def]
  have h2 : c * (φ c').1 = algebraMap ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin la.card))) k * (φ c').1 := by
    have := congrArg (fun x => (φ x).1) h1
    simp only [map_smul] at this
    exact this
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (φ c').2
  have h3 : c * (φ c').1 = 0 := by
    rw [← hy]
    have : c * (y * youngSymmetrizerN Tm) = rowSumN Tl * (colSumN Tl * y * rowSumN Tm) * colSumN Tm := by
      simp only [hc, youngSymmetrizer, rowSum, colSum, mul_assoc, youngSymmetrizerN, rowSumN_eq_rowSum,
        colSumN_eq_colSum]
    rw [this]
    exact rowSumN_mul_mul_colSumN_of_lex Tl Tm hlex _
  have h4 : (φ c').1 = 0 := by
    rw [h3] at h2
    have := congrArg (fun x => algebraMap ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin la.card))) k⁻¹ * x) h2
    simp only [mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk0, map_one, one_mul] at this
    exact this.symm
  have h5 : φ c' = 0 := Subtype.ext h4
  have h6 : c' = 0 := φ.injective (by rw [h5, map_zero])
  exact hcne (congrArg Subtype.val h6)

/-- For distinct Young diagrams, one of them is lexicographically larger than the other. -/
lemma exists_lex_of_ne {la mu : YoungDiagram} (h : la ≠ mu) :
    (∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k) ∨
      (∃ k, (∀ i < k, mu.rowLen i = la.rowLen i) ∧ la.rowLen k < mu.rowLen k) := by
  classical
  have hex : ∃ i, la.rowLen i ≠ mu.rowLen i := by
    by_contra hcon
    push Not at hcon
    apply h
    refine SetLike.ext fun ⟨i, j⟩ => ?_
    rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, hcon i]
  have hmin : ∀ i < Nat.find hex, la.rowLen i = mu.rowLen i := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this
  rcases lt_or_gt_of_ne (Nat.find_spec hex) with hlt | hgt
  · exact Or.inr ⟨Nat.find hex, fun i hi => (hmin i hi).symm, hlt⟩
  · exact Or.inl ⟨Nat.find hex, hmin, hgt⟩

/-- **Theorem 4.36 (non-isomorphism).** For Young diagrams `λ ≠ μ` with `n` boxes and fillings by
`0, …, n-1`, the modules `V_λ = ℂ[S_n] c_λ` and `V_μ = ℂ[S_n] c_μ` are not isomorphic. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem isEmpty_linearEquiv_span_youngSymmetrizerN {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n)
    (Tm : mu ≃ Fin n) (h : la ≠ mu) :
    IsEmpty (Ideal.span {youngSymmetrizerN Tl} ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {youngSymmetrizerN Tm}) := by
  rcases exists_lex_of_ne h with hl | hl
  · exact isEmpty_linearEquiv_of_lex Tl Tm hl
  · have := isEmpty_linearEquiv_of_lex Tm Tl hl
    exact ⟨fun φ => this.false φ.symm⟩

/-! ### Corollary 4.38: the `V_λ` are all the irreducible representations -/

lemma isSimpleModule_span_youngSymmetrizerN {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) :
    IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) (Ideal.span {youngSymmetrizerN T}) := by
  have hn := card_eq_of_equiv T
  subst hn
  exact isSimpleModule_span_youngSymmetrizer T

/-- The number of conjugacy classes of `S_n` is at most the number of partitions of `n` (in fact equal): the
cycle type with the fixed points added gives an injection. -/
lemma natCard_conjClasses_perm_le (α : Type*) [Fintype α] [DecidableEq α] :
    Nat.card (ConjClasses (Equiv.Perm α)) ≤ Nat.card (Nat.Partition (Fintype.card α)) := by
  refine Nat.card_le_card_of_injective
    (Quotient.lift (fun σ : Equiv.Perm α => σ.partition)
      (fun a b h => Equiv.Perm.partition_eq_of_isConj.1 h)) ?_
  intro x y
  induction x using Quotient.inductionOn with | _ a => ?_
  induction y using Quotient.inductionOn with | _ b => ?_
  intro h
  exact Quotient.sound (Equiv.Perm.partition_eq_of_isConj.2 h)

/-- Young diagrams with `n` boxes. -/
abbrev DiagramsOfSize (n : ℕ) := {la : YoungDiagram // la.card = n}

/-- A filling of a diagram with `n` boxes by `0, …, n-1` (chosen noncomputably). -/
noncomputable def spechtTableau {n : ℕ} (la : DiagramsOfSize n) : la.1 ≃ Fin n :=
  Finset.equivFinOfCardEq (s := la.1.cells) la.2

/-- The Specht module `V_λ = ℂ[S_n] c_λ`, for a diagram `λ` with `n` boxes. -/
noncomputable def spechtModule {n : ℕ} (la : DiagramsOfSize n) :
    Ideal (MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :=
  Ideal.span {youngSymmetrizerN (spechtTableau la)}

/-- An isomorphism of the representations attached to two left ideals gives an isomorphism of modules. -/
noncomputable def linearEquivOfRepEquiv {G : Type*} [Group G]
    (S S' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))
    (e : Representation.Equiv (Representation.ofModule (k := ℂ) (G := G) S)
      (Representation.ofModule (k := ℂ) (G := G) S')) :
    S ≃ₗ[MonoidAlgebra ℂ G] S' := by
  have key : ∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) S),
      e ((Representation.ofModule (k := ℂ) (G := G) S).asAlgebraHom a v) =
        (Representation.ofModule (k := ℂ) (G := G) S').asAlgebraHom a (e v) := by
    intro a v
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | single g r =>
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      simp only [LinearMap.smul_apply, map_smul]
      exact congrArg _ (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)
  let f : ∀ {S S' : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G)}
      (e : Representation.Equiv (Representation.ofModule (k := ℂ) (G := G) S)
        (Representation.ofModule (k := ℂ) (G := G) S')),
      (∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) S),
        e ((Representation.ofModule (k := ℂ) (G := G) S).asAlgebraHom a v) =
          (Representation.ofModule (k := ℂ) (G := G) S').asAlgebraHom a (e v)) →
      (S →ₗ[MonoidAlgebra ℂ G] S') := fun {S S'} e key =>
    { toFun := fun s => (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S')
        (e ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm s))
      map_add' := fun x y => by simp
      map_smul' := fun a s => by
        have h1 := key a ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm s)
        rw [Representation.ofModule_asAlgebraHom_apply_apply] at h1
        simp only [AddEquiv.apply_symm_apply] at h1
        have h2 := congrArg (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S') h1
        rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
        simp only [AddEquiv.apply_symm_apply] at h2
        simp only [RingHom.id_apply]
        exact h2 }
  have key' : ∀ (a : MonoidAlgebra ℂ G) (v : RestrictScalars ℂ (MonoidAlgebra ℂ G) S'),
      e.symm ((Representation.ofModule (k := ℂ) (G := G) S').asAlgebraHom a v) =
        (Representation.ofModule (k := ℂ) (G := G) S).asAlgebraHom a (e.symm v) := by
    intro a v
    have h := congrArg e.symm (key a (e.symm v))
    simp at h
    simpa using h.symm
  refine LinearEquiv.ofLinearMap (f e key) (f e.symm key') ?_ ?_
  · ext s
    simp [f]
  · ext s
    simp [f]

section Main

variable (n : ℕ)

/-- The Specht module `V_λ` as an irreducible representation of `S_n` over `ℂ`. -/
noncomputable def spechtIrrRep (la : DiagramsOfSize n) : IrrRep ℂ (Equiv.Perm (Fin n)) :=
  IrrRep.ofSimple (k := ℂ) (G := Equiv.Perm (Fin n)) (spechtModule la)
    (hS := isSimpleModule_span_youngSymmetrizerN (spechtTableau la))

private lemma spechtIrrRep_character_injective :
    Function.Injective fun la : DiagramsOfSize n => (spechtIrrRep n la).ρ.character := by
  have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  intro la mu h
  by_contra hne
  have hne' : la.1 ≠ mu.1 := fun h' => hne (Subtype.ext h')
  obtain ⟨e⟩ := (nonempty_equiv_iff_character_eq (spechtIrrRep n la) (spechtIrrRep n mu)).2 h
  have := isEmpty_linearEquiv_span_youngSymmetrizerN (spechtTableau la) (spechtTableau mu) hne'
  exact this.false (linearEquivOfRepEquiv (spechtModule la) (spechtModule mu) e)

/-- The character of the Specht module `V_λ`, as an element of the set of irreducible characters. -/
noncomputable def spechtChar (la : DiagramsOfSize n) : irrChars ℂ (Equiv.Perm (Fin n)) :=
  ⟨(spechtIrrRep n la).ρ.character, spechtIrrRep n la, rfl⟩

/-- The characters of the Specht modules are exactly the irreducible characters of `S_n`, each occurring for
one partition only. -/
theorem spechtChar_bijective : Function.Bijective (spechtChar n) := by
  have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hinj : Function.Injective (spechtChar n) := fun a b h =>
    spechtIrrRep_character_injective n (congrArg Subtype.val h)
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_irrChars (k := ℂ) (G := Equiv.Perm (Fin n)), Nat.card_congr YoungDiagram.equivPartition]
  have := natCard_conjClasses_perm_le (Fin n)
  rwa [Fintype.card_fin] at this

/-- **Corollary 4.38 (the Specht modules exhaust the irreducible representations; count form).** The
irreducible representations of `S_n` over `ℂ` (up to isomorphism, i.e. their characters) are in bijection with
the partitions of `n`, via `λ ↦ V_λ`. -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem card_irrChars_perm_eq_card_partition :
    Nat.card (irrChars ℂ (Equiv.Perm (Fin n))) = Nat.card (Nat.Partition n) :=
  (Nat.card_congr ((Equiv.ofBijective _ (spechtChar_bijective n)).symm.trans
    YoungDiagram.equivPartition))

/-- **Corollary 4.38 (the Specht modules exhaust the irreducible representations).** Every irreducible
representation of `S_n` over `ℂ` is isomorphic to the Specht module `V_λ = ℂ[S_n] c_λ` for some partition `λ`
of `n` (the partition is unique by Theorem 4.36). -/
@[kb "etingof2011" "Theorem 4.36, p. 58"]
theorem exists_equiv_spechtModule (Y : IrrRep ℂ (Equiv.Perm (Fin n))) :
    ∃ la : DiagramsOfSize n, Nonempty (Representation.Equiv Y.ρ
      (Representation.ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (spechtModule la))) := by
  have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  obtain ⟨la, hla⟩ := (spechtChar_bijective n).2 ⟨Y.ρ.character, Y, rfl⟩
  refine ⟨la, ?_⟩
  have h : Y.ρ.character = (spechtIrrRep n la).ρ.character := (congrArg Subtype.val hla).symm
  exact (nonempty_equiv_iff_character_eq Y (spechtIrrRep n la)).2 h

end Main

end UndergradKB.RepresentationTheory
