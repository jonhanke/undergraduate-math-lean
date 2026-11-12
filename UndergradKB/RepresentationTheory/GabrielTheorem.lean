import UndergradKB.RepresentationTheory.GabrielBasics

/-! # Gabriel's theorem (Etingof et al., Theorem 5.23, Theorem 5.34, Corollaries 5.35-5.37)

Let `G` be a positive definite graph on `Fin n` (a Dynkin diagram, `Roots.IsDynkin`) and `Q` an orientation of `G`
(`IsOrientation G Q`: a quiver structure on `Fin n` with one arrow, in one direction, between adjacent vertices,
and no other arrows). Over any field `k`:

* Theorem 5.34 (`exists_reflChain_simple`): for every finite-dimensional indecomposable representation `V`,
  applying reflection functors `F_i^+` at sinks in a suitable order (`ReflChain`, up to isomorphism at each
  step) eventually gives a representation that is simple at some vertex, i.e. whose dimension vector is a simple
  root.
* Corollary 5.35 (`isPositiveRoot_dimVec`): the dimension vector of every finite-dimensional indecomposable
  representation is a positive root.
* Corollary 5.36 (`isomorphic_of_dimVec_eq`): two finite-dimensional indecomposable representations with the same
  dimension vector are isomorphic.
* Corollary 5.37 (`exists_indecomposable_of_isPositiveRoot`): every positive root is the dimension vector of a
  finite-dimensional indecomposable representation.
* Theorem 5.23 (`gabriel`, `gabriel_finiteType`): hence there are finitely many indecomposable representations up
  to isomorphism, and the dimension vector is a bijection from their isomorphism classes onto the positive roots.

The proof follows the book: by Lemma 5.33, applied to the Coxeter element of a sink-admissible ordering of the
vertices (`Gabriel.exists_sinkAdm_reflAlong_neg`), the successive simple reflections of the dimension vector
eventually acquire a negative coordinate; by Propositions 5.28 and 5.30 the reflected representations stay
indecomposable with dimension vector reflected by `s_i` until one of them is simple at the vertex being used. For
Corollary 5.36 one goes back with `F_i^-` (Proposition 5.29); for Corollary 5.37 one starts from a simple
representation and applies `F_i^-` at sources. Along the way the spaces are replaced by `k^d` (`QRep.normRep`) so
that all representations live in the universe of `k`.

The converse direction of Gabriel's theorem (a connected quiver of finite type has a Dynkin underlying graph,
Problem 5.4) is not formalized.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open Roots QRep

set_option linter.unusedSectionVars false

noncomputable section

universe u w w' a

variable {k : Type u} [Field k] {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Chains of reflection functors -/

/-- `ReflChain Q V Q' V'`: the representation `V'` of the quiver `Q'` is obtained from the representation `V` of
`Q` by applying reflection functors `F_i^+` at sinks one after the other, each result being replaced by an
isomorphic representation with spaces in the universe of `k`. -/
inductive ReflChain : (Q : Quiver.{a} (Fin n)) → @QRep.{u, 0, u, a} k (Fin n) _ Q →
    (Q' : Quiver.{a} (Fin n)) → @QRep.{u, 0, u, a} k (Fin n) _ Q' → Prop
  | refl (Q : Quiver.{a} (Fin n)) (V : @QRep.{u, 0, u, a} k (Fin n) _ Q) : ReflChain Q V Q V
  | step (Q : Quiver.{a} (Fin n)) (V : @QRep.{u, 0, u, a} k (Fin n) _ Q) (i : Fin n)
      [@Fintype (@InArrows (Fin n) Q i)] (hi : @Quiver.IsSink _ Q i)
      (W : @QRep.{u, 0, u, a} k (Fin n) _ (@reversedAt _ Q i))
      (hW : @QRep.Isomorphic k (Fin n) _ (@reversedAt _ Q i) W (@reflectSink k _ (Fin n) Q V i _ hi))
      {Q' : Quiver.{a} (Fin n)} {V' : @QRep.{u, 0, u, a} k (Fin n) _ Q'}
      (h : ReflChain (@reversedAt _ Q i) W Q' V') : ReflChain Q V Q' V'

/-! ### Auxiliary facts -/

theorem reflectSink_finite {Q : Quiver.{a} (Fin n)} [∀ x y : Fin n, Fintype (@Quiver.Hom _ Q x y)]
    (V : @QRep.{u, 0, w, a} k (Fin n) _ Q) [∀ j, Module.Finite k (@QRep.obj _ _ _ Q V j)] (i : Fin n)
    (hi : @Quiver.IsSink _ Q i) (x : Fin n) :
    Module.Finite k (@QRep.obj k (Fin n) _ (@reversedAt _ Q i) (@reflectSink k _ (Fin n) Q V i _ hi) x) :=
  show Module.Finite k ↥(@sinkL k _ (Fin n) Q V i _ x) from inferInstance

theorem reflectSource_finite {Q : Quiver.{a} (Fin n)} [∀ x y : Fin n, Fintype (@Quiver.Hom _ Q x y)]
    (V : @QRep.{u, 0, w, a} k (Fin n) _ Q) [∀ j, Module.Finite k (@QRep.obj _ _ _ Q V j)] (i : Fin n)
    (hi : @Quiver.IsSource _ Q i) (x : Fin n) :
    Module.Finite k (@QRep.obj k (Fin n) _ (@reversedAt _ Q i) (@reflectSource k _ (Fin n) Q V i hi) x) :=
  show Module.Finite k ↥(@sourceL k _ (Fin n) Q V i x) from inferInstance

theorem dimZ_eq_simpleRoot_iff [Q : Quiver.{a} (Fin n)] {V : QRep.{u, 0, w, a} k (Fin n)}
    [∀ j, Module.Finite k (V.obj j)] (i : Fin n) : V.IsSimpleAt i ↔ V.dimZ = simpleRoot i := by
  rw [isSimpleAt_iff_dimVec]
  constructor
  · intro h; funext x
    simp only [dimZ, h x, simpleRoot, Pi.single_apply]
    split_ifs <;> simp
  · intro h x
    have := congrFun h x
    simp only [dimZ, simpleRoot, Pi.single_apply] at this
    split_ifs at this ⊢ <;> omega

theorem dimZ_ne_zero [Q : Quiver.{a} (Fin n)] {V : QRep.{u, 0, w, a} k (Fin n)} [∀ j, Module.Finite k (V.obj j)]
    (hV : V.IsIndecomposable) : V.dimZ ≠ 0 := by
  intro h
  apply hV.1
  apply Subrep.ext; intro x
  have hx : Module.finrank k (V.obj x) = 0 := by
    have := congrFun h x
    simp only [dimZ, dimVec, Pi.zero_apply, Nat.cast_eq_zero] at this
    exact this
  haveI : Subsingleton (V.obj x) := Module.finrank_zero_iff.1 hx
  exact bot_eq_top_of_subsingleton'

theorem dimZ_nonneg [Q : Quiver.{a} (Fin n)] (V : QRep.{u, 0, w, a} k (Fin n)) (x : Fin n) :
    0 ≤ V.dimZ x := Nat.cast_nonneg _

theorem dimZ_injective [Q : Quiver.{a} (Fin n)] {V : QRep.{u, 0, w, a} k (Fin n)}
    {W : QRep.{u, 0, w', a} k (Fin n)} (h : V.dimZ = W.dimZ) : V.dimVec = W.dimVec := by
  funext x
  have := congrFun h x
  simp only [dimZ] at this
  exact_mod_cast this

/-- Normalising a finite-dimensional indecomposable representation (single quiver structure in context). -/
theorem exists_norm [Q : Quiver.{a} (Fin n)] (W : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (W.obj j)]
    (hW : W.IsIndecomposable) :
    ∃ N : QRep.{u, 0, u, a} k (Fin n), (∀ j, Module.Finite k (N.obj j)) ∧ N.IsIndecomposable ∧
      N.dimZ = W.dimZ ∧ N.Isomorphic W := by
  have hiso := isomorphic_normRep W
  exact ⟨normRep W, normRep_finite W, hiso.isIndecomposable hW, hiso.dimZ_eq.symm, hiso.symm⟩

theorem simpleReflection_simpleRoot (i : Fin n) : simpleReflection G i (simpleRoot i) = -simpleRoot i := by
  rw [simpleReflection_apply, show form G (simpleRoot i) (simpleRoot i) = 2 from isRoot_simpleRoot G i]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  ring

theorem simpleReflection_apply_of_ne (i : Fin n) (β : Fin n → ℤ) {j : Fin n} (hj : j ≠ i) :
    simpleReflection G i β j = β j := by
  rw [simpleReflection_apply]
  simp [simpleRoot, Pi.single_apply, hj]

/-- For a positive definite graph, a positive root other than `α_i` is sent by `s_i` to a positive root. -/
theorem isPositiveRoot_simpleReflection (hP : PosDefinite G) {β : Fin n → ℤ} (hβ : IsPositiveRoot G β)
    {i : Fin n} (hne : β ≠ simpleRoot i) : IsPositiveRoot G (simpleReflection G i β) := by
  have hroot : IsRoot G (simpleReflection G i β) := isRoot_reflect G (isRoot_simpleRoot G i) hβ.1
  obtain ⟨j, hj, hjpos⟩ : ∃ j, j ≠ i ∧ 0 < β j := by
    by_contra hcon
    push Not at hcon
    have hβeq : β = Pi.single i (β i) := by
      funext x
      by_cases hx : x = i
      · subst hx; simp
      · simp only [Pi.single_apply, hx, if_false]
        exact le_antisymm (hcon x hx) (hβ.2 x)
    have h2 : form G β β = 2 := hβ.1
    rw [hβeq, form_eq_sum] at h2
    simp only [Pi.single_apply] at h2
    simp only [mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [cartanMatrix_apply] at h2
    simp only [if_true, SimpleGraph.irrefl, if_false] at h2
    have hb := hβ.2 i
    have hb1 : β i = 1 := by nlinarith
    exact hne (by rw [hβeq, hb1]; rfl)
  rcases isRoot_sign G hP hroot with h | h
  · exact ⟨hroot, h⟩
  · have := h j
    rw [simpleReflection_apply_of_ne G i β hj] at this
    omega

/-- An isomorphism is carried by `F_i^-` to an isomorphism. -/
theorem reflectSource_isomorphic {Q : Type} [Quiver.{a} Q] {V V' : QRep.{u, 0, w, a} k Q} {i : Q}
    (hi : Quiver.IsSource i) (h : QRep.Isomorphic V V') :
    @QRep.Isomorphic k Q _ (reversedAt i) (reflectSource V i hi) (reflectSource V' i hi) := by
  obtain ⟨f, g, h1, h2⟩ := h
  refine ⟨reflectSourceMap f i hi, reflectSourceMap g i hi, ?_, ?_⟩
  · rw [← reflectSourceMap_comp, h1, reflectSourceMap_id]
  · rw [← reflectSourceMap_comp, h2, reflectSourceMap_id]

/-! ### Theorem 5.34 and Corollary 5.35: the induction along a sink-admissible sequence -/

theorem chain_root : ∀ (L : List (Fin n)) (Q : Quiver.{a} (Fin n)), IsOrientation G Q → SinkAdm (arr Q) L →
    ∀ V : @QRep.{u, 0, u, a} k (Fin n) _ Q, (∀ j, Module.Finite k (@QRep.obj _ _ _ Q V j)) →
    @QRep.IsIndecomposable _ _ _ Q V → (∃ i, reflAlong G L (@dimZ _ _ _ Q V) i < 0) →
    IsRoot G (@dimZ _ _ _ Q V) ∧ ∃ (Q' : Quiver.{a} (Fin n)) (V' : @QRep.{u, 0, u, a} k (Fin n) _ Q') (i : Fin n),
      ReflChain Q V Q' V' ∧ @QRep.IsSimpleAt _ _ _ Q' V' i := by
  intro L
  induction L with
  | nil =>
    intro Q _ _ V _ _ hneg
    obtain ⟨i, hi⟩ := hneg
    exact absurd hi (not_lt.2 (dimZ_nonneg (Q := Q) V i))
  | cons i l ih =>
    intro Q hQ hadm V hfin hV hneg
    letI := hQ.fintype
    have hsink : Quiver.IsSink i := (IsOrientation.isSink_iff i).2 hadm.1
    by_cases hs : V.IsSimpleAt i
    · have hd : V.dimZ = simpleRoot i := (dimZ_eq_simpleRoot_iff i).1 hs
      exact ⟨hd ▸ isRoot_simpleRoot G i, Q, V, i, ReflChain.refl Q V, hs⟩
    · obtain ⟨hW, hd⟩ := reflectSink_indecomposable_dimVec G (hQ.card G) V i hsink hV hs
      have hWf := reflectSink_finite V i hsink
      set W := reflectSink V i hsink with hWdef
      obtain ⟨N, hNf, hN, hdN, hiso⟩ : ∃ N : @QRep.{u, 0, u, a} k (Fin n) _ (reversedAt i),
          (∀ j, Module.Finite k (@QRep.obj _ _ _ (reversedAt i) N j)) ∧
          @QRep.IsIndecomposable _ _ _ (reversedAt i) N ∧
          @dimZ _ _ _ (reversedAt i) N = simpleReflection G i V.dimZ ∧
          @QRep.Isomorphic _ _ _ (reversedAt i) N W := by
        letI : Quiver.{a} (Fin n) := reversedAt i
        haveI := hWf
        obtain ⟨N, h1, h2, h3, h4⟩ := exists_norm W hW
        exact ⟨N, h1, h2, h3.trans hd, h4⟩
      obtain ⟨hroot, hrest⟩ := ih (reversedAt i) (hQ.reversedAt G i)
        (by rw [arr_reversedAt]; exact hadm.2) N hNf hN (by rw [hdN]; exact hneg)
      rw [hdN] at hroot
      have hr : IsRoot G V.dimZ := (isRoot_reflAlong_iff G [i] _).1 hroot
      obtain ⟨Q', V', j, hch, hsj⟩ := hrest
      exact ⟨hr, Q', V', j, ReflChain.step Q V i hsink N hiso hch, hsj⟩

/-- **Theorem 5.34.** Let `Q` be an orientation of a positive definite graph `G` (a Dynkin quiver). For every
finite-dimensional indecomposable representation `V` (with spaces in the universe of `k`), there is a sequence
of reflection functors `F_i^+` at sinks, applied one after the other (up to isomorphism), leading from `V` to a
representation that is simple at some vertex `i`, so whose dimension vector is the simple root `α_i`. -/
@[kb "etingof2011" "Theorem 5.34, p. 95"]
theorem exists_reflChain_simple (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, u, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (hV : V.IsIndecomposable) :
    ∃ (Q' : Quiver.{a} (Fin n)) (V' : @QRep.{u, 0, u, a} k (Fin n) _ Q') (i : Fin n),
      ReflChain Q V Q' V' ∧ @QRep.IsSimpleAt _ _ _ Q' V' i ∧ @dimZ _ _ _ Q' V' = simpleRoot i := by
  obtain ⟨L, hL, hneg⟩ := exists_sinkAdm_reflAlong_neg G hP hQ.asymm hQ.adj (dimZ_ne_zero hV) (dimZ_nonneg V)
  obtain ⟨-, Q', V', i, hch, hs⟩ := chain_root G L Q hQ hL V inferInstance hV hneg
  haveI := @IsSimpleAt.finite k _ (Fin n) Q' V' i hs
  exact ⟨Q', V', i, hch, hs, (dimZ_eq_simpleRoot_iff (Q := Q') (V := V') i).1 hs⟩

/-- **Corollary 5.35.** For an orientation `Q` of a positive definite graph `G`, the dimension vector of every
finite-dimensional indecomposable representation of `Q` is a positive root. -/
@[kb "etingof2011" "Corollary 5.35, p. 95"]
theorem isPositiveRoot_dimVec (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (hV : V.IsIndecomposable) :
    IsPositiveRoot G V.dimZ := by
  have hiso := isomorphic_normRep V
  have hN := hiso.isIndecomposable hV
  rw [hiso.dimZ_eq]
  obtain ⟨L, hL, hneg⟩ := exists_sinkAdm_reflAlong_neg G hP hQ.asymm hQ.adj (dimZ_ne_zero hN)
    (dimZ_nonneg (normRep V))
  exact ⟨(chain_root G L Q hQ hL (normRep V) (normRep_finite V) hN hneg).1, dimZ_nonneg _⟩

/-! ### Corollary 5.36: uniqueness -/

theorem chain_iso : ∀ (L : List (Fin n)) (Q : Quiver.{a} (Fin n)), IsOrientation G Q → SinkAdm (arr Q) L →
    ∀ V V' : @QRep.{u, 0, u, a} k (Fin n) _ Q, (∀ j, Module.Finite k (@QRep.obj _ _ _ Q V j)) →
    (∀ j, Module.Finite k (@QRep.obj _ _ _ Q V' j)) →
    @QRep.IsIndecomposable _ _ _ Q V → @QRep.IsIndecomposable _ _ _ Q V' →
    @dimZ _ _ _ Q V = @dimZ _ _ _ Q V' → (∃ i, reflAlong G L (@dimZ _ _ _ Q V) i < 0) →
    @QRep.Isomorphic _ _ _ Q V V' := by
  intro L
  induction L with
  | nil =>
    intro Q _ _ V _ _ _ _ _ _ hneg
    obtain ⟨i, hi⟩ := hneg
    exact absurd hi (not_lt.2 (dimZ_nonneg (Q := Q) V i))
  | cons i l ih =>
    intro Q hQ hadm V V' hfin hfin' hV hV' hdd hneg
    letI := hQ.fintype
    have hsink : Quiver.IsSink i := (IsOrientation.isSink_iff i).2 hadm.1
    by_cases hs : V.IsSimpleAt i
    · have hs' : V'.IsSimpleAt i := by
        rw [dimZ_eq_simpleRoot_iff, ← hdd]
        exact (dimZ_eq_simpleRoot_iff i).1 hs
      exact isomorphic_of_isSimpleAt (hQ.noLoop G i) hs hs'
    · have hs' : ¬ V'.IsSimpleAt i := by
        rw [dimZ_eq_simpleRoot_iff, ← hdd]
        exact fun h => hs ((dimZ_eq_simpleRoot_iff i).2 h)
      obtain ⟨hW, hd⟩ := reflectSink_indecomposable_dimVec G (hQ.card G) V i hsink hV hs
      obtain ⟨hW', hd'⟩ := reflectSink_indecomposable_dimVec G (hQ.card G) V' i hsink hV' hs'
      have hWf := reflectSink_finite V i hsink
      have hWf' := reflectSink_finite V' i hsink
      have hsrc := isSource_reversedAt hsink
      have hsurj := (isSimpleAt_or_surjective_sumIn V i hsink hV).resolve_left hs
      have hsurj' := (isSimpleAt_or_surjective_sumIn V' i hsink hV').resolve_left hs'
      have e1 := (reflectSource_reflectSink_iso V i hsink hsurj).isomorphic
      have e2 := (reflectSource_reflectSink_iso V' i hsink hsurj').isomorphic
      set W := reflectSink V i hsink with hWdef
      set W' := reflectSink V' i hsink with hW'def
      have hd2 : @dimZ k _ (Fin n) (@reversedAt _ Q i) W = simpleReflection G i (dimZ V) := hd
      have hd2' : @dimZ k _ (Fin n) (@reversedAt _ Q i) W' = simpleReflection G i (dimZ V') := hd'
      have hFF : @QRep.Isomorphic _ _ _ (revrev i) (@reflectSource k _ (Fin n) (reversedAt i) W i hsrc)
          (@reflectSource k _ (Fin n) (reversedAt i) W' i hsrc) := by
        letI : Quiver.{a} (Fin n) := reversedAt i
        haveI := hWf
        haveI := hWf'
        obtain ⟨N, hNf, hN, hdN, hiso⟩ := exists_norm W hW
        obtain ⟨N', hNf', hN', hdN', hiso'⟩ := exists_norm W' hW'
        have hNN := ih (@reversedAt _ Q i) (hQ.reversedAt G i) (by rw [arr_reversedAt]; exact hadm.2) N N' hNf hNf'
          hN hN' (by rw [hdN, hdN', hd2, hd2', hdd]) (by rw [hdN, hd2]; exact hneg)
        exact reflectSource_isomorphic hsrc ((hiso.symm.trans hNN).trans hiso')
      exact (e1.trans (QRep.pullback_isomorphic _ (revrev i) _ hFF)).trans e2.symm

/-- **Corollary 5.36.** For an orientation `Q` of a positive definite graph `G`, two finite-dimensional
indecomposable representations of `Q` with the same dimension vector are isomorphic. -/
@[kb "etingof2011" "Corollary 5.36, p. 95"]
theorem isomorphic_of_dimVec_eq (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, w, a} k (Fin n)) (V' : QRep.{u, 0, w', a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)]
    [∀ j, Module.Finite k (V'.obj j)] (hV : V.IsIndecomposable) (hV' : V'.IsIndecomposable)
    (hd : V.dimVec = V'.dimVec) : V.Isomorphic V' := by
  have hiso := isomorphic_normRep V
  have hiso' := isomorphic_normRep V'
  have hN := hiso.isIndecomposable hV
  have hN' := hiso'.isIndecomposable hV'
  obtain ⟨L, hL, hneg⟩ := exists_sinkAdm_reflAlong_neg G hP hQ.asymm hQ.adj (dimZ_ne_zero hN)
    (dimZ_nonneg (normRep V))
  have hdd : (normRep V).dimZ = (normRep V').dimZ := by
    rw [← hiso.dimZ_eq, ← hiso'.dimZ_eq]
    funext x; simp [dimZ, hd]
  exact (hiso.trans (chain_iso G L Q hQ hL _ _ (normRep_finite V) (normRep_finite V') hN hN' hdd hneg)).trans
    hiso'.symm

/-! ### Corollary 5.37: existence -/

theorem chain_exists (hP : PosDefinite G) : ∀ (L : List (Fin n)) (Q : Quiver.{a} (Fin n)), IsOrientation G Q →
    SinkAdm (arr Q) L → ∀ β : Fin n → ℤ, IsPositiveRoot G β → (∃ i, reflAlong G L β i < 0) →
    ∃ V : @QRep.{u, 0, u, a} k (Fin n) _ Q, (∀ j, Module.Finite k (@QRep.obj _ _ _ Q V j)) ∧
      @QRep.IsIndecomposable _ _ _ Q V ∧ @dimZ _ _ _ Q V = β := by
  intro L
  induction L with
  | nil =>
    intro Q _ _ β hβ hneg
    obtain ⟨i, hi⟩ := hneg
    exact absurd hi (not_lt.2 (hβ.2 i))
  | cons i l ih =>
    intro Q hQ hadm β hβ hneg
    have hsink : Quiver.IsSink i := (IsOrientation.isSink_iff i).2 hadm.1
    by_cases hb : β = simpleRoot i
    · subst hb
      refine ⟨simpleRep k i, simpleRep_finite i, isIndecomposable_of_isSimpleAt (simpleRep_isSimpleAt i), ?_⟩
      exact (dimZ_eq_simpleRoot_iff i).1 (simpleRep_isSimpleAt i)
    · have hβ' := isPositiveRoot_simpleReflection G hP hβ hb
      obtain ⟨W, hWfin, hW, hWd⟩ := ih (reversedAt i) (hQ.reversedAt G i) (by rw [arr_reversedAt]; exact hadm.2)
        _ hβ' hneg
      have hsrc := isSource_reversedAt hsink
      obtain ⟨X, hXf, hX, hXd⟩ : ∃ X : @QRep.{u, 0, max a u, a} k (Fin n) _ (revrev i),
          (∀ j, Module.Finite k (@QRep.obj _ _ _ (revrev i) X j)) ∧
          @QRep.IsIndecomposable _ _ _ (revrev i) X ∧ @dimZ _ _ _ (revrev i) X = β := by
        letI : Quiver.{a} (Fin n) := reversedAt i
        letI := (hQ.reversedAt G i).fintype
        haveI := hWfin
        have hne : ¬ W.IsSimpleAt i := by
          intro h
          have h1 := (dimZ_eq_simpleRoot_iff i).1 h
          rw [hWd] at h1
          have h2 := congrArg (simpleReflection G i) h1
          rw [show simpleReflection G i (simpleReflection G i β) = β from
            reflect_involutive G _ (isRoot_simpleRoot G i) β, simpleReflection_simpleRoot] at h2
          have := hβ.2 i
          rw [h2] at this
          simp [simpleRoot] at this
        obtain ⟨hX, hXd⟩ := reflectSource_indecomposable_dimVec G ((hQ.reversedAt G i).card G) W i hsrc hW hne
        refine ⟨reflectSource W i hsrc, reflectSource_finite W i hsrc, hX, ?_⟩
        show (fun x => ((reflectSource W i hsrc).dimVec x : ℤ)) = β
        rw [hXd]
        show simpleReflection G i W.dimZ = β
        rw [hWd]
        exact reflect_involutive G _ (isRoot_simpleRoot G i) β
      have hP' : @QRep.IsIndecomposable k (Fin n) _ Q (rrPullback i X) :=
        QRep.pullback_isIndecomposable _ (revrev i) _ (fun x y => toRR_surjective i x y) X hX
      haveI : ∀ x, Module.Finite k ((rrPullback i X).obj x) := QRep.pullback_finite _ (revrev i) _ X
      have hiso := isomorphic_normRep (rrPullback i X)
      refine ⟨normRep (rrPullback i X), normRep_finite _, hiso.isIndecomposable hP', ?_⟩
      rw [← hiso.dimZ_eq]
      exact hXd

/-- **Corollary 5.37.** For an orientation `Q` of a positive definite graph `G`, every positive root is the
dimension vector of a finite-dimensional indecomposable representation of `Q`. -/
@[kb "etingof2011" "Corollary 5.37, p. 96"]
theorem exists_indecomposable_of_isPositiveRoot (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)]
    (hQ : IsOrientation G Q) {β : Fin n → ℤ} (hβ : IsPositiveRoot G β) :
    ∃ V : QRep.{u, 0, u, a} k (Fin n), (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧ V.dimZ = β := by
  obtain ⟨L, hL, hneg⟩ := exists_sinkAdm_reflAlong_neg G hP hQ.asymm hQ.adj hβ.1.ne_zero hβ.2
  exact chain_exists G hP L Q hQ hL β hβ hneg

/-! ### Theorem 5.23 -/

/-- **Gabriel's theorem (Theorem 5.23).** Let `Q` be an orientation of a Dynkin diagram `G` (connected, with
positive definite form). Then the dimension vector of every finite-dimensional indecomposable representation is a
positive root; every positive root is the dimension vector of one; and two with the same dimension vector are
isomorphic. So the dimension vector is a bijection from isomorphism classes of finite-dimensional indecomposable
representations onto the (finite) set of positive roots. -/
@[kb "etingof2011" "Theorem 5.23, p. 89"]
theorem gabriel (hD : IsDynkin G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q) :
    {β : Fin n → ℤ | IsPositiveRoot G β}.Finite ∧
    (∀ (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
      IsPositiveRoot G V.dimZ) ∧
    (∀ β, IsPositiveRoot G β → ∃ V : QRep.{u, 0, u, a} k (Fin n),
      (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧ V.dimZ = β) ∧
    (∀ (V : QRep.{u, 0, w, a} k (Fin n)) (V' : QRep.{u, 0, w', a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)]
      [∀ j, Module.Finite k (V'.obj j)], V.IsIndecomposable → V'.IsIndecomposable → V.dimVec = V'.dimVec →
      V.Isomorphic V') :=
  ⟨(roots_finite G hD.2).subset fun _ h => h.1,
    fun V _ hV => isPositiveRoot_dimVec G hD.2 hQ V hV,
    fun _ hβ => exists_indecomposable_of_isPositiveRoot G hD.2 hQ hβ,
    fun V V' _ _ hV hV' hd => isomorphic_of_dimVec_eq G hD.2 hQ V V' hV hV' hd⟩

/-- **Gabriel's theorem, finite type (Theorem 5.23).** An orientation of a Dynkin diagram has finitely many
indecomposable representations up to isomorphism: there is a finite family of finite-dimensional indecomposable
representations, indexed by the positive roots and with these as dimension vectors, such that every
finite-dimensional indecomposable representation is isomorphic to exactly one member of the family. -/
@[kb "etingof2011" "Theorem 5.23, p. 89"]
theorem gabriel_finiteType (hD : IsDynkin G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q) :
    ∃ M : {β : Fin n → ℤ // IsPositiveRoot G β} → QRep.{u, 0, u, a} k (Fin n),
      Finite {β : Fin n → ℤ // IsPositiveRoot G β} ∧
      (∀ β, (∀ j, Module.Finite k ((M β).obj j)) ∧ (M β).IsIndecomposable ∧ (M β).dimZ = β.1) ∧
      ∀ (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
        ∃! β, V.Isomorphic (M β) := by
  choose M hM using fun β : {β : Fin n → ℤ // IsPositiveRoot G β} =>
    exists_indecomposable_of_isPositiveRoot (k := k) G hD.2 hQ β.2
  have hfin : {β : Fin n → ℤ | IsPositiveRoot G β}.Finite := (roots_finite G hD.2).subset fun _ h => h.1
  refine ⟨M, hfin.to_subtype, hM, fun V _ hV => ?_⟩
  have hβ := isPositiveRoot_dimVec G hD.2 hQ V hV
  refine ⟨⟨V.dimZ, hβ⟩, ?_, fun β hiso => ?_⟩
  · haveI := (hM ⟨V.dimZ, hβ⟩).1
    refine isomorphic_of_dimVec_eq G hD.2 hQ V _ hV (hM ⟨V.dimZ, hβ⟩).2.1 (dimZ_injective ?_)
    exact (hM ⟨V.dimZ, hβ⟩).2.2.symm
  · apply Subtype.ext
    show β.1 = V.dimZ
    rw [hiso.dimZ_eq, (hM β).2.2]

end

end UndergradKB.RepresentationTheory.Gabriel
