import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.JordanHolderFitting
import UndergradKB.RepresentationTheory.ProjectiveCovers

/-! # Projective covers of simple modules: indecomposability, uniqueness, decomposition of `A`
(Etingof et al., Theorem 7.6)

Let `A` be a finite-dimensional algebra over a field `k` and `V₁, …, Vₙ` a complete list of its simple modules up to
isomorphism.  Call a finite-dimensional module `P` a *top-`i` module* (`IsTopModule k A V i P`) if
`dim Hom_A(P, Vⱼ) = δᵢⱼ` for all `j`.  We prove the following facts, which together with
`exists_projective_finrank_hom_eq_ite` give Theorem 7.6.

* A top-`i` module has a unique maximal submodule, hence it is indecomposable.
* Two projective top-`i` modules are isomorphic (uniqueness of `Pᵢ`).
* Every finite-dimensional projective module is isomorphic to a finite direct sum of the `Pᵢ`, obtained by splitting
  off one `Pᵢ` at a time along a surjection `P → Pᵢ` lifting a map `P → Vᵢ`.
* Consequently `A ≅ ⊕ (dim Vᵢ) Pᵢ`, and every indecomposable finite-dimensional projective is some `Pᵢ`.

The indecomposability is proved through the unique maximal submodule rather than through the locality of
`End(A e) ≅ (e A e)ᵒᵖ`; this is a different route to the same conclusion, and the endomorphism ring statement itself
is not formalized.
-/

namespace UndergradKB.RepresentationTheory

open Module

universe u

section Core

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {ι : Type*} [DecidableEq ι]
  {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

variable (A V) in
/-- The family `V` contains every simple `A`-module up to isomorphism. -/
def SimpleComplete : Prop :=
  ∀ (S : Type u) [AddCommGroup S] [Module A S] [IsSimpleModule A S], ∃ i, Nonempty (S ≃ₗ[A] V i)

variable (A k V) in
/-- A module `P` is a *top-`i` module* when `dim_k Hom_A(P, Vⱼ) = δᵢⱼ` for every `j`. -/
def IsTopModule (i : ι) (P : Type u) [AddCommGroup P] [Module A P] : Prop :=
  ∀ j, finrank k (P →ₗ[A] V j) = if j = i then 1 else 0

/-- The space of module maps between finite-dimensional modules is finite-dimensional. -/
theorem finite_linearMap_hom {P W : Type*} [AddCommGroup P] [Module A P] [Module k P]
    [IsScalarTower k A P] [FiniteDimensional k P] [AddCommGroup W] [Module A W] [Module k W]
    [IsScalarTower k A W] [FiniteDimensional k W] : Module.Finite k (P →ₗ[A] W) := by
  let ι' : (P →ₗ[A] W) →ₗ[k] (P →ₗ[k] W) :=
    { toFun := fun φ => φ.restrictScalars k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective ι' (fun φ ψ h => LinearMap.ext fun x => LinearMap.congr_fun h x)

section ModuleP

variable {P : Type u} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
  [FiniteDimensional k P]

/-- A map out of a module whose hom space into `Vⱼ` is zero-dimensional vanishes. -/
theorem hom_eq_zero_of_finrank_eq_zero (j : ι) (h : finrank k (P →ₗ[A] V j) = 0)
    (f : P →ₗ[A] V j) : f = 0 := by
  haveI := finite_linearMap_hom (k := k) (A := A) (P := P) (W := V j)
  exact finrank_zero_iff_forall_zero.1 h f

/-- A maximal submodule of a finitely generated module is the kernel of a map to a simple module
of the list. -/
theorem exists_hom_ker_eq_of_isCoatom (hcomp : SimpleComplete A V) [Module.Finite A P]
    {N : Submodule A P} (hN : IsCoatom N) :
    ∃ (j : ι) (f : P →ₗ[A] V j), LinearMap.ker f = N := by
  haveI : IsSimpleModule A (P ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨j, ⟨e⟩⟩ := hcomp (P ⧸ N)
  refine ⟨j, e.toLinearMap ∘ₗ N.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

/-- A nonzero finitely generated module has a nonzero map to some simple module of the list. -/
theorem exists_ne_zero_hom (hcomp : SimpleComplete A V) [Module.Finite A P] [Nontrivial P] :
    ∃ (j : ι) (f : P →ₗ[A] V j), f ≠ 0 := by
  obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A P)).resolve_left bot_ne_top
  obtain ⟨j, f, hf⟩ := exists_hom_ker_eq_of_isCoatom hcomp hN
  refine ⟨j, f, fun h0 => ?_⟩
  rw [h0, LinearMap.ker_zero] at hf
  exact hN.1 hf.symm

variable (k) in
include k in
theorem isNoetherian_of_finiteDimensional : IsNoetherian A P := isNoetherian_of_tower k inferInstance

variable {i : ι}

/-- A top-`i` module has a surjection `π` onto `Vᵢ` whose kernel contains every proper submodule
(so `ker π` is the unique maximal submodule). -/
theorem IsTopModule.exists_hom (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P) :
    ∃ π : P →ₗ[A] V i, π ≠ 0 ∧ Function.Surjective π ∧
      ∀ N : Submodule A P, N ≠ ⊤ → N ≤ LinearMap.ker π := by
  haveI : IsNoetherian A P := isNoetherian_of_finiteDimensional (k := k)
  have h1 := hP i
  rw [if_pos rfl] at h1
  obtain ⟨π, hπ0, hπ⟩ := finrank_eq_one_iff'.1 h1
  refine ⟨π, hπ0, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top]
    rcases eq_bot_or_eq_top (LinearMap.range π) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hπ0
    · exact h
  · intro N hN
    obtain ⟨N', hN', hNN'⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
    obtain ⟨j, f, hf⟩ := exists_hom_ker_eq_of_isCoatom hcomp hN'
    have hf0 : f ≠ 0 := fun h0 => hN'.1 (by rw [← hf, h0]; exact LinearMap.ker_zero)
    have hj : j = i := by
      by_contra hne
      have := hP j
      rw [if_neg hne] at this
      exact hf0 (hom_eq_zero_of_finrank_eq_zero j this f)
    subst hj
    obtain ⟨c, hc⟩ := hπ f
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hf0
      rw [← hc]
      simp
    calc N ≤ N' := hNN'
      _ = LinearMap.ker f := hf.symm
      _ ≤ LinearMap.ker π := by
        intro x hx
        rw [LinearMap.mem_ker, ← hc] at hx
        exact LinearMap.mem_ker.2 ((smul_eq_zero.1 hx).resolve_left hc0)

/-- A top-`i` module is nontrivial. -/
theorem IsTopModule.nontrivial (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P) :
    Nontrivial P := by
  obtain ⟨π, hπ0, -, -⟩ := hP.exists_hom hcomp
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hπ0 (LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp)

/-- **Etingof et al., Theorem 7.6 (indecomposability)**: a module `P` with `dim Hom_A(P, Vⱼ) = δᵢⱼ`
has a unique maximal submodule, hence is indecomposable.  In particular the projective `Pᵢ = A eᵢ`
is indecomposable. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem IsTopModule.isIndecomposable (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P) :
    IsIndecomposableModule A P := by
  obtain ⟨π, hπ0, -, hπ⟩ := hP.exists_hom hcomp
  haveI := hP.nontrivial hcomp
  refine ⟨this, fun p q hpq => ?_⟩
  by_contra h
  push_neg at h
  have hp : p ≠ ⊤ := fun hp => by
    have := hpq.disjoint
    rw [hp] at this
    exact h.2 (top_disjoint.1 this)
  have hq : q ≠ ⊤ := fun hq => by
    have := hpq.disjoint
    rw [hq] at this
    exact h.1 (disjoint_top.1 this)
  apply hπ0
  have : (⊤ : Submodule A P) ≤ LinearMap.ker π := by
    rw [← hpq.sup_eq_top]
    exact sup_le (hπ p hp) (hπ q hq)
  exact LinearMap.ker_eq_top.1 (top_le_iff.1 this)

/-- Splitting along a surjection with a section. -/
theorem exists_split {P' Q : Type*} [AddCommGroup P'] [Module A P'] [AddCommGroup Q] [Module A Q]
    (h : P' →ₗ[A] Q) (s : Q →ₗ[A] P') (hs : ∀ q, h (s q) = q) :
    Nonempty (P' ≃ₗ[A] Q × LinearMap.ker h) :=
  ⟨{ toFun := fun p => (h p, ⟨p - s (h p), by simp [LinearMap.mem_ker, hs]⟩)
     invFun := fun x => s x.1 + x.2.1
     map_add' := fun x y => Prod.ext (map_add h x y) (Subtype.ext (by simp; abel))
     map_smul' := fun a x => Prod.ext (map_smul h a x) (Subtype.ext (by simp [smul_sub]))
     left_inv := fun p => by simp
     right_inv := by
       rintro ⟨q, ⟨x, hx⟩⟩
       have hx' : h x = 0 := hx
       exact Prod.ext (by simp [hs, hx']) (Subtype.ext (by simp [hs, hx'])) }⟩

/-- A direct summand of a projective module is projective. -/
theorem projective_snd {P' Q K : Type*} [AddCommGroup P'] [Module A P'] [AddCommGroup Q]
    [Module A Q] [AddCommGroup K] [Module A K] [Module.Projective A P'] (e : P' ≃ₗ[A] Q × K) :
    Module.Projective A K :=
  Module.Projective.of_split (e.symm.toLinearMap ∘ₗ LinearMap.inr A Q K)
    (LinearMap.snd A Q K ∘ₗ e.toLinearMap) (by ext x; simp)

variable {Q : Type u} [AddCommGroup Q] [Module A Q] [Module k Q] [IsScalarTower k A Q]
  [FiniteDimensional k Q]

/-- If `P` is projective and top-`i`, and `Q` is top-`i`, there is a surjection `P → Q`. -/
theorem IsTopModule.exists_surjective_hom (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P)
    (hQ : IsTopModule k A V i Q) [Module.Projective A P] :
    ∃ h : P →ₗ[A] Q, Function.Surjective h := by
  obtain ⟨πP, hP0, -, -⟩ := hP.exists_hom hcomp
  obtain ⟨πQ, hQ0, hQs, hQN⟩ := hQ.exists_hom hcomp
  obtain ⟨h, hh⟩ := Module.projective_lifting_property πQ πP hQs
  refine ⟨h, ?_⟩
  rw [← LinearMap.range_eq_top]
  by_contra hne
  apply hP0
  refine LinearMap.ext fun x => ?_
  have h1 : πQ (h x) = 0 := LinearMap.mem_ker.1 (hQN _ hne ⟨x, rfl⟩)
  exact (LinearMap.congr_fun hh x).symm.trans h1

/-- **Etingof et al., Theorem 7.6 (uniqueness)**: two projective modules `P`, `Q` with
`dim Hom_A(−, Vⱼ) = δᵢⱼ` are isomorphic. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem IsTopModule.nonempty_equiv (hcomp : SimpleComplete A V) (hP : IsTopModule k A V i P)
    (hQ : IsTopModule k A V i Q) [Module.Projective A P] [Module.Projective A Q] :
    Nonempty (P ≃ₗ[A] Q) := by
  haveI : IsNoetherian A P := isNoetherian_of_finiteDimensional (k := k)
  obtain ⟨h, hh⟩ := hP.exists_surjective_hom hcomp hQ
  obtain ⟨s, hs⟩ := Module.projective_lifting_property h LinearMap.id hh
  have hs' : ∀ q, h (s q) = q := LinearMap.congr_fun hs
  suffices hker : LinearMap.ker h = ⊥ from
    ⟨LinearEquiv.ofBijective h ⟨LinearMap.ker_eq_bot.1 hker, hh⟩⟩
  by_contra hne
  haveI : Nontrivial (LinearMap.ker h) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨j, f, hf0⟩ := exists_ne_zero_hom hcomp (P := LinearMap.ker h)
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf0 (LinearMap.ext hcon)
  let r : P →ₗ[A] LinearMap.ker h :=
    (LinearMap.id - s ∘ₗ h).codRestrict (LinearMap.ker h)
      (fun p => by simp [LinearMap.mem_ker, hs'])
  have hry : r y.1 = y := Subtype.ext (by
    have : h y.1 = 0 := y.2
    simp [r, this])
  have hrs : ∀ q, r (s q) = 0 := fun q => Subtype.ext (by simp [r, hs'])
  obtain ⟨πQ, hQ0, -, -⟩ := hQ.exists_hom hcomp
  obtain ⟨q, hq⟩ : ∃ q, πQ q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (LinearMap.ext hcon)
  have hji : j = i := by
    by_contra hne'
    have := hP j
    rw [if_neg hne'] at this
    exact hy (by
      have := LinearMap.congr_fun (hom_eq_zero_of_finrank_eq_zero j this (f ∘ₗ r)) y.1
      simpa [hry] using this)
  subst hji
  have h1 := hP j
  rw [if_pos rfl] at h1
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c1, hc1⟩ := hv (πQ ∘ₗ h)
  obtain ⟨c2, hc2⟩ := hv (f ∘ₗ r)
  have hG : πQ q = c1 • v (s q) := by
    have := LinearMap.congr_fun hc1 (s q)
    simpa [hs'] using this.symm
  have hF0 : (f ∘ₗ r) (s q) = 0 := by simp [hrs]
  have hF : (f ∘ₗ r) (s q) = c2 • v (s q) := by
    have := LinearMap.congr_fun hc2 (s q)
    simpa using this.symm
  have hvq : v (s q) ≠ 0 := fun h0 => hq (by rw [hG, h0, smul_zero])
  have hc2z : c2 = 0 := by
    rw [hF0] at hF
    exact (smul_eq_zero.1 hF.symm).resolve_right hvq
  apply hy
  simpa [hry, hc2z] using (LinearMap.congr_fun hc2 y.1).symm

end ModuleP

section Family

variable (F : ι → Type u) [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)] [∀ i, Module k (F i)]
  [∀ i, IsScalarTower k A (F i)] [∀ i, FiniteDimensional k (F i)] [∀ i, Module.Projective A (F i)]

/-- Linear equivalence between a product indexed by `Option T` and the product of the head with the tail. -/
def piOptionLinearEquiv {T : Type} (c : T → ι) (j : ι) :
    (∀ a : Option T, F (a.elim j c)) ≃ₗ[A] F j × ∀ t, F (c t) :=
  { Equiv.piOptionEquivProd (β := fun a : Option T => F (a.elim j c)) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- **Etingof et al., Theorem 7.6 (decomposition of projectives)**: if `F i` are projective modules with
`dim Hom_A(F i, Vⱼ) = δᵢⱼ`, then every finite-dimensional projective module is isomorphic to a finite direct
sum (product) of modules `F (c t)`. -/
theorem exists_pi_equiv (hcomp : SimpleComplete A V) (hF : ∀ i, IsTopModule k A V i (F i))
    (n : ℕ) (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P] (hn : finrank k P = n) :
    ∃ (T : Type) (_ : Fintype T) (c : T → ι), Nonempty (P ≃ₗ[A] ∀ t, F (c t)) := by
  induction n using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · exact ⟨Empty, inferInstance, Empty.elim,
      ⟨LinearEquiv.ofSubsingleton P (∀ t : Empty, F (Empty.elim t))⟩⟩
  · have : IsNoetherian A P := isNoetherian_of_finiteDimensional k
    obtain ⟨j, f, hf0⟩ := exists_ne_zero_hom hcomp (P := P)
    obtain ⟨πj, -, hπs, hπN⟩ := (hF j).exists_hom hcomp
    obtain ⟨h, hh⟩ := Module.projective_lifting_property πj f hπs
    have hsurj : Function.Surjective h := by
      rw [← LinearMap.range_eq_top]
      by_contra hne
      apply hf0
      refine LinearMap.ext fun x => ?_
      have h1 : πj (h x) = 0 := LinearMap.mem_ker.1 (hπN _ hne ⟨x, rfl⟩)
      exact (LinearMap.congr_fun hh x).symm.trans h1
    obtain ⟨s, hs⟩ := Module.projective_lifting_property h LinearMap.id hsurj
    obtain ⟨e⟩ := exists_split h s (LinearMap.congr_fun hs)
    haveI : FiniteDimensional k (LinearMap.ker h) :=
      Module.Finite.of_injective ((LinearMap.ker h).subtype.restrictScalars k) Subtype.val_injective
    haveI : Module.Projective A (LinearMap.ker h) := projective_snd e
    haveI := (hF j).nontrivial hcomp
    have hfr : finrank k P = finrank k (F j) + finrank k (LinearMap.ker h) := by
      rw [(e.restrictScalars k).finrank_eq, Module.finrank_prod]
    have hpos : 0 < finrank k (F j) := Module.finrank_pos
    obtain ⟨T, hT, c, ⟨e2⟩⟩ := ih (finrank k (LinearMap.ker h)) (by omega) (LinearMap.ker h) rfl
    refine ⟨Option T, inferInstance, fun a => a.elim j c, ⟨?_⟩⟩
    exact e.trans ((LinearEquiv.prodCongr (LinearEquiv.refl A (F j)) e2).trans
      (piOptionLinearEquiv F c j).symm)

/-- Hom dimensions of a finite product of the `F (c t)`. -/
theorem finrank_hom_pi (hF : ∀ i, IsTopModule k A V i (F i)) {T : Type} [Fintype T] [DecidableEq T] (c : T → ι)
    (j : ι) : finrank k ((∀ t, F (c t)) →ₗ[A] V j) = Nat.card {t // c t = j} := by
  haveI : ∀ t, Module.Finite k (F (c t) →ₗ[A] V j) := fun t =>
    finite_linearMap_hom (k := k) (A := A) (P := F (c t)) (W := V j)
  have e1 := (LinearMap.lsum A (fun t => F (c t)) k (M := V j)).finrank_eq
  rw [← e1, Module.finrank_pi_fintype, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hF (c t) j]
  by_cases h : c t = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Etingof et al., Theorem 7.6 (classification)**: an indecomposable finite-dimensional projective
module is isomorphic to one of the `F j`. -/
theorem exists_equiv_of_indecomposable (hcomp : SimpleComplete A V)
    (hF : ∀ i, IsTopModule k A V i (F i))
    (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P] (hP : IsIndecomposableModule A P) :
    ∃ j, Nonempty (P ≃ₗ[A] F j) := by
  haveI := hP.1
  have : IsNoetherian A P := isNoetherian_of_finiteDimensional k
  obtain ⟨j, f, hf0⟩ := exists_ne_zero_hom hcomp (P := P)
  obtain ⟨πj, -, hπs, hπN⟩ := (hF j).exists_hom hcomp
  obtain ⟨h, hh⟩ := Module.projective_lifting_property πj f hπs
  have hsurj : Function.Surjective h := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    apply hf0
    refine LinearMap.ext fun x => ?_
    have h1 : πj (h x) = 0 := LinearMap.mem_ker.1 (hπN _ hne ⟨x, rfl⟩)
    exact (LinearMap.congr_fun hh x).symm.trans h1
  obtain ⟨s, hs⟩ := Module.projective_lifting_property h LinearMap.id hsurj
  have hs' : ∀ q, h (s q) = q := LinearMap.congr_fun hs
  refine ⟨j, ?_⟩
  have hc : IsCompl (LinearMap.ker h) (LinearMap.range s) := by
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      rintro x ⟨hx1, q, rfl⟩
      have : q = 0 := by rw [← hs' q]; exact LinearMap.mem_ker.1 hx1
      simp [this]
    · rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      exact ⟨x - s (h x), by simp [LinearMap.mem_ker, hs'], s (h x), ⟨h x, rfl⟩, by simp⟩
  rcases hP.2 _ _ hc with hk | hr
  · exact ⟨LinearEquiv.ofBijective h ⟨LinearMap.ker_eq_bot.1 hk, hsurj⟩⟩
  · exfalso
    haveI := (hF j).nontrivial hcomp
    obtain ⟨q, hq⟩ := exists_ne (0 : F j)
    apply hq
    have hmem : s q ∈ LinearMap.range s := ⟨q, rfl⟩
    rw [hr, Submodule.mem_bot] at hmem
    calc q = h (s q) := (hs' q).symm
      _ = 0 := by rw [hmem, map_zero]

end Family

end Core

section Final

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type u} [∀ i, AddCommGroup (V i)]
  [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)]
  [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

/-- A left ideal of a finite-dimensional algebra is finite-dimensional. -/
instance finiteDimensional_ideal (I : Ideal A) : FiniteDimensional k I :=
  Module.Finite.of_injective (I.subtype.restrictScalars k) Subtype.val_injective

/-- **Etingof et al., Theorem 7.6 (uniqueness, in terms of the left ideals `A e`)**: any finite-dimensional
projective module `P` with `dim Hom_A(P, Vⱼ) = δᵢⱼ` is isomorphic to `A e` for an idempotent `e`
with `A e` projective of the same type. -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem exists_idempotent_equiv_of_isTopModule
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (hcomp : SimpleComplete A V) (i : ι)
    (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    [FiniteDimensional k P] [Module.Projective A P] (hP : IsTopModule k A V i P) :
    ∃ e : A, IsIdempotentElem e ∧ Module.Projective A (Ideal.span {e}) ∧
      IsTopModule k A V i (Ideal.span {e}) ∧ Nonempty (P ≃ₗ[A] Ideal.span {e}) := by
  obtain ⟨e, he, hproj, hdim⟩ := exists_projective_finrank_hom_eq_ite (k := k) hV hcomp i
  haveI := hproj
  exact ⟨e, he, hproj, hdim, hP.nonempty_equiv hcomp (Q := Ideal.span {e}) hdim⟩

/-- **Etingof et al., Theorem 7.6**: for a finite-dimensional algebra `A` over an algebraically closed
field with complete list `V₁, …, Vₙ` of simple modules, there are idempotents `eᵢ` such that
* `Pᵢ = A eᵢ` is projective and indecomposable with `dim Hom_A(Pᵢ, Vⱼ) = δᵢⱼ`;
* `A ≅ ⊕ (dim Vᵢ) copies of Pᵢ` as a left module (here `T` indexes the summands, with `c t` the type of
  the `t`-th summand, and exactly `dim Vⱼ` summands are of type `j`);
* every indecomposable finite-dimensional projective module is isomorphic to some `Pᵢ`.

Uniqueness of `Pᵢ` up to isomorphism is `exists_idempotent_equiv_of_isTopModule`
(and `IsTopModule.nonempty_equiv`). -/
@[kb "etingof2011" "Theorem 7.6, p. 107"]
theorem exists_indecomposable_projectives
    (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (hcomp : SimpleComplete A V) :
    ∃ e : ι → A,
      (∀ i, IsIdempotentElem (e i) ∧ Module.Projective A (Ideal.span {e i}) ∧
        IsTopModule k A V i (Ideal.span {e i}) ∧ IsIndecomposableModule A (Ideal.span {e i})) ∧
      (∃ (T : Type) (c : T → ι), Finite T ∧ Nonempty (A ≃ₗ[A] ∀ t, Ideal.span {e (c t)}) ∧
        ∀ j, Nat.card {t // c t = j} = finrank k (V j)) ∧
      (∀ (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
        [FiniteDimensional k P] [Module.Projective A P], IsIndecomposableModule A P →
        ∃ i, Nonempty (P ≃ₗ[A] Ideal.span {e i})) := by
  classical
  choose e he using fun i => exists_projective_finrank_hom_eq_ite (k := k) hV hcomp i
  have hproj : ∀ i, Module.Projective A (Ideal.span {e i}) := fun i => (he i).2.1
  have hF : ∀ i, IsTopModule k A V i (Ideal.span {e i}) := fun i => (he i).2.2
  refine ⟨e, fun i => ⟨(he i).1, hproj i, hF i, (hF i).isIndecomposable hcomp⟩, ?_, ?_⟩
  · obtain ⟨T, hT, c, ⟨eq⟩⟩ := exists_pi_equiv (k := k) (fun i => Ideal.span {e i}) hcomp hF
      (finrank k A) A rfl
    haveI := hT
    refine ⟨T, c, inferInstance, ⟨eq⟩, fun j => ?_⟩
    have h1 : finrank k (A →ₗ[A] V j) = finrank k (V j) :=
      (LinearMap.ringLmapEquivSelf A k (V j)).finrank_eq
    have h2 : finrank k (A →ₗ[A] V j) = finrank k ((∀ t, Ideal.span {e (c t)}) →ₗ[A] V j) :=
      (LinearEquiv.congrLeft (V j) k eq).finrank_eq
    rw [← h1, h2]
    exact (finrank_hom_pi (fun i => Ideal.span {e i}) hF c j).symm
  · intro P _ _ _ _ _ _ hP
    exact exists_equiv_of_indecomposable (fun i => Ideal.span {e i}) hcomp hF P hP

end Final

end UndergradKB.RepresentationTheory
