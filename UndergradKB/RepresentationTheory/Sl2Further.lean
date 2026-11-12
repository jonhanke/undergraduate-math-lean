import UndergradKB.RepresentationTheory.Sl2
import UndergradKB.RepresentationTheory.Sl2Reducibility
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import UndergradKB.Common.Attr

/-! # Representations of sl(2): Jacobson-Morozov and Clebsch-Gordan (Etingof et al., Problem 1.55(l), (m))

Operator-level continuation of `Sl2.lean` and `Sl2Reducibility.lean` (relations `IsSl2Rel`).

* Jacobson-Morozov (Problem 1.55(l)): every nilpotent operator `E` on a finite-dimensional space
  extends to operators `H`, `E`, `F` satisfying the relations of `sl₂`
  (`exists_sl2_of_isNilpotent`).  The proof is by induction on the dimension: a cyclic block
  `k^(n+1) → V`, `a ↦ ∑ aᵢ Eⁱ v`, for a vector `v` of maximal nilpotency height has an
  `E`-invariant complement (the common kernel of the functionals `φ ∘ Eⁱ`), the standard
  operators (`stdF`, `stdE`, `-stdH`, with the roles of `e` and `f` exchanged) are transported to
  the block, and the induction hypothesis handles the complement.  The field is arbitrary (neither
  algebraically closed nor of characteristic zero is needed); only existence is formalised, not
  the uniqueness up to isomorphism.
* Clebsch-Gordan (Problem 1.55(m)): the tensor product `V_l ⊗ V_m` of the standard
  irreducibles (`tensorOp` for the action on tensor products) is the internal direct sum of
  invariant subspaces, irreducible for the restricted operators, indexed by `Fin (min l m + 1)`,
  with the `i`-th of dimension `l + m - 2 i + 1` (`clebsch_gordan`, with the multiplicity form
  `clebsch_gordan_count`).  By `irreducible_classification` each summand is isomorphic to
  `V_{l+m-2i}`.  The proof counts `h`-eigenspace dimensions in two ways: through the basis
  `eₐ ⊗ e_b` of the tensor product, and through the collected basis of a decomposition into
  irreducibles (from complete reducibility), where the number of summands of dimension `c + 1` is
  `dim ker (h - c) - dim ker (h - c - 2)`.
-/

namespace UndergradKB.RepresentationTheory.Sl2

open Module TensorProduct

universe u

section Transport

variable {k : Type*} [Field k]

/-- Relations of `sl₂` are preserved by algebra homomorphisms. -/
lemma IsSl2Rel.map {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B] {h e f : A}
    (r : IsSl2Rel k h e f) (σ : A →ₐ[k] B) : IsSl2Rel k (σ h) (σ e) (σ f) where
  ef := by rw [← map_mul, ← map_mul, ← map_sub, r.ef]
  he := by rw [← map_mul, ← map_mul, ← map_sub, r.he, map_smul]
  hf := by rw [← map_mul, ← map_mul, ← map_sub, r.hf, map_neg, map_smul]

/-- Relations of `sl₂` on two spaces give relations on the product. -/
lemma IsSl2Rel.prodMap {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    {h e f : Module.End k X} {h' e' f' : Module.End k Y}
    (r : IsSl2Rel k h e f) (r' : IsSl2Rel k h' e' f') :
    IsSl2Rel k (h.prodMap h') (e.prodMap e') (f.prodMap f') where
  ef := LinearMap.ext fun p => by
    have h1 := LinearMap.congr_fun r.ef p.1
    have h2 := LinearMap.congr_fun r'.ef p.2
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  he := LinearMap.ext fun p => by
    have h1 := LinearMap.congr_fun r.he p.1
    have h2 := LinearMap.congr_fun r'.he p.2
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  hf := LinearMap.ext fun p => by
    have h1 := LinearMap.congr_fun r.hf p.1
    have h2 := LinearMap.congr_fun r'.hf p.2
    exact Prod.ext (by simpa using h1) (by simpa using h2)

end Transport

section Jordan

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The linear map `a ↦ ∑ aᵢ Eⁱ v` from `k^(n+1)`. -/
noncomputable def jordanMap (E : Module.End k V) (v : V) (n : ℕ) : (Fin (n + 1) → k) →ₗ[k] V :=
  Fintype.linearCombination k (fun i : Fin (n + 1) => (E ^ (i : ℕ)) v)

lemma pow_apply_pow_apply (E : Module.End k V) (a b : ℕ) (v : V) :
    (E ^ a) ((E ^ b) v) = (E ^ (a + b)) v := by
  rw [pow_add, mul_apply_eq_comp]

lemma single_eq_bv (n : ℕ) (i : Fin (n + 1)) :
    (Pi.single i (1 : k) : Fin (n + 1) → k) = bv k n i := by
  funext j
  simp [bv, Pi.single_apply, Fin.ext_iff]

lemma jordanMap_bv (E : Module.End k V) (v : V) (n : ℕ) (hv : (E ^ (n + 1)) v = 0) (i : ℕ) :
    jordanMap E v n (bv k n i) = (E ^ i) v := by
  by_cases hi : i < n + 1
  · have : bv k n i = Pi.single (⟨i, hi⟩ : Fin (n + 1)) (1 : k) := by
      rw [single_eq_bv]
    rw [this]
    simp [jordanMap]
  · have h0 : bv k n i = 0 := by
      funext j
      have : (j : ℕ) ≠ i := by have := j.2; omega
      simp [bv, this]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
    rw [h0, map_zero, add_comm, ← pow_apply_pow_apply, hv, map_zero]

lemma jordanMap_stdF (E : Module.End k V) (v : V) (n : ℕ) (hv : (E ^ (n + 1)) v = 0)
    (a : Fin (n + 1) → k) : jordanMap E v n (stdF k n a) = E (jordanMap E v n a) := by
  have : jordanMap E v n ∘ₗ stdF k n = E ∘ₗ jordanMap E v n :=
    (Pi.basisFun k (Fin (n + 1))).ext fun i => by
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, single_eq_bv, stdF_bv,
        jordanMap_bv E v n hv]
      rw [pow_succ', mul_apply_eq_comp]
  exact LinearMap.congr_fun this a

lemma jordan_inj_aux (E : Module.End k V) (v : V) (n : ℕ) (hE : E ^ (n + 1) = 0)
    (φ : Module.Dual k V) (hφ : φ ((E ^ n) v) = 1) (a : Fin (n + 1) → k)
    (ha : ∀ l : Fin (n + 1), φ ((E ^ (l : ℕ)) (jordanMap E v n a)) = 0) : a = 0 := by
  have key : ∀ m : ℕ, ∀ i : Fin (n + 1), (i : ℕ) = m → a i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      have h1 := ha ⟨n - i, by omega⟩
      simp only [jordanMap, Fintype.linearCombination_apply, map_sum, map_smul, smul_eq_mul,
        pow_apply_pow_apply] at h1
      rw [Finset.sum_eq_single i] at h1
      · have : n - (i : ℕ) + i = n := by have := i.2; omega
        rw [this, hφ, mul_one] at h1
        exact h1
      · intro j _ hji
        rcases lt_or_gt_of_ne (fun h => hji (Fin.ext h) : (j : ℕ) ≠ i) with hlt | hgt
        · rw [ih j (by omega) j rfl, zero_mul]
        · have : E ^ (n - (i : ℕ) + j) = 0 := by
            obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ n - (i : ℕ) + j by
              have := i.2; omega)
            rw [ht, pow_add, hE, zero_mul]
          simp [this]
      · simp
  funext i
  exact key _ i rfl

/-- Induction step data: for a nilpotent `E` of index `n + 1` on a finite-dimensional space, a
Jordan block `k^(n+1) → V` and an `E`-invariant complement. -/
lemma exists_jordan_split [FiniteDimensional k V] (E : Module.End k V) (n : ℕ) (hE : E ^ (n + 1) = 0)
    (hn : E ^ n ≠ 0) :
    ∃ (v : V) (W : Submodule k V) (_ : ∀ x ∈ W, E x ∈ W)
      (Θ : ((Fin (n + 1) → k) × W) ≃ₗ[k] V),
      (∀ p, Θ p = jordanMap E v n p.1 + p.2) ∧ (E ^ (n + 1)) v = 0 ∧
        Module.finrank k W + (n + 1) = Module.finrank k V := by
  obtain ⟨v, hv⟩ : ∃ v, (E ^ n) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (LinearMap.ext hcon)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv
  let Φ : V →ₗ[k] (Fin (n + 1) → k) := LinearMap.pi fun l : Fin (n + 1) => φ ∘ₗ (E ^ (l : ℕ))
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule k V, W = LinearMap.ker Φ := ⟨_, rfl⟩
  have hmemW : ∀ x, x ∈ W ↔ ∀ l : Fin (n + 1), φ ((E ^ (l : ℕ)) x) = 0 := by
    intro x
    simp only [hWdef, LinearMap.mem_ker, Φ]
    constructor
    · intro h l
      exact congrFun h l
    · intro h
      funext l
      exact h l
  have hW : ∀ x ∈ W, E x ∈ W := by
    intro x hx
    rw [hmemW] at hx ⊢
    intro l
    by_cases hl : (l : ℕ) + 1 < n + 1
    · have := hx ⟨l + 1, hl⟩
      simpa [pow_succ, mul_apply_eq_comp] using this
    · have : (l : ℕ) = n := by have := l.2; omega
      rw [this, ← mul_apply_eq_comp, ← pow_succ, hE]
      simp
  have hvn : (E ^ (n + 1)) v = 0 := by rw [hE]; rfl
  have hinj : Function.Injective ((jordanMap E v n).coprod W.subtype) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, w⟩ h
    simp only [LinearMap.coprod_apply, Submodule.subtype_apply] at h
    have hw : jordanMap E v n a ∈ W := by
      have : jordanMap E v n a = -(w : V) := eq_neg_of_add_eq_zero_left h
      rw [this]; exact W.neg_mem w.2
    have ha : a = 0 := jordan_inj_aux E v n hE φ hφ a ((hmemW _).mp hw)
    subst ha
    simp only [map_zero, zero_add] at h
    exact Prod.ext rfl (Subtype.ext h)
  have hrank : Module.finrank k V ≤ (n + 1) + Module.finrank k W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [← hWdef] at h1
    have h2 : Module.finrank k (LinearMap.range Φ) ≤ n + 1 := by
      have := Submodule.finrank_le (LinearMap.range Φ)
      simpa using this
    omega
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  simp only [Module.finrank_fin_fun] at hle
  have hsurj : Function.Surjective ((jordanMap E v n).coprod W.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod]; simp only [Module.finrank_fin_fun]; omega)).mp hinj
  refine ⟨v, W, hW, LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun p => ?_, hvn, by omega⟩
  rfl

/-- Induction on the dimension: a nilpotent operator extends to an `sl₂` triple. -/
lemma exists_sl2_aux (d : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    Module.finrank k V = d → ∀ E : Module.End k V, IsNilpotent E →
      ∃ H F : Module.End k V, IsSl2Rel k H E F := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd E hE
  classical
  by_cases hV : Subsingleton V
  · refine ⟨0, 0, ?_, ?_, ?_⟩ <;> exact LinearMap.ext fun x => Subsingleton.elim _ _
  rw [not_subsingleton_iff_nontrivial] at hV
  have hex : ∃ m, E ^ m = 0 := hE
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero] at this
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (by simpa using LinearMap.congr_fun this x)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hEn : E ^ (n + 1) = 0 := by
    have := Nat.find_spec hex
    rwa [hn] at this
  have hEn' : E ^ n ≠ 0 := Nat.find_min hex (by omega)
  obtain ⟨v, W, hW, Θ, hΘ, hv, hrk⟩ := exists_jordan_split E n hEn hEn'
  have hnil : IsNilpotent (E.restrict hW) := Module.End.isNilpotent.restrict hW hE
  obtain ⟨HW, FW, rW⟩ := ih (Module.finrank k W) (by omega) rfl (E.restrict hW) hnil
  have rP := ((isSl2Rel_std k n).symm).prodMap rW
  have hσ : ∀ p, Θ ((stdF k n).prodMap (E.restrict hW) p) = E (Θ p) := by
    intro p
    rw [hΘ, hΘ]
    simp [jordanMap_stdF E v n hv]
  let σ := Θ.conjAlgEquiv k
  have hE' : σ ((stdF k n).prodMap (E.restrict hW)) = E := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conjAlgEquiv_apply]
    simpa using hσ (Θ.symm x)
  refine ⟨σ (((-stdH k n)).prodMap HW), σ ((stdE k n).prodMap FW), ?_⟩
  have := rP.map σ.toAlgHom
  simpa [hE'] using this

variable [FiniteDimensional k V]

/-- Problem 1.55(l) (Jacobson-Morozov lemma for `sl₂`): every nilpotent operator `E` on a
finite-dimensional vector space extends to operators `H`, `E`, `F` satisfying the defining relations
of `sl₂`.  (Existence only; the field need not be algebraically closed or of characteristic zero for
this direction.) -/
@[kb "etingof2011" "Problem 1.55(l), p. 21"]
theorem exists_sl2_of_isNilpotent (E : Module.End k V) (hE : IsNilpotent E) :
    ∃ H F : Module.End k V, IsSl2Rel k H E F :=
  exists_sl2_aux _ rfl E hE

end Jordan

section Tensor

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- The action of an element of `sl₂` on a tensor product: `g ⊗ 1 + 1 ⊗ g'`. -/
noncomputable def tensorOp (g : Module.End k V) (g' : Module.End k W) :
    Module.End k (V ⊗[k] W) :=
  TensorProduct.map g LinearMap.id + TensorProduct.map LinearMap.id g'

lemma tensorOp_tmul (g : Module.End k V) (g' : Module.End k W) (x : V) (y : W) :
    tensorOp g g' (x ⊗ₜ[k] y) = g x ⊗ₜ y + x ⊗ₜ g' y := by
  simp [tensorOp]

/-- The tensor product of two representations of the relations of `sl₂` again satisfies them. -/
lemma IsSl2Rel.tensor {h e f : Module.End k V} {h' e' f' : Module.End k W}
    (r : IsSl2Rel k h e f) (r' : IsSl2Rel k h' e' f') :
    IsSl2Rel k (tensorOp h h') (tensorOp e e') (tensorOp f f') where
  ef := TensorProduct.ext' fun x y => by
    have a := r.ef_apply x
    have b := r'.ef_apply y
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, tensorOp_tmul, map_add, a, b,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  he := TensorProduct.ext' fun x y => by
    have a := r.he_apply x
    have b := r'.he_apply y
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, tensorOp_tmul, map_add, a, b,
      TensorProduct.add_tmul, TensorProduct.tmul_add, LinearMap.smul_apply, smul_add,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    abel
  hf := TensorProduct.ext' fun x y => by
    have a := r.hf_apply x
    have b := r'.hf_apply y
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, tensorOp_tmul, map_add, a, b,
      LinearMap.smul_apply, smul_add,
      LinearMap.neg_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, neg_add]
    abel

end Tensor

section Eigen

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

open scoped Classical in
/-- If an operator is diagonal in a basis, the dimension of an eigenspace is the number of basis
vectors with that eigenvalue. -/
lemma finrank_eigenspace_eq_card {ι : Type*} [Fintype ι] (b : Basis ι k V) (T : Module.End k V)
    (w : ι → k) (hT : ∀ i, T (b i) = w i • b i) (c : k) :
    Module.finrank k (Module.End.eigenspace T c) = Fintype.card {i // w i = c} := by
  have hspan : Module.End.eigenspace T c =
      Submodule.span k (Set.range fun i : {i // w i = c} => b i) := by
    apply le_antisymm
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      have h1 : ∀ y, T y = ∑ i, (b.repr y i * w i) • b i := by
        intro y
        calc T y = T (∑ i, b.repr y i • b i) := by rw [b.sum_repr]
          _ = _ := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_smul, hT, smul_smul]
      have hrepr : ∀ i, b.repr x i * w i = c * b.repr x i := by
        intro i
        have := congrArg (fun z => b.repr z i) hx
        have h2 : b.repr (T x) i = b.repr x i * w i := by
          rw [h1 x, b.repr_sum_self]
        simp only [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
        exact this
      rw [← b.sum_repr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : w i = c
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · have : b.repr x i = 0 := by
          have := hrepr i
          have h3 : b.repr x i * (w i - c) = 0 := by linear_combination this
          rcases mul_eq_zero.mp h3 with h | h
          · exact h
          · exact absurd (sub_eq_zero.mp h) hi
        rw [this, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hT, hi]
  rw [hspan]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

end Eigen

section Combinatorics

lemma cnt_gen (μ M t : ℕ) :
    ∑ b : Fin (μ + 1), (if M = t + 2 * (b : ℕ) then 1 else 0) =
      if t ≤ M ∧ (M - t) % 2 = 0 ∧ (M - t) / 2 ≤ μ then 1 else 0 := by
  split_ifs with hc
  · rw [Finset.sum_eq_single (⟨(M - t) / 2, by omega⟩ : Fin (μ + 1))]
    · show (if M = t + 2 * ((M - t) / 2) then 1 else 0) = 1
      split_ifs with h
      · rfl
      · omega
    · intro i _ hi
      have : ¬ M = t + 2 * (i : ℕ) := by
        intro h; apply hi; ext; simp only; omega
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have : ¬ M = t + 2 * (i : ℕ) := by have := i.2; omega
    simp [this]

lemma card_sigma_subtype {ι : Type*} [Fintype ι] (m : ι → ℕ) (P : (Σ j, Fin (m j + 1)) → Prop)
    [DecidablePred P] :
    Fintype.card {p // P p} = ∑ j, ∑ i : Fin (m j + 1), if P ⟨j, i⟩ then 1 else 0 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma]

lemma sigma_count {ι : Type*} [Fintype ι] (n : ι → ℕ) (c : ℕ) :
    Fintype.card {p : (Σ j, Fin (n j + 1)) // n p.1 = c + 2 * (p.2 : ℕ)} =
      Fintype.card {p : (Σ j, Fin (n j + 1)) // n p.1 = (c + 2) + 2 * (p.2 : ℕ)} +
        Fintype.card {j // n j = c} := by
  rw [card_sigma_subtype, card_sigma_subtype, Fintype.card_subtype, Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := cnt_gen (n j) (n j) c
  have h2 := cnt_gen (n j) (n j) (c + 2)
  simp only at h1 h2 ⊢
  rw [h1, h2]
  split_ifs <;> omega

end Combinatorics

section Count

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {V : Type*} [AddCommGroup V]
  [Module k V] [FiniteDimensional k V] {h e f : Module.End k V}

/-- For a decomposition of a finite-dimensional `sl₂`-module into irreducible invariant subspaces,
the dimension of the `h`-eigenspace of eigenvalue `c` is the number of pairs `(j, i)` with
`i ≤ nⱼ` and `nⱼ = c + 2 i`, where `nⱼ + 1` is the dimension of the `j`-th summand. -/
theorem weight_count (r : IsSl2Rel k h e f) {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule k V) (hS : ∀ i, IsInv h e f (S i))
    (hirr : ∀ i, IsIrreducibleRep (h.restrict (hS i).1) (e.restrict (hS i).2.1)
      (f.restrict (hS i).2.2))
    (hint : DirectSum.IsInternal S) :
    ∃ n : ι → ℕ, (∀ j, Module.finrank k (S j) = n j + 1) ∧ ∀ c : ℕ,
      Module.finrank k (Module.End.eigenspace h (c : k)) =
        Fintype.card {p : (Σ j, Fin (n j + 1)) // n p.1 = c + 2 * (p.2 : ℕ)} := by
  classical
  have hex : ∀ j, ∃ (n : ℕ) (B : Basis (Fin (n + 1)) k (S j)),
      ∀ i, h (B i : V) = ((n : k) - 2 * ((i : ℕ) : k)) • (B i : V) := by
    intro j
    have rj := r.restrict (hS j)
    obtain ⟨v, n, hv, hs, -, -⟩ := rj.exists_highest_weight (hirr j)
    refine ⟨n, rj.primBasis hv rfl hs, fun i => ?_⟩
    have := congrArg Subtype.val (rj.h_pow_f hv i)
    rw [rj.primBasis_apply hv rfl hs]
    simpa using this
  choose n B hB using hex
  refine ⟨n, fun j => ?_, fun c => ?_⟩
  · rw [Module.finrank_eq_card_basis (B j)]
    simp
  · have hb : ∀ p, hint.collectedBasis B p = (B p.1 p.2 : V) :=
      fun p => congrFun (hint.collectedBasis_coe B) p
    have := finrank_eigenspace_eq_card (hint.collectedBasis B) h
      (fun p : Σ j, Fin (n j + 1) => ((n p.1 : ℕ) : k) - 2 * ((p.2 : ℕ) : k))
      (fun p => by rw [hb]; exact hB p.1 p.2) (c : k)
    rw [this]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    constructor
    · intro hp
      have : ((n p.1 : ℕ) : k) = ((c + 2 * (p.2 : ℕ) : ℕ) : k) := by
        push_cast; linear_combination hp
      exact_mod_cast this
    · intro hp
      have := congrArg (Nat.cast : ℕ → k) hp
      push_cast at this
      linear_combination this

end Count

section CG

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

omit [CharZero k] [IsAlgClosed k] in
lemma stdH_single (n : ℕ) (a : Fin (n + 1)) :
    stdH k n (Pi.single a 1) = ((n : k) - 2 * ((a : ℕ) : k)) • (Pi.single a 1 : Fin (n + 1) → k) := by
  funext j
  rw [stdH_apply]
  by_cases hj : j = a
  · subst hj; simp
  · simp [hj]

omit [IsAlgClosed k] in
/-- Eigenspace dimensions of `h` on `V_l ⊗ V_m`: the number of pairs `(a, b)` with
`l + m = c + 2 (a + b)`. -/
lemma tensor_weight_count (l m c : ℕ) :
    Module.finrank k (Module.End.eigenspace (tensorOp (stdH k l) (stdH k m)) (c : k)) =
      Fintype.card {p : Fin (l + 1) × Fin (m + 1) // l + m = c + 2 * ((p.1 : ℕ) + (p.2 : ℕ))} := by
  classical
  have := finrank_eigenspace_eq_card
    ((Pi.basisFun k (Fin (l + 1))).tensorProduct (Pi.basisFun k (Fin (m + 1))))
    (tensorOp (stdH k l) (stdH k m))
    (fun p : Fin (l + 1) × Fin (m + 1) =>
      (((l : k) - 2 * ((p.1 : ℕ) : k)) + ((m : k) - 2 * ((p.2 : ℕ) : k))))
    (by
      rintro ⟨a, b⟩
      simp only [Basis.tensorProduct_apply, Pi.basisFun_apply, tensorOp_tmul, stdH_single,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]) (c : k)
  rw [this]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun p => ?_)
  constructor
  · intro hp
    have : ((l + m : ℕ) : k) = ((c + 2 * ((p.1 : ℕ) + (p.2 : ℕ)) : ℕ) : k) := by
      push_cast; linear_combination hp
    exact_mod_cast this
  · intro hp
    have := congrArg (Nat.cast : ℕ → k) hp
    push_cast at this
    linear_combination this

/-- The number of `b` with `l + m = t + 2 b`. -/
noncomputable def gcount (l m t : ℕ) : ℕ :=
  ∑ b : Fin (m + 1), if l + m = t + 2 * (b : ℕ) then 1 else 0

lemma gcount_eq (l m t : ℕ) :
    gcount l m t = if t ≤ l + m ∧ (l + m - t) % 2 = 0 ∧ (l + m - t) / 2 ≤ m then 1 else 0 :=
  cnt_gen m (l + m) t

lemma Q_eq (l m c : ℕ) :
    Fintype.card {p : Fin (l + 1) × Fin (m + 1) // l + m = c + 2 * ((p.1 : ℕ) + (p.2 : ℕ))} =
      ∑ a : Fin (l + 1), gcount l m (c + 2 * (a : ℕ)) := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only
  rw [show c + 2 * ((a : ℕ) + (b : ℕ)) = c + 2 * (a : ℕ) + 2 * (b : ℕ) by ring]

lemma Q_rel (l m c : ℕ) :
    Fintype.card {p : Fin (l + 1) × Fin (m + 1) // l + m = c + 2 * ((p.1 : ℕ) + (p.2 : ℕ))} +
        gcount l m (c + 2 + 2 * l) =
      Fintype.card {p : Fin (l + 1) × Fin (m + 1) //
        l + m = (c + 2) + 2 * ((p.1 : ℕ) + (p.2 : ℕ))} + gcount l m c := by
  rw [Q_eq, Q_eq]
  have s1 : ∑ a : Fin (l + 1), gcount l m (c + 2 * (a : ℕ)) =
      gcount l m c + ∑ i : Fin l, gcount l m (c + 2 + 2 * (i : ℕ)) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, mul_zero, add_zero, Fin.val_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring
  have s2 : ∑ a : Fin (l + 1), gcount l m (c + 2 + 2 * (a : ℕ)) =
      ∑ i : Fin l, gcount l m (c + 2 + 2 * (i : ℕ)) + gcount l m (c + 2 + 2 * l) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  rw [s1, s2]
  ring

/-- The multiplicity function of the decomposition of `V_l ⊗ V_m`: the number of summands of
dimension `c + 1` is `1` if `c = l + m - 2 i` with `0 ≤ i ≤ min l m` and `0` otherwise. -/
theorem clebsch_gordan_count (l m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : ι → Submodule k
        (TensorProduct k (Fin (l + 1) → k) (Fin (m + 1) → k)))
      (hS : ∀ i, IsInv (tensorOp (stdH k l) (stdH k m)) (tensorOp (stdE k l) (stdE k m))
        (tensorOp (stdF k l) (stdF k m)) (S i)),
      (∀ i, IsIrreducibleRep ((tensorOp (stdH k l) (stdH k m)).restrict (hS i).1)
        ((tensorOp (stdE k l) (stdE k m)).restrict (hS i).2.1)
        ((tensorOp (stdF k l) (stdF k m)).restrict (hS i).2.2)) ∧ DirectSum.IsInternal S ∧
      ∃ n : ι → ℕ, (∀ j, Module.finrank k (S j) = n j + 1) ∧ ∀ c : ℕ,
        Fintype.card {j // n j = c} =
          if c ≤ l + m ∧ (l + m - c) % 2 = 0 ∧ (l + m - c) / 2 ≤ min l m then 1 else 0 := by
  have r := (isSl2Rel_std k l).tensor (isSl2Rel_std k m)
  obtain ⟨ι, hι, hdec, S, hS, hirr, hint⟩ := r.exists_internal_irreducible
  obtain ⟨n, hn, hcount⟩ := weight_count r S hS hirr hint
  refine ⟨ι, hι, hdec, S, hS, hirr, hint, n, hn, fun c => ?_⟩
  have e1 := hcount c
  have e2 := hcount (c + 2)
  rw [tensor_weight_count] at e1 e2
  have e3 := sigma_count n c
  have e4 := Q_rel l m c
  rw [gcount_eq, gcount_eq] at e4
  split_ifs at e4 ⊢ <;> omega

/-- Clebsch-Gordan decomposition (Problem 1.55(m)): over an algebraically closed field of
characteristic zero, the tensor product `V_l ⊗ V_m` of the standard irreducible representations
`k^(l+1)` and `k^(m+1)` of the relations of `sl₂` (with `h`, `e`, `f` acting by the derivation rule
`g ⊗ 1 + 1 ⊗ g`) is the internal direct sum of invariant subspaces `S j`, each irreducible for the
restricted operators, indexed by `Fin (min l m + 1)`, the `i`-th having dimension `l + m - 2 i + 1`.
By `irreducible_classification` the `i`-th summand is thus isomorphic to `V_{l+m-2i}`. -/
@[kb "etingof2011" "Problem 1.55(m), p. 21"]
theorem clebsch_gordan (l m : ℕ) :
    ∃ (S : Fin (min l m + 1) → Submodule k
        (TensorProduct k (Fin (l + 1) → k) (Fin (m + 1) → k)))
      (hS : ∀ i, IsInv (tensorOp (stdH k l) (stdH k m)) (tensorOp (stdE k l) (stdE k m))
        (tensorOp (stdF k l) (stdF k m)) (S i)),
      (∀ i, IsIrreducibleRep ((tensorOp (stdH k l) (stdH k m)).restrict (hS i).1)
        ((tensorOp (stdE k l) (stdE k m)).restrict (hS i).2.1)
        ((tensorOp (stdF k l) (stdF k m)).restrict (hS i).2.2)) ∧ DirectSum.IsInternal S ∧
      ∀ i, Module.finrank k (S i) = l + m - 2 * (i : ℕ) + 1 := by
  obtain ⟨ι, hι, hdec, S, hS, hirr, hint, n, hn, hc⟩ := clebsch_gordan_count (k := k) l m
  have hcond : ∀ j, n j ≤ l + m ∧ (l + m - n j) % 2 = 0 ∧ (l + m - n j) / 2 ≤ min l m := by
    intro j
    have h1 := hc (n j)
    have h2 : 0 < Fintype.card {j' // n j' = n j} := Fintype.card_pos_iff.mpr ⟨⟨j, rfl⟩⟩
    by_contra hcon
    simp only [hcon, ↓reduceIte] at h1
    omega
  have hone : ∀ j, ∀ j', n j' = n j → j' = j := by
    intro j j' hj
    have h1 := hc (n j)
    simp only [hcond j, and_self, ite_true] at h1
    have := Fintype.card_le_one_iff.mp h1.le ⟨j', hj⟩ ⟨j, rfl⟩
    exact congrArg Subtype.val this
  let φ : ι → Fin (min l m + 1) := fun j => ⟨(l + m - n j) / 2, by have := hcond j; omega⟩
  have hinj : Function.Injective φ := by
    intro j j' h
    have h' : (l + m - n j) / 2 = (l + m - n j') / 2 := congrArg Fin.val h
    have := hcond j
    have := hcond j'
    exact (hone j j' (by omega)).symm
  have hsurj : Function.Surjective φ := by
    intro i
    have hi := i.2
    have h1 := hc (l + m - 2 * (i : ℕ))
    have hcc : l + m - 2 * (i : ℕ) ≤ l + m ∧ (l + m - (l + m - 2 * (i : ℕ))) % 2 = 0 ∧
        (l + m - (l + m - 2 * (i : ℕ))) / 2 ≤ min l m := by omega
    simp only [hcc, and_self, ite_true] at h1
    obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card {j // n j = l + m - 2 * (i : ℕ)})
    exact ⟨j, Fin.ext (by simp only [φ]; omega)⟩
  let e : ι ≃ Fin (min l m + 1) := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨fun i => S (e.symm i), fun i => hS _, fun i => hirr _, ?_, fun i => ?_⟩
  · obtain ⟨hind, hsup⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top S).mp hint
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hind.comp e.symm.injective, ?_⟩
    rw [e.symm.iSup_comp (g := S)]
    exact hsup
  · rw [hn]
    have := hcond (e.symm i)
    have h2 : (φ (e.symm i) : ℕ) = i := by
      have := e.apply_symm_apply i
      exact congrArg Fin.val this
    simp only [φ] at h2
    omega

end CG

end UndergradKB.RepresentationTheory.Sl2
