import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsClassify

namespace UndergradKB.RepresentationTheory

open Module Set.powersetCard

section Abstract

variable {G W ι : Type*} [Group G] [AddCommGroup W] [Module ℂ W]

/-- If the vectors `b i` are simultaneous eigenvectors for the elements of `T`, with characters separated by
`T`, and an invariant subspace `U` contains a combination `∑ c k • b k` with `c i ≠ 0`, then `b i ∈ U`. -/
theorem mem_of_eigen_sum (ρ : Representation ℂ G W) (b : ι → W) (χ : ι → G → ℂ) (T : Set G)
    (heig : ∀ i, ∀ g ∈ T, ρ g (b i) = χ i g • b i)
    (hsep : ∀ i j, i ≠ j → ∃ g ∈ T, χ i g ≠ χ j g)
    (U : Submodule ℂ W) (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) :
    ∀ (n : ℕ) (s : Finset ι) (c : ι → ℂ) (i : ι), s.card = n → i ∈ s → c i ≠ 0 →
      ∑ k ∈ s, c k • b k ∈ U → b i ∈ U := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s c i hn his hci hf
  by_cases hj : ∃ j ∈ s, j ≠ i
  · obtain ⟨j, hjs, hji⟩ := hj
    obtain ⟨g, hgT, hg⟩ := hsep i j (Ne.symm hji)
    have key : ρ g (∑ k ∈ s, c k • b k) - χ j g • ∑ k ∈ s, c k • b k =
        ∑ k ∈ s.erase j, (c k * (χ k g - χ j g)) • b k := by
      rw [Finset.sum_erase s (f := fun k => (c k * (χ k g - χ j g)) • b k) (by simp), map_sum,
        Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, heig k g hgT, smul_smul, smul_smul, mul_sub, sub_smul, mul_comm (χ j g) (c k)]
    have hmem : ρ g (∑ k ∈ s, c k • b k) - χ j g • ∑ k ∈ s, c k • b k ∈ U :=
      U.sub_mem (hU g _ hf) (U.smul_mem _ hf)
    rw [key] at hmem
    refine ih (s.erase j).card ?_ (s.erase j) (fun k => c k * (χ k g - χ j g)) i rfl
      (Finset.mem_erase.2 ⟨Ne.symm hji, his⟩) (mul_ne_zero hci (sub_ne_zero.2 hg)) hmem
    rw [← hn]
    exact Finset.card_erase_lt_of_mem hjs
  · push Not at hj
    have hs : s = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨his, fun j hjs => hj j hjs⟩
    subst hs
    rw [Finset.sum_singleton] at hf
    have := U.smul_mem (c i)⁻¹ hf
    rwa [smul_smul, inv_mul_cancel₀ hci, one_smul] at this

/-- Irreducibility from a spanning family of weight vectors with separated weights, in which any member of an
invariant subspace forces all the others to lie in it. -/
theorem isIrredRep_of_weight_family (ρ : Representation ℂ G W) (b : ι → W) [Nonempty ι]
    (hb : ∀ i, b i ≠ 0) (hspan : Submodule.span ℂ (Set.range b) = ⊤)
    (χ : ι → G → ℂ) (T : Set G)
    (heig : ∀ i, ∀ g ∈ T, ρ g (b i) = χ i g • b i)
    (hsep : ∀ i j, i ≠ j → ∃ g ∈ T, χ i g ≠ χ j g)
    (hmove : ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, ρ g w ∈ U) → ∀ i j, b i ∈ U → b j ∈ U) :
    IsIrredRep ρ := by
  classical
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨⟨b i, 0, hb i⟩⟩
  · by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      obtain ⟨f, hfU, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hf : f ∈ Submodule.span ℂ (Set.range b) := hspan ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc
        exact hf0 hc.symm
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hc0
      have hi' : c i ≠ 0 := by simpa using hi
      have hfU' : ∑ k ∈ c.support, c k • b k ∈ U := by
        rw [Finsupp.sum] at hc
        rw [hc]; exact hfU
      have h1 := mem_of_eigen_sum ρ b χ T heig hsep U hU _ c.support (⇑c) i rfl
        (Finsupp.mem_support_iff.2 hi') hi' hfU'
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hmove U hU i j h1

end Abstract

section Exterior

variable (N m : ℕ)

/-- The representation of `GL_N(ℂ)` on the exterior power `Λ^m V`, `V = ℂ^N`, induced functorially from the
standard representation. -/
noncomputable def extPowRep : Representation ℂ (GL (Fin N) ℂ) (⋀[ℂ]^m (Fin N → ℂ)) where
  toFun g := exteriorPower.map m (stdRep N ℂ g)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    exact exteriorPower.map_comp (stdRep N ℂ h) (stdRep N ℂ g)

/-- The basis of wedge monomials `e_S = e_{s₁} ∧ ⋯ ∧ e_{s_m}` of `Λ^m V`, indexed by the `m`-element subsets. -/
noncomputable def extBasis : Basis (Set.powersetCard (Fin N) m) ℂ (⋀[ℂ]^m (Fin N → ℂ)) :=
  (Pi.basisFun ℂ (Fin N)).exteriorPower m

variable {N m}

lemma extBasis_apply (S : Set.powersetCard (Fin N) m) :
    extBasis N m S = exteriorPower.ιMulti_family ℂ m (Pi.basisFun ℂ (Fin N)) S :=
  exteriorPower.basis_apply _ _ _ _

lemma extPowRep_apply_ιMulti_family (g : GL (Fin N) ℂ) (S : Set.powersetCard (Fin N) m) :
    extPowRep N m g (extBasis N m S) =
      exteriorPower.ιMulti ℂ m (fun j => stdRep N ℂ g (Pi.basisFun ℂ (Fin N) (ofFinEmbEquiv.symm S j))) := by
  rw [extBasis_apply]
  show exteriorPower.map m (stdRep N ℂ g) _ = _
  rw [exteriorPower.map_apply_ιMulti_family]
  rfl

lemma diagGL_apply_diag (t : Fin N → ℂ) (hx : ∀ i, t i ≠ 0) (x : Fin N) :
    ((diagGL N t hx : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) x x = t x := by
  simp [diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

lemma stdRep_diagGL_single (t : Fin N → ℂ) (hx : ∀ i, t i ≠ 0) (i : Fin N) :
    stdRep N ℂ (diagGL N t hx) (Pi.basisFun ℂ (Fin N) i) = t i • Pi.basisFun ℂ (Fin N) i := by
  ext j
  simp [stdRep, diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.diagonal_apply, Pi.single_apply,
    Matrix.mulVec, dotProduct]
  split_ifs <;> simp_all

lemma prod_ofFinEmbEquiv (S : Set.powersetCard (Fin N) m) (t : Fin N → ℂ) :
    ∏ j : Fin m, t (ofFinEmbEquiv.symm S j) = ∏ x ∈ S.1, t x := by
  classical
  have himg : Finset.univ.image (ofFinEmbEquiv.symm S) = S.1 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem S x).trans mem_coe_iff.symm
  rw [← himg, Finset.prod_image (fun a _ b _ h => (ofFinEmbEquiv.symm S).injective h)]

/-- The wedge monomial `e_S` is an eigenvector of the diagonal matrix `diag(t)`, with eigenvalue `∏_{i ∈ S} t_i`. -/
lemma extPowRep_diag (t : Fin N → ℂ) (hx : ∀ i, t i ≠ 0) (S : Set.powersetCard (Fin N) m) :
    extPowRep N m (diagGL N t hx) (extBasis N m S) = (∏ x ∈ S.1, t x) • extBasis N m S := by
  rw [extPowRep_apply_ιMulti_family, extBasis_apply]
  simp only [stdRep_diagGL_single]
  rw [AlternatingMap.map_smul_univ, prod_ofFinEmbEquiv]
  rfl

lemma prod_update_two (S S' : Set.powersetCard (Fin N) m) (h : S ≠ S') :
    ∃ t : Fin N → ℂ, (∀ i, t i ≠ 0) ∧ ∏ x ∈ S.1, t x ≠ ∏ x ∈ S'.1, t x := by
  classical
  obtain ⟨i, hi, hi'⟩ := (exists_mem_notMem_iff_ne S S').1 h
  refine ⟨fun x => if x = i then 2 else 1, fun x => by dsimp only; split_ifs <;> norm_num, ?_⟩
  have h1 : i ∈ S.1 := mem_coe_iff.2 hi
  have h2 : i ∉ S'.1 := fun hh => hi' (mem_coe_iff.1 hh)
  rw [Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [h1, h2]

lemma exists_perm_orderEmb (S S' : Set.powersetCard (Fin N) m) :
    ∃ σ : Equiv.Perm (Fin N), ∀ j, σ (ofFinEmbEquiv.symm S j) = ofFinEmbEquiv.symm S' j := by
  classical
  set o := ofFinEmbEquiv.symm S with ho
  set o' := ofFinEmbEquiv.symm S' with ho'
  let f : Fin N → Fin N := Function.extend o o' id
  have hf : ∀ j, f (o j) = o' j := fun j => o.injective.extend_apply o' id j
  have hinj : Set.InjOn f ↑(Finset.univ.image o) := by
    intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [hf, hf] at hxy
    rw [o'.injective hxy]
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (α := Fin N) (β := Fin N) (t := Finset.univ)
    (by simp) (s := Finset.univ.image o) (f := f) (by simp) hinj
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun j => ?_⟩
  show ((g (o j) : Finset.univ) : Fin N) = _
  rw [hg (o j) (Finset.mem_image_of_mem _ (Finset.mem_univ _)), hf]

/-- The permutation matrix sending `e_i` to `e_{σ i}`, as an element of `GL_N(ℂ)`. -/
noncomputable def permGL (σ : Equiv.Perm (Fin N)) : GL (Fin N) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Equiv.Perm.permMatrix ℂ σ.symm) (by
    rw [Matrix.det_permutation]; simp)

lemma stdRep_permGL (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    stdRep N ℂ (permGL σ) (Pi.basisFun ℂ (Fin N) i) = Pi.basisFun ℂ (Fin N) (σ i) := by
  simp only [stdRep, permGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  show (Equiv.Perm.permMatrix ℂ σ.symm).mulVecLin _ = _
  rw [Matrix.mulVecLin_apply, Matrix.permMatrix_mulVec]
  ext x
  simp [Pi.single_apply, Equiv.symm_apply_eq]

lemma extPow_move (S S' : Set.powersetCard (Fin N) m) :
    ∃ g : GL (Fin N) ℂ, extPowRep N m g (extBasis N m S) = extBasis N m S' := by
  obtain ⟨σ, hσ⟩ := exists_perm_orderEmb S S'
  refine ⟨permGL σ, ?_⟩
  rw [extPowRep_apply_ιMulti_family, extBasis_apply]
  simp only [stdRep_permGL, hσ]
  rfl

/-- **Problem 3.19, exterior powers.**  For `m ≤ N` the exterior power `Λ^m V` of `V = ℂ^N` is an irreducible
representation of `GL_N(ℂ)`. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
theorem isIrredRep_extPowRep (hm : m ≤ N) : IsIrredRep (extPowRep N m) := by
  have : Nonempty (Set.powersetCard (Fin N) m) := Set.powersetCard.nonempty_iff.2 (by simpa using hm)
  refine isIrredRep_of_weight_family (extPowRep N m) (extBasis N m) (fun i => (extBasis N m).ne_zero i)
    (extBasis N m).span_eq
    (fun S g => ∏ x ∈ S.1, (g : Matrix (Fin N) (Fin N) ℂ) x x)
    {g | ∃ (t : Fin N → ℂ) (hx : ∀ i, t i ≠ 0), g = diagGL N t hx} ?_ ?_ ?_
  · rintro S g ⟨t, hx, rfl⟩
    rw [extPowRep_diag]
    simp only [diagGL_apply_diag]
  · intro S S' h
    obtain ⟨t, hx, ht⟩ := prod_update_two S S' h
    exact ⟨diagGL N t hx, ⟨t, hx, rfl⟩, by simpa only [diagGL_apply_diag] using ht⟩
  · intro U hU S S' hS
    obtain ⟨g, hg⟩ := extPow_move S S'
    rw [← hg]
    exact hU g _ hS

/-- `Λ^m V` is irreducible, in the form of Mathlib's `Representation.IsIrreducible`. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
theorem isIrreducible_extPowRep (hm : m ≤ N) : (extPowRep N m).IsIrreducible :=
  (isIrreducible_iff_isIrredRep _).2 (isIrredRep_extPowRep hm)

end Exterior

section Symmetric

open MvPolynomial

variable (N n : ℕ)

/-- The algebra endomorphism of `Sym V = ℂ[X_1, …, X_N]` induced by a matrix `M`: `X_j ↦ ∑_i M_{ij} X_i`
(the variable `X_j` stands for the basis vector `e_j`, and `M` sends `e_j` to its `j`-th column). -/
noncomputable def substAlg (M : Matrix (Fin N) (Fin N) ℂ) : MvPolynomial (Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N) ℂ :=
  aeval fun j => ∑ i, C (M i j) * X i

variable {N n}

lemma substAlg_X (M : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : substAlg N M (X j) = ∑ i, C (M i j) * X i :=
  aeval_X _ _

lemma substAlg_C (M : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) : substAlg N M (C a) = C a :=
  (substAlg N M).commutes a

lemma substAlg_one : substAlg N (1 : Matrix (Fin N) (Fin N) ℂ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [substAlg_X, Matrix.one_apply]

lemma substAlg_mul (M M' : Matrix (Fin N) (Fin N) ℂ) :
    substAlg N (M * M') = (substAlg N M).comp (substAlg N M') := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [substAlg_X, AlgHom.comp_apply, map_sum, map_mul, substAlg_C, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The representation of `GL_N(ℂ)` on the homogeneous polynomials of degree `n` in `N` variables, i.e. on the
symmetric power `S^n V` of `V = ℂ^N` (the variable `X_j` is the basis vector `e_j`). -/
noncomputable def symRep : Representation ℂ (GL (Fin N) ℂ) (homogeneousSubmodule (Fin N) ℂ n) where
  toFun g := (substAlg N (g : Matrix (Fin N) (Fin N) ℂ)).toLinearMap.restrict (fun f hf => by
    have h1 : (substAlg N (g : Matrix (Fin N) (Fin N) ℂ) f).IsHomogeneous (1 * n) :=
      IsHomogeneous.aeval hf _ (fun j => IsHomogeneous.sum _ _ _ fun i _ => by
        simpa using isHomogeneous_C_mul_X (R := ℂ) ((g : Matrix (Fin N) (Fin N) ℂ) i j) i)
    simpa using h1)
  map_one' := by
    ext f : 2
    simp [substAlg_one]
  map_mul' g h := by
    ext f : 2
    simp [substAlg_mul]

lemma symRep_coe (g : GL (Fin N) ℂ) (f : homogeneousSubmodule (Fin N) ℂ n) :
    ((symRep g f : homogeneousSubmodule (Fin N) ℂ n) : MvPolynomial (Fin N) ℂ) =
      substAlg N (g : Matrix (Fin N) (Fin N) ℂ) f := rfl

/-- Exponent vectors of degree `n`: the index set of the monomial basis of `S^n V`. -/
abbrev SymIdx (N n : ℕ) := {d : Fin N →₀ ℕ // d.degree = n}

/-- The monomial `X^d` as an element of the space of homogeneous polynomials of degree `n`. -/
noncomputable def symMon (d : SymIdx N n) : homogeneousSubmodule (Fin N) ℂ n :=
  ⟨monomial d.1 1, isHomogeneous_monomial 1 d.2⟩

lemma symMon_ne_zero (d : SymIdx N n) : symMon d ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp [symMon] at this

lemma monomial_eq_prod (e : Fin N →₀ ℕ) : monomial e (1 : ℂ) = ∏ i, X i ^ e i := by
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]

lemma substAlg_diag_X (t : Fin N → ℂ) (j : Fin N) :
    substAlg N (Matrix.diagonal t) (X j) = C (t j) * X j := by
  rw [substAlg_X, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

lemma substAlg_diag_monomial (t : Fin N → ℂ) (d : Fin N →₀ ℕ) :
    substAlg N (Matrix.diagonal t) (monomial d 1) = (∏ i, t i ^ d i) • monomial d 1 := by
  have e1 : substAlg N (Matrix.diagonal t) (∏ i, X i ^ d i) = ∏ i, (C (t i) * X i) ^ d i := by
    rw [map_prod]
    simp only [map_pow, substAlg_diag_X]
  have e2 : ∏ i, (C (t i) * X i) ^ d i = C (∏ i, t i ^ d i) * ∏ i, X i ^ d i := by
    simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [monomial_eq_prod, e1, e2, smul_eq_C_mul]

/-- The set of diagonal matrices. -/
def symT : Set (GL (Fin N) ℂ) := {g | ∃ (t : Fin N → ℂ) (hx : ∀ i, t i ≠ 0), g = diagGL N t hx}

/-- The weight (character of the torus) of the monomial `X^d`. -/
noncomputable def symχ (d : SymIdx N n) (g : GL (Fin N) ℂ) : ℂ :=
  ∏ i, ((g : Matrix (Fin N) (Fin N) ℂ) i i) ^ d.1 i

lemma symRep_diag_eig (d : SymIdx N n) (g : GL (Fin N) ℂ) (hg : g ∈ symT) :
    symRep g (symMon d) = symχ d g • symMon d := by
  obtain ⟨t, hx, rfl⟩ := hg
  apply Subtype.ext
  have hm : ((diagGL N t hx : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t := by
    simp [diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [symRep_coe, hm]
  simp only [symMon, symχ, hm, Matrix.diagonal_apply_eq]
  exact substAlg_diag_monomial t d.1

lemma symχ_sep (d d' : SymIdx N n) (h : d ≠ d') : ∃ g ∈ symT, symχ d g ≠ symχ d' g := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d.1 i ≠ d'.1 i := by
    by_contra hcon
    push Not at hcon
    exact h (Subtype.ext (Finsupp.ext hcon))
  have hx : ∀ j, (fun j : Fin N => if j = i then (2 : ℂ) else 1) j ≠ 0 := by
    intro j; dsimp only; split_ifs <;> norm_num
  refine ⟨diagGL N _ hx, ⟨_, hx, rfl⟩, ?_⟩
  have key : ∀ e : SymIdx N n, symχ e (diagGL N _ hx) = 2 ^ e.1 i := by
    intro e
    simp only [symχ, diagGL_apply_diag]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [key, key]
  intro hh
  have : (2 : ℕ) ^ d.1 i = 2 ^ d'.1 i := by exact_mod_cast hh
  exact hi (Nat.pow_right_injective le_rfl this)

lemma sum_symMon (f : homogeneousSubmodule (Fin N) ℂ n) :
    f = ∑ k ∈ f.1.support.subtype (fun d : Fin N →₀ ℕ => d.degree = n), f.1.coeff k.1 • symMon k := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, symMon, smul_monomial, smul_eq_mul, mul_one]
  rw [Finset.sum_subtype_eq_sum_filter (fun d => monomial d (f.1.coeff d)), Finset.filter_true_of_mem]
  · exact as_sum f.1
  · intro d hd
    rw [Finsupp.degree_eq_weight_one]
    exact f.2 (mem_support_iff.1 hd)

lemma span_symMon : Submodule.span ℂ (Set.range (symMon (N := N) (n := n))) = ⊤ := by
  have h1 : Submodule.map (homogeneousSubmodule (Fin N) ℂ n).subtype
      (Submodule.span ℂ (Set.range (symMon (N := N) (n := n)))) = homogeneousSubmodule (Fin N) ℂ n := by
    apply le_antisymm
    · rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
      exact (symMon d).2
    · intro f hf
      refine ⟨⟨f, hf⟩, ?_, rfl⟩
      rw [sum_symMon ⟨f, hf⟩]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact Submodule.map_injective_of_injective (Submodule.subtype_injective _)
    (h1.trans (Submodule.map_subtype_top _).symm)

/-- An invariant subspace containing `f` contains the monomial of every exponent occurring in `f`. -/
lemma symMon_mem_of_coeff (U : Submodule ℂ (homogeneousSubmodule (Fin N) ℂ n))
    (hU : ∀ g, ∀ w ∈ U, symRep g w ∈ U) (f : homogeneousSubmodule (Fin N) ℂ n) (hf : f ∈ U)
    (d : Fin N →₀ ℕ) (hd : f.1.coeff d ≠ 0) : ∃ h : d.degree = n, symMon ⟨d, h⟩ ∈ U := by
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact f.2 hd
  refine ⟨hdeg, ?_⟩
  refine mem_of_eigen_sum symRep symMon symχ symT (fun d g hg => symRep_diag_eig d g hg) symχ_sep U hU _
    _ (fun k => f.1.coeff k.1) ⟨d, hdeg⟩ rfl (Finset.mem_subtype.2 (mem_support_iff.2 hd)) hd ?_
  rw [← sum_symMon f]
  exact hf

/-- The elementary matrix `1 + E_{pq}` (`p ≠ q`), which sends `e_q` to `e_q + e_p` and fixes the other `e_j`. -/
noncomputable def elemGL (p q : Fin N) (hpq : p ≠ q) : GL (Fin N) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection p q (1 : ℂ)) (by
    rw [Matrix.det_transvection_of_ne p q hpq]; exact one_ne_zero)

lemma substAlg_elem_X_ne (p q : Fin N) {j : Fin N} (hj : j ≠ q) :
    substAlg N (Matrix.transvection p q (1 : ℂ)) (X j) = X j := by
  rw [substAlg_X, Finset.sum_eq_single j]
  · simp [Matrix.transvection, Ne.symm hj]
  · intro i _ hij
    simp [Matrix.transvection, hij, Ne.symm hj]
  · simp

lemma substAlg_elem_X_eq (p q : Fin N) (hpq : p ≠ q) :
    substAlg N (Matrix.transvection p q (1 : ℂ)) (X q) = X q + X p := by
  rw [substAlg_X, Finset.sum_eq_add_of_mem q p (Finset.mem_univ _) (Finset.mem_univ _) hpq.symm]
  · simp [Matrix.transvection, hpq]
  · intro i _ hi
    simp [Matrix.transvection, hi.1, Ne.symm hi.2]

lemma substAlg_elem_monomial (p q : Fin N) (hpq : p ≠ q) (e : Fin N →₀ ℕ) (he : e q = 0) (k : ℕ) :
    substAlg N (Matrix.transvection p q (1 : ℂ)) (monomial (e + Finsupp.single q (k + 1)) 1) =
      monomial e 1 * (X q + X p) ^ (k + 1) := by
  have h1 : substAlg N (Matrix.transvection p q (1 : ℂ)) (monomial e 1) = monomial e 1 := by
    rw [monomial_eq_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = q
    · subst hi; simp [he]
    · rw [map_pow, substAlg_elem_X_ne p q hi]
  rw [monomial_add_single, map_mul, map_pow, h1, substAlg_elem_X_eq p q hpq]

lemma coeff_term (p q : Fin N) (m j c : ℕ) (d : Fin N →₀ ℕ) :
    (X q ^ m * X p ^ j * (c : MvPolynomial (Fin N) ℂ)).coeff d =
      if Finsupp.single q m + Finsupp.single p j = d then (c : ℂ) else 0 := by
  have : X q ^ m * X p ^ j * (c : MvPolynomial (Fin N) ℂ) =
      monomial (Finsupp.single q m + Finsupp.single p j) (c : ℂ) := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, ← map_natCast (C : ℂ →+* MvPolynomial (Fin N) ℂ) c, C_apply,
      monomial_mul_monomial, monomial_mul_monomial]
    simp
  rw [this, coeff_monomial]

lemma coeff_pow_X_add_X (p q : Fin N) (hpq : p ≠ q) (k : ℕ) :
    ((X q + X p : MvPolynomial (Fin N) ℂ) ^ (k + 1)).coeff (Finsupp.single p 1 + Finsupp.single q k) =
      (k : ℂ) + 1 := by
  classical
  rw [add_pow, MvPolynomial.coeff_sum, Finset.sum_eq_single k]
  · have hk : k + 1 - k = 1 := by omega
    rw [coeff_term, hk]
    split_ifs with h
    · rw [Nat.choose_succ_self_right]; push_cast; ring
    · exact absurd (add_comm _ _) h
  · intro m _ hm
    rw [coeff_term]
    split_ifs with h
    · exfalso
      have := congrArg (fun f => f q) h
      simp [Ne.symm hpq] at this
      exact hm this
    · rfl
  · intro hk
    exfalso
    exact hk (Finset.mem_range.2 (by omega))

/-- Moving one unit of exponent from `q` to `p` stays inside an invariant subspace. -/
lemma symMon_move (U : Submodule ℂ (homogeneousSubmodule (Fin N) ℂ n))
    (hU : ∀ g, ∀ w ∈ U, symRep g w ∈ U) (d d' : SymIdx N n) (p q : Fin N) (hpq : p ≠ q)
    (hrel : d'.1 + Finsupp.single q 1 = d.1 + Finsupp.single p 1) (hd : symMon d ∈ U) :
    symMon d' ∈ U := by
  have hq : d.1 q = d'.1 q + 1 := by
    have := congrArg (fun f => f q) hrel
    simp [Finsupp.single_apply, Ne.symm hpq] at this
    omega
  obtain ⟨k, hk⟩ : ∃ k, d.1 q = k + 1 := ⟨d'.1 q, hq⟩
  set e := d.1.erase q with he
  have heq : e q = 0 := Finsupp.erase_same
  have hd1 : d.1 = e + Finsupp.single q (k + 1) := by
    ext i
    by_cases hi : i = q
    · subst hi; simp [he, hk]
    · simp [he, Finsupp.erase_ne hi, Finsupp.single_apply, Ne.symm hi]
  have hd2 : d'.1 = e + (Finsupp.single p 1 + Finsupp.single q k) := by
    ext i
    have := congrArg (fun f => f i) hrel
    simp only [Finsupp.add_apply, Finsupp.single_apply] at this
    simp only [he, Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
    split_ifs at * <;> subst_vars <;> omega
  have hf : symRep (elemGL p q hpq) (symMon d) ∈ U := hU _ _ hd
  have hcoef : (symRep (elemGL p q hpq) (symMon d)).1.coeff d'.1 ≠ 0 := by
    rw [symRep_coe]
    show (substAlg N (Matrix.transvection p q (1 : ℂ)) (monomial d.1 1)).coeff _ ≠ 0
    rw [hd1, substAlg_elem_monomial p q hpq e heq k, hd2, coeff_monomial_mul, coeff_pow_X_add_X p q hpq k]
    simp only [one_mul]
    exact_mod_cast Nat.succ_ne_zero k
  obtain ⟨h, hmem⟩ := symMon_mem_of_coeff U hU _ hf d'.1 hcoef
  exact hmem

/-- One elementary move between exponent vectors of degree `n`. -/
def SymStep (d d' : SymIdx N n) : Prop :=
  ∃ p q : Fin N, p ≠ q ∧ d'.1 + Finsupp.single q 1 = d.1 + Finsupp.single p 1

lemma SymStep.symm {d d' : SymIdx N n} (h : SymStep d d') : SymStep d' d := by
  obtain ⟨p, q, hpq, hrel⟩ := h
  exact ⟨q, p, hpq.symm, hrel.symm⟩

lemma symMon_mem_of_reach (U : Submodule ℂ (homogeneousSubmodule (Fin N) ℂ n))
    (hU : ∀ g, ∀ w ∈ U, symRep g w ∈ U) {d d' : SymIdx N n}
    (h : Relation.ReflTransGen SymStep d d') (hd : symMon d ∈ U) : symMon d' ∈ U := by
  induction h with
  | refl => exact hd
  | tail _ hstep ih =>
    obtain ⟨p, q, hpq, hrel⟩ := hstep
    exact symMon_move U hU _ _ p q hpq hrel ih

lemma degree_eq_sum_apply (d : Fin N →₀ ℕ) : d.degree = ∑ i, d i := Finsupp.degree_eq_sum d

lemma exists_step_up (p0 : Fin N) (d : SymIdx N n) (hd : d.1 p0 < n) :
    ∃ d' : SymIdx N n, SymStep d d' ∧ d'.1 p0 = d.1 p0 + 1 := by
  classical
  obtain ⟨q, hq, hq1⟩ : ∃ q, q ≠ p0 ∧ 1 ≤ d.1 q := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, d.1 i = d.1 p0 := by
      rw [Finset.sum_eq_single p0 (fun i _ hi => by have := hcon i hi; omega) (by simp)]
    have h2 := d.2
    rw [degree_eq_sum_apply, this] at h2
    omega
  have hrel : (d.1 - Finsupp.single q 1 + Finsupp.single p0 1) + Finsupp.single q 1 =
      d.1 + Finsupp.single p0 1 := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> subst_vars <;> omega
  have hdeg : (d.1 - Finsupp.single q 1 + Finsupp.single p0 1).degree = n := by
    have h1 := congrArg Finsupp.degree hrel
    rw [map_add (Finsupp.degree) _ (Finsupp.single q 1), map_add Finsupp.degree d.1,
      Finsupp.degree_single, Finsupp.degree_single] at h1
    have := d.2
    omega
  refine ⟨⟨_, hdeg⟩, ⟨p0, q, hq.symm, hrel⟩, ?_⟩
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  simp [hq]

lemma reach_symm {d d' : SymIdx N n} (h : Relation.ReflTransGen SymStep d d') :
    Relation.ReflTransGen SymStep d' d := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact Relation.ReflTransGen.head hs.symm ih

lemma reach_pivot (p0 : Fin N) (d : SymIdx N n) :
    Relation.ReflTransGen SymStep d ⟨Finsupp.single p0 n, by simp⟩ := by
  classical
  suffices h : ∀ r, ∀ d : SymIdx N n, n - d.1 p0 = r →
      Relation.ReflTransGen SymStep d ⟨Finsupp.single p0 n, by simp⟩ from h _ d rfl
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro d hr
  have hle : d.1 p0 ≤ n := by
    have := Finset.single_le_sum (f := fun i => d.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p0)
    have h2 := d.2
    rw [degree_eq_sum_apply] at h2
    simpa [h2] using this
  by_cases heq : d.1 p0 = n
  · have : d = ⟨Finsupp.single p0 n, by simp⟩ := by
      apply Subtype.ext
      ext i
      by_cases hi : i = p0
      · subst hi; simp [heq]
      · have h2 := d.2
        rw [degree_eq_sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p0), heq] at h2
        have h3 : ∑ j ∈ Finset.univ.erase p0, d.1 j = 0 := by omega
        have := (Finset.sum_eq_zero_iff.1 h3) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
        simp [this, Finsupp.single_apply, hi]
    rw [this]
  · obtain ⟨d', hstep, hd'⟩ := exists_step_up p0 d (lt_of_le_of_ne hle heq)
    exact Relation.ReflTransGen.head hstep (ih (n - d'.1 p0) (by omega) d' rfl)

/-- **Problem 3.19, symmetric powers.**  For `N ≥ 1`, the space of homogeneous polynomials of degree `n` in `N`
variables, with `GL_N(ℂ)` acting by the linear substitution `X_j ↦ ∑_i g_{ij} X_i` (that is, `S^n V` for
`V = ℂ^N` with the standard action on the basis vectors `X_j = e_j`), is irreducible. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
theorem isIrredRep_symRep [NeZero N] : IsIrredRep (symRep (N := N) (n := n)) := by
  have : Nonempty (SymIdx N n) := ⟨⟨Finsupp.single 0 n, by simp⟩⟩
  refine isIrredRep_of_weight_family symRep symMon symMon_ne_zero span_symMon symχ symT
    (fun d g hg => symRep_diag_eig d g hg) symχ_sep ?_
  intro U hU d d' hd
  have h1 := reach_pivot 0 d
  have h2 := reach_pivot 0 d'
  have h3 : Relation.ReflTransGen SymStep d d' :=
    h1.trans (reach_symm h2)
  exact symMon_mem_of_reach U hU h3 hd

/-- `S^n V` is irreducible, in the form of Mathlib's `Representation.IsIrreducible`. -/
@[kb "etingof2011" "Problem 3.19, p. 43"]
theorem isIrreducible_symRep [NeZero N] : (symRep (N := N) (n := n)).IsIrreducible :=
  (isIrreducible_iff_isIrredRep _).2 isIrredRep_symRep

end Symmetric

end UndergradKB.RepresentationTheory
