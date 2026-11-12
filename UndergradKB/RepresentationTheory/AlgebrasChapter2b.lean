import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.AdjoinRoot
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.JordanHolderFitting
import UndergradKB.RepresentationTheory.AlgebrasChapter2
import UndergradKB.RepresentationTheory.AlgebrasMisc
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Dixmier's lemma (Etingof et al., Problem 1.23)

For a simple module `V` over an algebra over an algebraically closed field `k` of cardinality larger than the
dimension of `V`, every endomorphism is a scalar.  In particular this holds for countable-dimensional irreducible
complex representations.  The proof shows that a non-scalar endomorphism `φ` is transcendental over `k` inside the
division algebra `End_A V`, so the elements `(φ - λ)⁻¹` are linearly independent, and evaluating at a fixed nonzero
vector gives `|k|` independent vectors in `V`.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Module Polynomial

section Dixmier

/-- In a division algebra over an algebraically closed field, an element that is not a scalar is a root of no
nonzero polynomial. -/
theorem aeval_ne_zero_of_not_scalar {k D : Type*} [Field k] [IsAlgClosed k] [DivisionRing D] [Algebra k D]
    (φ : D) (hφ : ∀ c : k, φ ≠ algebraMap k D c) :
    ∀ (n : ℕ) (p : k[X]), p.natDegree = n → p ≠ 0 → aeval φ p ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp
    by_cases hdeg : p.degree = 0
    · have ha : p.coeff 0 ≠ 0 := by
        intro h
        exact hp (by rw [Polynomial.eq_C_of_degree_eq_zero hdeg, h, map_zero])
      rw [Polynomial.eq_C_of_degree_eq_zero hdeg, aeval_C]
      exact fun h => ha ((algebraMap k D).injective (by rw [h, map_zero]))
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (p := p) (a := r)).2 hr
      have hpos : 0 < p.natDegree :=
        Nat.pos_of_ne_zero fun h => hdeg (by rw [degree_eq_natDegree hp, h]; rfl)
      have hq0 : p /ₘ (X - C r) ≠ 0 := by
        intro h
        rw [h, mul_zero] at hfac
        exact hp hfac.symm
      have hlt : (p /ₘ (X - C r)).natDegree < n := by
        rw [Polynomial.natDegree_divByMonic p (monic_X_sub_C r), natDegree_X_sub_C]
        omega
      have hp' : aeval φ p = (φ - algebraMap k D r) * aeval φ (p /ₘ (X - C r)) := by
        conv_lhs => rw [← hfac]
        simp
      rw [hp']
      exact mul_ne_zero (sub_ne_zero.2 (hφ r)) (ih _ hlt _ rfl hq0)

variable {k : Type*} {A : Type*} {V : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V] [IsSimpleModule A V]

/-- For a non-scalar endomorphism `φ` of a simple module over an algebraically closed field `k`, evaluating
the inverses `(φ - λ)⁻¹` (`λ ∈ k`) at a nonzero vector gives a `k`-linearly independent family of vectors indexed
by `k`. -/
theorem exists_linearIndependent_of_not_scalar [IsAlgClosed k] (φ : Module.End A V)
    (hφ : ∀ c : k, φ ≠ algebraMap k (Module.End A V) c) (v : V) (hv : v ≠ 0) :
    ∃ ψ : k → V, LinearIndependent k ψ := by
  classical
  refine ⟨fun c => (φ - algebraMap k (Module.End A V) c)⁻¹ v, ?_⟩
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hne : ∀ c : k, φ - algebraMap k (Module.End A V) c ≠ 0 := fun c => sub_ne_zero.2 (hφ c)
  set e : Module.End A V := ∑ j ∈ s, g j • (φ - algebraMap k (Module.End A V) j)⁻¹ with he_def
  have he : e v = 0 := by
    simp only [he_def, LinearMap.sum_apply, LinearMap.smul_apply]
    exact hg
  have he0 : e = 0 := by
    by_contra h
    apply hv
    calc v = (e⁻¹ * e) v := by rw [inv_mul_cancel₀ h]; rfl
      _ = e⁻¹ (e v) := rfl
      _ = 0 := by rw [he, map_zero]
  let PP : k[X] := ∏ j ∈ s, (X - C j)
  let p : k[X] := ∑ j ∈ s, C (g j) * ∏ l ∈ s.erase j, (X - C l)
  have hinv : ∀ j ∈ s, (φ - algebraMap k (Module.End A V) j)⁻¹ * aeval φ PP =
      aeval φ (∏ l ∈ s.erase j, (X - C l)) := by
    intro j hj
    simp only [PP]
    rw [← Finset.mul_prod_erase s (fun l => X - C l) hj, map_mul, ← mul_assoc]
    simp [inv_mul_cancel₀ (hne j)]
  have hp : aeval φ p = e * aeval φ PP := by
    simp only [p, he_def, Finset.sum_mul, map_sum, map_mul, aeval_C]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_mul_assoc, hinv j hj, Algebra.smul_def]
  have hp0 : p = 0 := by
    by_contra h
    exact aeval_ne_zero_of_not_scalar φ hφ _ p rfl h (by rw [hp, he0, zero_mul])
  have hev := congrArg (Polynomial.eval i) hp0
  simp only [p, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_zero] at hev
  rw [Finset.sum_eq_single i] at hev
  · rcases mul_eq_zero.1 hev with h | h
    · exact h
    · exfalso
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨l, hl, hl0⟩ := h
      exact (Finset.ne_of_mem_erase hl) (sub_eq_zero.1 hl0).symm
  · intro j hj hji
    have : i ∈ s.erase j := Finset.mem_erase.2 ⟨fun h => hji h.symm, hi⟩
    rw [Finset.prod_eq_zero this (by simp), mul_zero]
  · intro h
    exact (h hi).elim

/-- **Etingof et al., Problem 1.23 (Dixmier's lemma)**: if `V` is an irreducible representation of a complex
algebra `A` of countable dimension over `ℂ`, then every `A`-endomorphism of `V` is a scalar. -/
@[kb "etingof2011" "Problem 1.23, p. 10"]
theorem exists_eq_algebraMap_of_rank_le_aleph0 {A : Type*} {V : Type u} [Ring A] [Algebra ℂ A]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V] [IsSimpleModule A V]
    (hV : Module.rank ℂ V ≤ Cardinal.aleph0) (φ : Module.End A V) :
    ∃ c : ℂ, φ = algebraMap ℂ (Module.End A V) c := by
  by_contra h
  simp only [not_exists] at h
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨ψ, hψ⟩ := exists_linearIndependent_of_not_scalar φ h v hv
  have h1 : Cardinal.continuum ≤ Module.rank ℂ V := by
    have := hψ.cardinal_lift_le_rank
    rw [Cardinal.mk_complex] at this
    simpa using this
  exact absurd (h1.trans hV) (not_le.2 Cardinal.aleph0_lt_continuum)

end Dixmier

section Uniserial

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {t : R}

/-- Over a principal ideal domain, the submodules of `R / (tⁿ)` (`t` prime) form a chain. -/
theorem submodule_quotient_pow_total (ht : Prime t) (n : ℕ)
    (N₁ N₂ : Submodule R (R ⧸ Ideal.span {t ^ n})) : N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  have key : ∀ N : Submodule R (R ⧸ Ideal.span {t ^ n}),
      ∃ i ≤ n, N.comap (Ideal.span {t ^ n}).mkQ = Ideal.span {t ^ i} := by
    intro N
    obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (N.comap (Ideal.span {t ^ n}).mkQ)).principal
    have hmem : t ^ n ∈ N.comap (Ideal.span {t ^ n}).mkQ := by
      rw [Submodule.mem_comap, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self _)]
      exact N.zero_mem
    rw [hg] at hmem
    obtain ⟨i, hi, hass⟩ := (dvd_prime_pow ht n).1 (Ideal.mem_span_singleton.1 hmem)
    exact ⟨i, hi, hg.trans (Ideal.span_singleton_eq_span_singleton.2 hass)⟩
  obtain ⟨i, -, hi⟩ := key N₁
  obtain ⟨j, -, hj⟩ := key N₂
  have hsurj : Function.Surjective (Ideal.span {t ^ n}).mkQ := Submodule.mkQ_surjective _
  rcases le_total i j with h | h
  · right
    rw [← Submodule.comap_le_comap_iff_of_surjective hsurj, hi, hj]
    exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t h)
  · left
    rw [← Submodule.comap_le_comap_iff_of_surjective hsurj, hi, hj]
    exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t h)

/-- For a prime `t` of a principal ideal domain and `n ≥ 1`, the module `R / (tⁿ)` is indecomposable. -/
theorem isIndecomposableModule_quotient_pow (ht : Prime t) {n : ℕ} (hn : 1 ≤ n) :
    IsIndecomposableModule R (R ⧸ Ideal.span {t ^ n}) := by
  refine ⟨?_, fun p q hpq => ?_⟩
  · refine Ideal.Quotient.nontrivial_iff.2 ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ht.not_isUnit ((isUnit_pow_iff (show n ≠ 0 by omega)).1 h)
  · rcases submodule_quotient_pow_total ht n p q with h | h
    · exact Or.inl (hpq.disjoint.eq_bot_of_le h)
    · exact Or.inr (hpq.disjoint.symm.eq_bot_of_le h)

/-- For a prime `t` of a principal ideal domain, `R / (t)` is a simple module. -/
theorem isSimpleModule_quotient_prime (ht : Prime t) : IsSimpleModule R (R ⧸ Ideal.span {t}) :=
  isSimpleModule_iff_isCoatom.2
    (Ideal.isMaximal_def.1 (PrincipalIdealRing.isMaximal_of_irreducible ht.irreducible))

omit [IsPrincipalIdealRing R] in
/-- For a prime `t` of a principal ideal domain and `n ≥ 2`, the module `R / (tⁿ)` is not simple: the
multiples of `t` form a proper nonzero submodule. -/
theorem not_isSimpleModule_quotient_pow (ht : Prime t) {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSimpleModule R (R ⧸ Ideal.span {t ^ n}) := by
  intro hS
  let π := (Ideal.span {t ^ n}).mkQ
  let N : Submodule R (R ⧸ Ideal.span {t ^ n}) := Submodule.span R {π t}
  rcases eq_bot_or_eq_top N with h | h
  · have h1 : π t ∈ N := Submodule.mem_span_singleton_self _
    rw [h, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton] at h1
    have := (pow_dvd_pow_iff ht.ne_zero ht.not_isUnit).1 (by simpa using h1 : t ^ n ∣ t ^ 1)
    omega
  · have h1 : π 1 ∈ N := by rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
    rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Ideal.mem_span_singleton] at hc
    have hdt : t ∣ c • t - 1 := by
      refine dvd_trans (dvd_pow_self t (show n ≠ 0 by omega)) ?_
      simpa using hc
    have : t ∣ 1 := by
      have h2 : t ∣ c • t := by rw [smul_eq_mul]; exact dvd_mul_left t c
      have := dvd_sub h2 hdt
      simpa using this
    exact ht.not_isUnit (isUnit_of_dvd_one this)

end Uniserial

section KX

variable (k : Type*) [Field k]

/-- The Jordan-block module `V_{λ,n} = k[x] / (x - λ)ⁿ` over the polynomial algebra `k[x]` (a vector space of
dimension `n` on which `x` acts by a single Jordan block of eigenvalue `λ`). -/
abbrev JordanBlockModule (lam : k) (n : ℕ) : Type _ := k[X] ⧸ Ideal.span {(X - C lam) ^ n}

variable {k}

/-- **Etingof et al., Example 1.19**: the Jordan-block module `V_{λ,n}` (`n ≥ 1`) is indecomposable. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem isIndecomposableModule_jordanBlock (lam : k) {n : ℕ} (hn : 1 ≤ n) :
    IsIndecomposableModule k[X] (JordanBlockModule k lam n) :=
  isIndecomposableModule_quotient_pow (prime_X_sub_C lam) hn

/-- **Etingof et al., Example 1.19**: for `n ≥ 2` the Jordan-block module `V_{λ,n}` is not irreducible, so an
indecomposable module need not be irreducible. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem not_isSimpleModule_jordanBlock (lam : k) {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsSimpleModule k[X] (JordanBlockModule k lam n) :=
  not_isSimpleModule_quotient_pow (prime_X_sub_C lam) hn

/-- **Etingof et al., Example 1.19**: the one-dimensional modules `V_λ = V_{λ,1}` are irreducible. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem isSimpleModule_jordanBlock_one (lam : k) : IsSimpleModule k[X] (JordanBlockModule k lam 1) := by
  have := isSimpleModule_quotient_prime (prime_X_sub_C lam)
  let e : (k[X] ⧸ Ideal.span {X - C lam}) ≃ₗ[k[X]] JordanBlockModule k lam 1 :=
    Submodule.quotEquivOfEq _ _ (by rw [pow_one])
  exact IsSimpleModule.congr e.symm

/-- The Jordan-block module `V_{λ,n}` has dimension `n` over `k`. -/
theorem finrank_jordanBlock (lam : k) (n : ℕ) : Module.finrank k (JordanBlockModule k lam n) = n := by
  show Module.finrank k (k[X] ⧸ Ideal.span {(X - C lam) ^ n}) = n
  rw [finrank_quotient_span_eq_natDegree, natDegree_pow, natDegree_X_sub_C, mul_one]

variable {V : Type*} [AddCommGroup V] [Module k V] [Module k[X] V] [IsScalarTower k k[X] V]

/-- **Etingof et al., Example 1.19**: over an algebraically closed field, every finite-dimensional irreducible
`k[x]`-module is isomorphic to a one-dimensional module `V_λ`. -/
@[kb "etingof2011" "Example 1.19, p. 9"]
theorem exists_linearEquiv_jordanBlock_one_of_isSimpleModule [IsAlgClosed k] [IsSimpleModule k[X] V]
    [FiniteDimensional k V] : ∃ lam : k, Nonempty (V ≃ₗ[k[X]] JordanBlockModule k lam 1) := by
  have : Nontrivial V := IsSimpleModule.nontrivial k[X] V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := k[X]) (V := V) k).2
    (Module.toModuleEnd k[X] V (X : k[X]))
  have hX : (X : k[X]) • v = c • v := by
    have := congrArg (fun φ : Module.End k[X] V => φ v) hc
    simpa using this.symm
  let f : k[X] →ₗ[k[X]] V := LinearMap.toSpanSingleton k[X] V v
  have hf : ∀ r : k[X], f r = r • v := fun r => rfl
  have hne : f ≠ 0 := fun h => hv (by simpa [hf] using congrArg (fun g : k[X] →ₗ[k[X]] V => g 1) h)
  have hsurj : Function.Surjective f := LinearMap.surjective_of_ne_zero hne
  have hle : Ideal.span {X - C c} ≤ LinearMap.ker f := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hf, sub_smul, hX, C_eq_algebraMap,
      algebraMap_smul, sub_self]
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h
    have : (1 : k[X]) ∈ LinearMap.ker f := by rw [h]; trivial
    rw [LinearMap.mem_ker, hf, one_smul] at this
    exact hv this
  have heq : Ideal.span {X - C c} = LinearMap.ker f :=
    (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C c)).eq_of_le hker hle
  have heq' : Ideal.span {(X - C c) ^ 1} = LinearMap.ker f := by rw [pow_one]; exact heq
  let e1 : JordanBlockModule k c 1 ≃ₗ[k[X]] (k[X] ⧸ LinearMap.ker f) := Submodule.quotEquivOfEq _ _ heq'
  let e2 : (k[X] ⧸ LinearMap.ker f) ≃ₗ[k[X]] V := f.quotKerEquivOfSurjective hsurj
  exact ⟨c, ⟨(e1.trans e2).symm⟩⟩

end KX

section Copies

variable {k A V : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module A V] [Module k V]
  [IsScalarTower k A V] {ι : Type*}

/-- The map `(κ → V) → (ι → V)` given by a scalar matrix: `y ↦ (j ↦ ∑ₗ m j l • y l)`.  This is how the
`r`-fold copy of `V` is embedded in the `n`-fold copy by a matrix of size `n × r`. -/
def embedMatrix (k : Type*) (A : Type*) (V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V]
    [Module A V] [Module k V] [IsScalarTower k A V] {ι κ : Type*} [Fintype κ] (m : Matrix ι κ k) :
    (κ → V) →ₗ[A] (ι → V) where
  toFun y j := ∑ l, m j l • y l
  map_add' y z := by
    funext j
    simp [Finset.sum_add_distrib]
  map_smul' a y := by
    funext j
    simp [Finset.smul_sum, smul_comm a (m j _)]

theorem embedMatrix_apply {κ : Type*} [Fintype κ] (m : Matrix ι κ k) (y : κ → V) (j : ι) :
    embedMatrix k A V m y j = ∑ l, m j l • y l := rfl

/-- The scalar vectors `c` in `kⁿ` such that `c ⊗ v` lies in a submodule `U` of `Vⁿ`, for every `v ∈ V`. -/
def copiesScalar (U : Submodule A (ι → V)) : Submodule k (ι → k) where
  carrier := {c | ∀ v : V, (fun j => c j • v) ∈ U}
  add_mem' := by
    intro c d hc hd v
    have := U.add_mem (hc v) (hd v)
    convert this using 1
    funext j
    simp [add_smul]
  zero_mem' := by
    intro v
    convert U.zero_mem using 1
    funext j
    simp
  smul_mem' := by
    intro t c hc v
    have := U.smul_mem (algebraMap k A t) (hc v)
    convert this using 1
    funext j
    simp [mul_smul, algebraMap_smul]

theorem mem_copiesScalar {U : Submodule A (ι → V)} {c : ι → k} :
    c ∈ copiesScalar U ↔ ∀ v : V, (fun j => c j • v) ∈ U := Iff.rfl

variable [IsAlgClosed k] [IsSimpleModule A V] [FiniteDimensional k V]

open Module in
/-- Every element of a submodule `U` of `Vⁿ` (with `V` simple) is a finite sum of pure tensors `c ⊗ b` with
`c ∈ copiesScalar U`. -/
theorem exists_sum_of_mem_copies [Finite ι] (U : Submodule A (ι → V)) {u : ι → V} (hu : u ∈ U) :
    ∃ (d : ℕ) (c : Fin d → ι → k) (b : Fin d → V), (∀ l, c l ∈ copiesScalar U) ∧
      u = ∑ l, fun j => c l j • b l := by
  classical
  let T : Submodule k V := Submodule.span k (Set.range u)
  let bT : Module.Basis (Fin (finrank k T)) k T := Module.finBasis k T
  let b : Fin (finrank k T) → V := fun l => (bT l : V)
  have hb : LinearIndependent k b := bT.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  let c : Fin (finrank k T) → ι → k := fun l j => bT.repr ⟨u j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  have hexp : ∀ j, u j = ∑ l, c l j • b l := by
    intro j
    have hx := bT.sum_repr ⟨u j, Submodule.subset_span ⟨j, rfl⟩⟩
    have hx' := congrArg Subtype.val hx
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    exact hx'.symm
  refine ⟨finrank k T, c, b, fun l v => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_smul_eq_of_linearIndependent (k := k) (A := A) b hb
      (fun l' => if l' = l then v else 0)
    have : (fun j => c l j • v) = a • u := by
      funext j
      rw [Pi.smul_apply, hexp j, Finset.smul_sum]
      simp only [smul_comm a (c _ j)]
      simp [ha]
    rw [this]
    exact U.smul_mem a hu
  · funext j
    rw [Finset.sum_apply]
    exact hexp j

open Module in
/-- **Etingof et al., Proposition 2.2 / Remark 2.3 (one isotypic block)**: over an algebraically closed field, a
submodule of the `n`-fold direct sum `Vⁿ` of a finite-dimensional simple module `V` is the image of the `r`-fold
direct sum `Vʳ` under an injective map given by an `n × r` scalar matrix of rank `r`. -/
@[kb "etingof2011" "Remark 2.3, p. 23"]
theorem exists_matrix_eq_range_embedMatrix [Fintype ι] (U : Submodule A (ι → V)) :
    ∃ (r : ℕ) (m : Matrix ι (Fin r) k), m.rank = r ∧ Function.Injective (embedMatrix k A V m) ∧
      U = LinearMap.range (embedMatrix k A V m) := by
  classical
  let S : Submodule k (ι → k) := copiesScalar U
  let r := finrank k S
  let bS : Module.Basis (Fin r) k S := Module.finBasis k S
  let m : Matrix ι (Fin r) k := fun j l => (bS l : ι → k) j
  have hrank : m.rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have h1 := Submodule.map_span S.subtype (Set.range bS)
    rw [bS.span_eq, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
    have h2 : Set.range m.col = Set.range (S.subtype ∘ bS) := rfl
    rw [h2, ← h1]
  refine ⟨r, m, hrank, ?_, ?_⟩
  · -- injectivity
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hker : LinearMap.ker m.mulVecLin = ⊥ := by
      have h := LinearMap.finrank_range_add_finrank_ker m.mulVecLin
      have h' : finrank k (LinearMap.range m.mulVecLin) = r := hrank
      simp only [finrank_fin_fun] at h
      rw [← Submodule.finrank_eq_zero (R := k)]
      omega
    by_contra hy0
    obtain ⟨l0, hl0⟩ : ∃ l0, y l0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (funext h)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hl0
    have hmv : m.mulVecLin (fun l => φ (y l)) = 0 := by
      funext j
      have := congrArg φ (congrFun hy j)
      simp only [embedMatrix_apply, map_sum, map_smul, smul_eq_mul] at this
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
    have := (LinearMap.ker_eq_bot.1 hker) (hmv.trans (map_zero _).symm)
    have h3 := congrFun this l0
    simp [hφ] at h3
  · have key : ∀ (s : ι → k) (hs : s ∈ S) (v : V),
        (fun j => s j • v) ∈ LinearMap.range (embedMatrix k A V m) := by
      intro s hs v
      refine ⟨fun l => (bS.repr ⟨s, hs⟩ l) • v, ?_⟩
      funext j
      have hs' := congrFun (congrArg Subtype.val (bS.sum_repr ⟨s, hs⟩)) j
      simp only [embedMatrix_apply, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs'
      rw [← hs']
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    apply le_antisymm
    · intro u hu
      obtain ⟨d, c, b, hc, rfl⟩ := exists_sum_of_mem_copies (k := k) U hu
      exact Submodule.sum_mem _ fun l _ => key (c l) (hc l) (b l)
    · rintro _ ⟨y, rfl⟩
      have : embedMatrix k A V m y = ∑ l, fun j => m j l • y l := by
        funext j
        simp [embedMatrix_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => (bS l).2 (y l)

end Copies

section SubmoduleSum

variable {k A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

/-- The embedding of `⊕ᵢ rᵢ Vᵢ` into `⊕ᵢ nᵢ Vᵢ` by a family of scalar matrices `mᵢ` of size `nᵢ × rᵢ`. -/
def embedPi (k A : Type*) [Field k] [Ring A] [Algebra k A] (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)] [∀ i, IsScalarTower k A (V i)] {n r : ι → ℕ} (m : ∀ i, Matrix (Fin (n i)) (Fin (r i)) k) :
    (∀ i, Fin (r i) → V i) →ₗ[A] (∀ i, Fin (n i) → V i) :=
  LinearMap.pi fun i => embedMatrix k A (V i) (m i) ∘ₗ LinearMap.proj i

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)] in
theorem embedPi_apply {n r : ι → ℕ} (m : ∀ i, Matrix (Fin (n i)) (Fin (r i)) k)
    (y : ∀ i, Fin (r i) → V i) (i : ι) : embedPi k A V m y i = embedMatrix k A (V i) (m i) (y i) := rfl

/-- **Etingof et al., Proposition 2.2 and Remark 2.3**: let `V₁, …, Vₙ` be pairwise non-isomorphic
finite-dimensional simple modules over an algebraically closed field.  Every submodule of `⊕ᵢ nᵢ Vᵢ` is the image of
`⊕ᵢ rᵢ Vᵢ` under an injective map given by scalar matrices `mᵢ` of size `nᵢ × rᵢ` and full rank `rᵢ`; in
particular it is isomorphic to `⊕ᵢ rᵢ Vᵢ` with `rᵢ ≤ nᵢ`. -/
@[kb "etingof2011" "Proposition 2.2, p. 23"]
theorem exists_matrices_eq_range_embedPi (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (n : ι → ℕ)
    (U : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ (r : ι → ℕ) (m : ∀ i, Matrix (Fin (n i)) (Fin (r i)) k), (∀ i, (m i).rank = r i) ∧
      Function.Injective (embedPi k A V m) ∧ U = LinearMap.range (embedPi k A V m) := by
  classical
  let Ui : ∀ i, Submodule A (Fin (n i) → V i) := fun i =>
    U.comap (LinearMap.single A (fun i => Fin (n i) → V i) i)
  -- projections onto the isotypic blocks stay inside `U`
  have hproj : ∀ x ∈ U, ∀ i, (Pi.single i (x i) : ∀ i, Fin (n i) → V i) ∈ U := by
    intro x hx i
    obtain ⟨a, ha⟩ := density_pi_surjective (k := k) (A := A) hV
      (Pi.single i (LinearMap.id : Module.End k (V i)))
    have : a • x = Pi.single i (x i) := by
      funext j l
      have hj := congrFun ha j
      simp only [] at hj
      have : a • x j l = (Algebra.lsmul k k (V j) a : Module.End k (V j)) (x j l) := rfl
      rw [Pi.smul_apply, Pi.smul_apply, this, hj]
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [← this]
    exact U.smul_mem a hx
  choose r m hrank hinj hU using fun i =>
    exists_matrix_eq_range_embedMatrix (k := k) (A := A) (V := V i) (Ui i)
  refine ⟨r, m, hrank, ?_, ?_⟩
  · intro y z hyz
    funext i
    apply hinj i
    exact congrFun hyz i
  · apply le_antisymm
    · intro x hx
      have hxi : ∀ i, x i ∈ LinearMap.range (embedMatrix k A (V i) (m i)) := by
        intro i
        rw [← hU i]
        exact hproj x hx i
      choose y hy using hxi
      exact ⟨y, funext fun i => hy i⟩
    · rintro _ ⟨y, rfl⟩
      have hmem : ∀ i, (Pi.single i (embedPi k A V m y i) : ∀ i, Fin (n i) → V i) ∈ U := by
        intro i
        have : embedPi k A V m y i ∈ Ui i := by
          rw [hU i]
          exact ⟨y i, rfl⟩
        exact this
      have : embedPi k A V m y = ∑ i, Pi.single i (embedPi k A V m y i) :=
        (Finset.univ_sum_single _).symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => hmem i

variable (k) in
include k in
/-- **Etingof et al., Proposition 2.2**: every submodule of `⊕ᵢ nᵢ Vᵢ` (with the `Vᵢ` pairwise non-isomorphic
finite-dimensional simple modules over an algebraically closed field) is isomorphic to `⊕ᵢ rᵢ Vᵢ` for some
`rᵢ ≤ nᵢ`. -/
@[kb "etingof2011" "Proposition 2.2, p. 23"]
theorem exists_linearEquiv_pi_copies (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) (n : ι → ℕ)
    (U : Submodule A (∀ i, Fin (n i) → V i)) :
    ∃ r : ι → ℕ, (∀ i, r i ≤ n i) ∧ Nonempty (U ≃ₗ[A] ∀ i, Fin (r i) → V i) := by
  obtain ⟨r, m, hrank, hinj, hU⟩ := exists_matrices_eq_range_embedPi (k := k) hV n U
  refine ⟨r, fun i => ?_, ⟨?_⟩⟩
  · rw [← hrank i]
    exact Matrix.rank_le_height _
  · rw [hU]
    exact (LinearEquiv.ofInjective _ hinj).symm

end SubmoduleSum

end UndergradKB.RepresentationTheory
