import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialReps
import UndergradKB.RepresentationTheory.PowerSumsSchur
import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.RepresentationTheory.WeylCharacterTrace

/-! # The Weyl character formula for `GL_N(ℂ)` (Etingof et al., Theorem 4.63)

For a diagram `λ` with `n` boxes, `L_λ = Hom_{S_n}(V_λ, V^{⊗n})` with `V = ℂ^N` is the multiplicity space of the
Specht module `V_λ` in `V^{⊗n}`, a representation of `GL_N(ℂ)` (`swRepGL`).

* `trace_tensorPower_eq_sum`: the trace of `σ ∘ (g ⊗ ⋯ ⊗ g)` on `V^{⊗n}` is `∑_λ χ_λ(σ) tr(g, L_λ)`
  (from the Schur-Weyl decomposition).
* `trace_swRepGL_diagonal`: **Weyl character formula.** For `g = diag(x_1, …, x_N)`, the trace of `g` on `L_λ` is
  the Schur polynomial `S_λ(x)` when `λ` has at most `N` rows, and `0` otherwise.
* `finrank_swRepGL_eq_zero_iff`: `L_λ = 0` exactly when `λ` has more than `N` rows.
* `finrank_swRepGL`: the dimension formula `dim L_λ = ∏_{i<j} (λ_i - λ_j + j - i) / (j - i)`.

The character is computed at diagonal matrices, i.e. as a function of the eigenvalues, which is the form of the
book's statement. The proof follows the book: the trace of `σ ∘ (g ⊗ ⋯ ⊗ g)` on `V^{⊗n}` is computed once through
the Schur-Weyl decomposition and once directly (`trace_perm_comp_tensorPowerMap_diagonal`, giving the power-sum
polynomial of the cycle type of `σ`); Proposition 4.61 and the linear independence of the irreducible characters of
`S_n` then identify the coefficients.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open PiTensorProduct Finset
open scoped TensorProduct

section TracePi

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- The trace of a block-diagonal endomorphism of a finite product is the sum of the traces of the blocks. -/
theorem trace_pi_diag (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.trace R (∀ i, M i) (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace R (M i) (f i) := by
  have h : (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∑ i, (LinearMap.single R M i ∘ₗ f i) ∘ₗ LinearMap.proj i := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply]
  rw [h, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, LinearMap.proj_comp_single_same, LinearMap.id_comp]

/-- Conjugation invariance of the trace, for modules over a commutative semiring given a finite basis. -/
theorem trace_conj_of_basis {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M) (f : M →ₗ[R] M) (e : M ≃ₗ[R] N) :
    LinearMap.trace R N (e.conj f) = LinearMap.trace R M f := by
  rw [LinearMap.trace_eq_matrix_trace R b, LinearMap.trace_eq_matrix_trace R (b.map e)]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, LinearEquiv.conj_apply]

end TracePi

section Specht

variable {n : ℕ}

local notation "A" => MonoidAlgebra ℂ (Equiv.Perm (Fin n))

/-- The `ℂ`-linear identification of the representation space of `spechtIrrRep` with the Specht module. -/
noncomputable def spechtRestrictEquiv (la : DiagramsOfSize n) :
    RestrictScalars ℂ A (spechtModule la) ≃ₗ[ℂ] spechtModule la where
  toFun := RestrictScalars.addEquiv ℂ A (spechtModule la)
  invFun := (RestrictScalars.addEquiv ℂ A (spechtModule la)).symm
  map_add' := by simp
  map_smul' c x := by
    rw [RestrictScalars.addEquiv_map_smul, RingHom.id_apply, algebraMap_smul]
  left_inv := (RestrictScalars.addEquiv ℂ A (spechtModule la)).left_inv
  right_inv := (RestrictScalars.addEquiv ℂ A (spechtModule la)).right_inv

/-- The character of the Specht module at `σ` is the trace of left multiplication by `σ` on `V_λ`. -/
theorem spechtChar_apply_eq_trace (la : DiagramsOfSize n) (σ : Equiv.Perm (Fin n)) :
    ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ =
      LinearMap.trace ℂ (spechtModule la)
        (DistribSMul.toLinearMap ℂ (spechtModule la) (MonoidAlgebra.of ℂ _ σ)) := by
  change LinearMap.trace ℂ _ ((spechtIrrRep n la).ρ σ) = _
  refine (LinearMap.trace_conj' _ (spechtRestrictEquiv la)).symm.trans (congrArg _ ?_)
  refine LinearMap.ext fun s => ?_
  change spechtRestrictEquiv la ((Representation.ofModule (k := ℂ) (G := Equiv.Perm (Fin n)) (spechtModule la)) σ
    ((spechtRestrictEquiv la).symm s)) = _
  rw [← Representation.asAlgebraHom_of, Representation.ofModule_asAlgebraHom_apply_apply]
  exact ((RestrictScalars.addEquiv ℂ A _).apply_symm_apply _).trans
    (congrArg (MonoidAlgebra.of ℂ _ σ • ·) ((RestrictScalars.addEquiv ℂ A _).apply_symm_apply s))

end Specht

section Decomposition

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)

local notation "A" => MonoidAlgebra ℂ (Equiv.Perm (Fin n))

/-- The multiplicity space `Hom_{S_n}(V_λ, V^{⊗n})` is finite-dimensional. -/
instance instFiniteDimensionalSwHom (la : DiagramsOfSize n) :
    FiniteDimensional ℂ (spechtModule la →ₗ[A] tensorPowerModule V n) := by
  let b := Module.finBasis ℂ (spechtModule la)
  let F : (spechtModule la →ₗ[A] tensorPowerModule V n) →ₗ[ℂ]
      (Fin (Module.finrank ℂ (spechtModule la)) → tensorPowerModule V n) :=
    { toFun := fun f i => f (b i)
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  refine Module.Finite.of_injective F fun f f' h => ?_
  have h' : f.restrictScalars ℂ = f'.restrictScalars ℂ := b.ext fun i => congrFun h i
  exact LinearMap.ext fun x => LinearMap.congr_fun h' x

instance instFreeSwHom (la : DiagramsOfSize n) :
    Module.Free ℂ (spechtModule la →ₗ[A] tensorPowerModule V n) :=
  Module.Free.of_divisionRing ℂ (spechtModule la →ₗ[A] tensorPowerModule V n)

/-- `σ` acting on the factor `V_λ` of `V_λ ⊗ L_λ`, after `g` on the factor `L_λ`. -/
theorem map_smul_swPost_eq (la : DiagramsOfSize n) (σ : Equiv.Perm (Fin n)) (g : V →ₗ[ℂ] V)
    (t : spechtModule la ⊗[ℂ] (spechtModule la →ₗ[A] tensorPowerModule V n)) :
    TensorProduct.map (DistribSMul.toLinearMap ℂ (spechtModule la) (MonoidAlgebra.of ℂ _ σ)) (swPost n la g) t =
      MonoidAlgebra.of ℂ _ σ • TensorProduct.map LinearMap.id (swPost n la g) t := by
  induction t using TensorProduct.inductionOn with
  | tmul s f => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- The block-diagonal operator `⨁_λ σ ⊗ g` on `⨁_λ V_λ ⊗ L_λ`. -/
noncomputable def swBlockOp (σ : Equiv.Perm (Fin n)) (g : V →ₗ[ℂ] V) :
    Module.End ℂ (Π la : DiagramsOfSize n, spechtModule la ⊗[ℂ]
      (spechtModule la →ₗ[A] tensorPowerModule V n)) :=
  LinearMap.pi fun la => TensorProduct.map (DistribSMul.toLinearMap ℂ (spechtModule la) (MonoidAlgebra.of ℂ _ σ))
    (swPost n la g) ∘ₗ LinearMap.proj la

/-- The Schur-Weyl decomposition carries `⨁_λ σ ⊗ g` to `σ ∘ (g ⊗ ⋯ ⊗ g)`. -/
theorem schurWeylDecomposition_swBlockOp (σ : Equiv.Perm (Fin n)) (g : V →ₗ[ℂ] V) (z) :
    schurWeylDecomposition (V := V) n (swBlockOp n σ g z) =
      tensorPowerPermRep ℂ n V σ (tensorPowerMap n g (schurWeylDecomposition n z)) := by
  have h1 : swBlockOp n σ g z =
      MonoidAlgebra.of ℂ _ σ • (fun la => TensorProduct.map LinearMap.id (swPost n la g) (z la)) := by
    funext la
    exact map_smul_swPost_eq n la σ g (z la)
  rw [h1, map_smul, ← schurWeylDecomposition_equivariant, tensorPowerEnd_apply]
  change (tensorPowerPermRep ℂ n V).asAlgebraHom (MonoidAlgebra.of ℂ _ σ) _ = _
  rw [Representation.asAlgebraHom_of]

/-- **Trace through the Schur-Weyl decomposition.** The trace of `σ ∘ (g ⊗ ⋯ ⊗ g)` on `V^{⊗n}` is
`∑_λ χ_λ(σ) tr(g, L_λ)`, where `χ_λ` is the character of the Specht module `V_λ` and `L_λ = Hom_{S_n}(V_λ, V^{⊗n})`
carries `g` by post-composition. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem trace_tensorPower_eq_sum (σ : Equiv.Perm (Fin n)) (g : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (⨂[ℂ] _ : Fin n, V) (tensorPowerPermRep ℂ n V σ ∘ₗ tensorPowerMap n g) =
      ∑ la : DiagramsOfSize n,
        ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ *
          LinearMap.trace ℂ _ (swPost (V := V) n la g) := by
  classical
  let e := ((schurWeylDecomposition (V := V) n).restrictScalars ℂ).trans
    (tensorPowerPermRep ℂ n V).asModuleEquiv
  have h : e.conj (swBlockOp n σ g) = tensorPowerPermRep ℂ n V σ ∘ₗ tensorPowerMap n g := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply]
    change schurWeylDecomposition n (swBlockOp n σ g _) = _
    rw [schurWeylDecomposition_swBlockOp]
    exact congrArg (fun w => tensorPowerPermRep ℂ n V σ (tensorPowerMap n g w))
      ((schurWeylDecomposition (V := V) n).apply_symm_apply y)
  have h2 : LinearMap.trace ℂ _ (e.conj (swBlockOp n σ g)) = LinearMap.trace ℂ _ (swBlockOp n σ g) :=
    trace_conj_of_basis (Pi.basis fun la : DiagramsOfSize n =>
      (Module.finBasis ℂ (spechtModule la)).tensorProduct
        (Module.finBasis ℂ (spechtModule la →ₗ[A] tensorPowerModule V n) :
          Module.Basis _ ℂ (spechtModule la →ₗ[A] tensorPowerModule V n))) _ e
  rw [← h, h2, swBlockOp]
  refine (trace_pi_diag (R := ℂ) (M := fun la : DiagramsOfSize n => spechtModule la ⊗[ℂ]
    (spechtModule la →ₗ[A] tensorPowerModule V n)) _).trans ?_
  refine sum_congr rfl fun la _ => ?_
  refine (LinearMap.trace_tensorProduct' (R := ℂ) (M := spechtModule la)
    (N := spechtModule la →ₗ[A] tensorPowerModule V n) _ _).trans ?_
  rw [spechtChar_apply_eq_trace]

end Decomposition

section Weyl

variable (N : ℕ) {n : ℕ}

/-- The diagonal matrix `diag(x_1, …, x_N)` with nonzero entries, as an element of `GL_N(ℂ)`. -/
noncomputable def diagGL (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) : GL (Fin N) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal x) (by
    rw [Matrix.det_diagonal]
    exact prod_ne_zero_iff.2 fun i _ => hx i)

variable {N}

theorem swRepGL_apply (la : DiagramsOfSize n) (g : GL (Fin N) ℂ) :
    swRepGL N n la g = swPost n la (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) ℂ)) := rfl

/-- The value predicted by the Weyl character formula: `S_λ(x)` if `λ` has at most `N` rows, `0` otherwise. -/
noncomputable def weylValue (la : DiagramsOfSize n) (x : Fin N → ℂ) : ℂ :=
  if la.1.colLen 0 ≤ N then MvPolynomial.eval x (schurPoly (R := ℂ) fun j : Fin N => la.1.rowLen j) else 0

theorem rowVec_mem_partitionVecs (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    (fun j : Fin N => la.1.rowLen j) ∈ partitionVecs n N :=
  mem_partitionVecs.2 ⟨fun i j hij => la.1.rowLen_anti i j hij, sum_rowLen_eq la hN⟩

/-- A diagram with at most `N` rows is determined by its first `N` row lengths. -/
theorem eq_of_rowLen_eq {la mu : DiagramsOfSize n} (hla : la.1.colLen 0 ≤ N) (hmu : mu.1.colLen 0 ≤ N)
    (h : ∀ j : Fin N, la.1.rowLen j = mu.1.rowLen j) : la = mu := by
  apply (spechtChar_bijective n).1
  apply Subtype.ext
  rw [frobenius_character_formula la hla, frobenius_character_formula mu hmu]
  congr 1
  funext j
  exact h j

/-- Proposition 4.61 evaluated at `x`, rewritten as a sum over all diagrams with `n` boxes. -/
theorem sum_frobChar_mul_eval_schurPoly (σ : Equiv.Perm (Fin n)) (x : Fin N → ℂ) :
    ∑ μ ∈ partitionVecs n N, frobChar n N μ σ * MvPolynomial.eval x (schurPoly (R := ℂ) μ) =
      ∑ la : DiagramsOfSize n,
        ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ * weylValue la x := by
  classical
  rw [← sum_filter_add_sum_filter_not univ (fun la : DiagramsOfSize n => la.1.colLen 0 ≤ N)]
  rw [sum_eq_zero (s := univ.filter fun la : DiagramsOfSize n => ¬ la.1.colLen 0 ≤ N)
    (fun la hla => by simp [weylValue, (mem_filter.1 hla).2]), add_zero]
  symm
  refine sum_bij (fun la _ => fun j : Fin N => la.1.rowLen j)
    (fun la hla => rowVec_mem_partitionVecs la (mem_filter.1 hla).2)
    (fun la hla mu hmu h => eq_of_rowLen_eq (mem_filter.1 hla).2 (mem_filter.1 hmu).2 (fun j => congrFun h j))
    (fun μ hμ => ?_) (fun la hla => ?_)
  · obtain ⟨la, hN, hrow, -⟩ := exists_spechtChar_eq_frobChar hμ
    exact ⟨la, mem_filter.2 ⟨mem_univ _, hN⟩, funext hrow⟩
  · have hN := (mem_filter.1 hla).2
    simp only [weylValue, hN, ↓reduceIte]
    rw [frobenius_character_formula la hN]

/-- **Weyl character formula** (Etingof et al., Theorem 4.63).  Let `L_λ = Hom_{S_n}(V_λ, V^{⊗n})`, `V = ℂ^N`, as a
representation of `GL_N(ℂ)`.  At the diagonal matrix `diag(x_1, …, x_N)` its character is the Schur polynomial
`S_λ(x_1, …, x_N)` if `λ` has at most `N` rows, and `0` if `λ` has more than `N` rows. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem trace_swRepGL_diagonal (la : DiagramsOfSize n) (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    LinearMap.trace ℂ _ (swRepGL N n la (diagGL N x hx)) = weylValue la x := by
  classical
  have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  set t : DiagramsOfSize n → ℂ := fun mu =>
    LinearMap.trace ℂ _ (swPost (V := Fin N → ℂ) n mu (Matrix.mulVecLin (Matrix.diagonal x))) with ht
  have key : ∀ σ, ∑ mu, ((spechtChar n mu : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ * t mu =
      ∑ mu, ((spechtChar n mu : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) σ * weylValue mu x := by
    intro σ
    rw [ht, ← trace_tensorPower_eq_sum, trace_perm_comp_tensorPowerMap_diagonal,
      cyclePoly_eq_sum_frobChar_schurPoly, map_sum, ← sum_frobChar_mul_eval_schurPoly]
    refine sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.smul_eval]
  have hli : LinearIndependent ℂ
      (fun mu : DiagramsOfSize n => ((spechtChar n mu : irrChars ℂ (Equiv.Perm (Fin n))) :
        Equiv.Perm (Fin n) → ℂ)) :=
    LinearIndependent.comp (linearIndepOn_irrChars (k := ℂ) (G := Equiv.Perm (Fin n))) (spechtChar n)
      (spechtChar_bijective n).1
  have h0 := Fintype.linearIndependent_iff.1 hli (fun mu => t mu - weylValue mu x) (by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, sum_sub_distrib]
    rw [sub_eq_zero]
    simpa only [mul_comm] using key σ) la
  exact sub_eq_zero.1 h0

theorem diagGL_one : diagGL N (fun _ => (1 : ℂ)) (fun _ => one_ne_zero) = 1 :=
  Units.ext (by simp [diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero])

/-- The dimension of `L_λ` is the value of the Weyl character formula at the identity. -/
theorem finrank_swRepGL_eq_weylValue (la : DiagramsOfSize n) :
    (Module.finrank ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) : ℂ) = weylValue la (fun _ : Fin N => 1) := by
  rw [← trace_swRepGL_diagonal la (fun _ => 1) (fun _ => one_ne_zero), diagGL_one, map_one]
  let b : Module.Basis _ ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) := Module.finBasis ℂ _
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_one, Matrix.trace_one, Fintype.card_fin]

/-- The Weyl dimension formula at `x = (1, …, 1)`, for a diagram with at most `N` rows. -/
theorem weylValue_one (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    weylValue la (fun _ : Fin N => 1) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, ((la.1.rowLen i - la.1.rowLen j + ((j : ℕ) - (i : ℕ)) : ℕ) : ℂ)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : ℂ) := by
  simp only [weylValue, hN, ↓reduceIte]
  rw [← MvPolynomial.aeval_eq_eval]
  exact schurPoly_one (K := ℂ) (fun j : Fin N => la.1.rowLen j) (fun i j hij => la.1.rowLen_anti i j hij)

theorem weylValue_one_ne_zero (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    weylValue la (fun _ : Fin N => 1) ≠ 0 := by
  rw [weylValue_one la hN]
  refine div_ne_zero (prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj => ?_)
    (prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj => ?_)
  · have h' : i < j := mem_Ioi.1 hj
    have : (i : ℕ) < j := h'
    exact Nat.cast_ne_zero.2 (by omega)
  · have h' : i < j := mem_Ioi.1 hj
    have : (i : ℕ) < j := h'
    exact Nat.cast_ne_zero.2 (by omega)

/-- **Weyl dimension formula** (Etingof et al., Theorem 4.63).  For a diagram `λ` with at most `N` rows,
`dim L_λ = ∏_{i<j} (λ_i - λ_j + j - i) / (j - i)`. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem finrank_swRepGL (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    (Module.finrank ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) : ℂ) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, ((la.1.rowLen i - la.1.rowLen j + ((j : ℕ) - (i : ℕ)) : ℕ) : ℂ)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : ℂ) := by
  rw [finrank_swRepGL_eq_weylValue, weylValue_one la hN]

/-- **Etingof et al., Theorem 4.63, vanishing.**  `L_λ = 0` exactly when `λ` has more than `N` rows. -/
@[kb "etingof2011" "Theorem 4.63, p. 67"]
theorem finrank_swRepGL_eq_zero_iff (la : DiagramsOfSize n) :
    Module.finrank ℂ (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      tensorPowerModule (Fin N → ℂ) n) = 0 ↔ N < la.1.colLen 0 := by
  constructor
  · intro h
    by_contra hN
    have h1 := finrank_swRepGL_eq_weylValue (N := N) la
    rw [h, Nat.cast_zero] at h1
    exact weylValue_one_ne_zero la (not_lt.1 hN) h1.symm
  · intro hN
    have h1 := finrank_swRepGL_eq_weylValue (N := N) la
    simp only [weylValue, not_le.2 hN, ↓reduceIte] at h1
    exact_mod_cast h1

end Weyl

end UndergradKB.RepresentationTheory
