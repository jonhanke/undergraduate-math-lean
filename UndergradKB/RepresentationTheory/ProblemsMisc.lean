import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurFunctors
import UndergradKB.RepresentationTheory.McKayConnected

/-! # Miscellaneous problems (Etingof et al.: Problems 1.24, 1.54, 3.20, 3.26)

* Problem 1.24: `quotient_mvPolynomial_idempotent` (every idempotent `A`-endomorphism of `A ⧸ I` is `0` or
  `1`) and `quotient_mvPolynomial_indecomposable` (two complementary submodules of `A ⧸ I` : one of them is
  trivial), where `A = k[x_1, …, x_n]`, `I` is a proper ideal containing all homogeneous polynomials of
  large degree.  The proof shows that the polynomials without constant term become nilpotent in `A ⧸ I`.
* Problem 1.54: `lieTensorHomEquiv`, a linear equivalence
  `Hom_g(V ⊗ W, U) ≃ Hom_g(V, U ⊗ W^*)` for a finite-dimensional module `W` over a Lie algebra `L` over a
  field (finite-dimensionality of `V` and `U` is not needed).  Here `Hom_g` is Mathlib's `LieModuleHom`
  (equivalent to `Hom_{U(g)}`), and the Lie module structures on `V ⊗ W` and on `W^*` come from Mathlib.
* Problem 3.26: `tensorPowerRep` (the representation `V^{⊗n}` with `g` acting as `ρ(g)^{⊗n}`),
  `character_tensorPowerRep` (its character is the `n`-th power of the character of `V`), and
  `exists_injective_intertwining_tensorPower` (for a faithful finite-dimensional complex representation of a
  finite group, every irreducible representation embeds into some `V^{⊗n}`).  The book states the stronger
  claim with the symmetric power `S^n V`; only the `V^{⊗n}` form is proved here.  The proof reuses the
  Burnside-Brauer argument `exists_pairing_character_pow_ne_zero` from `McKayConnected.lean`.
* Problem 3.20: `graph_automorphisms_commute_of_simple_spectrum` (if all roots of the characteristic
  polynomial of the real adjacency matrix of a finite simple graph are simple, any two graph automorphisms
  commute) and `adjMatrix_charpoly_roots_not_nodup` (so a graph with nonabelian automorphism group has a
  repeated eigenvalue).  Mathlib has no group structure on `G ≃g G`, so commutation is stated through
  `Iso.trans`.  The proof uses permutation matrices and the spectral theorem, not the book's phrasing with
  the `±1` action on eigenlines.
-/

namespace UndergradKB.RepresentationTheory

section Problem124

variable {k : Type*} [Field k] {n : ℕ}

lemma support_pow_degree_ge (h : MvPolynomial (Fin n) k) (h0 : MvPolynomial.constantCoeff h = 0)
    (N : ℕ) : ∀ s ∈ (h ^ N).support, N ≤ s.degree := by
  classical
  induction N with
  | zero => intro s _; exact Nat.zero_le _
  | succ N ih =>
    intro s hs
    have hs' := MvPolynomial.support_mul (h ^ N) h hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs'
    rw [pow_succ] at hs
    have h1 := ih a ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      have : h.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp hb
      exact this (by rw [← MvPolynomial.constantCoeff_eq]; exact h0)
    have h2 : 0 < b.degree := by
      rcases Nat.eq_zero_or_pos b.degree with h | h
      · exact absurd ((Finsupp.degree_eq_zero_iff _).mp h) hb0
      · exact h
    rw [map_add]
    omega

lemma mem_ideal_of_support_degree_ge (I : Ideal (MvPolynomial (Fin n) k)) {N : ℕ}
    (hN : ∀ d ≥ N, ∀ p : MvPolynomial (Fin n) k, p.IsHomogeneous d → p ∈ I)
    (p : MvPolynomial (Fin n) k) (hp : ∀ s ∈ p.support, N ≤ s.degree) : p ∈ I := by
  rw [MvPolynomial.as_sum p]
  refine I.sum_mem fun s hs => hN _ (hp s hs) _ ?_
  exact MvPolynomial.isHomogeneous_monomial _ rfl

/-- In `A ⧸ I`, the image of a polynomial without constant term is nilpotent. -/
lemma isNilpotent_mk_of_constantCoeff_eq_zero (I : Ideal (MvPolynomial (Fin n) k)) {N : ℕ}
    (hN : ∀ d ≥ N, ∀ p : MvPolynomial (Fin n) k, p.IsHomogeneous d → p ∈ I)
    (h : MvPolynomial (Fin n) k) (h0 : MvPolynomial.constantCoeff h = 0) :
    IsNilpotent (Ideal.Quotient.mk I h) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_ideal_of_support_degree_ge I hN _ (support_pow_degree_ge h h0 N)

/-- Idempotents of the quotient ring `A ⧸ I` are `0` or `1`. -/
lemma quotient_mvPolynomial_idempotent_elem (I : Ideal (MvPolynomial (Fin n) k)) {N : ℕ}
    (hN : ∀ d ≥ N, ∀ p : MvPolynomial (Fin n) k, p.IsHomogeneous d → p ∈ I)
    (a : MvPolynomial (Fin n) k ⧸ I) (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  set c := MvPolynomial.constantCoeff g with hc
  set h := g - MvPolynomial.C c with hh
  have h0 : MvPolynomial.constantCoeff h = 0 := by simp [hh, hc]
  have hnil := isNilpotent_mk_of_constantCoeff_eq_zero I hN h h0
  have hg : Ideal.Quotient.mk I g = Ideal.Quotient.mk I (MvPolynomial.C c) + Ideal.Quotient.mk I h := by
    rw [← map_add]; simp [hh]
  by_cases hc0 : c = 0
  · left
    have : Ideal.Quotient.mk I g = Ideal.Quotient.mk I h := by simp [hg, hc0]
    rw [this] at ha ⊢
    obtain ⟨m, hm⟩ := hnil
    have := ha.pow_succ_eq m
    rw [pow_succ, hm, zero_mul] at this
    exact this.symm
  · right
    have hu : IsUnit (Ideal.Quotient.mk I (MvPolynomial.C c)) :=
      ((isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C).map _
    have hu' : IsUnit (Ideal.Quotient.mk I g) := by
      rw [hg]
      exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu').mp ha

/-- Problem 1.24 (endomorphism form). -/
@[kb "etingof2011" "Problem 1.24, p. 11"]
theorem quotient_mvPolynomial_idempotent (I : Ideal (MvPolynomial (Fin n) k)) {N : ℕ}
    (hN : ∀ d ≥ N, ∀ p : MvPolynomial (Fin n) k, p.IsHomogeneous d → p ∈ I)
    (e : Module.End (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I))
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  set a : MvPolynomial (Fin n) k ⧸ I := e 1 with ha
  have key : ∀ x, e x = x * a := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hsm : ∀ (g : MvPolynomial (Fin n) k) (y : MvPolynomial (Fin n) k ⧸ I),
        g • y = Ideal.Quotient.mk I g * y := fun _ _ => rfl
    have : Ideal.Quotient.mk I f = f • (1 : MvPolynomial (Fin n) k ⧸ I) := by
      rw [hsm]; simp
    rw [this, map_smul, ← ha, hsm, hsm]
    simp [mul_comm]
  have hae : IsIdempotentElem a := by
    have := congrArg (fun f => f 1) he.eq
    simp only [mul_apply_eq_comp] at this
    rw [← ha] at this
    rw [key a] at this
    exact this
  rcases quotient_mvPolynomial_idempotent_elem I hN a hae with h | h
  · left; ext; simp [key, h]
  · right; ext; simp [key, h]

/-- Problem 1.24: `A ⧸ I` is indecomposable as an `A`-module. -/
@[kb "etingof2011" "Problem 1.24, p. 11"]
theorem quotient_mvPolynomial_indecomposable (I : Ideal (MvPolynomial (Fin n) k)) {N : ℕ}
    (hN : ∀ d ≥ N, ∀ p : MvPolynomial (Fin n) k, p.IsHomogeneous d → p ∈ I)
    (p q : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)) (hpq : IsCompl p q) :
    p = ⊥ ∨ q = ⊥ := by
  rcases quotient_mvPolynomial_idempotent I hN (p.projection q hpq)
    (Submodule.isIdempotentElem_projection hpq) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have h1 := Submodule.projection_apply_of_mem_left hpq hx
    rw [h] at h1
    simpa [eq_comm] using h1
  · right
    rw [eq_bot_iff]
    intro x hx
    have h1 := (Submodule.projection_apply_eq_zero_iff hpq).mpr hx
    rw [h] at h1
    simpa using h1

end Problem124

section Problem320

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix commuting with a diagonal matrix with distinct entries is diagonal. -/
lemma exists_diagonal_of_commute_diagonal {d : n → ℝ} (hd : Function.Injective d)
    {M : Matrix n n ℝ} (h : M * diagonal d = diagonal d * M) : M = diagonal (fun i => M i i) := by
  ext i j
  have h1 := congr_fun (congr_fun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  by_cases hij : i = j
  · subst hij; simp
  · have : M i j * (d j - d i) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · simp [h2, hij]
    · exact absurd (hd (by linarith)).symm hij

/-- Two matrices commuting with a real symmetric matrix having pairwise distinct eigenvalues commute. -/
lemma commute_of_commute_hermitian {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) {M N : Matrix n n ℝ}
    (hM : Commute M A) (hN : Commute N A) : Commute M N := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ) with hU
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h2 : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hD : star U * A * U = diagonal hA.eigenvalues := by
    have := hA.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply] using this
  have key : ∀ {M : Matrix n n ℝ}, Commute M A →
      star U * M * U = diagonal (fun i => (star U * M * U) i i) := by
    intro M hM
    apply exists_diagonal_of_commute_diagonal hinj
    rw [← hD]
    have : (star U * M * U) * (star U * A * U) = star U * (M * A) * U := by
      simp only [mul_assoc]
      rw [← mul_assoc U, h2, one_mul]
    have h3 : (star U * A * U) * (star U * M * U) = star U * (A * M) * U := by
      simp only [mul_assoc]
      rw [← mul_assoc U, h2, one_mul]
    rw [this, h3, hM.eq]
  have recon : ∀ X : Matrix n n ℝ, X = U * (star U * X * U) * star U := by
    intro X
    calc X = (U * star U) * X * (U * star U) := by rw [h2, one_mul, mul_one]
      _ = U * (star U * X * U) * star U := by simp only [mul_assoc]
  have hMN : (star U * M * U) * (star U * N * U) = (star U * N * U) * (star U * M * U) := by
    rw [key hM, key hN, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  have e1 : (star U * M * U) * (star U * N * U) = star U * (M * N) * U := by
    simp only [mul_assoc]
    rw [← mul_assoc U, h2, one_mul]
  have e2 : (star U * N * U) * (star U * M * U) = star U * (N * M) * U := by
    simp only [mul_assoc]
    rw [← mul_assoc U, h2, one_mul]
  rw [e1, e2] at hMN
  have := congrArg (fun X => U * X * star U) hMN
  rw [← recon, ← recon] at this
  exact this

/-- The permutation matrix of a map `f`, with entry `(i, j)` equal to `1` iff `f i = j`. -/
def permMat (f : n → n) : Matrix n n ℝ := (1 : Matrix n n ℝ).submatrix f id

lemma permMat_mul (f : n → n) (B : Matrix n n ℝ) : permMat f * B = B.submatrix f id := by
  ext i j
  simp [permMat, Matrix.mul_apply, Matrix.one_apply]

lemma permMat_mul_permMat (f g : n → n) : permMat f * permMat g = permMat (g ∘ f) := by
  rw [permMat_mul]
  rfl

omit [Fintype n] in
lemma permMat_injective {f g : n → n} (h : permMat f = permMat g) : f = g := by
  funext i
  have := congr_fun (congr_fun h i) (f i)
  simp [permMat, Matrix.one_apply] at this
  exact this.symm

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma commute_permMat_adjMatrix (f : G ≃g G) : Commute (permMat f) (G.adjMatrix ℝ) := by
  unfold Commute SemiconjBy
  rw [permMat_mul]
  ext i j
  have hj : f (f.symm j) = j := f.apply_symm_apply j
  simp only [Matrix.submatrix_apply, id]
  rw [Matrix.mul_apply, Finset.sum_eq_single (f.symm j)]
  · simp only [permMat, Matrix.submatrix_apply, id, Matrix.one_apply, hj, ite_true, mul_one,
      SimpleGraph.adjMatrix_apply]
    have : G.Adj (f i) j ↔ G.Adj i (f.symm j) := by
      have := f.map_adj_iff (v := i) (w := f.symm j)
      rwa [hj] at this
    simp only [this]
  · intro k _ hk
    have : f k ≠ j := fun h => hk (by rw [← h]; simp)
    simp [permMat, this]
  · simp

/-- **Problem 3.20.**  If all roots of the characteristic polynomial of the (real) adjacency matrix of
a finite simple graph are simple, then any two automorphisms of the graph commute. -/
@[kb "etingof2011" "Problem 3.20, p. 43"]
theorem graph_automorphisms_commute_of_simple_spectrum
    (hsimple : (G.adjMatrix ℝ).charpoly.roots.Nodup) (f g : G ≃g G) : f.trans g = g.trans f := by
  have hA : (G.adjMatrix ℝ).IsHermitian := G.isHermitian_adjMatrix ℝ
  have hinj : Function.Injective hA.eigenvalues := by
    have := hA.roots_charpoly_eq_eigenvalues
    rw [this] at hsimple
    have h2 := (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hsimple
    intro a b hab
    exact h2 a (Finset.mem_univ _) b (Finset.mem_univ _) (by simpa using hab)
  have hc := commute_of_commute_hermitian hA hinj (commute_permMat_adjMatrix f)
    (commute_permMat_adjMatrix g)
  have := permMat_injective ((permMat_mul_permMat f g).symm.trans
    (hc.eq.trans (permMat_mul_permMat g f)))
  ext i
  exact congr_fun this i

/-- **Problem 3.20**, contrapositive form: if two automorphisms of a finite simple graph do not
commute, the adjacency matrix has a repeated eigenvalue (a multiple root of the characteristic
polynomial). -/
@[kb "etingof2011" "Problem 3.20, p. 43"]
theorem adjMatrix_charpoly_roots_not_nodup (f g : G ≃g G) (hfg : f.trans g ≠ g.trans f) :
    ¬ (G.adjMatrix ℝ).charpoly.roots.Nodup :=
  fun h => hfg (graph_automorphisms_commute_of_simple_spectrum h f g)

end Problem320

section Problem154

open TensorProduct

variable {K : Type*} [Field K] {L : Type*} [LieRing L] [LieAlgebra K L]
  {V W U : Type*} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
  [AddCommGroup U] [Module K U] [LieRingModule L U] [LieModule K L U]

variable (K W U) in
/-- The identification `U ⊗ W^* ≃ Hom(W, U)` (for finite-dimensional `W`). -/
noncomputable def tensorDualHomEquiv [Module.Finite K W] :
    U ⊗[K] Module.Dual K W ≃ₗ[K] (W →ₗ[K] U) :=
  (TensorProduct.comm K U (Module.Dual K W)).trans (dualTensorHomEquiv K W U)

lemma tensorDualHomEquiv_tmul [Module.Finite K W] (u : U) (φ : Module.Dual K W) (w : W) :
    tensorDualHomEquiv K W U (u ⊗ₜ φ) w = φ w • u := rfl

/-- The identification `U ⊗ W^* ≃ Hom(W, U)` is compatible with the action of `L`. -/
lemma tensorDualHomEquiv_lie [Module.Finite K W] (x : L) (t : U ⊗[K] Module.Dual K W) :
    tensorDualHomEquiv K W U ⁅x, t⁆ = ⁅x, tensorDualHomEquiv K W U t⁆ := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [lie_add, map_add, ha, hb]
  | tmul u φ =>
    rw [TensorProduct.LieModule.lie_tmul_right, map_add]
    ext w
    simp [tensorDualHomEquiv_tmul, LieHom.lie_apply, Module.Dual.lie_apply, sub_eq_add_neg]

variable (K V W U) in
/-- Curry a linear map `V ⊗ W → U` and then identify `Hom(W, U)` with `U ⊗ W^*`. -/
noncomputable def curryDual [Module.Finite K W] :
    (V ⊗[K] W →ₗ[K] U) ≃ₗ[K] (V →ₗ[K] U ⊗[K] Module.Dual K W) :=
  (TensorProduct.lift.equiv (RingHom.id K) V W U).symm.trans
    (LinearEquiv.congrRight (tensorDualHomEquiv K W U).symm)

lemma curryDual_lie_iff [Module.Finite K W] (f : V ⊗[K] W →ₗ[K] U) :
    (∀ (x : L) (m : V ⊗[K] W), f ⁅x, m⁆ = ⁅x, f m⁆) ↔
      ∀ (x : L) (v : V), curryDual K V W U f (⁅x, v⁆ : V) = ⁅x, curryDual K V W U f v⁆ := by
  have hc : ∀ v, tensorDualHomEquiv K W U (curryDual K V W U f v) = TensorProduct.curry f v := by
    intro v
    simp [curryDual]
    rfl
  have h1 : ∀ (x : L) (v : V), curryDual K V W U f (⁅x, v⁆ : V) = ⁅x, curryDual K V W U f v⁆ ↔
      TensorProduct.curry f (⁅x, v⁆ : V) = ⁅x, TensorProduct.curry f v⁆ := by
    intro x v
    rw [← (tensorDualHomEquiv K W U).injective.eq_iff, tensorDualHomEquiv_lie, hc, hc]
  simp only [h1]
  constructor
  · intro h x v
    ext w
    have := h x (v ⊗ₜ w)
    simp only [TensorProduct.LieModule.lie_tmul_right, map_add] at this
    simp only [TensorProduct.curry_apply, LieHom.lie_apply]
    exact eq_sub_of_add_eq this
  · intro h x m
    induction m using TensorProduct.inductionOn with
    | add a b ha hb => simp only [lie_add, map_add, ha, hb]
    | tmul v w =>
      have := LinearMap.congr_fun (h x v) w
      simp only [TensorProduct.curry_apply, LieHom.lie_apply] at this
      simp only [TensorProduct.LieModule.lie_tmul_right, map_add]
      rw [this]; abel

/-- **Problem 1.54.**  For a finite-dimensional module `W`, Lie module homomorphisms
`V ⊗ W → U` correspond linearly to Lie module homomorphisms `V → U ⊗ W^*`. -/
@[kb "etingof2011" "Problem 1.54, p. 20"]
noncomputable def lieTensorHomEquiv [Module.Finite K W] :
    (V ⊗[K] W →ₗ⁅K, L⁆ U) ≃ₗ[K] (V →ₗ⁅K, L⁆ U ⊗[K] Module.Dual K W) where
  toFun F := ⟨curryDual K V W U F.toLinearMap,
    fun {x m} => (curryDual_lie_iff F.toLinearMap).mp (fun x m => F.map_lie x m) x m⟩
  invFun G := ⟨(curryDual K V W U).symm G.toLinearMap, fun {x m} => by
    refine (curryDual_lie_iff ((curryDual K V W U).symm G.toLinearMap)).mpr ?_ x m
    intro x v
    simp⟩
  map_add' F G := by
    ext v
    change curryDual K V W U ((F : V ⊗[K] W →ₗ[K] U) + (G : V ⊗[K] W →ₗ[K] U)) v = _
    simp
  map_smul' c F := by
    ext v
    change curryDual K V W U (c • (F : V ⊗[K] W →ₗ[K] U)) v = _
    simp
  left_inv F := by ext m; simp
  right_inv G := by ext v; simp

end Problem154

section Problem326

open Module Representation PiTensorProduct
open scoped TensorProduct

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The trace of the `n`-th tensor power of an endomorphism is the `n`-th power of its trace. -/
lemma trace_tensorPowerMap [Module.Finite k V] (n : ℕ) (T : V →ₗ[k] V) :
    LinearMap.trace k (⨂[k] _ : Fin n, V) (tensorPowerMap n T) = (LinearMap.trace k V T) ^ n := by
  classical
  let b := Module.finBasis k V
  let B := Basis.piTensorProduct (fun _ : Fin n => b)
  rw [LinearMap.trace_eq_matrix_trace k B, LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, B, Basis.piTensorProduct_apply,
    tensorPowerMap, PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
  rw [Finset.sum_pow', Fintype.piFinset_univ]

instance [Module.Finite k V] (n : ℕ) : Module.Finite k (⨂[k] _ : Fin n, V) :=
  Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin n => Module.finBasis k V))

variable {G : Type*} [Group G]

variable (k) in
/-- The tensor power `V^{⊗n}` of a representation `V`, with `g` acting as `ρ(g) ⊗ ⋯ ⊗ ρ(g)`. -/
noncomputable def tensorPowerRep (ρ : Representation k G V) (n : ℕ) :
    Representation k G (⨂[k] _ : Fin n, V) where
  toFun g := tensorPowerMap n (ρ g)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by
    simp only [map_mul]
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, tensorPowerMap_comp]

/-- The character of `V^{⊗n}` is the `n`-th power of the character of `V`. -/
theorem character_tensorPowerRep [Module.Finite k V] (ρ : Representation k G V) (n : ℕ) (g : G) :
    (tensorPowerRep k ρ n).character g = (ρ.character g) ^ n :=
  trace_tensorPowerMap n (ρ g)

/-- **Problem 3.26** (tensor power form).  If `ρ` is a faithful finite-dimensional complex representation
of a finite group `G`, then every irreducible representation of `G` embeds, by an injective intertwining map, into
some tensor power `V^{⊗n}`. -/
@[kb "etingof2011" "Problem 3.26, p. 45"]
theorem exists_injective_intertwining_tensorPower [Fintype G] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ) (X : IrrRep ℂ G) :
    ∃ n : ℕ, ∃ f : IntertwiningMap X.ρ (tensorPowerRep ℂ ρ n), Function.Injective f := by
  have hinv : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨n, hn⟩ := exists_pairing_character_pow_ne_zero ρ hρ ⟨X.ρ.character, X, rfl⟩
  have hfin := Representation.card_inv_mul_sum_char_mul_char_eq_finrank X.ρ (tensorPowerRep ℂ ρ n)
  have hp : pairing (ρ.character ^ n) X.ρ.character =
      (finrank ℂ (IntertwiningMap X.ρ (tensorPowerRep ℂ ρ n)) : ℂ) := by
    rw [pairing_apply, ← hfin]
    simp [character_tensorPowerRep]
  rw [hp] at hn
  have hpos : 0 < finrank ℂ (IntertwiningMap X.ρ (tensorPowerRep ℂ ρ n)) :=
    Nat.pos_of_ne_zero (fun h => hn (by simp [h]))
  have := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f, hf⟩ := exists_ne (0 : IntertwiningMap X.ρ (tensorPowerRep ℂ ρ n))
  exact ⟨n, f, (IsIrreducible.injective_or_eq_zero f).resolve_right hf⟩

end Problem326

end UndergradKB.RepresentationTheory
