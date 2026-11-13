import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dual.Lemmas
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Characters
import UndergradKB.RepresentationTheory.ProblemsGL

/-! # Problem 3.26 (symmetric power form)

The symmetric power `S^n V` of `V = ℂ^N` is modelled, as in `ProblemsGL.lean`, by the homogeneous polynomials of
degree `n` in `N` variables, the variable `X_j` standing for the basis vector `e_j` and a matrix `M` acting by
`X_j ↦ ∑_i M_{ij} X_i` (so that `e_j ↦ ∑_i M_{ij} e_i`).  For a representation `ρ : G → GL_N(ℂ)` the
representation on `S^n V` is `symRep ∘ ρ`.

We show that for a faithful `ρ` of a finite group, every irreducible representation embeds into some `S^n V`.
The proof follows the book's hint: a point `u` whose orbit under `G` has `|G|` distinct points, the evaluation map
from polynomials onto functions on `G`, and a lift of the intertwiner `X → Fun(G)` obtained by averaging.
-/

namespace UndergradKB.RepresentationTheory

open MvPolynomial

section Sym

variable {N : ℕ}

lemma aeval_substAlg (M : Matrix (Fin N) (Fin N) ℂ) (p : Fin N → ℂ) (f : MvPolynomial (Fin N) ℂ) :
    aeval p (substAlg N M f) = aeval (Matrix.vecMul p M) f := by
  have : (aeval p).comp (substAlg N M) = aeval (Matrix.vecMul p M) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [substAlg_X, Matrix.vecMul, dotProduct, mul_comm]
  exact AlgHom.congr_fun this f

lemma substAlg_isHomogeneous (M : Matrix (Fin N) (Fin N) ℂ) {f : MvPolynomial (Fin N) ℂ} {n : ℕ}
    (hf : f.IsHomogeneous n) : (substAlg N M f).IsHomogeneous n := by
  have h1 : (substAlg N M f).IsHomogeneous (1 * n) :=
    IsHomogeneous.aeval hf _ (fun j => IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using isHomogeneous_C_mul_X (R := ℂ) (M i j) i)
  simpa using h1

lemma homogeneousComponent_substAlg (M : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) (f : MvPolynomial (Fin N) ℂ) :
    homogeneousComponent m (substAlg N M f) = substAlg N M (homogeneousComponent m f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have hm : (monomial d a).IsHomogeneous d.degree := isHomogeneous_monomial a rfl
    have hm' : substAlg N M (monomial d a) ∈ homogeneousSubmodule (Fin N) ℂ d.degree :=
      (mem_homogeneousSubmodule _ _).mpr (substAlg_isHomogeneous M hm)
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hm),
      homogeneousComponent_of_mem hm']
    split_ifs <;> simp
  | add p q hp hq => simp [map_add, hp, hq]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

lemma exists_point_injective (ρ : G →* GL (Fin N) ℂ) (hρ : Function.Injective ρ) :
    ∃ u : Fin N → ℂ, Function.Injective fun g : G ↦
      Matrix.vecMul u (ρ g : Matrix (Fin N) (Fin N) ℂ) := by
  classical
  let pairs : Finset (G × G) := Finset.univ.filter fun q ↦ q.1 ≠ q.2
  let S : Finset (Subspace ℂ (Fin N → ℂ)) := pairs.image fun q ↦
    LinearMap.ker (Matrix.vecMulLinear ((ρ q.1 : Matrix (Fin N) (Fin N) ℂ) - (ρ q.2 : Matrix (Fin N) (Fin N) ℂ)))
  have hS : (⊤ : Subspace ℂ (Fin N → ℂ)) ∉ S := by
    intro h
    obtain ⟨q, hq, hker⟩ := Finset.mem_image.mp h
    have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
    have hne' : (ρ q.1 : Matrix (Fin N) (Fin N) ℂ) ≠ ρ q.2 := fun h' ↦ hne (hρ (Units.ext h'))
    obtain ⟨i, j, hij⟩ : ∃ i j, ((ρ q.1 : Matrix (Fin N) (Fin N) ℂ) - ρ q.2) i j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne' (sub_eq_zero.mp (Matrix.ext hc))
    have hmem : (Pi.single i (1 : ℂ) : Fin N → ℂ) ∈ LinearMap.ker (Matrix.vecMulLinear
        ((ρ q.1 : Matrix (Fin N) (Fin N) ℂ) - (ρ q.2 : Matrix (Fin N) (Fin N) ℂ))) := by
      rw [hker]; trivial
    have := congrFun (LinearMap.mem_ker.mp hmem) j
    apply hij
    simpa [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.single_apply] using this
  obtain ⟨u, hu⟩ : ∃ u : Fin N → ℂ, u ∉ ⋃ p ∈ S, (p : Set (Fin N → ℂ)) := by
    by_contra hc
    push Not at hc
    exact Subspace.biUnion_ne_univ_of_top_notMem hS (Set.eq_univ_of_forall hc)
  refine ⟨u, fun g g' h ↦ ?_⟩
  by_contra hne
  apply hu
  simp only [Set.mem_iUnion]
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ (g, g'), hne⟩), ?_⟩
  show u ∈ LinearMap.ker _
  rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply, Matrix.vecMul_sub]
  exact sub_eq_zero.mpr h

lemma exists_poly_single (pt : G → Fin N → ℂ) (hpt : Function.Injective pt) (g0 : G) :
    ∃ f : MvPolynomial (Fin N) ℂ, ∀ g, aeval (pt g) f = if g = g0 then 1 else 0 := by
  have hj : ∀ g, g ≠ g0 → ∃ j, pt g0 j ≠ pt g j := by
    intro g hg
    by_contra hc
    push Not at hc
    exact hg (hpt (funext fun j ↦ (hc j).symm))
  choose j hj using hj
  refine ⟨∏ g : {g : G // g ≠ g0}, (X (j g.1 g.2) - C (pt g.1 (j g.1 g.2))) *
    C ((pt g0 (j g.1 g.2) - pt g.1 (j g.1 g.2))⁻¹), ?_⟩
  intro g1
  simp only [map_prod, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · subst h
    refine Finset.prod_eq_one fun g _ ↦ ?_
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (hj g.1 g.2))
  · exact Finset.prod_eq_zero (Finset.mem_univ ⟨g1, h⟩) (by simp)

/-- Evaluation of polynomials at the points `pt g`. -/
noncomputable def evalOrbit (pt : G → Fin N → ℂ) : MvPolynomial (Fin N) ℂ →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi fun g ↦ (aeval (pt g)).toLinearMap

lemma evalOrbit_surjective (pt : G → Fin N → ℂ) (hpt : Function.Injective pt) :
    Function.Surjective (evalOrbit pt) := by
  intro F
  choose f hf using exists_poly_single pt hpt
  refine ⟨∑ g0, F g0 • f g0, ?_⟩
  ext g
  simp [evalOrbit, map_sum, hf, Finset.sum_apply]

/-- The algebra map `substAlg` of `ρ h`, as a linear map. -/
noncomputable def substLin (ρ : G →* GL (Fin N) ℂ) (h : G) :
    MvPolynomial (Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N) ℂ :=
  (substAlg N (ρ h : Matrix (Fin N) (Fin N) ℂ)).toLinearMap

lemma substLin_mul (ρ : G →* GL (Fin N) ℂ) (a b : G) (y : MvPolynomial (Fin N) ℂ) :
    substLin ρ (a * b) y = substLin ρ a (substLin ρ b y) := by
  simp [substLin, map_mul, substAlg_mul]

lemma evalOrbit_substLin (ρ : G →* GL (Fin N) ℂ) (u : Fin N → ℂ) (h g : G) (f : MvPolynomial (Fin N) ℂ) :
    evalOrbit (fun g : G ↦ Matrix.vecMul u (ρ g : Matrix (Fin N) (Fin N) ℂ)) (substLin ρ h f) g =
      evalOrbit (fun g : G ↦ Matrix.vecMul u (ρ g : Matrix (Fin N) (Fin N) ℂ)) f (g * h) := by
  simp [evalOrbit, substLin, aeval_substAlg, Matrix.vecMul_vecMul, map_mul]

/-- There is a nonzero equivariant linear map from an irreducible representation to the polynomial ring
(with `G` acting by `substAlg ∘ ρ`), assuming `ρ` is faithful. -/
theorem exists_intertwining_polynomial (ρ : G →* GL (Fin N) ℂ) (hρ : Function.Injective ρ)
    (X : IrrRep ℂ G) :
    ∃ L : X.V →ₗ[ℂ] MvPolynomial (Fin N) ℂ, L ≠ 0 ∧ ∀ k x, L (X.ρ k x) = substLin ρ k (L x) := by
  obtain ⟨u, hu⟩ := exists_point_injective ρ hρ
  generalize hpt : (fun g : G ↦ Matrix.vecMul u (ρ g : Matrix (Fin N) (Fin N) ℂ)) = pt at hu
  have hev : ∀ h g f, evalOrbit pt (substLin ρ h f) g = evalOrbit pt f (g * h) := by
    subst hpt; exact fun h g f ↦ evalOrbit_substLin ρ u h g f
  have hsurj := evalOrbit_surjective pt hu
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (evalOrbit pt)
    (LinearMap.range_eq_top.mpr hsurj)
  -- a nonzero functional
  have hnt : Nontrivial X.V := by
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hd := finrank_ne_zero_of_isIrreducible (ρ := X.ρ)
    exact Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero fun h0 ↦ hd (by rw [h0, Nat.cast_zero]))
  obtain ⟨x0, hx0⟩ := exists_ne (0 : X.V)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Module.Dual ℂ X.V, ξ x0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff ℂ x0).mp hc)
  let Φ : X.V →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun g ↦ ξ ∘ₗ (X.ρ g)
  have hΦ : ∀ h x g, Φ (X.ρ h x) g = Φ x (g * h) := by
    intro h x g
    simp [Φ, map_mul]
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let L : X.V →ₗ[ℂ] MvPolynomial (Fin N) ℂ :=
    (Nat.card G : ℂ)⁻¹ • ∑ h : G, substLin ρ h⁻¹ ∘ₗ s ∘ₗ Φ ∘ₗ (X.ρ h)
  have hLx : ∀ x, L x = (Nat.card G : ℂ)⁻¹ • ∑ h : G, substLin ρ h⁻¹ (s (Φ (X.ρ h x))) := by
    intro x; simp [L]
  have hπs : ∀ y, evalOrbit pt (s y) = y := fun y ↦ LinearMap.congr_fun hs y
  refine ⟨L, ?_, ?_⟩
  · intro h0
    have key : ∀ h : G, evalOrbit pt (substLin ρ h⁻¹ (s (Φ (X.ρ h x0)))) 1 = ξ x0 := by
      intro h
      rw [hev, hπs, hΦ]
      simp [Φ]
    have h1 : evalOrbit pt (L x0) 1 = ξ x0 := by
      rw [hLx, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
      simp only [key, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
        smul_eq_mul]
      field_simp
    rw [h0] at h1
    simp at h1
    exact hξ h1.symm
  · intro k x
    rw [hLx, hLx, map_smul, map_sum]
    refine congrArg (fun t ↦ (Nat.card G : ℂ)⁻¹ • t) ?_
    refine Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h ↦ ?_
    show _ = substLin ρ k (substLin ρ (h * k)⁻¹ (s (Φ (X.ρ (h * k) x))))
    rw [← substLin_mul, show k * (h * k)⁻¹ = h⁻¹ by group, map_mul]
    rfl

/-- The representation of `G` on the symmetric power `S^n V` of `V = ℂ^N`, modelled by the homogeneous
polynomials of degree `n` in `N` variables (variable `X_j` = basis vector `e_j`), with `g` acting through the
matrix `ρ g` by `X_j ↦ ∑_i (ρ g)_{ij} X_i`, i.e. as `S^n (ρ g)`. -/
noncomputable def symPowerRep (ρ : G →* GL (Fin N) ℂ) (n : ℕ) :
    Representation ℂ G (homogeneousSubmodule (Fin N) ℂ n) :=
  (symRep (N := N) (n := n)).comp ρ

/-- **Problem 3.26** (symmetric power form).  Let `ρ : G → GL_N(ℂ)` be a faithful representation of a finite
group (so `V = ℂ^N` is a faithful finite-dimensional complex representation).  Then every irreducible
representation of `G` embeds, by an injective intertwining map, into the symmetric power `S^n V` for some `n`.
Here `S^n V` is the space of homogeneous polynomials of degree `n` in `N` variables with `g` acting by
`symPowerRep ρ n = S^n (ρ g)` (the variable `X_j` is the basis vector `e_j`). -/
@[kb "etingof2011" "Problem 3.26, p. 45"]
theorem exists_injective_intertwining_symPower (ρ : G →* GL (Fin N) ℂ) (hρ : Function.Injective ρ)
    (X : IrrRep ℂ G) :
    ∃ n : ℕ, ∃ f : Representation.IntertwiningMap X.ρ (symPowerRep ρ n), Function.Injective f := by
  obtain ⟨L, hL0, hLeq⟩ := exists_intertwining_polynomial ρ hρ X
  obtain ⟨x0, hx0⟩ := DFunLike.ne_iff.mp hL0
  obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m (L x0) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx0
    rw [LinearMap.zero_apply, ← sum_homogeneousComponent (L x0)]
    exact Finset.sum_eq_zero fun i _ ↦ hc i
  let Lm : X.V →ₗ[ℂ] homogeneousSubmodule (Fin N) ℂ m :=
    LinearMap.codRestrict _ ((homogeneousComponent m : MvPolynomial (Fin N) ℂ →ₗ[ℂ] _) ∘ₗ L)
      fun x ↦ homogeneousComponent_mem m (L x)
  have hf : ∀ (g : G) (v : X.V), Lm (X.ρ g v) = symPowerRep ρ m g (Lm v) := by
    intro g v
    apply Subtype.ext
    change homogeneousComponent m (L (X.ρ g v)) = substAlg N (ρ g : Matrix (Fin N) (Fin N) ℂ)
      (homogeneousComponent m (L v))
    rw [hLeq, ← homogeneousComponent_substAlg]
    rfl
  let f : Representation.IntertwiningMap X.ρ (symPowerRep ρ m) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap X.ρ (symPowerRep ρ m) Lm hf
  refine ⟨m, f, ?_⟩
  refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 ↦ hm ?_
  have := congrArg (fun F : Representation.IntertwiningMap X.ρ (symPowerRep ρ m) ↦
    ((F x0 : homogeneousSubmodule (Fin N) ℂ m) : MvPolynomial (Fin N) ℂ)) h0
  simpa [f, Lm] using this

end Sym

end UndergradKB.RepresentationTheory
