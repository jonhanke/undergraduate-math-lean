import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurWeyl

/-! # Polynomial and rational representations of `GL_N(k)` (Etingof et al., Definition 4.65)

A representation of `GL_N(k)` is *polynomial* when the coefficient functions `g ↦ φ (ρ g w)` are polynomial
functions of the matrix entries of `g`, and *rational* when they are polynomial in the entries and `1 / det g`.

* `polyFunctions`, `ratFunctions`: the two subalgebras of `GL_N(k) → k`.
* `IsPolynomialRep`, `IsRationalRep`: basis-free definitions, with the matrix formulation proved equivalent
  (`isPolynomialRep_iff_forall_basis`, `isPolynomialRep_iff_exists_polynomials`, and the rational analogues).
* Examples and closure: the standard representation, powers of the determinant, tensor products, duals,
  subrepresentations and quotients, tensor powers.
* `IsPolynomialRep.isRationalRep`, `IsRationalRep.exists_polynomial_tprod_detPow`: polynomial implies rational and
  a rational representation becomes polynomial after twisting by a high enough power of the determinant.

Missing for the full statement of Definition 4.65 (classification of the irreducibles by highest weights
`λ₁ ≥ ⋯ ≥ λ_N`): the weight theory of the diagonal torus on rational representations and the highest weight
vector argument; that part is not formalized here.
-/

namespace UndergradKB.RepresentationTheory

open Matrix MvPolynomial PiTensorProduct
open scoped TensorProduct

section Functions

variable (N : ℕ) (k : Type*) [Field k]

/-- The matrix entries of `g ∈ GL_N(k)`, indexed by pairs. -/
def glEntries (g : GL (Fin N) k) : Fin N × Fin N → k := fun p => (g : Matrix (Fin N) (Fin N) k) p.1 p.2

/-- The generic determinant, as a polynomial in the matrix entries. -/
noncomputable def detPoly : MvPolynomial (Fin N × Fin N) k := (mvPolynomialX (Fin N) (Fin N) k).det

variable {N k}

theorem eval_detPoly (g : GL (Fin N) k) :
    eval (glEntries N k g) (detPoly N k) = (g : Matrix (Fin N) (Fin N) k).det := by
  rw [detPoly, eval_det_mvPolynomialX]
  congr 1

theorem det_ne_zero' (g : GL (Fin N) k) : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
  Matrix.GeneralLinearGroup.det_ne_zero g

variable (N k)

/-- The functions `GL_N(k) → k` that are polynomials in the matrix entries. -/
def polyFunctions : Subalgebra k (GL (Fin N) k → k) where
  carrier := {f | ∃ P : MvPolynomial (Fin N × Fin N) k, ∀ g, f g = eval (glEntries N k g) P}
  mul_mem' := by
    rintro _ _ ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, fun g => by simp [hP, hQ]⟩
  add_mem' := by
    rintro _ _ ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun g => by simp [hP, hQ]⟩
  algebraMap_mem' := fun r => ⟨C r, fun g => by simp⟩

/-- Functions of the form `P(g) / det(g)^m`, for a fixed exponent `m`. -/
def ratAt (m : ℕ) : Set (GL (Fin N) k → k) :=
  {f | ∃ P : MvPolynomial (Fin N × Fin N) k,
    ∀ g, f g = eval (glEntries N k g) P / (g : Matrix (Fin N) (Fin N) k).det ^ m}

variable {N k}

theorem ratAt_mono {m m' : ℕ} (h : m ≤ m') : ratAt N k m ⊆ ratAt N k m' := by
  rintro f ⟨P, hP⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨P * detPoly N k ^ j, fun g => ?_⟩
  have := det_ne_zero' g
  rw [hP g, map_mul, map_pow, eval_detPoly, pow_add]
  field_simp

variable (N k)

/-- The functions `GL_N(k) → k` that are polynomials in the matrix entries and `1 / det`. -/
def ratFunctions : Subalgebra k (GL (Fin N) k → k) where
  carrier := {f | ∃ m, f ∈ ratAt N k m}
  mul_mem' := by
    rintro _ _ ⟨m, P, hP⟩ ⟨n, Q, hQ⟩
    refine ⟨m + n, P * Q, fun g => ?_⟩
    simp only [Pi.mul_apply, hP, hQ, map_mul, pow_add]
    field_simp
  add_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨P, hP⟩ := ratAt_mono (le_max_left m n) hm
    obtain ⟨Q, hQ⟩ := ratAt_mono (le_max_right m n) hn
    exact ⟨max m n, P + Q, fun g => by simp [hP, hQ, add_div]⟩
  algebraMap_mem' := fun r => ⟨0, C r, fun g => by simp⟩

variable {N k}

theorem mem_polyFunctions_iff (f : GL (Fin N) k → k) :
    f ∈ polyFunctions N k ↔ ∃ P : MvPolynomial (Fin N × Fin N) k, ∀ g, f g = eval (glEntries N k g) P :=
  Iff.rfl

theorem mem_ratFunctions_iff (f : GL (Fin N) k → k) :
    f ∈ ratFunctions N k ↔ ∃ (P : MvPolynomial (Fin N × Fin N) k) (m : ℕ),
      ∀ g, f g = eval (glEntries N k g) P / (g : Matrix (Fin N) (Fin N) k).det ^ m := by
  constructor
  · rintro ⟨m, P, hP⟩
    exact ⟨P, m, hP⟩
  · rintro ⟨P, m, hP⟩
    exact ⟨m, P, hP⟩

theorem polyFunctions_le_ratFunctions : polyFunctions N k ≤ ratFunctions N k := by
  rintro f ⟨P, hP⟩
  exact ⟨0, P, fun g => by simp [hP]⟩

/-- A polynomial in functions lying in a subalgebra lies in the subalgebra. -/
theorem eval_mem_subalgebra (S : Subalgebra k (GL (Fin N) k → k))
    (F : Fin N × Fin N → GL (Fin N) k → k) (hF : ∀ p, F p ∈ S) (P : MvPolynomial (Fin N × Fin N) k) :
    (fun g => eval (fun p => F p g) P) ∈ S := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have := S.algebraMap_mem a
    convert this using 1
    funext g
    simp
  | add p q hp hq =>
    have := S.add_mem hp hq
    convert this using 1
    funext g
    simp
  | mul_X p i hp =>
    have := S.mul_mem hp (hF i)
    convert this using 1
    funext g
    simp

theorem glEntries_mem_polyFunctions (p : Fin N × Fin N) :
    (fun g => glEntries N k g p) ∈ polyFunctions N k :=
  ⟨X p, fun g => by simp⟩

theorem det_mem_polyFunctions :
    (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k).det) ∈ polyFunctions N k :=
  ⟨detPoly N k, fun g => (eval_detPoly g).symm⟩

/-- The entries of `g⁻¹` are rational functions of `g` (adjugate over determinant). -/
theorem glEntries_inv_mem_ratFunctions (p : Fin N × Fin N) :
    (fun g : GL (Fin N) k => glEntries N k g⁻¹ p) ∈ ratFunctions N k := by
  refine ⟨1, (mvPolynomialX (Fin N) (Fin N) k).adjugate p.1 p.2, fun g => ?_⟩
  have h1 : eval (glEntries N k g) ((mvPolynomialX (Fin N) (Fin N) k).adjugate p.1 p.2)
      = (g : Matrix (Fin N) (Fin N) k).adjugate p.1 p.2 := by
    have := congrFun (congrFun
      (RingHom.map_adjugate (eval (glEntries N k g)) (mvPolynomialX (Fin N) (Fin N) k)) p.1) p.2
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    have h2 : (eval (glEntries N k g)).mapMatrix (mvPolynomialX (Fin N) (Fin N) k) = (g : Matrix _ _ k) :=
      mvPolynomialX_mapMatrix_eval (g : Matrix (Fin N) (Fin N) k)
    simp only [RingHom.mapMatrix_apply] at h2
    rw [h2]
  rw [h1]
  simp only [glEntries, Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Matrix.smul_apply,
    Ring.inverse_eq_inv', smul_eq_mul, pow_one]
  field_simp

/-- Composition with inversion sends rational functions to rational functions. -/
theorem ratFunctions_comp_inv {f : GL (Fin N) k → k} (hf : f ∈ ratFunctions N k) :
    (fun g => f g⁻¹) ∈ ratFunctions N k := by
  obtain ⟨P, m, hP⟩ := (mem_ratFunctions_iff f).mp hf
  have h1 := eval_mem_subalgebra (ratFunctions N k) (fun p g => glEntries N k g⁻¹ p)
    glEntries_inv_mem_ratFunctions P
  have h2 := (ratFunctions N k).pow_mem
    (polyFunctions_le_ratFunctions (det_mem_polyFunctions (N := N) (k := k))) m
  have := (ratFunctions N k).mul_mem h1 h2
  convert this using 1
  funext g
  have hd := det_ne_zero' g
  have h3 : (g⁻¹ : GL (Fin N) k).val.det = ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv]
    simp [Ring.inverse_eq_inv']
  rw [hP g⁻¹, h3]
  simp [inv_pow]

end Functions

section Defs

variable {N : ℕ} {k : Type*} [Field k] {W : Type*} [AddCommMonoid W] [Module k W]

/-- Coefficient functions of `ρ` all lie in the subalgebra `S` of functions on `GL_N(k)`. -/
def IsSRep (S : Subalgebra k (GL (Fin N) k → k)) (ρ : Representation k (GL (Fin N) k) W) : Prop :=
  ∀ (w : W) (φ : Module.Dual k W), (fun g => φ (ρ g w)) ∈ S

/-- A representation of `GL_N(k)` is *polynomial* if all its coefficient functions `g ↦ φ (ρ g w)` are polynomials
in the entries of `g`. For finite-dimensional `W` this says that the matrix entries in some (equivalently any)
basis are polynomials in the entries `g_ij` (`isPolynomialRep_iff_exists_polynomials`). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
def IsPolynomialRep (ρ : Representation k (GL (Fin N) k) W) : Prop := IsSRep (polyFunctions N k) ρ

/-- A representation of `GL_N(k)` is *rational* if all its coefficient functions are polynomials in the entries of
`g` and `1 / det g`. For finite-dimensional `W` the matrix entries in some (equivalently any) basis have the form
`P (g) / det (g) ^ m` (`isRationalRep_iff_exists_polynomials`). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
def IsRationalRep (ρ : Representation k (GL (Fin N) k) W) : Prop := IsSRep (ratFunctions N k) ρ

end Defs

section Reps

variable {N : ℕ} {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

variable {S : Subalgebra k (GL (Fin N) k → k)} {ρ : Representation k (GL (Fin N) k) W}

theorem isSRep_iff_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι k W) :
    IsSRep S ρ ↔ ∀ i j, (fun g => b.repr (ρ g (b j)) i) ∈ S := by
  constructor
  · intro h i j
    simpa using h (b j) (b.coord i)
  · intro h w φ
    have key : (fun g => φ (ρ g w)) =
        ∑ j, b.repr w j • ∑ i, φ (b i) • (fun g => b.repr (ρ g (b j)) i) := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => rw [← b.sum_repr w]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have e := congrArg φ (b.sum_repr (ρ g (b j)))
      rw [map_sum] at e
      simp only [map_smul, smul_eq_mul] at e
      rw [← e]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [key]
    exact S.sum_mem fun j _ => S.smul_mem (S.sum_mem fun i _ => S.smul_mem (h i j) _) _

/-- Basis independence: for a finite-dimensional representation the polynomiality of the matrix entries in one
basis is equivalent to that in every basis. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_iff_forall_basis [FiniteDimensional k W] :
    IsPolynomialRep ρ ↔ ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι k W) (i j : ι),
      (fun g => b.repr (ρ g (b j)) i) ∈ polyFunctions N k := by
  constructor
  · intro h ι _ b
    exact (isSRep_iff_basis b).mp h
  · intro h
    exact (isSRep_iff_basis (Module.finBasis k W)).mpr fun i j => h _ _ i j

theorem isPolynomialRep_iff_exists_basis [FiniteDimensional k W] :
    IsPolynomialRep ρ ↔ ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι k W), ∀ i j,
      (fun g => b.repr (ρ g (b j)) i) ∈ polyFunctions N k := by
  rw [isPolynomialRep_iff_forall_basis]
  constructor
  · intro h
    exact ⟨_, inferInstance, Module.finBasis k W, h _ _⟩
  · rintro ⟨ι, _, b, hb⟩ ι' _ b'
    exact (isSRep_iff_basis b').mp ((isSRep_iff_basis b).mpr hb)

theorem isRationalRep_iff_forall_basis [FiniteDimensional k W] :
    IsRationalRep ρ ↔ ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι k W) (i j : ι),
      (fun g => b.repr (ρ g (b j)) i) ∈ ratFunctions N k := by
  constructor
  · intro h ι _ b
    exact (isSRep_iff_basis b).mp h
  · intro h
    exact (isSRep_iff_basis (Module.finBasis k W)).mpr fun i j => h _ _ i j

/-- Matrix form of polynomiality: in a basis, the matrix of `ρ g` has entries `P_ij (g_ab)` for polynomials
`P_ij` independent of `g`. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_iff_exists_polynomials {ι : Type*} [Fintype ι] (b : Module.Basis ι k W) :
    IsPolynomialRep ρ ↔ ∃ P : ι → ι → MvPolynomial (Fin N × Fin N) k,
      ∀ (g : GL (Fin N) k) i j, b.repr (ρ g (b j)) i = eval (glEntries N k g) (P i j) := by
  rw [IsPolynomialRep, isSRep_iff_basis b]
  constructor
  · intro h
    choose P hP using fun i j => h i j
    exact ⟨P, fun g i j => hP i j g⟩
  · rintro ⟨P, hP⟩ i j
    exact ⟨P i j, fun g => hP g i j⟩

/-- Matrix form of rationality: in a basis, the matrix of `ρ g` has entries `P_ij (g) / det (g) ^ m` for
polynomials `P_ij` and one exponent `m`. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isRationalRep_iff_exists_polynomials {ι : Type*} [Fintype ι] (b : Module.Basis ι k W) :
    IsRationalRep ρ ↔ ∃ (m : ℕ) (P : ι → ι → MvPolynomial (Fin N × Fin N) k),
      ∀ (g : GL (Fin N) k) i j, b.repr (ρ g (b j)) i =
        eval (glEntries N k g) (P i j) / (g : Matrix (Fin N) (Fin N) k).det ^ m := by
  rw [IsRationalRep, isSRep_iff_basis b]
  constructor
  · intro h
    choose P m hP using fun i j => (mem_ratFunctions_iff _).mp (h i j)
    refine ⟨Finset.univ.sup fun p : ι × ι => m p.1 p.2, ?_⟩
    have hmem : ∀ i j, (fun g => b.repr (ρ g (b j)) i) ∈
        ratAt N k (Finset.univ.sup fun p : ι × ι => m p.1 p.2) := fun i j =>
      ratAt_mono (Finset.le_sup (f := fun p : ι × ι => m p.1 p.2) (Finset.mem_univ (i, j)))
        ⟨P i j, hP i j⟩
    choose Q hQ using hmem
    exact ⟨Q, fun g i j => hQ i j g⟩
  · rintro ⟨m, P, hP⟩ i j
    exact (mem_ratFunctions_iff _).mpr ⟨P i j, m, fun g => hP g i j⟩

/-- A subalgebra inclusion transfers coefficient conditions. -/
theorem IsSRep.mono {S' : Subalgebra k (GL (Fin N) k → k)} (hS : S ≤ S') (h : IsSRep S ρ) : IsSRep S' ρ :=
  fun w φ => hS (h w φ)

/-- Every polynomial representation is rational. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsPolynomialRep.isRationalRep (h : IsPolynomialRep ρ) : IsRationalRep ρ :=
  IsSRep.mono polyFunctions_le_ratFunctions h

end Reps

section Closure

variable {N : ℕ} {k : Type*} [Field k]
variable {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
variable {S : Subalgebra k (GL (Fin N) k → k)}

/-- Coefficient conditions pull back along an injective equivariant map. -/
theorem IsSRep.of_injective {ρ : Representation k (GL (Fin N) k) W} {ρ' : Representation k (GL (Fin N) k) W'}
    (f : W →ₗ[k] W') (hf : Function.Injective f) (hcomm : ∀ g w, f (ρ g w) = ρ' g (f w))
    (h : IsSRep S ρ') : IsSRep S ρ := by
  intro w φ
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  have := h (f w) (φ ∘ₗ l)
  convert this using 2 with g
  simp only [LinearMap.comp_apply, ← hcomm]
  exact (congrArg φ (LinearMap.congr_fun hl _)).symm

/-- `IsSRep.of_injective` for a source that is only given as an additive monoid (a vector space without a chosen
negation, such as a space of module maps). -/
theorem IsSRep.of_injective_of_monoid {V : Type*} [AddCommMonoid V] [Module k V]
    {ρ : Representation k (GL (Fin N) k) V} {ρ' : Representation k (GL (Fin N) k) W'}
    (f : V →ₗ[k] W') (hf : Function.Injective f) (hcomm : ∀ g w, f (ρ g w) = ρ' g (f w))
    (h : IsSRep S ρ') : IsSRep S ρ := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  exact IsSRep.of_injective (W := V) f hf hcomm h

/-- Coefficient conditions push forward along a surjective equivariant map. -/
theorem IsSRep.of_surjective {ρ : Representation k (GL (Fin N) k) W} {ρ' : Representation k (GL (Fin N) k) W'}
    (f : W →ₗ[k] W') (hf : Function.Surjective f) (hcomm : ∀ g w, f (ρ g w) = ρ' g (f w))
    (h : IsSRep S ρ) : IsSRep S ρ' := by
  intro w' φ
  obtain ⟨w, rfl⟩ := hf w'
  have := h w (φ ∘ₗ f)
  convert this using 2 with g
  simp [hcomm]

/-- A subrepresentation of a polynomial (rational) representation is polynomial (rational). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsSRep.subrepresentation {ρ : Representation k (GL (Fin N) k) W} (h : IsSRep S ρ)
    (U : Submodule k W) (hU : ∀ g, U ≤ U.comap (ρ g)) : IsSRep S (ρ.subrepresentation U hU) :=
  IsSRep.of_injective U.subtype U.injective_subtype (fun _ _ => rfl) h

/-- A quotient of a polynomial (rational) representation is polynomial (rational). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsSRep.quotient {ρ : Representation k (GL (Fin N) k) W} (h : IsSRep S ρ)
    (U : Submodule k W) (hU : ∀ g, U ≤ U.comap (ρ g)) : IsSRep S (ρ.quotient U hU) :=
  IsSRep.of_surjective U.mkQ (Submodule.mkQ_surjective U) (fun _ _ => rfl) h

/-- Tensor products of polynomial (rational) representations are polynomial (rational). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsSRep.tprod {ρ : Representation k (GL (Fin N) k) W} {ρ' : Representation k (GL (Fin N) k) W'}
    [FiniteDimensional k W] [FiniteDimensional k W'] (h : IsSRep S ρ) (h' : IsSRep S ρ') :
    IsSRep S (ρ.tprod ρ') := by
  have b1 := Module.finBasis k W
  have b2 := Module.finBasis k W'
  rw [isSRep_iff_basis ((Module.finBasis k W).tensorProduct (Module.finBasis k W'))]
  rintro ⟨i, i'⟩ ⟨j, j'⟩
  have e1 := (isSRep_iff_basis (Module.finBasis k W)).mp h i j
  have e2 := (isSRep_iff_basis (Module.finBasis k W')).mp h' i' j'
  have := S.mul_mem e2 e1
  convert this using 1
  funext g
  simp [Module.Basis.tensorProduct_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply]

theorem IsPolynomialRep.tprod {ρ : Representation k (GL (Fin N) k) W} {ρ' : Representation k (GL (Fin N) k) W'}
    [FiniteDimensional k W] [FiniteDimensional k W'] (h : IsPolynomialRep ρ) (h' : IsPolynomialRep ρ') :
    IsPolynomialRep (ρ.tprod ρ') := IsSRep.tprod h h'

theorem IsRationalRep.tprod {ρ : Representation k (GL (Fin N) k) W} {ρ' : Representation k (GL (Fin N) k) W'}
    [FiniteDimensional k W] [FiniteDimensional k W'] (h : IsRationalRep ρ) (h' : IsRationalRep ρ') :
    IsRationalRep (ρ.tprod ρ') := IsSRep.tprod h h'

/-- The dual of a (finite-dimensional) rational representation is rational. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsRationalRep.dual {ρ : Representation k (GL (Fin N) k) W} [FiniteDimensional k W]
    (h : IsRationalRep ρ) : IsRationalRep ρ.dual := by
  intro f Φ
  obtain ⟨w, rfl⟩ := (Module.evalEquiv k W).surjective Φ
  exact ratFunctions_comp_inv (f := fun g => f (ρ g w)) (h w f)

end Closure

section Examples

variable (N : ℕ) (k : Type*) [Field k]

/-- The standard representation `V = k^N` of `GL_N(k)`. -/
noncomputable def stdRep : Representation k (GL (Fin N) k) (Fin N → k) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.mulVecLin_mul, Module.End.mul_eq_comp]

/-- The `m`-th power of the determinant (`m` an integer) as a one-dimensional representation of `GL_N(k)`. -/
noncomputable def detRep (m : ℤ) : Representation k (GL (Fin N) k) k where
  toFun g := LinearMap.mulLeft k (((Matrix.GeneralLinearGroup.det g) ^ m : kˣ) : k)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp [mul_zpow]

variable {N k}

theorem detRep_coeff (m : ℤ) (w : k) (φ : Module.Dual k k) :
    (fun g => φ (detRep N k m g w)) =
      φ w • fun g : GL (Fin N) k => (((Matrix.GeneralLinearGroup.det g) ^ m : kˣ) : k) := by
  funext g
  simp only [detRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.mulLeft_apply, Pi.smul_apply, smul_eq_mul]
  generalize (((Matrix.GeneralLinearGroup.det g) ^ m : kˣ) : k) = c
  exact (φ.map_smul c w).trans (mul_comm c (φ w))

theorem detPow_mem_polyFunctions (m : ℕ) :
    (fun g : GL (Fin N) k => (((Matrix.GeneralLinearGroup.det g) ^ (m : ℤ) : kˣ) : k))
      ∈ polyFunctions N k :=
  (mem_polyFunctions_iff _).mpr ⟨detPoly N k ^ m, fun g => by simp [eval_detPoly]⟩

/-- The standard representation is polynomial. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_stdRep : IsPolynomialRep (stdRep N k) := by
  rw [IsPolynomialRep, isSRep_iff_basis (Pi.basisFun k (Fin N))]
  intro i j
  refine ⟨X (i, j), fun g => ?_⟩
  simp [stdRep, glEntries]

/-- A nonnegative power of the determinant is a polynomial representation. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_detRep (m : ℕ) : IsPolynomialRep (detRep N k m) := by
  intro w φ
  rw [detRep_coeff]
  exact Subalgebra.smul_mem _ (detPow_mem_polyFunctions m) _

/-- Every integer power of the determinant is a rational representation. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isRationalRep_detRep (m : ℤ) : IsRationalRep (detRep N k m) := by
  intro w φ
  rw [detRep_coeff]
  refine Subalgebra.smul_mem _ ?_ _
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · exact polyFunctions_le_ratFunctions (detPow_mem_polyFunctions n)
  · refine (mem_ratFunctions_iff _).mpr ⟨1, n, fun g => ?_⟩
    have := det_ne_zero' g
    simp [_root_.zpow_neg]

end Examples

section Twist

variable {N : ℕ} {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

/-- A rational representation becomes polynomial after tensoring with a high enough power of the determinant. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem IsRationalRep.exists_polynomial_tprod_detRep {ρ : Representation k (GL (Fin N) k) W}
    [FiniteDimensional k W] (h : IsRationalRep ρ) :
    ∃ m : ℕ, IsPolynomialRep (ρ.tprod (detRep N k m)) := by
  obtain ⟨m, P, hP⟩ := (isRationalRep_iff_exists_polynomials (Module.finBasis k W)).mp h
  refine ⟨m, ?_⟩
  rw [IsPolynomialRep, isSRep_iff_basis ((Module.finBasis k W).tensorProduct
    (Module.Basis.singleton Unit k))]
  rintro ⟨i, u⟩ ⟨j, u'⟩
  refine (mem_polyFunctions_iff _).mpr ⟨P i j, fun g => ?_⟩
  have hd := det_ne_zero' g
  simp only [Module.Basis.tensorProduct_apply, Representation.tprod_apply, TensorProduct.map_tmul,
    Module.Basis.tensorProduct_repr_tmul_apply, hP]
  simp [detRep]
  field_simp

end Twist

section TensorPower

variable (N : ℕ) (k : Type*) [Field k]

/-- The tensor power `V^{⊗n}` of the standard representation `V = k^N`, with `g` acting as `g ⊗ ⋯ ⊗ g`. -/
noncomputable def tensorPowerGL (n : ℕ) :
    Representation k (GL (Fin N) k) (⨂[k] _ : Fin n, Fin N → k) where
  toFun g := tensorPowerMap n (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) k))
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by
    simp only [Units.val_mul, Matrix.mulVecLin_mul, tensorPowerMap_comp]
    rfl

variable {N k}

/-- The tensor power `V^{⊗n}` is a polynomial representation of `GL_N(k)`. -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_tensorPowerGL (n : ℕ) : IsPolynomialRep (tensorPowerGL N k n) := by
  rw [IsPolynomialRep, isSRep_iff_basis (Basis.piTensorProduct
    (fun _ : Fin n => Pi.basisFun k (Fin N)))]
  intro I J
  refine (mem_polyFunctions_iff _).mpr ⟨∏ l : Fin n, X (I l, J l), fun g => ?_⟩
  simp [tensorPowerGL, tensorPowerMap, Basis.piTensorProduct_apply,
    Basis.piTensorProduct_repr_tprod_apply, glEntries]

end TensorPower

section NotPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The diagonal matrix `diag(x, 1, …, 1)` with `x ≠ 0` in the slot `i₀`, as an element of `GL_N(k)`. -/
noncomputable def diagUnit (i₀ : Fin N) (x : k) (hx : x ≠ 0) : GL (Fin N) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (Function.update (1 : Fin N → k) i₀ x)) (by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]
    simpa using hx)

theorem det_diagUnit (i₀ : Fin N) (x : k) (hx : x ≠ 0) :
    ((diagUnit i₀ x hx : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = x := by
  change (Matrix.diagonal (Function.update (1 : Fin N → k) i₀ x)).det = x
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]
  simp

/-- A polynomial function on `GL_N(k)` restricts to a polynomial in one variable along the diagonal matrices
`diag(x, 1, …, 1)`. -/
theorem exists_polynomial_diagUnit (i₀ : Fin N) (P : MvPolynomial (Fin N × Fin N) k) :
    ∃ Q : Polynomial k, ∀ (x : k) (hx : x ≠ 0),
      Polynomial.eval x Q = eval (glEntries N k (diagUnit i₀ x hx)) P := by
  refine ⟨MvPolynomial.aeval (fun p : Fin N × Fin N =>
    if p.1 = p.2 then (if p.1 = i₀ then Polynomial.X else 1) else 0) P, fun x hx => ?_⟩
  have h1 : ∀ p : Fin N × Fin N, glEntries N k (diagUnit i₀ x hx) p =
      Polynomial.eval x (if p.1 = p.2 then (if p.1 = i₀ then Polynomial.X else 1) else 0) := by
    rintro ⟨a, b⟩
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = i₀
      · subst ha
        simp [glEntries, diagUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero]
      · simp [glEntries, diagUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, ha]
    · simp [glEntries, diagUnit, Matrix.GeneralLinearGroup.mkOfDetNeZero, hab]
  have h2 := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom x) (algebraMap k (Polynomial k))
    (fun p : Fin N × Fin N => if p.1 = p.2 then (if p.1 = i₀ then Polynomial.X else 1) else 0) P
  have h3 : (Polynomial.evalRingHom x).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext; simp
  rw [h3] at h2
  rw [MvPolynomial.aeval_def]
  show Polynomial.evalRingHom x _ = _
  rw [h2]
  simp only [MvPolynomial.eval]
  congr 1
  funext p
  exact (h1 p).symm

/-- The inverse of the determinant is not a polynomial representation (for `N ≥ 1` over an infinite field). -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem not_isPolynomialRep_detRep_neg [Infinite k] (hN : 0 < N) (m : ℕ) (hm : 0 < m) :
    ¬ IsPolynomialRep (detRep N k (-(m : ℤ))) := by
  intro h
  have h1 := h 1 LinearMap.id
  rw [detRep_coeff] at h1
  obtain ⟨P, hP⟩ := h1
  obtain ⟨Q, hQ⟩ := exists_polynomial_diagUnit (⟨0, hN⟩ : Fin N) P
  have hroot : ∀ x : k, x ≠ 0 → (Q * Polynomial.X ^ m - 1).IsRoot x := by
    intro x hx
    have e := hP (diagUnit ⟨0, hN⟩ x hx)
    rw [← hQ x hx] at e
    have hd : (((Matrix.GeneralLinearGroup.det (diagUnit ⟨0, hN⟩ x hx)) : kˣ) : k) = x :=
      det_diagUnit _ x hx
    simp only [LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, one_mul, _root_.zpow_neg, zpow_natCast,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hd] at e
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, ← e]
    field_simp
    simp
  have hzero : Q * Polynomial.X ^ m - 1 = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine ((Set.infinite_univ (α := k)).sdiff (Set.finite_singleton (0 : k))).mono ?_
    intro x hx
    exact hroot x hx.2
  have := congrArg (Polynomial.eval 0) hzero
  simp [hm.ne'] at this

end NotPolynomial

section Pi

variable {N : ℕ} {k : Type*} [Field k] {ι : Type*} (X : ι → Type*) [∀ i, AddCommGroup (X i)]
  [∀ i, Module k (X i)]

/-- The product of a family of representations of `GL_N(k)`. -/
noncomputable def piRep (ρ : ∀ i, Representation k (GL (Fin N) k) (X i)) :
    Representation k (GL (Fin N) k) (∀ i, X i) where
  toFun g := LinearMap.pi fun i => (ρ i g) ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp [Module.End.one_eq_id]
  map_mul' g h := by
    ext x i
    simp [Module.End.mul_eq_comp]

variable {X}

/-- A finite product of polynomial (rational) representations is polynomial (rational). -/
theorem IsSRep.pi [Fintype ι] [DecidableEq ι] {S : Subalgebra k (GL (Fin N) k → k)}
    {ρ : ∀ i, Representation k (GL (Fin N) k) (X i)} (h : ∀ i, IsSRep S (ρ i)) :
    IsSRep S (piRep X ρ) := by
  intro w φ
  have key : (fun g => φ (piRep X ρ g w)) =
      ∑ i, (fun g => (φ ∘ₗ LinearMap.single k X i) (ρ i g (w i))) := by
    funext g
    simp only [Finset.sum_apply]
    conv_lhs => rw [← Finset.univ_sum_single (piRep X ρ g w)]
    rw [map_sum]
    rfl
  rw [key]
  exact S.sum_mem fun i _ => h i _ _

end Pi

section SchurWeylPolynomial

variable (N n : ℕ)

/-- The Schur-Weyl multiplicity space `Hom_{S_n}(V_λ, V^{⊗n})`, with `V = ℂ^N`, is a polynomial
representation of `GL_N(ℂ)`: the action is `swRep` pulled back along `GL_N(ℂ) → GL(ℂ^N)`. -/
noncomputable def swRepGL (la : DiagramsOfSize n) : Representation ℂ (GL (Fin N) ℂ)
    (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule (Fin N → ℂ) n) :=
  (swRep (V := Fin N → ℂ) n la).comp (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := ℂ)).toMonoidHom

@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem isPolynomialRep_swRepGL (la : DiagramsOfSize n) : IsPolynomialRep (k := ℂ) (N := N) (swRepGL N n la) := by
  let b := Module.finBasis ℂ (spechtModule la)
  let F : (spechtModule la →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule (Fin N → ℂ) n) →ₗ[ℂ]
      (Fin (Module.finrank ℂ (spechtModule la)) → ⨂[ℂ] _ : Fin n, Fin N → ℂ) :=
    { toFun := fun f i => f (b i)
      map_add' := fun f f' => rfl
      map_smul' := fun c f => rfl }
  refine IsSRep.of_injective_of_monoid F ?_ ?_
    (IsSRep.pi (X := fun _ => ⨂[ℂ] _ : Fin n, Fin N → ℂ) (fun _ => isPolynomialRep_tensorPowerGL n))
  · intro f f' h
    have h' : f.restrictScalars ℂ = f'.restrictScalars ℂ :=
      b.ext fun i => congrFun h i
    exact LinearMap.ext fun x => LinearMap.congr_fun h' x
  · intro g f
    funext i
    rfl

end SchurWeylPolynomial


end UndergradKB.RepresentationTheory
