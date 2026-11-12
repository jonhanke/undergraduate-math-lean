import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import UndergradKB.Common.Attr

/-! # Cyclic modules and examples of Lie algebras (Etingof et al., Chapter 1)

* Problem 1.25: `IsCyclicVector`, and `isCyclic_iff_exists_quotient_equiv` (a module is cyclic iff it is
  isomorphic to `A ⧸ I` for a left ideal `I`).
* §1.9: `heisenberg` (strictly upper triangular `3 × 3` matrices as a Lie subalgebra) with the explicit
  basis `heisX`, `heisY`, `heisC`; `aff1X`, `aff1Y` with `[X, Y] = Y`; `sl2E`, `sl2F`, `sl2H` forming an
  `sl₂`-triple in `Matrix (Fin 2) (Fin 2) k`.

The universal enveloping algebra presentation of Example 1.46 is not reachable in Mathlib's current
`UniversalEnvelopingAlgebra` API without a substantial development, so it is not covered here.
-/

namespace UndergradKB.RepresentationTheory

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Cyclic modules -/

section Cyclic

variable (A : Type*) {M : Type*} [Ring A] [AddCommGroup M] [Module A M]

/-- `v` is a cyclic vector of the `A`-module `M` when it generates `M`. -/
@[kb "etingof2011" "Problem 1.25, p. 11"]
def IsCyclicVector (v : M) : Prop := Submodule.span A {v} = ⊤

/-- A module is cyclic if it has a cyclic vector. -/
@[kb "etingof2011" "Problem 1.25, p. 11"]
def IsCyclicModule (A : Type*) (M : Type*) [Ring A] [AddCommGroup M] [Module A M] : Prop :=
  ∃ v : M, IsCyclicVector A v

/-- A module is cyclic iff it is isomorphic to a quotient `A ⧸ I` of the regular module by a left ideal. -/
@[kb "etingof2011" "Problem 1.25, p. 11"]
theorem isCyclic_iff_exists_quotient_equiv :
    IsCyclicModule A M ↔ ∃ I : Ideal A, Nonempty ((A ⧸ I) ≃ₗ[A] M) := by
  constructor
  · rintro ⟨v, hv⟩
    have hsurj : Function.Surjective (LinearMap.toSpanSingleton A M v) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
      exact hv
    exact ⟨_, ⟨(LinearMap.quotKerEquivOfSurjective _ hsurj)⟩⟩
  · rintro ⟨I, ⟨e⟩⟩
    refine ⟨e (Submodule.Quotient.mk 1), ?_⟩
    unfold IsCyclicVector
    rw [Submodule.eq_top_iff']
    intro m
    obtain ⟨q, rfl⟩ := e.surjective m
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I q
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

end Cyclic

/-! ### The Heisenberg Lie algebra -/

section Heisenberg

variable (k : Type*) [CommRing k]

/-- The Heisenberg Lie algebra: strictly upper triangular `3 × 3` matrices, a Lie subalgebra of
`Matrix (Fin 3) (Fin 3) k`. -/
@[kb "etingof2011" "§1.9, p. 16"]
def heisenberg : LieSubalgebra k (Matrix (Fin 3) (Fin 3) k) where
  carrier := {M | ∀ i j, j ≤ i → M i j = 0}
  add_mem' := by
    intro a b ha hb i j hij
    simp [ha i j hij, hb i j hij]
  zero_mem' := by intro i j _; simp
  smul_mem' := by
    intro c a ha i j hij
    simp [ha i j hij]
  lie_mem' := by
    intro a b ha hb i j hij
    simp only [Set.mem_ofPred_eq] at *
    rw [Ring.lie_def]
    have key : ∀ a b : Matrix (Fin 3) (Fin 3) k, (∀ i j, j ≤ i → a i j = 0) →
        (∀ i j, j ≤ i → b i j = 0) → ∀ i j, j ≤ i → (a * b) i j = 0 := by
      intro a b ha hb i j hij
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l ≤ i
      · simp [ha i l hl]
      · have : j ≤ l := le_trans hij (le_of_lt (not_le.mp hl))
        simp [hb l j this]
    simp [key a b ha hb i j hij, key b a hb ha i j hij]

/-- The basis element `x = E₁₂` of the Heisenberg Lie algebra. -/
def heisX : Matrix (Fin 3) (Fin 3) k := Matrix.single 0 1 1
/-- The basis element `y = E₂₃` of the Heisenberg Lie algebra. -/
def heisY : Matrix (Fin 3) (Fin 3) k := Matrix.single 1 2 1
/-- The basis element `c = E₁₃` of the Heisenberg Lie algebra. -/
def heisC : Matrix (Fin 3) (Fin 3) k := Matrix.single 0 2 1

variable {k}

@[kb "etingof2011" "§1.9, p. 16"]
theorem heisX_mem : heisX k ∈ heisenberg k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [heisX, Matrix.single_apply]

@[kb "etingof2011" "§1.9, p. 16"]
theorem heisY_mem : heisY k ∈ heisenberg k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [heisY, Matrix.single_apply]

@[kb "etingof2011" "§1.9, p. 16"]
theorem heisC_mem : heisC k ∈ heisenberg k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [heisC, Matrix.single_apply]

/-- `[x, y] = c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem heis_lie_x_y : ⁅heisX k, heisY k⁆ = heisC k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, heisX, heisY, heisC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- `[x, c] = 0`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem heis_lie_x_c : ⁅heisX k, heisC k⁆ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, heisX, heisC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- `[y, c] = 0`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem heis_lie_y_c : ⁅heisY k, heisC k⁆ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, heisY, heisC, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

/-- A matrix lies in the Heisenberg Lie algebra iff it is a combination `a x + b y + c z` of `x, y, c`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem mem_heisenberg_iff (M : Matrix (Fin 3) (Fin 3) k) :
    M ∈ heisenberg k ↔ ∃ a b c : k, M = a • heisX k + b • heisY k + c • heisC k := by
  constructor
  · intro h
    have h' : ∀ i j, j ≤ i → M i j = 0 := h
    refine ⟨M 0 1, M 1 2, M 0 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisX, heisY, heisC, Matrix.add_apply] <;> exact h' _ _ (by decide)
  · rintro ⟨a, b, c, rfl⟩
    exact add_mem (add_mem ((heisenberg k).smul_mem a (heisX_mem)) ((heisenberg k).smul_mem b heisY_mem))
      ((heisenberg k).smul_mem c heisC_mem)

/-- The matrices `x, y, c` are linearly independent. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem heis_linearIndependent [Nontrivial k] :
    LinearIndependent k ![heisX k, heisY k, heisC k] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three] at hg
  have h01 := congrFun (congrFun hg 0) 1
  have h12 := congrFun (congrFun hg 1) 2
  have h02 := congrFun (congrFun hg 0) 2
  simp [heisX, heisY, heisC, Matrix.single_apply] at h01 h12 h02
  intro i
  fin_cases i <;> simp [h01, h12, h02]

end Heisenberg

/-! ### The Lie algebra aff(1) -/

section Aff

variable (k : Type*) [CommRing k]

/-- `X = E₁₁` in the realisation of `aff(1)` by `2 × 2` matrices. -/
def aff1X : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 0 1
/-- `Y = E₁₂` in the realisation of `aff(1)` by `2 × 2` matrices. -/
def aff1Y : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 1 1

variable {k}

/-- The two-dimensional Lie algebra `aff(1)` has `[X, Y] = Y`. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem aff1_lie_X_Y : ⁅aff1X k, aff1Y k⁆ = aff1Y k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, aff1X, aff1Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

/-- `aff(1)` is not abelian. -/
@[kb "etingof2011" "§1.9, p. 16"]
theorem aff1_lie_ne_zero [Nontrivial k] : ⁅aff1X k, aff1Y k⁆ ≠ 0 := by
  rw [aff1_lie_X_Y]
  intro h
  have := congrFun (congrFun h 0) 1
  simp [aff1Y, Matrix.single_apply] at this

end Aff

/-! ### sl(2) -/

section Sl2

variable (k : Type*) [CommRing k]

/-- `e = E₁₂`. -/
def sl2E : Matrix (Fin 2) (Fin 2) k := !![0, 1; 0, 0]
/-- `f = E₂₁`. -/
def sl2F : Matrix (Fin 2) (Fin 2) k := !![0, 0; 1, 0]
/-- `h = diag(1, -1)`. -/
def sl2H : Matrix (Fin 2) (Fin 2) k := !![1, 0; 0, -1]

variable {k}

/-- The explicit matrices `h, e, f` form an `sl₂`-triple: `[h,e] = 2e`, `[h,f] = -2f`, `[e,f] = h`. -/
@[kb "etingof2011" "§1.9, p. 15"]
theorem isSl2Triple_sl2 [Nontrivial k] [NeZero (2 : k)] :
    IsSl2Triple (sl2H k) (sl2E k) (sl2F k) where
  h_ne_zero := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp [sl2H] at this
  lie_e_f := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ring.lie_def, sl2E, sl2F, sl2H, Matrix.mul_apply, Fin.sum_univ_two]  <;> ring
  lie_h_e_nsmul := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ring.lie_def, sl2E, sl2H, Matrix.mul_apply, Fin.sum_univ_two]  <;> ring
  lie_h_f_nsmul := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ring.lie_def, sl2F, sl2H, Matrix.mul_apply, Fin.sum_univ_two]  <;> ring

/-- The matrices `e, f, h` are traceless, i.e. lie in `sl 2`. -/
@[kb "etingof2011" "§1.9, p. 15"]
theorem sl2_mem_sl :
    sl2E k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k ∧ sl2F k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k ∧
      sl2H k ∈ LieAlgebra.SpecialLinear.sl (Fin 2) k := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [LieAlgebra.SpecialLinear.sl, LieSubalgebra.mem_mk_iff, Matrix.trace, Fin.sum_univ_two,
      sl2E, sl2F, sl2H, Matrix.diag]

end Sl2

end UndergradKB.RepresentationTheory
