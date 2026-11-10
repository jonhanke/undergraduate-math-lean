import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import UndergradKB.Common.Attr

/-! # Hefferon chapter Five (Hefferon-only rows) -/

namespace UndergradKB.LinearAlgebra.Course

open Polynomial

section Poly

variable {K : Type*} [Field K]

/-- With `deg 0 = -∞`, the degree of a product is the sum of the degrees. -/
@[kb "hefferon2020" "Five.I.1.1, p. 408"]
theorem hefferon_Five_I_1_1 (f g : K[X]) : (f * g).degree = f.degree + g.degree :=
  Polynomial.degree_mul

/-- The multiplicity of a root `a` of a nonzero `p` is the largest `n` with `(x - a)^n ∣ p`. -/
@[kb "hefferon2020" "Five.I.1.mult, p. 409"]
theorem hefferon_Five_I_1_mult (p : K[X]) (hp : p ≠ 0) (a : K) :
    IsGreatest {n : ℕ | (X - C a) ^ n ∣ p} (p.rootMultiplicity a) :=
  ⟨Polynomial.pow_rootMultiplicity_dvd p a, fun _ hn => (Polynomial.le_rootMultiplicity_iff hp).2 hn⟩

/-- Dividing `p(x)` by `x - a` leaves the constant remainder `p(a)`. -/
@[kb "hefferon2020" "Five.I.1.4, p. 409"]
theorem hefferon_Five_I_1_4 (p : K[X]) (a : K) :
    p % (X - C a) = C (p.eval a) ∧ p %ₘ (X - C a) = C (p.eval a) :=
  ⟨Polynomial.mod_X_sub_C_eq_C_eval p a, Polynomial.modByMonic_X_sub_C_eq_C_eval p a⟩

end Poly

section Annihilating

variable {K : Type*} [Field K]

/-- Every square matrix is annihilated by a nonzero polynomial of degree at most `n^2`
(Cayley-Hamilton gives one of degree `n`). -/
@[kb "hefferon2020" "Five.IV.1.intro, p. 450"]
theorem hefferon_Five_IV_1_intro {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    ∃ p : K[X], p ≠ 0 ∧ aeval A p = 0 ∧ p.natDegree ≤ Fintype.card n ^ 2 := by
  refine ⟨A.charpoly, (Matrix.charpoly_monic A).ne_zero, Matrix.aeval_self_charpoly A, ?_⟩
  rw [Matrix.charpoly_natDegree_eq_dim]
  exact Nat.le_self_pow (by norm_num) _

/-- Every linear transformation of a finite-dimensional space is annihilated by a nonzero
polynomial. -/
@[kb "hefferon2020" "Five.IV.1.intro, p. 450"]
theorem hefferon_Five_IV_1_intro_map {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) : ∃ p : K[X], p ≠ 0 ∧ aeval T p = 0 :=
  ⟨T.charpoly, (LinearMap.charpoly_monic T).ne_zero, LinearMap.aeval_self_charpoly T⟩

end Annihilating

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The geometric multiplicity of an eigenvalue is at least one and at most the algebraic
multiplicity. -/
@[kb "hefferon2020" "Five.II.3.13, p. 428", kb "hefferon2020" "Five.II.3.mult, p. 428"]
theorem hefferon_Five_II_3_13 (T : Module.End K V) (μ : K) (h : T.HasEigenvalue μ) :
    1 ≤ Module.finrank K (T.eigenspace μ) ∧
      Module.finrank K (T.eigenspace μ) ≤ T.charpoly.rootMultiplicity μ :=
  ⟨Submodule.one_le_finrank_iff.2 (Module.End.hasEigenvalue_iff.1 h),
    LinearMap.finrank_eigenspace_le T μ⟩

/-- The characteristic polynomial of a map does not depend on the basis used to compute it. -/
@[kb "hefferon2020" "Five.II.3.35, p. 426"]
theorem hefferon_Five_II_3_35 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (T : Module.End K V) (B : Module.Basis ι K V) (D : Module.Basis κ K V) :
    (LinearMap.toMatrix B B T).charpoly = (LinearMap.toMatrix D D T).charpoly := by
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end Eigen

section Nilpotent

/-- The index of nilpotency of a nilpotent element is the least power that is zero. -/
@[kb "hefferon2020" "Five.III.2.index, p. 440"]
theorem hefferon_Five_III_2_index {M : Type*} [MonoidWithZero M] (x : M) (hx : IsNilpotent x) :
    IsLeast {k : ℕ | x ^ k = 0} (nilpotencyClass x) :=
  ⟨pow_nilpotencyClass hx, fun _ hk => Nat.sInf_le hk⟩

end Nilpotent

end UndergradKB.LinearAlgebra.Course
