import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Matrix.Mul
import UndergradKB.Common.Attr

/-! # Hilbert series (Etingof et al., Problem 1.38)

The Hilbert series of a graded algebra is `Σ dim A[d] t^d`; we state the coefficient formulas.

* (a) `finrank_homogeneousSubmodule`: polynomials in `m` variables.
* (b) `finrank_tensorPower_fin`: the degree-`d` piece of the free (tensor) algebra on `m`
  generators is `V ⊗ ⋯ ⊗ V` (`d` factors, `V = k^m`), of dimension `m ^ d`.
* (c) `finrank_exteriorPower_fin`: the exterior algebra.
-/

namespace UndergradKB.RepresentationTheory

open Module
open scoped TensorProduct

section Hilbert

variable (k : Type*) [Field k] (m d : ℕ)

/-- Book claim 1.38(a): the coefficient of `t^d` in the Hilbert series of `k[x_1, …, x_m]`
(graded by degree) is the dimension of the space of homogeneous polynomials of degree `d`, which is
`(m + d - 1).choose d` (the coefficient of `t^d` in `1/(1-t)^m`). -/
@[kb "etingof2011" "Problem 1.38, p. 14"]
theorem finrank_homogeneousSubmodule :
    finrank k (MvPolynomial.homogeneousSubmodule (Fin m) k d) = (m + d - 1).choose d := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let s : Set (Fin m →₀ ℕ) := {x | x.degree = d}
  let e : s ≃ (Finset.univ : Finset (Fin m)).finsuppAntidiag d :=
    Equiv.subtypeEquivRight (fun x => by
      simp [s, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum])
  let : Fintype s := Fintype.ofEquiv _ e.symm
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) s).finrank_eq,
    Module.finrank_finsupp_self, Fintype.card_congr e, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp

/-- Book claim 1.38(b): the free algebra on `m` generators is graded by word length; its degree-`d`
piece is the `d`-th tensor power of `V = k^m` (tensor algebra), of dimension `m ^ d`, the
coefficient of `t^d` in `1/(1-mt)`. -/
@[kb "etingof2011" "Problem 1.38, p. 14"]
theorem finrank_tensorPower_fin :
    finrank k (⨂[k]^d (Fin m → k)) = m ^ d := by
  classical
  let b : Basis (Fin d → Fin m) k (⨂[k]^d (Fin m → k)) :=
    Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin m))
  rw [Module.finrank_eq_card_basis b]
  simp

/-- Book claim 1.38(c): the degree-`d` piece of the exterior algebra of `k^m` has dimension
`m.choose d`, the coefficient of `t^d` in `(1+t)^m`. -/
@[kb "etingof2011" "Problem 1.38, p. 14"]
theorem finrank_exteriorPower_fin :
    finrank k (⋀[k]^d (Fin m → k)) = m.choose d := by
  simp

end Hilbert

section Paths

open Quiver

variable {Q : Type*} [Quiver Q] [Fintype Q] [DecidableEq Q] [∀ i j : Q, Finite (i ⟶ j)]

/-- The adjacency matrix of a finite quiver: `C i j` is the number of arrows `i ⟶ j`. -/
noncomputable def adjMatrix : Matrix Q Q ℕ := Matrix.of fun i j => Nat.card (i ⟶ j)

/-- Paths of length `d + 1` from `i` to `j` are paths of length `d` from `i` to some `b`
followed by an arrow `b ⟶ j`. -/
noncomputable def pathsSuccEquiv (i j : Q) (d : ℕ) :
    (Σ b : Q, {p : Path i b // p.length = d} × (b ⟶ j)) ≃ {p : Path i j // p.length = d + 1} :=
  Equiv.ofBijective
    (fun x => ⟨x.2.1.1.cons x.2.2, by simp [x.2.1.2]⟩)
    ⟨by
      rintro ⟨b, ⟨p, hp⟩, e⟩ ⟨b', ⟨p', hp'⟩, e'⟩ h
      simp only [Subtype.mk.injEq, Path.cons.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      simp only [heq_eq_eq] at h1 h2
      subst h1 h2
      rfl,
     by
      rintro ⟨p, hp⟩
      cases p with
      | nil => simp at hp
      | cons q e =>
        exact ⟨⟨_, ⟨q, by simpa using hp⟩, e⟩, rfl⟩⟩

theorem pathsZero (i j : Q) :
    Finite {p : Path i j // p.length = 0} ∧
      Nat.card {p : Path i j // p.length = 0} = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    haveI : Unique {p : Path i i // p.length = 0} :=
      ⟨⟨⟨Path.nil, rfl⟩⟩, fun ⟨p, hp⟩ => Subtype.ext (Path.eq_nil_of_length_zero p hp)⟩
    exact ⟨inferInstance, by simp⟩
  · haveI : IsEmpty {p : Path i j // p.length = 0} :=
      ⟨fun ⟨p, hp⟩ => h (Path.eq_of_length_zero p hp)⟩
    exact ⟨inferInstance, by simp [h]⟩

theorem finite_pathsOfLength (i j : Q) (d : ℕ) : Finite {p : Path i j // p.length = d} := by
  classical
  induction d generalizing j with
  | zero => exact (pathsZero i j).1
  | succ d ih =>
    have : ∀ b, Finite {p : Path i b // p.length = d} := ih
    exact Finite.of_surjective _ (pathsSuccEquiv i j d).surjective

/-- Book claim 1.38(d): for a finite quiver with adjacency matrix `C`, the number of paths of length
`d` from `i` to `j` is `(C ^ d) i j`; so the degree-`d` part of the path algebra (graded by path
length) has dimension equal to the sum of all entries of `C ^ d`, which is the coefficient of `t^d`
in the Hilbert series. -/
@[kb "etingof2011" "Problem 1.38, p. 14"]
theorem card_pathsOfLength (i j : Q) (d : ℕ) :
    Nat.card {p : Path i j // p.length = d} = ((adjMatrix (Q := Q)) ^ d) i j := by
  classical
  induction d generalizing j with
  | zero => rw [(pathsZero i j).2]; simp [Matrix.one_apply]
  | succ d ih =>
    have : ∀ b, Finite {p : Path i b // p.length = d} := fun b => finite_pathsOfLength i b d
    rw [← Nat.card_congr (pathsSuccEquiv i j d), Nat.card_sigma, pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.card_prod, ih]
    rfl

end Paths

end UndergradKB.RepresentationTheory
