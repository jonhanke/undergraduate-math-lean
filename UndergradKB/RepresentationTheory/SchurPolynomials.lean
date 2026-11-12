import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import UndergradKB.Common.Attr

/-! # Cauchy determinant, Schur polynomials as alternant quotients (Etingof et al., §4.18-4.20)

* **Lemma 4.48** (`cauchy_det`): the Cauchy determinant `det (1 / (z_i - y_j))` over a field.
* **§4.20** (`schurPoly`): the alternant `D_λ = det (x_i ^ (λ_j + N - j))` is divisible by the Vandermonde
  product `Δ = ∏_{i<j} (x_i - x_j)` in `R[x_1, …, x_N]`, with quotient the Schur polynomial `S_λ`
  (`alternant_eq_vandermondeDelta_mul_schurPoly`).  Indices are `0`-based, so the exponent of column `j` is
  `λ_j + (N - 1 - j)`.
-/

namespace UndergradKB.RepresentationTheory

open Matrix Finset Fin

/-! ### Lemma 4.48: the Cauchy determinant -/

section Cauchy

variable {K : Type*} [Field K]

theorem cauchy_det_aux : ∀ {n : ℕ} (z y : Fin n → K), (∀ i j, z i - y j ≠ 0) →
    det (of fun i j => 1 / (z i - y j)) =
      (∏ i, ∏ j ∈ Ioi i, ((z j - z i) * (y i - y j))) / ∏ i, ∏ j, (z i - y j) := by
  intro n
  induction n with
  | zero => intro z y h; simp
  | succ n ih =>
  intro z y h
  set M : Matrix (Fin (n+1)) (Fin (n+1)) K := of fun i j => 1 / (z i - y j) with hM
  set C : Matrix (Fin (n+1)) (Fin (n+1)) K :=
    of fun i j => if j = 0 then 1 else 1 / (z i - y j) with hC
  set w : Fin (n+1) → K := fun j => if j = 0 then 1 else y j - y 0 with hw
  set v : Fin (n+1) → K := fun i => 1 / (z i - y 0) with hv
  have h1 : det M = (∏ i, v i) * ((∏ j, w j) * det C) := by
    have e1 : det M = det (of fun i j => v i * (w j * C i j)) := by
      rw [← det_transpose M, ← det_transpose (of fun i j => v i * (w j * C i j))]
      refine det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then 0 else 1) 0 (by simp)
        (fun i j => ?_)
      by_cases hi : i = 0
      · subst hi
        simp [hM, hC, hw, hv]
      · have h1 := h j i
        have h2 := h j 0
        simp only [transpose_apply, of_apply, hM, hC, hw, hv, hi, ite_false, ite_true]
        field_simp
        ring
    rw [e1]
    exact (det_mul_column v (of fun i j => w j * C i j)).trans (by rw [det_mul_row w C])
  set D : Matrix (Fin (n+1)) (Fin (n+1)) K :=
    of fun i j => if i = 0 then C 0 j else C i j - C 0 j with hD
  have h2 : det C = (∏ i : Fin n, (z 0 - z i.succ)) * ((∏ j : Fin n, 1 / (z 0 - y j.succ)) *
      det (of fun (i j : Fin n) => 1 / (z i.succ - y j.succ))) := by
    have e1 : det C = det D := by
      refine det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then 0 else 1) 0 (by simp)
        (fun i j => ?_)
      by_cases hi : i = 0
      · subst hi; simp [hD]
      · simp [hD, hi]
    rw [e1, det_succ_column_zero, Fin.sum_univ_succ]
    have : ∀ i : Fin n, D i.succ 0 = 0 := by
      intro i; simp [hD, hC]
    simp only [this, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul, Fin.succAbove_zero]
    have h00 : D 0 0 = 1 := by simp [hD, hC]
    rw [h00, one_mul]
    have : D.submatrix Fin.succ Fin.succ = of fun (i j : Fin n) =>
        (z 0 - z i.succ) * ((1 / (z 0 - y j.succ)) * (1 / (z i.succ - y j.succ))) := by
      ext i j
      have h1 := h i.succ j.succ
      have h2 := h 0 j.succ
      simp only [submatrix_apply, of_apply, hD, hC, Fin.succ_ne_zero, ite_false]
      field_simp
      ring
    rw [this]
    exact (det_mul_column _ (of fun (i j : Fin n) =>
      (1 / (z 0 - y j.succ)) * (1 / (z i.succ - y j.succ)))).trans
      (congrArg _ (det_mul_row (fun j : Fin n => 1 / (z 0 - y j.succ))
        (of fun (i j : Fin n) => 1 / (z i.succ - y j.succ))))
  have hN : (∏ i : Fin (n+1), ∏ j ∈ Ioi i, ((z j - z i) * (y i - y j))) =
      (∏ j : Fin n, ((z j.succ - z 0) * (y 0 - y j.succ))) *
        ∏ i : Fin n, ∏ j ∈ Ioi i, ((z j.succ - z i.succ) * (y i.succ - y j.succ)) := by
    simp only [prod_univ_succ, Ioi_zero_eq_map, Finset.prod_map, coe_succEmb, prod_Ioi_succ]
  have hD' : (∏ i : Fin (n+1), ∏ j : Fin (n+1), (z i - y j)) =
      ((z 0 - y 0) * ∏ j : Fin n, (z 0 - y j.succ)) *
        ∏ i : Fin n, ((z i.succ - y 0) * ∏ j : Fin n, (z i.succ - y j.succ)) := by
    simp only [prod_univ_succ]
  rw [h1, h2, ih (fun i => z i.succ) (fun j => y j.succ) (fun i j => h _ _), hN, hD']
  have hv' : (∏ i, v i) = 1 / ((z 0 - y 0) * ∏ i : Fin n, (z i.succ - y 0)) := by
    simp only [hv, prod_univ_succ, one_div, prod_inv_distrib, mul_inv]
  have hw' : (∏ j, w j) = ∏ j : Fin n, (y j.succ - y 0) := by
    simp [hw, prod_univ_succ]
  rw [hv', hw']
  have hz1 : ∀ j : Fin n, z 0 - y j.succ ≠ 0 := fun j => h _ _
  have hz2 : ∀ i : Fin n, z i.succ - y 0 ≠ 0 := fun i => h _ _
  have hz3 : ∀ i j : Fin n, z i.succ - y j.succ ≠ 0 := fun i j => h _ _
  have hz4 : z 0 - y 0 ≠ 0 := h _ _
  have p1 : ∏ j : Fin n, (z 0 - y j.succ) ≠ 0 := prod_ne_zero_iff.2 (fun j _ => hz1 j)
  have p2 : ∏ i : Fin n, (z i.succ - y 0) ≠ 0 := prod_ne_zero_iff.2 (fun j _ => hz2 j)
  have p3 : ∏ i : Fin n, ∏ j : Fin n, (z i.succ - y j.succ) ≠ 0 :=
    prod_ne_zero_iff.2 (fun i _ => prod_ne_zero_iff.2 (fun j _ => hz3 i j))
  have q1 : ∏ i : Fin n, ((z i.succ - y 0) * ∏ j : Fin n, (z i.succ - y j.succ)) =
      (∏ i : Fin n, (z i.succ - y 0)) * ∏ i : Fin n, ∏ j : Fin n, (z i.succ - y j.succ) :=
    prod_mul_distrib
  have q2 : (∏ j : Fin n, (y j.succ - y 0)) * ∏ i : Fin n, (z 0 - z i.succ) =
      ∏ j : Fin n, ((z j.succ - z 0) * (y 0 - y j.succ)) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun j _ => by ring)
  have q3 : (∏ j : Fin n, 1 / (z 0 - y j.succ)) = 1 / ∏ j : Fin n, (z 0 - y j.succ) := by
    simp [prod_inv_distrib]
  rw [q1, q3]
  rw [← q2]
  field_simp

/-- **Lemma 4.48 (Cauchy determinant).** Over a field, for `z_i - y_j ≠ 0`,
`det (1 / (z_i - y_j)) = ∏_{i<j} (z_j - z_i)(y_i - y_j) / ∏_{i,j} (z_i - y_j)`. -/
@[kb "etingof2011" "Lemma 4.48, p. 62"]
theorem cauchy_det {n : ℕ} (z y : Fin n → K) (h : ∀ i j, z i - y j ≠ 0) :
    det (of fun i j => 1 / (z i - y j)) =
      (∏ i, ∏ j ∈ Ioi i, ((z j - z i) * (y i - y j))) / ∏ i, ∏ j, (z i - y j) :=
  cauchy_det_aux z y h

lemma prod_pair_mul : ∀ {n : ℕ} (x : Fin n → K),
    ∏ i, ∏ j ∈ Ioi i, (x i * x j) = ∏ i, x i ^ (n - 1)
  | 0, x => by simp
  | n + 1, x => by
    have hN : (∏ i : Fin (n+1), ∏ j ∈ Ioi i, (x i * x j)) =
        (∏ j : Fin n, (x 0 * x j.succ)) *
          ∏ i : Fin n, ∏ j ∈ Ioi i, (x i.succ * x j.succ) := by
      simp only [prod_univ_succ, Ioi_zero_eq_map, Finset.prod_map, coe_succEmb, prod_Ioi_succ]
    rw [hN, prod_pair_mul (fun i : Fin n => x i.succ), prod_mul_distrib, Finset.prod_const, card_univ,
      Fintype.card_fin, prod_univ_succ (fun i : Fin (n+1) => x i ^ (n + 1 - 1)), Nat.add_sub_cancel,
      mul_assoc]
    congr 1
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    have := i.pos
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    simp [pow_succ']

/-- **Corollary 4.49 (Cauchy identity).**  Over a field, for `x_i ≠ 0` and `1 - x_i y_j ≠ 0`,
`det (1 / (1 - x_i y_j)) = ∏_{i<j} (x_i - x_j)(y_i - y_j) / ∏_{i,j} (1 - x_i y_j)`. -/
@[kb "etingof2011" "Corollary 4.49, p. 62"]
theorem cauchy_identity {n : ℕ} (x y : Fin n → K) (hx : ∀ i, x i ≠ 0)
    (h : ∀ i j, 1 - x i * y j ≠ 0) :
    det (of fun i j => 1 / (1 - x i * y j)) =
      (∏ i, ∏ j ∈ Ioi i, ((x i - x j) * (y i - y j))) / ∏ i, ∏ j, (1 - x i * y j) := by
  set z : Fin n → K := fun i => (x i)⁻¹ with hz
  have hzy : ∀ i j, z i - y j = (1 - x i * y j) / x i := by
    intro i j
    have := hx i
    simp only [hz]
    field_simp
  have hz0 : ∀ i j, z i - y j ≠ 0 := fun i j => by
    rw [hzy]; exact div_ne_zero (h i j) (hx i)
  have e1 : (of fun i j => 1 / (1 - x i * y j) : Matrix (Fin n) (Fin n) K) =
      of fun i j => z i * (1 / (z i - y j)) := by
    ext i j
    have h1 := h i j
    have h2 := hx i
    simp only [of_apply, hz]
    field_simp
  have e2 : det (of fun i j => z i * (1 / (z i - y j))) =
      (∏ i, z i) * det (of fun i j => 1 / (z i - y j)) := det_mul_column z _
  rw [e1, e2, cauchy_det z y hz0]
  have hN : (∏ i, ∏ j ∈ Ioi i, ((z j - z i) * (y i - y j))) =
      (∏ i, ∏ j ∈ Ioi i, ((x i - x j) * (y i - y j))) / ∏ i, ∏ j ∈ Ioi i, (x i * x j) := by
    rw [← prod_div_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    rw [← prod_div_distrib]
    refine prod_congr rfl (fun j _ => ?_)
    have := hx i
    have := hx j
    simp only [hz]
    field_simp
  have hD : (∏ i, ∏ j, (z i - y j)) = (∏ i, ∏ j, (1 - x i * y j)) / ∏ i, x i ^ n := by
    rw [← prod_div_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    simp only [hzy]
    rw [prod_div_distrib, Finset.prod_const, card_univ, Fintype.card_fin]
  have hxn : (∏ i, x i ^ n) = (∏ i, x i) * ∏ i, x i ^ (n - 1) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    have := i.pos
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    simp [pow_succ']
  have hz1 : (∏ i, z i) = (∏ i, x i)⁻¹ := by simp [hz, prod_inv_distrib]
  have p1 : (∏ i, x i) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hx i
  have p2 : (∏ i, x i ^ (n - 1)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)
  have p3 : (∏ i, ∏ j, (1 - x i * y j)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j _ => h i j
  rw [hN, hD, hz1, prod_pair_mul, hxn]
  field_simp

/-- The Cauchy identity written as a signed sum over permutations. -/
@[kb "etingof2011" "Corollary 4.49, p. 62"]
theorem cauchy_identity_sum {n : ℕ} (x y : Fin n → K) (hx : ∀ i, x i ≠ 0)
    (h : ∀ i j, 1 - x i * y j ≠ 0) :
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ j, 1 / (1 - x j * y (σ j)) =
      (∏ i, ∏ j ∈ Ioi i, ((x i - x j) * (y i - y j))) / ∏ i, ∏ j, (1 - x i * y j) := by
  rw [← cauchy_identity x y hx h, ← det_transpose, det_apply]
  simp [transpose_apply]

end Cauchy

/-! ### Schur polynomials as alternant quotients -/

section Schur

open scoped BigOperators

variable (R : Type*) [CommRing R] (N : ℕ)

/-- The Vandermonde product `Δ = ∏_{i<j} (x_i - x_j)` in `R[x_1, …, x_N]`. -/
noncomputable def vandermondeDelta : MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

variable {R N}

/-- The alternant `det (x_i ^ l_j)` of an exponent vector `l`. -/
noncomputable def alternant (l : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  det (of fun i j => (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ l j)

/-- The exponents `λ_j + N - j` (with `j` counted from `1`; here `0`-based, `λ_j + (N - 1 - j)`) of the
alternant `D_λ`. -/
def schurExp (lam : Fin N → ℕ) (j : Fin N) : ℕ := lam j + (j.rev : ℕ)

/-- The alternant `D_λ = det (x_i ^ (λ_j + N - j))`. -/
@[kb "etingof2011" "§4.20 definition, p. 66"]
noncomputable def schurAlternant (lam : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  alternant (schurExp lam)

/-- The monic polynomial `∏_k (T - x_k)` over `R[x_1, …, x_N]`, which kills every `x_i`. -/
noncomputable abbrev schurNodal (R : Type*) [CommRing R] (N : ℕ) :
    Polynomial (MvPolynomial (Fin N) R) :=
  Lagrange.nodal Finset.univ (fun k : Fin N => (MvPolynomial.X k : MvPolynomial (Fin N) R))

variable [Nontrivial R]

/-- The matrix of coefficients of `T ^ (λ_j + N - j) mod ∏_k (T - x_k)`, in decreasing powers. -/
noncomputable def schurCoeffMatrix (lam : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  of fun c j => ((Polynomial.X ^ schurExp lam j) %ₘ schurNodal R N).coeff (c.rev : ℕ)

/-- The Schur polynomial `S_λ`, defined as the determinant of the matrix expressing the powers
`x_i ^ (λ_j + N - j)` in the basis `x_i ^ (N - c)`, so that `D_λ = Δ * S_λ`. -/
@[kb "etingof2011" "§4.20 definition, p. 66"]
noncomputable def schurPoly (lam : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  det (schurCoeffMatrix (R := R) lam)

lemma schurNodal_ne_one (i : Fin N) : schurNodal R N ≠ 1 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [Lagrange.natDegree_nodal] at this
  simp at this
  exact absurd this (by have := i.pos; omega)

lemma alternant_schurExp_matrix (lam : Fin N → ℕ) :
    (of fun i j => (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ schurExp lam j) =
      projVandermonde (1 : Fin N → MvPolynomial (Fin N) R) MvPolynomial.X * schurCoeffMatrix lam := by
  refine Matrix.ext fun i j => ?_
  have hdeg : ((Polynomial.X ^ schurExp lam j) %ₘ schurNodal R N).natDegree < N := by
    have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ schurExp lam j)
      (Lagrange.nodal_monic (s := Finset.univ) (v := fun k : Fin N => (MvPolynomial.X k : MvPolynomial (Fin N) R))) (schurNodal_ne_one i)
    simpa using this
  have hroot : Polynomial.eval (MvPolynomial.X i : MvPolynomial (Fin N) R) (schurNodal R N) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hmod := congrArg (Polynomial.eval (MvPolynomial.X i : MvPolynomial (Fin N) R))
    (Polynomial.modByMonic_add_div (Polynomial.X ^ schurExp lam j) (schurNodal R N))
  rw [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul, add_zero, Polynomial.eval_pow,
    Polynomial.eval_X] at hmod
  rw [of_apply, ← hmod, Polynomial.eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range
    (fun c => ((Polynomial.X ^ schurExp lam j) %ₘ schurNodal R N).coeff c *
      (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ c) N, Matrix.mul_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun c => ?_)
  have hc := c.isLt
  simp [projVandermonde_apply, schurCoeffMatrix, mul_comm]
  congr 2
  omega

omit [Nontrivial R] in
lemma det_projVandermonde_one :
    det (projVandermonde (1 : Fin N → MvPolynomial (Fin N) R) MvPolynomial.X) =
      vandermondeDelta R N := by
  rw [det_projVandermonde]
  simp [vandermondeDelta]

/-- **Divisibility by the Vandermonde product.** The alternant `D_λ` equals `Δ * S_λ` in
`R[x_1, …, x_N]`; so `S_λ` is a polynomial and `D_λ / Δ`. -/
@[kb "etingof2011" "§4.20 definition, p. 66"]
theorem schurAlternant_eq_vandermondeDelta_mul_schurPoly (lam : Fin N → ℕ) :
    schurAlternant (R := R) lam = vandermondeDelta R N * schurPoly lam := by
  unfold schurAlternant alternant schurPoly
  rw [alternant_schurExp_matrix, det_mul, det_projVandermonde_one]

omit [Nontrivial R] in
/-- The Schur polynomial is the unique polynomial with `D_λ = Δ * S_λ` (over a domain). -/
theorem schurPoly_unique [IsDomain R] (lam : Fin N → ℕ) (S : MvPolynomial (Fin N) R)
    (h : schurAlternant (R := R) lam = vandermondeDelta R N * S) : S = schurPoly lam := by
  have hne : vandermondeDelta R N ≠ 0 := by
    unfold vandermondeDelta
    refine prod_ne_zero_iff.2 (fun i _ => prod_ne_zero_iff.2 (fun j hj => ?_))
    rw [sub_ne_zero]
    intro hij
    have := MvPolynomial.X_injective (σ := Fin N) (R := R) hij
    exact (ne_of_gt (mem_Ioi.1 hj)) this.symm
  rw [schurAlternant_eq_vandermondeDelta_mul_schurPoly] at h
  exact (mul_left_cancel₀ hne h).symm

/-! ### Specialisations (Proposition 4.62) -/

omit [Nontrivial R] in
lemma aeval_schurAlternant {B : Type*} [CommRing B] [Algebra R B] (p : Fin N → B) (lam : Fin N → ℕ) :
    MvPolynomial.aeval p (schurAlternant (R := R) lam) = det (of fun i j => p i ^ schurExp lam j) := by
  unfold schurAlternant alternant
  have := (MvPolynomial.aeval p : MvPolynomial (Fin N) R →ₐ[R] B).toRingHom.map_det
    (of fun i j => (MvPolynomial.X i : MvPolynomial (Fin N) R) ^ schurExp lam j)
  convert this using 2
  ext i j
  simp

omit [Nontrivial R] in
lemma aeval_vandermondeDelta {B : Type*} [CommRing B] [Algebra R B] (p : Fin N → B) :
    MvPolynomial.aeval p (vandermondeDelta R N) = ∏ i : Fin N, ∏ j ∈ Ioi i, (p i - p j) := by
  simp [vandermondeDelta]

/-- The alternant evaluated at the geometric progression `x_i = z ^ i` is a Vandermonde determinant in
the nodes `z ^ l_j`. -/
lemma det_geom_alternant {B : Type*} [CommRing B] (z : B) (l : Fin N → ℕ) :
    det (of fun (i j : Fin N) => (z ^ (i : ℕ)) ^ l j) =
      ∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ l j - z ^ l i) := by
  have : (of fun (i j : Fin N) => (z ^ (i : ℕ)) ^ l j) = (vandermonde fun j => z ^ l j)ᵀ := by
    ext i j
    simp [← pow_mul, mul_comm]
  rw [this, det_transpose, det_vandermonde]

/-- **Proposition 4.62 (first half).** In a field, at the geometric progression `x_i = z ^ i`
(with the points distinct), the Schur polynomial is the quotient of two products of differences of powers of
`z`: `S_λ(1, z, …, z^{N-1}) = ∏_{i<j} (z^{l_j} - z^{l_i}) / ∏_{i<j} (z^i - z^j)` with
`l_j = λ_j + N - j`. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem schurPoly_geom {K : Type*} [Field K] (z : K) (lam : Fin N → ℕ)
    (hz : ∀ i j : Fin N, i < j → z ^ (i : ℕ) ≠ z ^ (j : ℕ)) :
    MvPolynomial.aeval (fun i : Fin N => z ^ (i : ℕ)) (schurPoly (R := K) lam) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ schurExp lam j - z ^ schurExp lam i)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ (i : ℕ) - z ^ (j : ℕ)) := by
  have hne : (∏ i : Fin N, ∏ j ∈ Ioi i, (z ^ (i : ℕ) - z ^ (j : ℕ))) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 (hz i j (mem_Ioi.1 hj))
  have h := congrArg (MvPolynomial.aeval (fun i : Fin N => z ^ (i : ℕ)))
    (schurAlternant_eq_vandermondeDelta_mul_schurPoly (R := K) lam)
  rw [map_mul, aeval_schurAlternant, aeval_vandermondeDelta, det_geom_alternant] at h
  rw [eq_div_iff hne, mul_comm]
  exact h.symm

omit [Nontrivial R] in
/-- **Proposition 4.62 (second half).**  For a partition `λ` (weakly decreasing), the value of the Schur
polynomial at `(1, …, 1)` satisfies
`S_λ(1, …, 1) * ∏_{i<j} (j - i) = ∏_{i<j} (λ_i - λ_j + j - i)`, over any domain.  This is the product formula
of the book with the denominators cleared, see `schurPoly_one` for the quotient form. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem schurPoly_one_mul [IsDomain R] (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.aeval (fun _ : Fin N => (1 : R)) (schurPoly (R := R) lam) *
        (∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : R)) =
      ∏ i : Fin N, ∏ j ∈ Ioi i, ((lam i - lam j + ((j : ℕ) - (i : ℕ)) : ℕ) : R) := by
  set T : Polynomial R := Polynomial.X with hT
  set s : Polynomial R :=
    MvPolynomial.aeval (fun i : Fin N => T ^ (i : ℕ)) (schurPoly (R := R) lam) with hs
  have h := congrArg (MvPolynomial.aeval (fun i : Fin N => T ^ (i : ℕ)))
    (schurAlternant_eq_vandermondeDelta_mul_schurPoly (R := R) lam)
  rw [map_mul, aeval_schurAlternant, aeval_vandermondeDelta, det_geom_alternant] at h
  -- factor each difference
  have hnum : ∀ i j : Fin N, j ∈ Ioi i →
      T ^ schurExp lam j - T ^ schurExp lam i =
        (T ^ schurExp lam j * ∑ t ∈ range (lam i - lam j + ((j : ℕ) - (i : ℕ))), T ^ t) * (1 - T) := by
    intro i j hj
    have hij0 : i < j := mem_Ioi.1 hj
    have hij : (i : ℕ) < j := hij0
    have hl := hlam hij0.le
    have hjN := j.isLt
    have : schurExp lam i = schurExp lam j + (lam i - lam j + ((j : ℕ) - (i : ℕ))) := by
      simp only [schurExp, Fin.val_rev]; omega
    rw [mul_assoc, geom_sum_mul_neg, this, pow_add]
    ring
  have hden : ∀ i j : Fin N, j ∈ Ioi i →
      T ^ (i : ℕ) - T ^ (j : ℕ) =
        (T ^ (i : ℕ) * ∑ t ∈ range ((j : ℕ) - (i : ℕ)), T ^ t) * (1 - T) := by
    intro i j hj
    have hij0 : i < j := mem_Ioi.1 hj
    have hij : (i : ℕ) < j := hij0
    obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = i + k := ⟨(j : ℕ) - i, by omega⟩
    have hk2 : (j : ℕ) - i = k := by omega
    rw [hk2, hk, pow_add, mul_assoc, geom_sum_mul_neg]
    ring
  rw [prod_congr rfl (fun i _ => prod_congr rfl (fun j hj => hnum i j hj)),
    prod_congr rfl (fun i _ => prod_congr rfl (fun j hj => hden i j hj))] at h
  simp only [prod_mul_distrib] at h
  have hQ : (∏ i : Fin N, ∏ j ∈ Ioi i, (1 - T : Polynomial R)) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j _ => ?_
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [hT] at this
  have h' : (∏ i : Fin N, ∏ j ∈ Ioi i,
      (T ^ schurExp lam j * ∑ t ∈ range (lam i - lam j + ((j : ℕ) - (i : ℕ))), T ^ t)) =
      s * ∏ i : Fin N, ∏ j ∈ Ioi i, (T ^ (i : ℕ) * ∑ t ∈ range ((j : ℕ) - (i : ℕ)), T ^ t) := by
    apply mul_right_cancel₀ hQ
    simp only [prod_mul_distrib] at h ⊢
    rw [h]
    ring
  have h1 := congrArg (Polynomial.aeval (1 : R)) h'
  have hev : Polynomial.aeval (1 : R) s =
      MvPolynomial.aeval (fun _ : Fin N => (1 : R)) (schurPoly (R := R) lam) := by
    have := congrArg (fun φ => φ (schurPoly (R := R) lam))
      (MvPolynomial.comp_aeval (R := R) (fun i : Fin N => T ^ (i : ℕ)) (Polynomial.aeval (1 : R)))
    simpa [hs, hT] using this
  rw [map_mul, hev] at h1
  have e : ∀ k m : ℕ, Polynomial.aeval (1 : R) (T ^ k * ∑ t ∈ range m, T ^ t) = (m : R) := by
    intro k m
    simp [hT]
  simp only [map_prod, e] at h1
  exact h1.symm

/-- **Proposition 4.62 (second half), quotient form.**  In a field of characteristic zero, for a weakly
decreasing `λ`, `S_λ(1, …, 1) = ∏_{i<j} (λ_i - λ_j + j - i) / (j - i)`. -/
@[kb "etingof2011" "Proposition 4.62, p. 66"]
theorem schurPoly_one {K : Type*} [Field K] [CharZero K] (lam : Fin N → ℕ) (hlam : Antitone lam) :
    MvPolynomial.aeval (fun _ : Fin N => (1 : K)) (schurPoly (R := K) lam) =
      (∏ i : Fin N, ∏ j ∈ Ioi i, ((lam i - lam j + ((j : ℕ) - (i : ℕ)) : ℕ) : K)) /
        ∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : K) := by
  have hne : (∏ i : Fin N, ∏ j ∈ Ioi i, (((j : ℕ) - (i : ℕ) : ℕ) : K)) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j hj => ?_
    have hij0 : i < j := mem_Ioi.1 hj
    have hij : (i : ℕ) < j := hij0
    exact Nat.cast_ne_zero.2 (by omega)
  rw [eq_div_iff hne]
  exact schurPoly_one_mul lam hlam

end Schur

end UndergradKB.RepresentationTheory
