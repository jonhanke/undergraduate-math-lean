import Mathlib.Algebra.MvPolynomial.PDeriv
import UndergradKB.RepresentationTheory.ProblemsBranching
import UndergradKB.Common.Attr

/-! # Problems 4.51 and 4.52: contents and the Jucys-Murphy element (Etingof et al.)

* `content μ` is the content `∑_{(i,j) ∈ μ} (j - i)` (column minus row) of a Young diagram.
* **Problem 4.51** (`content_spechtChar`): for the sum `C_n` of the transpositions of `S_n`, which acts on the
  irreducible `V_λ` by a scalar, the scalar is `c(λ)`; on the level of characters
  `(n choose 2) χ_λ(τ) = c(λ) χ_λ(1)` for a transposition `τ`.  The proof uses the Frobenius character formula
  and the operators `D = ∑ x_i² ∂_i`, `L = ∑ x_i² ∂_i²` on polynomials: `L` is diagonal on monomials, `L (p₁ g) =
  p₁ L g + 2 D g`, `D (p₁ g) = p₂ g + p₁ D g`, `D Δ = (N-1) p₁ Δ` and `L Δ = ε(ρ) Δ`, which gives
  `L (p₁^n Δ) = (ε(ρ) + 2n(N-1)) p₁^n Δ + n(n-1) p₂ p₁^{n-2} Δ`; comparing coefficients of `x^{λ+ρ}` gives the claim.
* **Problem 4.52**, combinatorial core: removing a box changes the content by the content of the box
  (`content_sub_content_removeCorner`), contents of boxes lie in `[1-n, n-1]`, distinct corners have distinct
  contents, and a diagram has a unique corner iff it is rectangular.
-/

namespace UndergradKB.RepresentationTheory

open Finset MvPolynomial
open scoped Classical

namespace Content

variable {N : ℕ}

/-! ### Two operators on polynomials -/

/-- `D = ∑ x_i² ∂_i`. -/
noncomputable def opD : MvPolynomial (Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N) ℂ :=
  ∑ i : Fin N, (LinearMap.mulLeft ℂ (X i ^ 2 : MvPolynomial (Fin N) ℂ)) ∘ₗ (pderiv i).toLinearMap

/-- `L = ∑ x_i² ∂_i²`. -/
noncomputable def opL : MvPolynomial (Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N) ℂ :=
  ∑ i : Fin N, (LinearMap.mulLeft ℂ (X i ^ 2 : MvPolynomial (Fin N) ℂ)) ∘ₗ
    ((pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap)

theorem opD_apply (f : MvPolynomial (Fin N) ℂ) : opD f = ∑ i, X i ^ 2 * pderiv i f := by
  simp [opD, LinearMap.sum_apply]

theorem opL_apply (f : MvPolynomial (Fin N) ℂ) : opL f = ∑ i, X i ^ 2 * pderiv i (pderiv i f) := by
  simp [opL, LinearMap.sum_apply]

/-- The power sum `p₁ = x₁ + ⋯ + x_N`. -/
noncomputable def P1 : MvPolynomial (Fin N) ℂ := ∑ i, X i

theorem pderiv_P1 (i : Fin N) : pderiv i (P1 : MvPolynomial (Fin N) ℂ) = 1 := by
  simp [P1, pderiv_X, Pi.single_apply]

theorem pderiv_mul_P1 (i : Fin N) (g : MvPolynomial (Fin N) ℂ) :
    pderiv i (P1 * g) = P1 * pderiv i g + g := by
  rw [Derivation.leibniz, pderiv_P1, smul_eq_mul, smul_eq_mul, mul_one]

theorem opD_mul_P1 (g : MvPolynomial (Fin N) ℂ) :
    opD (P1 * g) = psum (Fin N) ℂ 2 * g + P1 * opD g := by
  have h : ∀ i, X i ^ 2 * pderiv i (P1 * g) = X i ^ 2 * g + P1 * (X i ^ 2 * pderiv i g) := by
    intro i
    rw [pderiv_mul_P1, mul_add, mul_left_comm, add_comm]
  rw [opD_apply, opD_apply, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rfl

theorem opL_mul_P1 (g : MvPolynomial (Fin N) ℂ) : opL (P1 * g) = P1 * opL g + 2 * opD g := by
  have h : ∀ i, X i ^ 2 * pderiv i (pderiv i (P1 * g)) =
      P1 * (X i ^ 2 * pderiv i (pderiv i g)) + 2 * (X i ^ 2 * pderiv i g) := by
    intro i
    rw [pderiv_mul_P1, map_add, Derivation.leibniz, pderiv_P1, smul_eq_mul, smul_eq_mul, mul_one]
    ring
  rw [opL_apply, opL_apply, opD_apply, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- The Leibniz rule for `D`. -/
theorem opD_mul (f g : MvPolynomial (Fin N) ℂ) : opD (f * g) = f * opD g + g * opD f := by
  have h : ∀ i, X i ^ 2 * pderiv i (f * g) = f * (X i ^ 2 * pderiv i g) + g * (X i ^ 2 * pderiv i f) := by
    intro i
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [opD_apply, opD_apply, opD_apply, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

theorem opD_X (k : Fin N) : opD (X k : MvPolynomial (Fin N) ℂ) = X k ^ 2 := by
  rw [opD_apply]
  simp [pderiv_X, Pi.single_apply]

theorem opD_prod {ι : Type*} (S : Finset ι) (f g : ι → MvPolynomial (Fin N) ℂ)
    (h : ∀ k, opD (f k) = g k * f k) :
    opD (∏ k ∈ S, f k) = (∑ k ∈ S, g k) * ∏ k ∈ S, f k := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, zero_mul]
    rw [opD_apply]
    simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, opD_mul, ih, h]
    ring

open FrobeniusDet

theorem opD_X_sub (i j : Fin N) :
    opD (X i - X j : MvPolynomial (Fin N) ℂ) = (X i + X j) * (X i - X j) := by
  rw [map_sub, opD_X, opD_X]; ring

theorem sum_sum_Ioi_add (N : ℕ) :
    ∑ i : Fin N, ∑ j ∈ Ioi i, ((X i + X j : MvPolynomial (Fin N) ℂ)) = ((N - 1 : ℕ) : ℂ) • P1 := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fin.card_Ioi]
  have h2 : ∑ i : Fin N, ∑ j ∈ Ioi i, (X j : MvPolynomial (Fin N) ℂ) =
      ∑ j : Fin N, (j : ℕ) • (X j : MvPolynomial (Fin N) ℂ) := by
    rw [Finset.sum_comm' (t' := (univ : Finset (Fin N))) (s' := fun j => Iio j)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_const, Fin.card_Iio]
    · intro x y
      simp [Finset.mem_Ioi, Finset.mem_Iio]
  rw [h2, ← Finset.sum_add_distrib, P1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul, Nat.cast_smul_eq_nsmul]
  congr 1
  have := i.isLt
  omega

/-- `D Δ = (N-1) p₁ Δ`. -/
theorem opD_Delta : opD (vandermondeDelta ℂ N) = ((N - 1 : ℕ) : ℂ) • (P1 * vandermondeDelta ℂ N) := by
  unfold vandermondeDelta
  have inner : ∀ i : Fin N, opD (∏ j ∈ Ioi i, (X i - X j : MvPolynomial (Fin N) ℂ)) =
      (∑ j ∈ Ioi i, (X i + X j : MvPolynomial (Fin N) ℂ)) * ∏ j ∈ Ioi i, (X i - X j) :=
    fun i => opD_prod _ _ _ (fun j => opD_X_sub i j)
  rw [opD_prod Finset.univ _ (fun i => ∑ j ∈ Ioi i, (X i + X j : MvPolynomial (Fin N) ℂ)) inner,
    sum_sum_Ioi_add, smul_mul_assoc]

/-- The eigenvalue of `L` on the monomial `x^s`. -/
def eps (s : Fin N →₀ ℕ) : ℕ := ∑ i, s i * (s i - 1)

theorem opL_monomial (t : Fin N →₀ ℕ) (a : ℂ) :
    opL (monomial t a) = (eps t : ℂ) • monomial t a := by
  rw [opL_apply, eps, Nat.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pderiv_monomial, pderiv_monomial, X_pow_eq_monomial, monomial_mul, smul_monomial]
  by_cases h : 2 ≤ t i
  · have hexp : Finsupp.single i 2 + (t - Finsupp.single i 1 - Finsupp.single i 1) = t := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [hj]
    rw [hexp]
    congr 1
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply, if_true, one_mul]
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    simp [smul_eq_mul]
    ring
  · have hz : t i = 0 ∨ t i = 1 := by omega
    rcases hz with h0 | h1
    · simp [h0]
    · simp [h1]

theorem coeff_opL (f : MvPolynomial (Fin N) ℂ) (s : Fin N →₀ ℕ) :
    (opL f).coeff s = (eps s : ℂ) * f.coeff s := by
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [opL_monomial, coeff_smul, coeff_monomial]
    by_cases h : u = s
    · subst h; simp [smul_eq_mul]
    · simp [h]
  | add p q hp hq =>
    have e : ∀ (u v : MvPolynomial (Fin N) ℂ), (u + v).coeff s = u.coeff s + v.coeff s := fun u v => rfl
    rw [map_add, e, e, hp, hq, mul_add]

/-- `ε(ρ)`, the eigenvalue of `L` on the monomials of `Δ`. -/
def epsRho (N : ℕ) : ℕ := ∑ i : Fin N, rhoExp N i * (rhoExp N i - 1)

theorem eps_deltaExp (σ : Equiv.Perm (Fin N)) : eps (deltaExp σ) = epsRho N := by
  unfold eps epsRho
  simp_rw [deltaExp_apply]
  exact Equiv.sum_comp σ.symm (fun i => rhoExp N i * (rhoExp N i - 1))

/-- `L Δ = ε(ρ) Δ`. -/
theorem opL_Delta : opL (vandermondeDelta ℂ N) = (epsRho N : ℂ) • vandermondeDelta ℂ N := by
  rw [vandermondeDelta_eq_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, opL_monomial, eps_deltaExp]
  exact smul_comm _ _ _

theorem coeff_natCast_mul (k : ℕ) (f : MvPolynomial (Fin N) ℂ) (s : Fin N →₀ ℕ) :
    ((k : MvPolynomial (Fin N) ℂ) * f).coeff s = (k : ℂ) * f.coeff s := by
  rw [← map_natCast (C : ℂ →+* MvPolynomial (Fin N) ℂ) k, coeff_C_mul]

theorem opD_Delta' : opD (vandermondeDelta ℂ N) = ((N - 1 : ℕ) : MvPolynomial (Fin N) ℂ) *
    (P1 * vandermondeDelta ℂ N) := by
  rw [opD_Delta, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem opL_Delta' : opL (vandermondeDelta ℂ N) = (epsRho N : MvPolynomial (Fin N) ℂ) *
    vandermondeDelta ℂ N := by
  rw [opL_Delta, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/-- `D (p₁^{i+1} Δ) = (N-1) p₁^{i+2} Δ + (i+1) p₂ p₁^i Δ`. -/
theorem opD_pow_Delta (i : ℕ) :
    opD (P1 ^ (i + 1) * vandermondeDelta ℂ N) =
      ((N - 1 : ℕ) : MvPolynomial (Fin N) ℂ) * (P1 ^ (i + 2) * vandermondeDelta ℂ N) +
        ((i + 1 : ℕ) : MvPolynomial (Fin N) ℂ) * (psum (Fin N) ℂ 2 * P1 ^ i * vandermondeDelta ℂ N) := by
  induction i with
  | zero =>
    have : P1 ^ (0 + 1) * vandermondeDelta ℂ N = P1 * vandermondeDelta ℂ N := by rw [zero_add, pow_one]
    rw [this, opD_mul_P1, opD_Delta']
    push_cast
    ring
  | succ i ih =>
    have : P1 ^ (i + 1 + 1) * vandermondeDelta ℂ N = P1 * (P1 ^ (i + 1) * vandermondeDelta ℂ N) := by ring
    rw [this, opD_mul_P1, ih]
    push_cast
    ring

/-- `L (p₁^{i+2} Δ) = (ε(ρ) + 2(i+2)(N-1)) p₁^{i+2} Δ + (i+2)(i+1) p₂ p₁^i Δ`. -/
theorem opL_pow_Delta (i : ℕ) :
    opL (P1 ^ (i + 2) * vandermondeDelta ℂ N) =
      ((epsRho N + 2 * (i + 2) * (N - 1) : ℕ) : MvPolynomial (Fin N) ℂ) *
          (P1 ^ (i + 2) * vandermondeDelta ℂ N) +
        (((i + 2) * (i + 1) : ℕ) : MvPolynomial (Fin N) ℂ) *
          (psum (Fin N) ℂ 2 * P1 ^ i * vandermondeDelta ℂ N) := by
  induction i with
  | zero =>
    have : P1 ^ (0 + 2) * vandermondeDelta ℂ N = P1 * (P1 * vandermondeDelta ℂ N) := by ring
    rw [this, opL_mul_P1, opL_mul_P1, opL_Delta', opD_Delta', opD_mul_P1, opD_Delta']
    push_cast
    ring
  | succ i ih =>
    have : P1 ^ (i + 1 + 2) * vandermondeDelta ℂ N = P1 * (P1 ^ (i + 2) * vandermondeDelta ℂ N) := by ring
    have hD := opD_pow_Delta (N := N) (i + 1)
    rw [this, opL_mul_P1, ih]
    have hD' : opD (P1 ^ (i + 2) * vandermondeDelta ℂ N) = _ := hD
    rw [hD']
    push_cast
    ring

/-! ### The transposition and the coefficient comparison -/

theorem extPerm_swap {m : ℕ} (a b : Fin m) :
    Branching.extPerm (Equiv.swap a b) = Equiv.swap a.succ b.succ := by
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [Branching.extPerm_zero, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm
      (Fin.succ_ne_zero b).symm]
  · rw [Branching.extPerm_succ]
    by_cases h1 : j = a
    · subst h1; simp
    · by_cases h2 : j = b
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne
          (fun h => h1 (Fin.succ_injective _ h)) (fun h => h2 (Fin.succ_injective _ h))]

/-- The transposition `(i, i+1)` of `Fin (i+2)`, built by iterated extension of `(0 1)`. -/
noncomputable def trans : (i : ℕ) → Equiv.Perm (Fin (i + 2))
  | 0 => Equiv.swap 0 1
  | i + 1 => Branching.extPerm (trans i)

theorem trans_eq_swap (i : ℕ) :
    trans i = Equiv.swap (⟨i, by omega⟩ : Fin (i + 2)) ⟨i + 1, by omega⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show Branching.extPerm (trans i) = _
    rw [ih, extPerm_swap]
    rfl

theorem cyclePoly_swap_two (N : ℕ) :
    cyclePoly 2 N (Equiv.swap (0 : Fin 2) 1) = psum (Fin N) ℂ 2 := by
  have h3 : cyclePoly 2 N (Equiv.swap (0 : Fin 2) 1) =
      ∏ q : CycleClasses (Equiv.swap (0 : Fin 2) 1), psum (Fin N) ℂ (classSize (Equiv.swap (0 : Fin 2) 1) q) := by
    unfold cyclePoly
    rw [prod_classSize_eq _ (fun m => psum (Fin N) ℂ m), Fintype.card_fin]
  rw [h3]
  have hsame : ∀ a : Fin 2, Equiv.Perm.SameCycle (Equiv.swap (0 : Fin 2) 1) a 0 := by
    intro a
    fin_cases a
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp⟩
  have hq : ∀ q : CycleClasses (Equiv.swap (0 : Fin 2) 1), q = Quotient.mk _ (0 : Fin 2) := by
    intro q
    induction q using Quotient.inductionOn with | _ a => ?_
    exact Quotient.sound (hsame a)
  rw [Finset.prod_eq_single (Quotient.mk _ (0 : Fin 2))]
  · have : classSize (Equiv.swap (0 : Fin 2) 1) (Quotient.mk _ (0 : Fin 2)) = 2 := by
      unfold classSize
      rw [Finset.filter_true_of_mem]
      · simp
      · intro a _
        exact Quotient.sound (hsame a)
    rw [this]
  · intro b _ hb
    exact absurd (hq b) hb
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cyclePoly_trans (i N : ℕ) :
    cyclePoly (i + 2) N (trans i) = P1 ^ i * psum (Fin N) ℂ 2 := by
  induction i with
  | zero => simpa [trans] using cyclePoly_swap_two N
  | succ i ih =>
    show cyclePoly (i + 1 + 2) N (Branching.extPerm (trans i)) = _
    rw [Branching.cyclePoly_extPerm, ih, pow_succ]
    simp only [P1]
    ring

/-- **The coefficient comparison**: `n(n-1) θ_λ(τ) = (ε(λ+ρ) - ε(ρ) - 2n(N-1)) θ_λ(1)`. -/
theorem frobChar_trans (i N : ℕ) (lam : Fin N → ℕ) :
    ((i + 2) * (i + 1) : ℂ) * frobChar (i + 2) N lam (trans i) =
      ((eps (shiftExp lam) : ℂ) - epsRho N - 2 * (i + 2) * ((N - 1 : ℕ) : ℂ)) *
        frobChar (i + 2) N lam 1 := by
  have h := congrArg (fun f : MvPolynomial (Fin N) ℂ => f.coeff (shiftExp lam))
    (opL_pow_Delta (N := N) i)
  have hadd : ∀ (u v : MvPolynomial (Fin N) ℂ) (s : Fin N →₀ ℕ),
      (u + v).coeff s = u.coeff s + v.coeff s := fun u v s => rfl
  simp only [coeff_opL, hadd, coeff_natCast_mul] at h
  have e1 : frobChar (i + 2) N lam 1 = (P1 ^ (i + 2) * vandermondeDelta ℂ N).coeff (shiftExp lam) := by
    unfold frobChar
    rw [cyclePoly_one, mul_comm]
    rfl
  have e2 : frobChar (i + 2) N lam (trans i) =
      (psum (Fin N) ℂ 2 * P1 ^ i * vandermondeDelta ℂ N).coeff (shiftExp lam) := by
    unfold frobChar
    rw [cyclePoly_trans]
    congr 1
    ring
  rw [e1, e2]
  push_cast at h
  linear_combination -h

/-! ### Contents of Young diagrams -/

/-- The content `∑_{(i,j) ∈ μ} (j - i)` (column minus row) of a Young diagram. -/
def content (μ : YoungDiagram) : ℤ := ∑ c ∈ μ.cells, ((c.2 : ℤ) - c.1)

theorem two_mul_sum_range (m : ℕ) (i : ℤ) :
    2 * ∑ j ∈ range m, ((j : ℤ) - i) = (m : ℤ) * ((m : ℤ) - 1) - 2 * i * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem content_eq_sum_rows (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    content μ = ∑ i ∈ range N, ∑ j ∈ range (μ.rowLen i), ((j : ℤ) - i) := by
  unfold content
  rw [Finset.sum_sigma' (range N) (fun i => range (μ.rowLen i)) (fun i j => ((j : ℤ) - i))]
  symm
  refine Finset.sum_nbij' (fun x => (x.1, x.2)) (fun c => ⟨c.1, c.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    rw [YoungDiagram.mem_cells]
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hx.2
  · intro c hc
    rw [YoungDiagram.mem_cells] at hc
    have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hc
    have h0 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hc
    have h2 := YoungDiagram.mem_iff_lt_colLen.mp h0
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨by omega, h1⟩
  · intro x _; rfl
  · intro c _; rfl
  · intro x _; rfl

theorem two_mul_content (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    2 * content μ = ∑ i : Fin N, ((μ.rowLen i : ℤ) * ((μ.rowLen i : ℤ) - 1) - 2 * (i : ℕ) * μ.rowLen i) := by
  rw [content_eq_sum_rows μ hN, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
    (fun i => 2 * ∑ j ∈ range (μ.rowLen i), ((j : ℤ) - i)) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [two_mul_sum_range]

theorem natCast_mul_pred (x : ℕ) : ((x * (x - 1) : ℕ) : ℤ) = (x : ℤ) * ((x : ℤ) - 1) := by
  cases x with
  | zero => simp
  | succ x => simp

theorem eps_sub (lam : Fin N → ℕ) :
    (eps (shiftExp lam) : ℤ) - epsRho N - 2 * ((∑ i, lam i : ℕ) : ℤ) * ((N - 1 : ℕ) : ℤ) =
      ∑ i : Fin N, ((lam i : ℤ) * ((lam i : ℤ) - 1) - 2 * ((i : ℕ) : ℤ) * lam i) := by
  unfold eps epsRho
  rw [Nat.cast_sum, Nat.cast_sum, Nat.cast_sum]
  simp_rw [natCast_mul_pred]
  have h2 : 2 * (∑ i, (lam i : ℤ)) * ((N - 1 : ℕ) : ℤ) = ∑ i, 2 * (lam i : ℤ) * ((N - 1 : ℕ) : ℤ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [h2, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hrho : (rhoExp N i : ℤ) = (N : ℤ) - 1 - ((i : ℕ) : ℤ) := by
    simp only [rhoExp, Fin.val_rev]
    omega
  have hs : ((shiftExp lam) i : ℤ) = (lam i : ℤ) + (rhoExp N i : ℤ) := by
    simp [shiftExp]
  rw [hs, hrho]
  have hN1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  rw [hN1]
  ring

theorem trans_aux (i : ℕ) (la : DiagramsOfSize (i + 2)) :
    ((i + 2) * (i + 1) : ℂ) * (spechtChar (i + 2) la).1 (trans i) =
      2 * (content la.1 : ℂ) * (spechtChar (i + 2) la).1 1 := by
  set N := la.1.colLen 0 with hNdef
  have hN : la.1.colLen 0 ≤ N := le_rfl
  have hform := fun g => congrFun (frobenius_character_formula la hN) g
  rw [hform, hform]
  have hlam := sum_rowLen_eq la hN
  have h1 := frobChar_trans i N (fun j : Fin N => la.1.rowLen j)
  have h2 := eps_sub (N := N) (fun j : Fin N => la.1.rowLen j)
  rw [hlam, ← two_mul_content la.1 hN] at h2
  have h3 : ((eps (shiftExp fun j : Fin N => la.1.rowLen j) : ℂ) - epsRho N -
      2 * ((i : ℂ) + 2) * ((N - 1 : ℕ) : ℂ)) = 2 * (content la.1 : ℂ) := by
    have := congrArg (Int.cast : ℤ → ℂ) h2
    push_cast at this
    linear_combination this
  rw [h3] at h1
  exact h1

end Content

open Content

/-- **Etingof et al., Problem 4.51** (character level): for a transposition `τ ∈ S_n`,
`(n choose 2) χ_λ(τ) = c(λ) χ_λ(1)`, where `c(λ) = ∑_{(i,j) ∈ λ} (j - i)` is the content.  Since the sum `C_n` of
all transpositions is central, it acts on the irreducible `V_λ` by the scalar `(n choose 2) χ_λ(τ) / dim V_λ`,
which is therefore `c(λ)`. -/
@[kb "etingof2011" "Problem 4.51, p. 63"]
theorem content_spechtChar {n : ℕ} (la : DiagramsOfSize n) {a b : Fin n} (hab : a ≠ b) :
    (n.choose 2 : ℂ) * (spechtChar n la).1 (Equiv.swap a b) =
      (content la.1 : ℂ) * (spechtChar n la).1 1 := by
  have hn : 2 ≤ n := by
    have h1 := a.isLt
    have h2 := b.isLt
    have h3 : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
    omega
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 2 := ⟨n - 2, by omega⟩
  have hconj : IsConj (Equiv.swap a b) (trans i) := by
    rw [trans_eq_swap]
    exact Equiv.Perm.isConj_swap hab (fun h => by have := congrArg Fin.val h; simp at this)
  have hcl := mem_classFunctions_of_mem_irrChars (spechtChar (i + 2) la)
  rw [classFunctions_isConj hcl hconj]
  have h := trans_aux i la
  rw [Nat.cast_choose_two]
  push_cast
  have : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp
  push_cast at h
  linear_combination h

/-! ### Problem 4.52: the combinatorial core -/

open Branching

/-- Removing the box `c` changes the content by the content `j - i` of the box. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem content_sub_content_removeCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) :
    content μ - content (removeCorner μ c hc) = (c.2 : ℤ) - c.1 := by
  unfold content
  have : (removeCorner μ c hc).cells = μ.cells.erase c := rfl
  rw [this, Finset.sum_erase_eq_sub ((YoungDiagram.mem_cells _).mpr hc.1)]
  ring

/-- The contents `j - i` of the boxes of a diagram with `n` boxes lie in `[1-n, n-1]`. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem content_box_bounds {μ : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ μ) :
    1 - (μ.card : ℤ) ≤ (c.2 : ℤ) - c.1 ∧ (c.2 : ℤ) - c.1 ≤ (μ.card : ℤ) - 1 := by
  have h1 : c.2 + 1 ≤ μ.card := by
    have : (Finset.range (c.2 + 1)).image (fun j => (c.1, j)) ⊆ μ.cells := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact (YoungDiagram.mem_cells _).mpr (μ.up_left_mem le_rfl (by omega) hc)
    have := Finset.card_le_card this
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)] at this
    simpa using this
  have h2 : c.1 + 1 ≤ μ.card := by
    have : (Finset.range (c.1 + 1)).image (fun i => (i, c.2)) ⊆ μ.cells := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact (YoungDiagram.mem_cells _).mpr (μ.up_left_mem (by omega) le_rfl hc)
    have := Finset.card_le_card this
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)] at this
    simpa using this
  constructor <;> omega

/-- Two different corners of a diagram have different contents. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem content_corner_injective {μ : YoungDiagram} {c c' : ℕ × ℕ} (hc : IsCorner μ c)
    (hc' : IsCorner μ c') (h : (c.2 : ℤ) - c.1 = (c'.2 : ℤ) - c'.1) : c = c' := by
  by_contra hne
  have key : ∀ {d d' : ℕ × ℕ}, IsCorner μ d → IsCorner μ d' → d.1 < d'.1 → d'.2 < d.2 := by
    intro d d' hd hd' hlt
    by_contra hle
    push Not at hle
    exact hd.2.1 (μ.up_left_mem (by omega) hle hd'.1)
  rcases lt_trichotomy c.1 c'.1 with hlt | heq | hgt
  · have := key hc hc' hlt; omega
  · have h1 := rowLen_corner hc
    have h2 := rowLen_corner hc'
    rw [heq] at h1
    exact hne (Prod.ext heq (by omega))
  · have := key hc' hc hgt; omega

/-- A diagram is rectangular if all its nonempty rows have the same length. -/
def IsRect (μ : YoungDiagram) : Prop := ∀ i < μ.colLen 0, μ.rowLen i = μ.rowLen 0

/-- A diagram has at most one corner iff it is rectangular. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem unique_corner_iff_isRect (μ : YoungDiagram) :
    (∀ c c' : ℕ × ℕ, IsCorner μ c → IsCorner μ c' → c = c') ↔ IsRect μ := by
  constructor
  · intro huniq i hi
    by_contra hne
    have hle : μ.rowLen i ≤ μ.rowLen 0 := μ.rowLen_anti 0 i (Nat.zero_le _)
    have hlt : μ.rowLen i < μ.rowLen 0 := lt_of_le_of_ne hle hne
    have hi0 : i ≠ 0 := fun h => by subst h; exact hne rfl
    -- the first row shorter than the first one
    have hex : ∃ j, μ.rowLen j < μ.rowLen 0 := ⟨i, hlt⟩
    obtain ⟨i0, hi0min⟩ : ∃ i0, μ.rowLen i0 < μ.rowLen 0 ∧ ∀ j < i0, μ.rowLen j = μ.rowLen 0 := by
      refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => ?_⟩
      have h1 := Nat.find_min hex hj
      have h2 := μ.rowLen_anti 0 j (Nat.zero_le _)
      push Not at h1
      omega
    obtain ⟨hi0lt, hi0eq⟩ := hi0min
    have hi0le : i0 ≤ i := by
      by_contra hgt
      push Not at hgt
      have := hi0eq i hgt
      omega
    have hpos : 0 < μ.rowLen 0 := by
      have : (0, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      exact YoungDiagram.mem_iff_lt_rowLen.mp this
    have hi0pos : 0 < i0 := by
      rcases Nat.eq_zero_or_pos i0 with h | h
      · subst h; omega
      · exact h
    -- corner 1: end of the last full row
    have c1 : IsCorner μ (i0 - 1, μ.rowLen 0 - 1) := by
      have hr := hi0eq (i0 - 1) (by omega)
      refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
      · rw [YoungDiagram.mem_iff_lt_rowLen]
        simp only
        have : i0 - 1 + 1 = i0 := by omega
        rw [this]; omega
      · rw [YoungDiagram.mem_iff_lt_rowLen]
        simp only
        omega
    -- corner 2: end of the last row
    have hk : 0 < μ.colLen 0 := by omega
    have hmem : (μ.colLen 0 - 1, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hpos2 : 0 < μ.rowLen (μ.colLen 0 - 1) := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have c2 : IsCorner μ (μ.colLen 0 - 1, μ.rowLen (μ.colLen 0 - 1) - 1) := by
      refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
      · intro h
        have := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le _) h)
        simp only at this
        omega
      · rw [YoungDiagram.mem_iff_lt_rowLen]
        simp only
        omega
    have heq := huniq _ _ c1 c2
    have := congrArg Prod.snd heq
    simp only at this
    have hle2 : μ.rowLen (μ.colLen 0 - 1) ≤ μ.rowLen i0 := μ.rowLen_anti i0 _ (by omega)
    omega
  · intro hR c c' hc hc'
    have key : ∀ {d : ℕ × ℕ}, IsCorner μ d → d = (μ.colLen 0 - 1, μ.rowLen 0 - 1) := by
      intro d hd
      have hd1 : d.1 < μ.colLen 0 := by
        have := μ.up_left_mem le_rfl (Nat.zero_le d.2) hd.1
        exact YoungDiagram.mem_iff_lt_colLen.mp this
      have hr := hR d.1 hd1
      have h2 := rowLen_corner hd
      have hlast : d.1 + 1 ≥ μ.colLen 0 := by
        by_contra hlt
        push Not at hlt
        apply hd.2.1
        rw [YoungDiagram.mem_iff_lt_rowLen, hR (d.1 + 1) hlt]
        omega
      ext <;> simp <;> omega
    rw [key hc, key hc']

/-- The operator `C_n = ∑_{a < b} (a b)` (written as half the sum over ordered pairs) on a representation of `S_n`. -/
noncomputable def transpositionSum {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, ρ (Equiv.swap p.1 p.2)

/-- The operator `C_n` commutes with the action of `S_n`. -/
theorem transpositionSum_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (g : Equiv.Perm (Fin n)) :
    transpositionSum ρ ∘ₗ ρ g = ρ g ∘ₗ transpositionSum ρ := by
  have hre : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, ρ (Equiv.swap (g p.1) (g p.2)) =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, ρ (Equiv.swap p.1 p.2) := by
    refine Finset.sum_nbij' (fun p => (g p.1, g p.2)) (fun p => (g⁻¹ p.1, g⁻¹ p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
      exact fun h => hp (g.injective h)
    · intro p hp
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp ⊢
      exact fun h => hp (g⁻¹.injective h)
    · intro p _; simp
    · intro p _; simp
    · intro p _; rfl
  refine LinearMap.ext fun v => ?_
  have key : ∀ p : Fin n × Fin n, ρ g (ρ (Equiv.swap p.1 p.2) v) =
      ρ (Equiv.swap (g p.1) (g p.2)) (ρ g v) := by
    intro p
    rw [← mul_apply_eq_comp, ← map_mul, Equiv.mul_swap_eq_swap_mul, map_mul, mul_apply_eq_comp]
  simp only [transpositionSum, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, key]
  congr 1
  have := congrArg (fun f : V →ₗ[ℂ] V => f (ρ g v)) hre
  simpa [LinearMap.sum_apply] using this.symm

/-- **Etingof et al., Problem 4.51** (representation level): the sum `C_n` of all transpositions acts on the
Specht module `V_λ` of `S_n` (`n ≥ 2`) as the scalar `c(λ)`. -/
@[kb "etingof2011" "Problem 4.51, p. 63"]
theorem transpositionSum_spechtIrrRep {n : ℕ} (hn : 2 ≤ n) (la : DiagramsOfSize n)
    (v : (spechtIrrRep n la).V) :
    transpositionSum (spechtIrrRep n la).ρ v = (content la.1 : ℂ) • v := by
  set X := spechtIrrRep n la with hX
  obtain ⟨z, hz⟩ := exists_eq_smul_id_of_commute (ρ := X.ρ) (transpositionSum X.ρ)
    (transpositionSum_comm X.ρ)
  have hd : (Module.finrank ℂ X.V : ℂ) ≠ 0 := by
    have : Invertible (Nat.card (Equiv.Perm (Fin n)) : ℂ) := invertibleNatCard
    exact finrank_ne_zero_of_isIrreducible (ρ := X.ρ)
  have hC : (n.choose 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  -- the trace of `C_n`
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
      (n.choose 2 : ℂ) * LinearMap.trace ℂ X.V (X.ρ (Equiv.swap p.1 p.2)) =
        (content la.1 : ℂ) * (Module.finrank ℂ X.V : ℂ) := by
    intro p hp
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hp
    have := content_spechtChar la hp
    rw [← Representation.char_one X.ρ] at *
    exact this
  have hcard : (((Finset.univ : Finset (Fin n)).offDiag.card : ℕ) : ℂ) = 2 * (n.choose 2 : ℂ) := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.cast_choose_two,
      Nat.cast_sub (by nlinarith)]
    have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    push_cast
    field_simp
  have htr : LinearMap.trace ℂ X.V (transpositionSum X.ρ) =
      (content la.1 : ℂ) * (Module.finrank ℂ X.V : ℂ) := by
    unfold transpositionSum
    rw [map_smul, map_sum]
    have hsum : (n.choose 2 : ℂ) * ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        LinearMap.trace ℂ X.V (X.ρ (Equiv.swap p.1 p.2)) =
        2 * (n.choose 2 : ℂ) * ((content la.1 : ℂ) * (Module.finrank ℂ X.V : ℂ)) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcard]
    have hA : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        LinearMap.trace ℂ X.V (X.ρ (Equiv.swap p.1 p.2)) =
        2 * ((content la.1 : ℂ) * (Module.finrank ℂ X.V : ℂ)) := by
      apply mul_left_cancel₀ hC
      rw [hsum]; ring
    rw [hA, smul_eq_mul]
    ring
  have hz' : LinearMap.trace ℂ X.V (transpositionSum X.ρ) = z * (Module.finrank ℂ X.V : ℂ) := by
    rw [hz, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hzc : z = (content la.1 : ℂ) := mul_right_cancel₀ hd (hz'.symm.trans htr)
  rw [hz, hzc]
  rfl

/-! ### Problem 4.52: the spectrum of `E = C_n - C_{n-1}` on `V_μ` (trace form) -/

/-- The element `C_n` of the group algebra. -/
noncomputable def transpositionElt (n : ℕ) : MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  (1 / 2 : ℂ) • ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
    MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) (Equiv.swap p.1 p.2)

theorem asAlgebraHom_transpositionElt {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    ρ.asAlgebraHom (transpositionElt n) = transpositionSum ρ := by
  unfold transpositionElt transpositionSum
  rw [map_smul, map_sum]
  simp [Representation.asAlgebraHom_of]

/-- The restriction of the Specht module `V_μ` of `S_{m+1}` to `S_m`. -/
noncomputable def resRep {m : ℕ} (μ : DiagramsOfSize (m + 1)) :
    Representation ℂ (Equiv.Perm (Fin m)) (spechtIrrRep (m + 1) μ).V :=
  (spechtIrrRep (m + 1) μ).ρ.comp (extHom m)

/-- The restriction of `V_μ` to `S_m` has the traces of the `V_{μ - c}`, for every element of the group
algebra. -/
theorem trace_res_eq {m : ℕ} (μ : DiagramsOfSize (m + 1)) (a : MonoidAlgebra ℂ (Equiv.Perm (Fin m))) :
    LinearMap.trace ℂ (spechtIrrRep (m + 1) μ).V ((resRep μ).asAlgebraHom a) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c},
        LinearMap.trace ℂ (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).V
          ((spechtIrrRep m (removeCornerDiag μ c.1 c.2)).ρ.asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]
  | single g r =>
    simp only [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    exact restrict_spechtChar μ g

theorem transpositionSum_eq_algebraMap {m : ℕ} (hm : 2 ≤ m) (la : DiagramsOfSize m) :
    transpositionSum (spechtIrrRep m la).ρ =
      algebraMap ℂ (Module.End ℂ (spechtIrrRep m la).V) (content la.1 : ℂ) :=
  LinearMap.ext fun v => by
    rw [transpositionSum_spechtIrrRep hm la v, Module.algebraMap_end_apply]

theorem trace_aeval_scalar {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (z : ℂ)
    (P : Polynomial ℂ) :
    LinearMap.trace ℂ W (Polynomial.aeval (algebraMap ℂ (Module.End ℂ W) z) P) =
      P.eval z * (Module.finrank ℂ W : ℂ) := by
  rw [Polynomial.aeval_algebraMap_apply, Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id,
    smul_eq_mul]
  simp

/-- `Tr_{V_μ} P(C_{n-1}) = ∑_{λ = μ - box} dim V_λ · P(c(λ))`. -/
theorem trace_aeval_res {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) (P : Polynomial ℂ) :
    LinearMap.trace ℂ (spechtIrrRep (m + 1) μ).V (Polynomial.aeval (transpositionSum (resRep μ)) P) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c},
        P.eval (content (removeCorner μ.1 c.1 c.2) : ℂ) *
          (Module.finrank ℂ (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).V : ℂ) := by
  have h1 : Polynomial.aeval (transpositionSum (resRep μ)) P =
      (resRep μ).asAlgebraHom (Polynomial.aeval (transpositionElt m) P) := by
    rw [← asAlgebraHom_transpositionElt (resRep μ), Polynomial.aeval_algHom_apply]
  rw [h1, trace_res_eq]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 : (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).ρ.asAlgebraHom
      (Polynomial.aeval (transpositionElt m) P) =
      Polynomial.aeval (transpositionSum (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).ρ) P := by
    rw [← asAlgebraHom_transpositionElt (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).ρ,
      Polynomial.aeval_algHom_apply]
  rw [h2, transpositionSum_eq_algebraMap hm, trace_aeval_scalar]
  rfl

theorem sum_offDiag_fin {k : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin k × Fin k → M) :
    ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag, F p =
      ∑ a : Fin k, ∑ b : Fin k, if a ≠ b then F (a, b) else 0 := by
  have h : (Finset.univ : Finset (Fin k)).offDiag =
      (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2) := by
    ext p; simp [Finset.mem_offDiag]
  rw [h, Finset.sum_filter, Fintype.sum_prod_type]

/-- `C_n = C_{n-1} + (0 1) + ⋯ + (0 m)` on any representation of `S_{m+1}`. -/
theorem transpositionSum_split {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (Fin (m + 1))) V) :
    transpositionSum ρ = transpositionSum (ρ.comp (extHom m)) +
      ∑ j : Fin m, ρ (Equiv.swap 0 j.succ) := by
  unfold transpositionSum
  rw [sum_offDiag_fin, sum_offDiag_fin, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, ne_eq, not_true_eq_false, if_false, zero_add, Fin.succ_ne_zero,
    not_false_eq_true, if_true, Fin.succ_inj]
  have h1 : ∀ i : Fin m, ρ (Equiv.swap i.succ 0) = ρ (Equiv.swap 0 i.succ) := fun i => by
    rw [Equiv.swap_comm]
  have h2 : ∀ i j : Fin m, ρ (Equiv.swap i.succ j.succ) = (ρ.comp (extHom m)) (Equiv.swap i j) := fun i j => by
    show _ = ρ (Branching.extPerm (Equiv.swap i j))
    rw [extPerm_swap]
  have h0 : ∀ i : Fin m, ¬ ((0 : Fin (m + 1)) = i.succ) := fun i => (Fin.succ_ne_zero i).symm
  simp only [h0, h1, h2, Finset.sum_add_distrib, smul_add, not_false_eq_true, if_true]
  module

/-- The operator `E = C_n - C_{n-1}` (the sum of the transpositions `(0 j)`) on `V_μ`. -/
noncomputable def jmOp {m : ℕ} (μ : DiagramsOfSize (m + 1)) :
    (spechtIrrRep (m + 1) μ).V →ₗ[ℂ] (spechtIrrRep (m + 1) μ).V :=
  transpositionSum (spechtIrrRep (m + 1) μ).ρ - transpositionSum (resRep μ)

/-- `E = C_n - C_{n-1}` is the sum of the transpositions `(0 j)`, `1 ≤ j ≤ m` (the book's `(1 2) + ⋯ + (1 n)`,
with the points numbered from `0`). -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem jmOp_eq_sum {m : ℕ} (μ : DiagramsOfSize (m + 1)) :
    jmOp μ = ∑ j : Fin m, (spechtIrrRep (m + 1) μ).ρ (Equiv.swap 0 j.succ) := by
  unfold jmOp resRep
  rw [transpositionSum_split]
  abel

/-- **Etingof et al., Problem 4.52(a)** (trace form): for every polynomial `P`,
`Tr_{V_μ} P(E) = ∑ P(c) · dim V_{μ - c}`, the sum over the corners `c` of `μ`, `P` evaluated at the content
`j - i` of the corner box.  So `E` has the integer eigenvalues `j - i` (contents of the corners, which lie in
`[1-n, n-1]`) with multiplicity `dim V_{μ - c}`; all the moments `Tr E^k` are given by this formula. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem trace_aeval_jmOp {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) (P : Polynomial ℂ) :
    LinearMap.trace ℂ (spechtIrrRep (m + 1) μ).V (Polynomial.aeval (jmOp μ) P) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c},
        P.eval ((c.1.2 : ℂ) - (c.1.1 : ℂ)) *
          (Module.finrank ℂ (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).V : ℂ) := by
  set z : ℂ := (content μ.1 : ℂ) with hz
  have hC : transpositionSum (spechtIrrRep (m + 1) μ).ρ =
      algebraMap ℂ (Module.End ℂ (spechtIrrRep (m + 1) μ).V) z :=
    transpositionSum_eq_algebraMap (by omega) μ
  have hE : jmOp μ = Polynomial.aeval (transpositionSum (resRep μ)) (Polynomial.C z - Polynomial.X) := by
    simp [jmOp, hC]
  rw [hE, ← Polynomial.aeval_comp, trace_aeval_res hm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hsub := content_sub_content_removeCorner c.2
  have hsub' : z - (content (removeCorner μ.1 c.1 c.2) : ℂ) = (c.1.2 : ℂ) - (c.1.1 : ℂ) := by
    have := congrArg (Int.cast : ℤ → ℂ) hsub
    push_cast at this
    rw [hz]
    linear_combination this
  simp [Polynomial.eval_comp, hsub']

/-- **Etingof et al., Problem 4.52(b)** (one direction): if `E` acts on `V_μ` by a scalar, then `μ` has a
unique corner (so `μ` is rectangular, by `unique_corner_iff_isRect`).  The proof compares the first moments
`Tr E^k` of `trace_aeval_jmOp` and uses that the contents of the different corners are different. -/
@[kb "etingof2011" "Problem 4.52, p. 63"]
theorem unique_corner_of_jmOp_scalar {m : ℕ} (hm : 2 ≤ m) (μ : DiagramsOfSize (m + 1)) (s : ℂ)
    (hs : jmOp μ = algebraMap ℂ (Module.End ℂ (spechtIrrRep (m + 1) μ).V) s)
    (c c' : {c : ℕ × ℕ // IsCorner μ.1 c}) : c = c' := by
  set d : {c : ℕ × ℕ // IsCorner μ.1 c} → ℕ :=
    fun c => Module.finrank ℂ (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).V with hd
  have hdpos : ∀ c, 0 < d c := by
    intro c
    have : Invertible (Nat.card (Equiv.Perm (Fin m)) : ℂ) := invertibleNatCard
    have h := finrank_ne_zero_of_isIrreducible (ρ := (spechtIrrRep m (removeCornerDiag μ c.1 c.2)).ρ)
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  set e : {c : ℕ × ℕ // IsCorner μ.1 c} → ℝ := fun c => (c.1.2 : ℝ) - c.1.1 with he
  have key : ∀ P : Polynomial ℂ, P.eval s * (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V : ℂ) =
      ∑ c, P.eval ((e c : ℝ) : ℂ) * (d c : ℂ) := by
    intro P
    have h := trace_aeval_jmOp hm μ P
    rw [hs, trace_aeval_scalar] at h
    rw [h]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [he, hd]
  have hD : (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V : ℂ) = ∑ c, (d c : ℂ) := by
    simpa using key 1
  have hA : s * (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V : ℂ) = ∑ c, ((e c : ℝ) : ℂ) * (d c : ℂ) := by
    simpa using key Polynomial.X
  have hB : ∑ c, (((e c : ℝ) : ℂ) - s) ^ 2 * (d c : ℂ) = 0 := by
    have h1 := key ((Polynomial.X - Polynomial.C s) ^ 2)
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h1
    exact h1.symm
  -- `s` is real
  have hDpos : (0 : ℝ) < (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V : ℝ) := by
    rw [show (Module.finrank ℂ (spechtIrrRep (m + 1) μ).V : ℝ) = ∑ c, (d c : ℝ) by exact_mod_cast hD]
    obtain ⟨c0⟩ : Nonempty {c : ℕ × ℕ // IsCorner μ.1 c} := ⟨c⟩
    exact Finset.sum_pos (fun i _ => by exact_mod_cast hdpos i) ⟨c, Finset.mem_univ _⟩
  have him : s.im = 0 := by
    have h := congrArg Complex.im hA
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_add] at h
    have h2 : (∑ c, ((e c : ℝ) : ℂ) * (d c : ℂ)).im = 0 := by
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
      exact Complex.ofReal_im _
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_right hDpos.ne'
  have hs' : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  -- the variance vanishes
  have hvar : ∑ x, (e x - s.re) ^ 2 * (d x : ℝ) = 0 := by
    have h := congrArg Complex.re hB
    rw [Complex.re_sum, Complex.zero_re] at h
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hs', ← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact (Complex.ofReal_re _).symm
  have hall : ∀ x, e x = s.re := by
    intro x
    have hnn : ∀ y ∈ (Finset.univ : Finset {c : ℕ × ℕ // IsCorner μ.1 c}),
        0 ≤ (e y - s.re) ^ 2 * (d y : ℝ) := fun y _ => by positivity
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hvar x (Finset.mem_univ _)
    have hdx : (d x : ℝ) ≠ 0 := by exact_mod_cast (hdpos x).ne'
    have h3 : (e x - s.re) ^ 2 = 0 := (mul_eq_zero.mp this).resolve_right hdx
    linarith [pow_eq_zero_iff (two_ne_zero) |>.mp h3]
  apply Subtype.ext
  apply content_corner_injective c.2 c'.2
  have h1 := hall c
  have h2 := hall c'
  have : ((c.1.2 : ℝ) - c.1.1) = ((c'.1.2 : ℝ) - c'.1.1) := by
    simp only [he] at h1 h2
    linarith
  exact_mod_cast this

end UndergradKB.RepresentationTheory
