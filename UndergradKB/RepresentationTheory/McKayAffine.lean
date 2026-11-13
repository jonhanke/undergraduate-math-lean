import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.GroupTheory.OrderOfElement
import UndergradKB.RepresentationTheory.McKayConnected
import UndergradKB.RepresentationTheory.FrobeniusDivisibility
import UndergradKB.Common.Attr

/-! # The McKay graph of a finite subgroup of `SU(2)` is affine (Etingof et al., Problem 5.5(c))

For a finite subgroup `G ≠ 1` of `SU(2)` with its natural 2-dimensional representation `V`, let `R = (r_ij)` be the
McKay matrix (`r_ij` the multiplicity of `V_j` in `V ⊗ V_i`) and `A = 2 I - R` (`mckayCartan`). Following the
book's hint:

* `mckayCartan_form`: for real `x` and `f = ∑ x_i χ_i`, the quadratic form is `xᵀ A x = |G|⁻¹ ∑_g (2 - χ_V(g)) |f(g)|²`;
  since `χ_V(g)` is real and at most `2`, `A` is positive semidefinite (`mckayCartan_posSemidef`);
* the form vanishes only when `f` vanishes off the identity (`χ_V(g) = 2` forces `g = 1`), i.e. when `x` is a
  multiple of the dimension vector (`mckayCartan_ker`); the dimension vector is in the kernel, so `A` is not
  definite (`mckayCartan_not_posDef`);
* no self-loops (`mckay_natRep_self_eq_zero_of_ne_bot`): if `-1 ∈ G` this is `mckay_natRep_self_eq_zero`;
  otherwise `|G|` is odd (an element of order two of `SU(2)` is `-1`), so `V` is not irreducible (Frobenius
  divisibility), has an invariant line with character `ψ`, `χ_V = ψ + ψ(·⁻¹)`, and `r_ii = 2 (ψ χ_i, χ_i)` is even;
  `r_ii = 2` is excluded by semidefiniteness and the kernel;
* `mckay_isAffineDynkin`: the McKay graph is connected, loopless, with symmetric multiplicities, and `A` is positive
  semidefinite but not definite: an affine Dynkin graph in the book's sense (Problem 5.3(g), multiple edges allowed).

The identification with the list of affine diagrams of the book's pictures (Problem 5.3(g)) is the separate
classification statement.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module Matrix ComplexConjugate

open scoped Classical

set_option linter.unusedSectionVars false

/-! ### Facts on `SU(2)` -/

section SU2Facts

/-- For a `2 × 2` matrix of determinant one, `M² - (tr M) M + 1 = 0` (Cayley-Hamilton). -/
theorem fin_two_sq_sub_trace_smul_add_one {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.det = 1) :
    M * M - M.trace • M + 1 = 0 := by
  rw [Matrix.det_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first
    | linear_combination -h
    | ring

/-- If a `2 × 2` matrix of determinant one has eigenvalue `c` then its trace is `c + c⁻¹`. -/
theorem trace_eq_of_eigenvector {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.det = 1) {v : Fin 2 → ℂ} (hv : v ≠ 0)
    {c : ℂ} (hc : M *ᵥ v = c • v) : M.trace = c + c⁻¹ := by
  have hCH := congrArg (· *ᵥ v) (fin_two_sq_sub_trace_smul_add_one h)
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hc,
    Matrix.mulVec_smul, Matrix.one_mulVec, Matrix.zero_mulVec] at hCH
  have hv' : (c * c - M.trace * c + 1) • v = 0 := by
    rw [add_smul, sub_smul, mul_smul, mul_smul, one_smul]; exact hCH
  have hq : c * c - M.trace * c + 1 = 0 := (smul_eq_zero.1 hv').resolve_right hv
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hq
  field_simp
  linear_combination -hq

/-- An element of `SU(2)` of square one is `1` or `-1`. -/
theorem su2_eq_one_or_neg_one {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (h2 : M * M = 1) : M = 1 ∨ M = -1 := by
  have hdet : M.det = 1 := hM.2
  have hadj : M.adjugate * M = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  have hMadj : M = M.adjugate := by
    calc M = M.adjugate * M * M := by rw [hadj, Matrix.one_mul]
      _ = M.adjugate := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [Matrix.adjugate_fin_two] at hMadj
  have e00 := congrFun (congrFun hMadj 0) 0
  have e01 := congrFun (congrFun hMadj 0) 1
  have e10 := congrFun (congrFun hMadj 1) 0
  have e11 := congrFun (congrFun hMadj 1) 1
  simp at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have hb : M 0 1 = 0 := by linear_combination (1 / 2 : ℂ) * e01
  have hc : M 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * e10
  have hsq : M 0 0 * M 0 0 = 1 := by rw [hb, hc, ← e00] at hdet; linear_combination hdet
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, h, ← e00]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, h, ← e00]

/-- The diagonal entries of a unitary `2 × 2` matrix have absolute value at most one, so the real part of the
trace is at most two. -/
theorem re_trace_le_two {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    M.trace.re ≤ 2 := by
  have h1 : star M * M = 1 := hM.1
  have d0 := congrFun (congrFun h1 0) 0
  have d1 := congrFun (congrFun h1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at d0 d1
  have n0 : Complex.normSq (M 0 0) ≤ 1 := by
    have := congrArg Complex.re d0
    simp [Complex.mul_re] at this
    nlinarith [Complex.normSq_apply (M 0 0), Complex.normSq_apply (M 1 0), Complex.normSq_nonneg (M 1 0)]
  have n1 : Complex.normSq (M 1 1) ≤ 1 := by
    have := congrArg Complex.re d1
    simp [Complex.mul_re] at this
    nlinarith [Complex.normSq_apply (M 1 1), Complex.normSq_apply (M 0 1), Complex.normSq_nonneg (M 0 1)]
  have r0 : (M 0 0).re ≤ 1 := by
    have := Complex.re_sq_le_normSq (M 0 0)
    nlinarith
  have r1 : (M 1 1).re ≤ 1 := by
    have := Complex.re_sq_le_normSq (M 1 1)
    nlinarith
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith

end SU2Facts

/-! ### The form `2 I - R` -/

section Form

variable (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- The character of the natural representation is real valued. -/
theorem natRep_character_conj (g : G) : conj ((natRep G).character g) = (natRep G).character g := by
  rw [← character_inv_eq_conj, natRep_character_inv]

theorem natRep_character_eq_re (g : G) :
    (natRep G).character g = (((natRep G).character g).re : ℂ) :=
  (Complex.conj_eq_iff_re.1 (natRep_character_conj G g)).symm

theorem natRep_character_re_le (g : G) : ((natRep G).character g).re ≤ 2 := by
  rw [natRep_character]
  exact re_trace_le_two g.1.2.1

/-- If the character of the natural representation takes the value `2` at `g`, then `g = 1`. -/
theorem eq_one_of_natRep_character_re (g : G) (h : ((natRep G).character g).re = 2) : g = 1 := by
  have h2 : (natRep G).character g = (finrank ℂ (Fin 2 → ℂ) : ℂ) := by
    rw [natRep_character_eq_re, h, finrank_natRep]; norm_num
  have := eq_one_of_character_eq_finrank (natRep G) g h2
  exact natRep_injective G (by rw [this, map_one])

/-- The real McKay matrix `R = (r_ij)` of the natural representation. -/
noncomputable def mckayR : Matrix (irrChars ℂ G) (irrChars ℂ G) ℝ :=
  fun i j ↦ (mckay (natRep G) i j).re

/-- The matrix `A = 2 I - R` of the McKay graph (the book's `a_ij = 2 δ_ij - r_ij`). -/
noncomputable def mckayCartan : Matrix (irrChars ℂ G) (irrChars ℂ G) ℝ :=
  2 • (1 : Matrix (irrChars ℂ G) (irrChars ℂ G) ℝ) - mckayR G

/-- The dimension vector `(dim V_i)_i` of the irreducible representations. -/
noncomputable def dimVec : irrChars ℂ G → ℝ := fun i ↦ ((i : G → ℂ) 1).re

theorem mckay_eq_re (i j : irrChars ℂ G) : mckay (natRep G) i j = (mckayR G i j : ℂ) := by
  obtain ⟨n, hn⟩ := exists_natCast_mckay (natRep G) i j
  simp [mckayR, hn]

theorem mckayR_symm (i j : irrChars ℂ G) : mckayR G i j = mckayR G j i := by
  simp only [mckayR, mckay_natRep_symm G i j]

theorem irrChar_one_eq_re (i : irrChars ℂ G) : (i : G → ℂ) 1 = (dimVec G i : ℂ) := by
  obtain ⟨X, hX⟩ := i.2
  have hX' : (i : G → ℂ) = X.ρ.character := hX.symm
  rw [dimVec, hX', char_one]
  simp

theorem dimVec_pos (i : irrChars ℂ G) : 0 < dimVec G i := by
  obtain ⟨X, hX⟩ := i.2
  have hX' : (i : G → ℂ) = X.ρ.character := hX.symm
  rw [dimVec, hX', char_one]
  have := finrank_ne_zero_of_isIrreducible (ρ := X.ρ)
  simp only [Complex.natCast_re, Nat.cast_pos]
  exact Nat.pos_of_ne_zero (fun h ↦ this (by simp [h]))

theorem irrChar_inv (i : irrChars ℂ G) (g : G) : (i : G → ℂ) g⁻¹ = conj ((i : G → ℂ) g) := by
  obtain ⟨X, hX⟩ := i.2
  rw [← hX]
  exact character_inv_eq_conj X.ρ g

/-- The class function `f = ∑ x_i χ_i` attached to a real vector `x`. -/
noncomputable def mckayFun (x : irrChars ℂ G → ℝ) : G → ℂ := ∑ i, (x i : ℂ) • (i : G → ℂ)

theorem mckayFun_apply (x : irrChars ℂ G → ℝ) (g : G) :
    mckayFun G x g = ∑ i, (x i : ℂ) * (i : G → ℂ) g := by
  simp [mckayFun, Finset.sum_apply]

theorem mckayFun_inv (x : irrChars ℂ G → ℝ) (g : G) : mckayFun G x g⁻¹ = conj (mckayFun G x g) := by
  simp [mckayFun_apply, irrChar_inv, map_sum]

theorem pairing_irr (i j : irrChars ℂ G) :
    pairing (i : G → ℂ) (j : G → ℂ) = if i = j then 1 else 0 := by
  rw [pairing_irrChars i.2 j.2]
  simp [Subtype.ext_iff]

theorem pairing_mckayFun_irr (x : irrChars ℂ G → ℝ) (j : irrChars ℂ G) :
    pairing (mckayFun G x) (j : G → ℂ) = x j := by
  simp [mckayFun, map_sum, pairing_irr]

theorem pairing_mckayFun_self (x : irrChars ℂ G → ℝ) :
    pairing (mckayFun G x) (mckayFun G x) = ∑ i, ((x i) ^ 2 : ℝ) := by
  conv_lhs => rw [show mckayFun G x = mckayFun G x from rfl]
  rw [show pairing (mckayFun G x) (mckayFun G x) = ∑ j, (x j : ℂ) * pairing (mckayFun G x) (j : G → ℂ) by
    simp [mckayFun, map_sum, Finset.mul_sum]]
  simp [pairing_mckayFun_irr, sq]

theorem pairing_char_mul_mckayFun (x : irrChars ℂ G → ℝ) :
    pairing ((natRep G).character * mckayFun G x) (mckayFun G x) =
      ∑ i, ∑ j, ((x i * mckayR G i j * x j : ℝ) : ℂ) := by
  have h1 : (natRep G).character * mckayFun G x = ∑ i, (x i : ℂ) • ((natRep G).character * (i : G → ℂ)) := by
    simp [mckayFun, Finset.mul_sum]
  rw [h1]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mckayFun]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mckay, mckay_eq_re]
  push_cast
  rw [mckayR_symm G j i]
  ring

theorem mckayCartan_mulVec_apply (x : irrChars ℂ G → ℝ) (i : irrChars ℂ G) :
    (mckayCartan G *ᵥ x) i = 2 * x i - ∑ j, mckayR G i j * x j := by
  rw [mckayCartan, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [mulVec, dotProduct]

/-- **Etingof et al., Problem 5.5(c)** (hint): for a real vector `x` and `f = ∑ x_i χ_i`,
`xᵀ (2 I - R) x = |G|⁻¹ ∑_g (2 - χ_V(g)) |f(g)|²`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_form (x : irrChars ℂ G → ℝ) :
    x ⬝ᵥ (mckayCartan G *ᵥ x) =
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, (2 - ((natRep G).character g).re) * Complex.normSq (mckayFun G x g) := by
  have hMx := mckayCartan_mulVec_apply G x
  have hL : x ⬝ᵥ (mckayCartan G *ᵥ x) = 2 * ∑ i, x i ^ 2 - ∑ i, ∑ j, x i * mckayR G i j * x j := by
    rw [dotProduct]
    simp only [hMx, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
    · refine Finset.sum_congr rfl fun i _ ↦ ?_; refine Finset.sum_congr rfl fun j _ ↦ ?_; ring
  apply Complex.ofReal_injective
  have hP1 := pairing_mckayFun_self G x
  have hP2 := pairing_char_mul_mckayFun G x
  rw [pairing_apply] at hP1 hP2
  simp only [Pi.mul_apply] at hP2
  have key : ∀ g : G, (((2 - ((natRep G).character g).re) * Complex.normSq (mckayFun G x g) : ℝ) : ℂ) =
      2 * (mckayFun G x g * mckayFun G x g⁻¹) - (natRep G).character g * mckayFun G x g * mckayFun G x g⁻¹ := by
    intro g
    have hχ := natRep_character_eq_re G g
    set r := ((natRep G).character g).re
    rw [mckayFun_inv, hχ, mul_assoc (r : ℂ), Complex.mul_conj]
    push_cast
    ring
  calc (((x ⬝ᵥ (mckayCartan G *ᵥ x)) : ℝ) : ℂ)
      = 2 * ∑ i, ((x i ^ 2 : ℝ) : ℂ) - ∑ i, ∑ j, ((x i * mckayR G i j * x j : ℝ) : ℂ) := by
        rw [hL]; push_cast; ring
    _ = 2 * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, mckayFun G x g * mckayFun G x g⁻¹) -
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, (natRep G).character g * mckayFun G x g * mckayFun G x g⁻¹ := by
        rw [hP1, hP2]; push_cast; ring
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (((2 - ((natRep G).character g).re) *
          Complex.normSq (mckayFun G x g) : ℝ) : ℂ) := by
        rw [Finset.sum_congr rfl fun g _ ↦ key g, Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
    _ = _ := by push_cast; rfl

/-- **Etingof et al., Problem 5.5(c)**: the matrix `2 I - R` of the McKay graph is symmetric. -/
theorem mckayCartan_isHermitian : (mckayCartan G).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, mckayCartan, mckayR, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply]
  rw [mckay_natRep_symm G j i]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem mckayCartan_form_nonneg (x : irrChars ℂ G → ℝ) : 0 ≤ x ⬝ᵥ (mckayCartan G *ᵥ x) := by
  rw [mckayCartan_form]
  refine mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun g _ ↦ ?_)
  exact mul_nonneg (by linarith [natRep_character_re_le G g]) (Complex.normSq_nonneg _)

/-- **Etingof et al., Problem 5.5(c)**: the matrix `2 I - R` of the McKay graph of a finite subgroup of `SU(2)` is
positive semidefinite. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_posSemidef : (mckayCartan G).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨mckayCartan_isHermitian G, fun x ↦ ?_⟩
  simpa using mckayCartan_form_nonneg G x

/-- If the form vanishes at `x`, the class function `f = ∑ x_i χ_i` vanishes off the identity. -/
theorem mckayFun_eq_zero_of_form_eq_zero {x : irrChars ℂ G → ℝ} (hx : x ⬝ᵥ (mckayCartan G *ᵥ x) = 0)
    {g : G} (hg : g ≠ 1) : mckayFun G x g = 0 := by
  rw [mckayCartan_form] at hx
  have hc : (Nat.card G : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have hs := (mul_eq_zero.1 hx).resolve_left hc
  have hnn : ∀ g ∈ Finset.univ, 0 ≤ (2 - ((natRep G).character g).re) * Complex.normSq (mckayFun G x g) :=
    fun g _ ↦ mul_nonneg (by linarith [natRep_character_re_le G g]) (Complex.normSq_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs g (Finset.mem_univ _)
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (eq_one_of_natRep_character_re G g (by linarith)) hg
  · exact Complex.normSq_eq_zero.1 h

/-- **Etingof et al., Problem 5.5(c)**: the form of `2 I - R` vanishes only on multiples of the dimension
vector. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_form_eq_zero {x : irrChars ℂ G → ℝ} (hx : x ⬝ᵥ (mckayCartan G *ᵥ x) = 0) :
    ∃ c : ℝ, x = c • dimVec G := by
  refine ⟨x trivIrrChar, funext fun i ↦ ?_⟩
  have key : ∀ j : irrChars ℂ G, (x j : ℂ) = (Nat.card G : ℂ)⁻¹ * (mckayFun G x 1 * (j : G → ℂ) 1) := by
    intro j
    rw [← pairing_mckayFun_irr G x j, pairing_apply]
    congr 1
    rw [Finset.sum_eq_single 1]
    · simp
    · intro g _ hg
      rw [mckayFun_eq_zero_of_form_eq_zero G hx hg, zero_mul]
    · simp
  have ki := key i
  have kt := key trivIrrChar
  rw [coe_trivIrrChar, Pi.one_apply, mul_one] at kt
  rw [← mul_assoc, ← kt, irrChar_one_eq_re] at ki
  apply Complex.ofReal_injective
  rw [ki]
  simp [mul_comm]

/-- **Etingof et al., Problem 5.5(c)**: the kernel of `2 I - R` is spanned by the dimension vector. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_ker {x : irrChars ℂ G → ℝ} (hx : mckayCartan G *ᵥ x = 0) : ∃ c : ℝ, x = c • dimVec G :=
  mckayCartan_form_eq_zero G (by rw [hx, dotProduct_zero])

/-- **Etingof et al., Problem 5.5(c)**: the dimension vector is in the kernel of `2 I - R`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_mulVec_dimVec : mckayCartan G *ᵥ dimVec G = 0 := by
  funext i
  have h := sum_mckay_mul_dim (natRep G) i
  rw [finrank_natRep] at h
  simp only [mckay_eq_re, irrChar_one_eq_re] at h
  have h' : ∑ j, mckayR G i j * dimVec G j = 2 * dimVec G i := by
    apply Complex.ofReal_injective
    push_cast
    exact h
  rw [mckayCartan_mulVec_apply, h', Pi.zero_apply]
  ring

/-- **Etingof et al., Problem 5.5(c)**: the matrix `2 I - R` is not positive definite. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckayCartan_not_posDef : ¬ (mckayCartan G).PosDef := by
  intro h
  have hne : dimVec G ≠ 0 := fun h0 ↦ by
    have := dimVec_pos G trivIrrChar
    rw [h0] at this
    exact lt_irrefl _ this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 h).2 hne
  rw [mckayCartan_mulVec_dimVec] at this
  simp at this

end Form

/-! ### No self-loops -/

section Loops

variable (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G] [Invertible (Nat.card G : ℂ)]

theorem form_single (i : irrChars ℂ G) :
    (Pi.single i 1 : irrChars ℂ G → ℝ) ⬝ᵥ (mckayCartan G *ᵥ Pi.single i 1) = 2 - mckayR G i i := by
  rw [single_dotProduct, mckayCartan_mulVec_apply]
  simp [Pi.single_apply]

/-- A diagonal entry `r_ii = 2` is impossible for a nontrivial `G`: the form would vanish at the basis vector
`e_i`, so `χ_i` would vanish off the identity. -/
theorem mckayR_self_ne_two (hG : G ≠ ⊥) (i : irrChars ℂ G) : mckayR G i i ≠ 2 := by
  intro h2
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hG
    rw [eq_bot_iff]
    intro a ha
    have := hall ⟨a, ha⟩
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  set e : irrChars ℂ G → ℝ := Pi.single i 1 with he
  have hform : e ⬝ᵥ (mckayCartan G *ᵥ e) = 0 := by
    rw [he, form_single, h2]; norm_num
  have hf : mckayFun G e = (i : G → ℂ) := by
    simp [mckayFun, he, Pi.single_apply]
  have hvan : ∀ g : G, g ≠ 1 → (i : G → ℂ) g = 0 := fun g hg ↦ by
    rw [← hf]; exact mckayFun_eq_zero_of_form_eq_zero G hform hg
  have hpair : pairing (i : G → ℂ) ((trivIrrChar : irrChars ℂ G) : G → ℂ) ≠ 0 := by
    rw [pairing_apply, coe_trivIrrChar, Finset.sum_eq_single 1]
    · simp only [Pi.one_apply, mul_one, irrChar_one_eq_re]
      exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne'))
        (Complex.ofReal_ne_zero.2 (dimVec_pos G i).ne')
    · intro g _ hg; rw [hvan g hg, zero_mul]
    · simp
  rw [pairing_irr] at hpair
  have hit : i = trivIrrChar := by
    by_contra hne; exact hpair (if_neg hne)
  have := hvan g hg
  rw [hit, coe_trivIrrChar] at this
  exact one_ne_zero this

theorem mckayR_self_le_two (i : irrChars ℂ G) : mckayR G i i ≤ 2 := by
  have h := mckayCartan_form_nonneg G (Pi.single i 1)
  rw [form_single] at h
  linarith

/-- If `|G|` is odd, the natural representation is not irreducible (an irreducible representation has dimension
dividing `|G|`). -/
theorem not_isIrreducible_natRep (hodd : Odd (Fintype.card G)) : ¬ (natRep G).IsIrreducible := by
  intro h
  have := finrank_dvd_card (k := ℂ) (natRep G)
  rw [finrank_natRep] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)

/-- A subgroup of `SU(2)` not containing `-1` has odd order. -/
theorem odd_card_of_forall_ne_neg_one (h : ∀ z : G, (z.1.1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1) :
    Odd (Fintype.card G) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hodd
  have hg2 : g * g = 1 := by
    have h1 := pow_orderOf_eq_one g
    rw [hg] at h1
    simpa [sq] using h1
  have hM : (g.1.1 : Matrix (Fin 2) (Fin 2) ℂ) * g.1.1 = 1 := by
    have := congrArg (fun a : G ↦ (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ)) hg2
    simpa using this
  rcases su2_eq_one_or_neg_one g.1.2 hM with h1 | h1
  · have : g = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · exact h g h1

/-- An invariant line of the natural representation gives a one-dimensional representation `σ` with
`χ_V(g) = χ_σ(g) + χ_σ(g⁻¹)`. -/
theorem exists_line_character (hirr : ¬ (natRep G).IsIrreducible) :
    ∃ (W : Subrepresentation (natRep G)), ∀ g : G,
      (natRep G).character g = W.toRepresentation.character g + W.toRepresentation.character g⁻¹ := by
  have hW : ∃ W : Subrepresentation (natRep G), W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hno
    push Not at hno
    apply hirr
    have hnt : (⊥ : Subrepresentation (natRep G)) ≠ ⊤ := by
      intro h
      have := congrArg (fun W : Subrepresentation (natRep G) ↦ W.toSubmodule) h
      have h1 : (Pi.single 0 1 : Fin 2 → ℂ) ∈ (⊤ : Subrepresentation (natRep G)).toSubmodule :=
        Submodule.mem_top
      rw [← this] at h1
      have h1' : (Pi.single 0 1 : Fin 2 → ℂ) = 0 := (Submodule.mem_bot ℂ).1 h1
      simpa using congrFun h1' 0
    exact { toNontrivial := ⟨⟨⊥, ⊤, hnt⟩⟩
            eq_bot_or_eq_top := fun W ↦ by
              by_cases hb : W = ⊥
              · exact Or.inl hb
              · exact Or.inr (hno W hb) }
  obtain ⟨W, hb, ht⟩ := hW
  refine ⟨W, fun g ↦ ?_⟩
  have hb' : W.toSubmodule ≠ ⊥ := fun h ↦ hb (Subrepresentation.toSubmodule_injective h)
  have ht' : W.toSubmodule ≠ ⊤ := fun h ↦ ht (Subrepresentation.toSubmodule_injective h)
  have hlt := Submodule.finrank_lt ht'
  have hpos : finrank ℂ W.toSubmodule ≠ 0 := fun h ↦ hb' (Submodule.finrank_eq_zero.1 h)
  rw [finrank_natRep] at hlt
  have h1 : finrank ℂ W.toSubmodule = 1 := by omega
  obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.1 h1
  -- scalar of each group element on the line
  have hsc : ∀ h : G, ∃ c : ℂ, natRep G h (v : Fin 2 → ℂ) = c • (v : Fin 2 → ℂ) ∧
      W.toRepresentation h = c • LinearMap.id := by
    intro h
    obtain ⟨c, hc⟩ := hspan (W.toRepresentation h v)
    refine ⟨c, ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simpa [Subrepresentation.toRepresentation] using this.symm
    · apply LinearMap.ext
      intro w
      obtain ⟨t, ht⟩ := hspan w
      rw [← ht]
      simp only [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply]
  have htr : ∀ h : G, ∀ c : ℂ, W.toRepresentation h = c • LinearMap.id → W.toRepresentation.character h = c := by
    intro h c hc
    rw [Representation.character, hc, map_smul, LinearMap.trace_id, h1]
    simp
  obtain ⟨c, hcv, hcW⟩ := hsc g
  obtain ⟨c', hcv', hcW'⟩ := hsc g⁻¹
  rw [htr g c hcW, htr g⁻¹ c' hcW']
  have hvne : (v : Fin 2 → ℂ) ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  have hcc : c' * c = 1 := by
    have : natRep G g⁻¹ (natRep G g (v : Fin 2 → ℂ)) = (v : Fin 2 → ℂ) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hcv, map_smul, hcv', smul_smul] at this
    have h2 : (c * c' - 1) • (v : Fin 2 → ℂ) = 0 := by rw [sub_smul, this, one_smul, sub_self]
    have := (smul_eq_zero.1 h2).resolve_right hvne
    linear_combination this
  have hc'eq : c' = c⁻¹ := eq_inv_of_mul_eq_one_left hcc
  rw [natRep_character, hc'eq]
  refine trace_eq_of_eigenvector g.1.2.2 hvne ?_
  simpa [natRep, Matrix.toLin'_apply] using hcv

/-- **Etingof et al., Problem 5.5(c)**: the McKay graph of a finite subgroup `G ≠ 1` of `SU(2)` has no
self-loops. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_natRep_self_eq_zero_of_ne_bot (hG : G ≠ ⊥) (i : irrChars ℂ G) : mckay (natRep G) i i = 0 := by
  by_cases hz : ∃ z : G, (z.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = -1
  · obtain ⟨z, hz⟩ := hz
    exact mckay_natRep_self_eq_zero G z hz i
  push Not at hz
  obtain ⟨W, hW⟩ := exists_line_character G (not_isIrreducible_natRep G (odd_card_of_forall_ne_neg_one G hz))
  -- `r_ii = 2 a` with `a` a natural number
  have hdouble : mckay (natRep G) i i = 2 * mckay W.toRepresentation i i := by
    unfold mckay
    simp only [pairing_apply, Pi.mul_apply, hW, add_mul, Finset.sum_add_distrib, mul_add]
    have hre : ∑ g : G, W.toRepresentation.character g⁻¹ * (i : G → ℂ) g * (i : G → ℂ) g⁻¹ =
        ∑ g : G, W.toRepresentation.character g * (i : G → ℂ) g * (i : G → ℂ) g⁻¹ := by
      refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g ↦ ?_
      simp only [Equiv.inv_apply, inv_inv]
      ring
    rw [hre]
    ring
  obtain ⟨n, hn⟩ := exists_natCast_mckay W.toRepresentation i i
  rw [hn] at hdouble
  have hle := mckayR_self_le_two G i
  have hne := mckayR_self_ne_two G hG i
  rw [mckayR, hdouble] at hle hne
  have hre : ((2 : ℂ) * (n : ℂ)).re = 2 * n := by simp
  rw [hre] at hle hne
  rw [hdouble]
  have : n = 0 := by
    rcases Nat.lt_or_ge n 1 with h | h
    · omega
    · exfalso
      have h' : (n : ℝ) ≤ 1 := by linarith
      have : n = 1 := by exact_mod_cast le_antisymm (by exact_mod_cast h') h
      subst this
      norm_num at hne
  simp [this]

end Loops

/-! ### Headline -/

/-- **Etingof et al., Problem 5.5(c)**: for a finite subgroup `G ≠ 1` of `SU(2)` with its natural 2-dimensional
representation, the McKay graph is an affine Dynkin graph in the book's sense (Problem 5.3(g), multiple edges
allowed): its edge multiplicities `r_ij` are natural numbers with `r_ij = r_ji`, it has no self-loops, it is
connected, and `2 I - R` is positive semidefinite but not positive definite, with kernel spanned by the vector
of dimensions of the irreducible representations. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_isAffineDynkin (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hG : G ≠ ⊥) :
    (∀ i j, ∃ n : ℕ, mckay (natRep G) i j = n) ∧ (∀ i j, mckay (natRep G) i j = mckay (natRep G) j i) ∧
    (∀ i, mckay (natRep G) i i = 0) ∧
    (∀ i j, Relation.ReflTransGen (fun a b ↦ mckay (natRep G) a b ≠ 0) i j) ∧
    (mckayCartan G).PosSemidef ∧ ¬ (mckayCartan G).PosDef ∧
    ∀ x, mckayCartan G *ᵥ x = 0 → ∃ c : ℝ, x = c • dimVec G :=
  ⟨exists_natCast_mckay _, mckay_natRep_symm G, mckay_natRep_self_eq_zero_of_ne_bot G hG,
    mckay_natRep_connected G, mckayCartan_posSemidef G, mckayCartan_not_posDef G,
    fun _ hx ↦ mckayCartan_ker G hx⟩

end UndergradKB.RepresentationTheory
