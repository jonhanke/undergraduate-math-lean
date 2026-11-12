import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Ring.GeomSum
import UndergradKB.RepresentationTheory.FrobeniusDefs
import UndergradKB.Common.Attr

/-! # The determinant identity behind the Frobenius character formula (Etingof et al., §4.16-4.19)

In `2N` variables `x_1, …, x_N, y_1, …, y_N` the Cauchy identity (Corollary 4.49) reads
`Δ(x) Δ(y) / ∏_{i,j} (1 - x_i y_j) = ∑_σ sign σ ∏_j 1 / (1 - x_j y_{σ j})`.
Clearing denominators gives a polynomial identity (`cauchy_poly`).  Multiplying it by truncated geometric series
and comparing coefficients of `x^a y^b` gives a purely combinatorial statement (`signed_sum_contingency`):
the signed sum over `σ, τ` of the numbers of `N × N` matrices of naturals with row sums `a - ρ σ` and column sums
`b - ρ τ` equals the signed number of permutations `π` with `b = a ∘ π`.  For strictly decreasing `a, b` (of the
form `λ + ρ`) this is `1` if `a = b` and `0` otherwise; this is the orthonormality of the functions `θ_λ` in the
proof of Theorem 4.47.
-/

namespace UndergradKB.RepresentationTheory

open Finset MvPolynomial

namespace FrobeniusDet

variable {N : ℕ}

/-- The variable `x_i` of `ℂ[x, y]`. -/
noncomputable abbrev xv (i : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℂ := X (Sum.inl i)

/-- The variable `y_j` of `ℂ[x, y]`. -/
noncomputable abbrev yv (j : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℂ := X (Sum.inr j)

/-! ### The polynomial Cauchy identity -/

/-- The Cauchy identity with denominators cleared:
`∑_σ sign σ ∏_j ∏_{k ≠ σ j} (1 - x_j y_k) = ∏_{i<j} (x_i - x_j)(y_i - y_j)`. -/
theorem cauchy_poly :
    ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ •
        ∏ j, ∏ k ∈ univ.erase (σ j), (1 - xv j * yv k) =
      ∏ i, ∏ j ∈ Ioi i, ((xv i - xv j) * (yv i - yv j)) := by
  let s : Fin N ⊕ Fin N → Set ℂ := Sum.elim (fun _ => Set.range fun m : ℕ => ((m : ℂ) + 1))
    (fun _ => Set.range fun m : ℕ => -((m : ℂ) + 1))
  have hs : ∀ i, (s i).Infinite := by
    rintro (i | i)
    · refine Set.infinite_range_of_injective fun a b h => ?_
      simpa using h
    · refine Set.infinite_range_of_injective fun a b h => ?_
      simpa using h
  refine funext_set s hs fun v hv => ?_
  have hx : ∀ i, ∃ m : ℕ, v (Sum.inl i) = (m : ℂ) + 1 := fun i => by
    obtain ⟨m, hm⟩ := hv (Sum.inl i) (Set.mem_univ _)
    exact ⟨m, hm.symm⟩
  have hy : ∀ j, ∃ m : ℕ, v (Sum.inr j) = -((m : ℂ) + 1) := fun j => by
    obtain ⟨m, hm⟩ := hv (Sum.inr j) (Set.mem_univ _)
    exact ⟨m, hm.symm⟩
  set x : Fin N → ℂ := fun i => v (Sum.inl i)
  set y : Fin N → ℂ := fun j => v (Sum.inr j)
  have hx0 : ∀ i, x i ≠ 0 := fun i => by
    obtain ⟨m, hm⟩ := hx i
    simp only [x, hm]
    exact_mod_cast Nat.succ_ne_zero m
  have hxy : ∀ i j, 1 - x i * y j ≠ 0 := fun i j => by
    obtain ⟨m, hm⟩ := hx i
    obtain ⟨m', hm'⟩ := hy j
    simp only [x, y, hm, hm']
    have : (1 : ℂ) - ((m : ℂ) + 1) * -((m' : ℂ) + 1) = ((1 + (m + 1) * (m' + 1) : ℕ) : ℂ) := by
      push_cast; ring
    rw [this, Nat.cast_ne_zero]
    omega
  have key := cauchy_identity_sum x y hx0 hxy
  have hQ : (∏ i, ∏ j, (1 - x i * y j)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun j _ => hxy i j
  simp only [map_sum, map_prod, map_sub, map_mul, map_one, eval_X, map_zsmul_unit]
  rw [eq_div_iff hQ] at key
  rw [← key, sum_mul]
  refine sum_congr rfl fun σ _ => ?_
  rw [smul_mul_assoc]
  congr 1
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [← mul_prod_erase univ (fun k => 1 - x j * y k) (mem_univ (σ j)), ← mul_assoc,
    one_div_mul_cancel (hxy j (σ j)), one_mul]

/-! ### Monomial expansions -/

/-- A product of powers of variables is a monomial. -/
lemma prod_X_pow_eq_monomial {τ ι : Type*} [Fintype ι] (f : ι → τ) (e : ι → ℕ) :
    ∏ i, (X (f i) : MvPolynomial τ ℂ) ^ e i = monomial (∑ i, Finsupp.single (f i) (e i)) 1 := by
  rw [monomial_sum_one]
  simp [X_pow_eq_monomial]

/-- The exponent vector `∑_j (ρ_j) e_{σ j}` of the term of `Δ` indexed by `σ`. -/
noncomputable def deltaExp (σ : Equiv.Perm (Fin N)) : Fin N →₀ ℕ :=
  ∑ j, Finsupp.single (σ j) (rhoExp N j)

lemma deltaExp_apply (σ : Equiv.Perm (Fin N)) (i : Fin N) : deltaExp σ i = rhoExp N (σ.symm i) := by
  classical
  rw [deltaExp, Finsupp.finsetSum_apply, Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro j _ hj
    refine Finsupp.single_eq_of_ne' fun h => hj ?_
    rw [← h, Equiv.symm_apply_apply]
  · simp

/-- **The Vandermonde product as an alternating sum of monomials.**
`Δ = ∏_{i<j} (x_i - x_j) = ∑_σ sign σ x^{ρ ∘ σ⁻¹}`. -/
theorem vandermondeDelta_eq_sum :
    vandermondeDelta ℂ N = ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • monomial (deltaExp σ) (1 : ℂ) := by
  rw [← det_projVandermonde_one, Matrix.det_apply]
  refine sum_congr rfl fun σ _ => ?_
  congr 1
  simp only [Matrix.projVandermonde_apply, Pi.one_apply, one_pow, one_mul]
  exact prod_X_pow_eq_monomial (fun j => σ j) (fun j => (j.rev : ℕ))

/-- **The function `θ_λ` as a signed sum of coefficients of `∏_m p_m^{i_m}`.** -/
theorem frobChar_eq_sum (n : ℕ) (lam : Fin N → ℕ) (g : Equiv.Perm (Fin n)) :
    frobChar n N lam g = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (if deltaExp σ ≤ shiftExp lam then (cyclePoly n N g).coeff (shiftExp lam - deltaExp σ) else 0) := by
  unfold frobChar
  rw [vandermondeDelta_eq_sum, sum_mul, coeff_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [smul_mul_assoc, Units.smul_def, coeff_smul, coeff_monomial_mul', zsmul_eq_mul]
  split_ifs <;> simp

/-! ### Exponent vectors in `2N` variables -/

/-- The exponent vector of `x^a y^b`. -/
noncomputable def pairExp (a b : Fin N → ℕ) : Fin N ⊕ Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim a b)

@[simp] lemma pairExp_inl (a b : Fin N → ℕ) (i : Fin N) : pairExp a b (Sum.inl i) = a i := rfl

@[simp] lemma pairExp_inr (a b : Fin N → ℕ) (i : Fin N) : pairExp a b (Sum.inr i) = b i := rfl

lemma pairExp_le_iff (a b c d : Fin N → ℕ) : pairExp a b ≤ pairExp c d ↔ a ≤ c ∧ b ≤ d := by
  simp only [Finsupp.le_def, Sum.forall, pairExp_inl, pairExp_inr, Pi.le_def]

lemma pairExp_sub (a b c d : Fin N → ℕ) : pairExp c d - pairExp a b = pairExp (c - a) (d - b) := by
  ext (i | i) <;> simp

lemma pairExp_inj {a b c d : Fin N → ℕ} : pairExp a b = pairExp c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrArg (fun f => f (Sum.inl i)) h
    · simpa using congrArg (fun f => f (Sum.inr i)) h
  · rintro ⟨rfl, rfl⟩
    rfl

lemma rename_deltaExp_pair (σ τ : Equiv.Perm (Fin N)) :
    (deltaExp σ).mapDomain Sum.inl + (deltaExp τ).mapDomain Sum.inr =
      pairExp (fun i => rhoExp N (σ.symm i)) (fun i => rhoExp N (τ.symm i)) := by
  ext (i | i)
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_of_notMem_range,
      deltaExp_apply]
  · simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range,
      deltaExp_apply]

/-- `Δ(x) Δ(y)` as a double alternating sum of monomials. -/
theorem deltaDelta_eq_sum :
    ∏ i, ∏ j ∈ Ioi i, ((xv i - xv j) * (yv i - yv j)) =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) •
        monomial (pairExp (fun i => rhoExp N (σ.symm i)) (fun i => rhoExp N (τ.symm i))) (1 : ℂ) := by
  have hx : ∏ i, ∏ j ∈ Ioi i, (xv i - xv j) = rename Sum.inl (vandermondeDelta ℂ N) := by
    simp [vandermondeDelta, map_prod]
  have hy : ∏ i, ∏ j ∈ Ioi i, (yv i - yv j) = rename Sum.inr (vandermondeDelta ℂ N) := by
    simp [vandermondeDelta, map_prod]
  simp_rw [mul_comm (xv _ - xv _), prod_mul_distrib]
  rw [mul_comm, hx, hy, vandermondeDelta_eq_sum, map_sum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  rw [map_zsmul_unit, map_zsmul_unit, rename_monomial, rename_monomial, Units.smul_def, Units.smul_def,
    zsmul_eq_mul, zsmul_eq_mul, ← rename_deltaExp_pair, ← mul_one (1 : ℂ), ← monomial_mul_monomial,
    Algebra.smul_def]
  simp only [map_intCast]
  push_cast
  ring

/-! ### Truncated geometric series -/

/-- The truncated geometric series `1 + z + ⋯ + z^{D-1}`. -/
noncomputable def geomT (D : ℕ) (z : MvPolynomial (Fin N ⊕ Fin N) ℂ) : MvPolynomial (Fin N ⊕ Fin N) ℂ :=
  ∑ k ∈ range D, z ^ k

lemma xy_pow (i j : Fin N) (k : ℕ) :
    (xv i * yv j) ^ k = monomial (Finsupp.single (Sum.inl i) k + Finsupp.single (Sum.inr j) k) (1 : ℂ) := by
  rw [mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- The ideal generated by the `x_j ^ D`. -/
noncomputable def truncIdeal (D : ℕ) : Ideal (MvPolynomial (Fin N ⊕ Fin N) ℂ) :=
  Ideal.span (Set.range fun j : Fin N => xv j ^ D)

/-- Elements of the ideal generated by the `x_j ^ D` have no monomials with all `x`-exponents below `D`. -/
lemma coeff_eq_zero_of_mem_truncIdeal {D : ℕ} {p : MvPolynomial (Fin N ⊕ Fin N) ℂ} (hp : p ∈ truncIdeal D)
    {m : Fin N ⊕ Fin N →₀ ℕ} (hm : ∀ j, m (Sum.inl j) < D) : p.coeff m = 0 := by
  classical
  suffices h : ∀ m : Fin N ⊕ Fin N →₀ ℕ, (∀ j, m (Sum.inl j) < D) → p.coeff m = 0 from h m hm
  refine Submodule.span_induction (p := fun p _ => ∀ m : Fin N ⊕ Fin N →₀ ℕ,
    (∀ j, m (Sum.inl j) < D) → p.coeff m = 0) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨j, rfl⟩ m hm
    show (xv j ^ D).coeff m = 0
    rw [X_pow_eq_monomial, coeff_monomial, if_neg]
    intro h
    have := congrArg (fun f => f (Sum.inl j)) h
    simp only [Finsupp.single_eq_same] at this
    exact absurd (hm j) (by omega)
  · intro m _
    simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro a x _ hx m hm
    rw [smul_eq_mul, coeff_mul]
    refine sum_eq_zero fun st hst => ?_
    rw [Finset.mem_antidiagonal] at hst
    rw [hx st.2 fun j => lt_of_le_of_lt (by rw [← hst]; simp) (hm j), mul_zero]

lemma prod_sub_one_mem_truncIdeal (D : ℕ) (S : Fin N → Finset (Fin N)) :
    (∏ j, ∏ k ∈ S j, (1 - (xv j * yv k) ^ D)) - 1 ∈ truncIdeal (N := N) D := by
  rw [← Ideal.Quotient.eq]
  have h0 : ∀ j, Ideal.Quotient.mk (truncIdeal (N := N) D) (xv j ^ D) = 0 := fun j =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [map_prod, mul_pow, h0]

/-- Multiplying by an element congruent to `1` modulo the `x_j ^ D` does not change low coefficients. -/
lemma coeff_mul_of_sub_one_mem {D : ℕ} (p q : MvPolynomial (Fin N ⊕ Fin N) ℂ) (hq : q - 1 ∈ truncIdeal D)
    {m : Fin N ⊕ Fin N →₀ ℕ} (hm : ∀ j, m (Sum.inl j) < D) : (p * q).coeff m = p.coeff m := by
  have : p * q = p + p * (q - 1) := by ring
  rw [this, MvPolynomial.coeff_add, coeff_eq_zero_of_mem_truncIdeal (Ideal.mul_mem_left _ p hq) hm, add_zero]

/-! ### Coefficients of products of geometric series -/

/-- The box `[0, D)^{N × N}` of matrices. -/
noncomputable abbrev matBox (N D : ℕ) : Finset (Fin N → Fin N → ℕ) :=
  Fintype.piFinset fun _ : Fin N => Fintype.piFinset fun _ : Fin N => range D

lemma prod_geomT_eq_sum (D : ℕ) :
    ∏ i : Fin N, ∏ j : Fin N, geomT D (xv i * yv j) =
      ∑ M ∈ matBox N D, monomial (pairExp (fun i => ∑ j, M i j) (fun j => ∑ i, M i j)) (1 : ℂ) := by
  classical
  unfold geomT
  simp_rw [xy_pow]
  rw [prod_congr rfl fun i _ => prod_univ_sum (fun _ => range D) _, prod_univ_sum]
  refine sum_congr rfl fun M _ => ?_
  have hE : ∑ i, ∑ j, (Finsupp.single (Sum.inl i) (M i j) + Finsupp.single (Sum.inr j) (M i j)) =
      pairExp (fun i => ∑ j, M i j) (fun j => ∑ i, M i j) := by
    ext (i | i)
    · simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply, Sum.inl.injEq,
        reduceCtorEq, if_false, add_zero, pairExp_inl]
      rw [Finset.sum_eq_single i (fun i' _ h => by simp [h]) (by simp)]
      simp
    · simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply, Sum.inr.injEq,
        reduceCtorEq, if_false, zero_add, pairExp_inr]
      refine sum_congr rfl fun i' _ => ?_
      rw [Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)]
      simp
  rw [← hE, monomial_sum_one]
  refine prod_congr rfl fun i _ => ?_
  rw [monomial_sum_one]

lemma coeff_prod_geomT (D : ℕ) (α β : Fin N → ℕ) :
    (∏ i : Fin N, ∏ j : Fin N, geomT D (xv i * yv j)).coeff (pairExp α β) =
      (((matBox N D).filter fun M => (∀ i, ∑ j, M i j = α i) ∧ ∀ j, ∑ i, M i j = β j).card : ℂ) := by
  classical
  rw [prod_geomT_eq_sum, coeff_sum]
  simp only [coeff_monomial, pairExp_inj, funext_iff]
  rw [sum_boole]

lemma card_matBox_eq_contingency {D : ℕ} (α β : Fin N → ℕ) (hD : ∑ i, α i < D) :
    ((matBox N D).filter fun M => (∀ i, ∑ j, M i j = α i) ∧ ∀ j, ∑ i, M i j = β j).card =
      contingency α β := by
  unfold contingency
  congr 1
  ext M
  simp only [mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 : α i ≤ ∑ i, α i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    rw [h.1 i] at h1
    omega
  · rintro ⟨-, h⟩
    refine ⟨fun i j => ?_, h⟩
    have h1 : M i j ≤ ∑ j, M i j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 : α i ≤ ∑ i, α i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    rw [h.1 i] at h1
    omega

lemma coeff_prod_geomT_perm (D : ℕ) (σ : Equiv.Perm (Fin N)) (a b : Fin N → ℕ) :
    (∏ j : Fin N, geomT D (xv j * yv (σ j))).coeff (pairExp a b) =
      if (∀ j, a j < D) ∧ b = a ∘ σ.symm then 1 else 0 := by
  classical
  unfold geomT
  simp_rw [xy_pow]
  rw [prod_univ_sum (fun _ => range D), coeff_sum]
  have hexp : ∀ r : Fin N → ℕ, ∏ j, monomial (Finsupp.single (Sum.inl j) (r j) +
      Finsupp.single (Sum.inr (σ j)) (r j)) (1 : ℂ) = monomial (pairExp r (r ∘ σ.symm)) 1 := by
    intro r
    rw [← monomial_sum_one]
    congr 2
    ext (i | i)
    · simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply, Sum.inl.injEq,
        reduceCtorEq, if_false, add_zero, pairExp_inl]
      rw [Finset.sum_eq_single i (fun i' _ h => by simp [h]) (by simp)]
      simp
    · simp only [Finsupp.finsetSum_apply, Finsupp.add_apply, Finsupp.single_apply, reduceCtorEq,
        if_false, zero_add, Sum.inr.injEq, pairExp_inr, Function.comp_apply]
      rw [Finset.sum_eq_single (σ.symm i)]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro h
        exact hj (by rw [← h, Equiv.symm_apply_apply])
      · simp
  simp_rw [hexp, coeff_monomial, pairExp_inj]
  have : ∀ r : Fin N → ℕ, (r = a ∧ r ∘ σ.symm = b) ↔ (r = a ∧ b = a ∘ σ.symm) := by
    intro r
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨rfl, h.symm⟩
  simp_rw [this, ite_and]
  rw [sum_ite_eq']
  simp only [Fintype.mem_piFinset, mem_range]

/-! ### The signed count of contingency tables -/

lemma cauchy_term_mul (D : ℕ) (σ : Equiv.Perm (Fin N)) :
    (∏ j, ∏ k ∈ univ.erase (σ j), (1 - xv j * yv k)) * ∏ i : Fin N, ∏ j : Fin N, geomT D (xv i * yv j) =
      (∏ j : Fin N, geomT D (xv j * yv (σ j))) * ∏ j, ∏ k ∈ univ.erase (σ j), (1 - (xv j * yv k) ^ D) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [← mul_prod_erase univ (fun k => geomT D (xv j * yv k)) (mem_univ (σ j))]
  have : ∏ k ∈ univ.erase (σ j), (1 - (xv j * yv k) ^ D) =
      ∏ k ∈ univ.erase (σ j), ((1 - xv j * yv k) * geomT D (xv j * yv k)) := by
    refine prod_congr rfl fun k _ => ?_
    rw [geomT, mul_neg_geom_sum]
  rw [this, prod_mul_distrib]
  ring

/-- **The signed count of contingency tables.**  For exponent vectors `a, b`,
`∑_{σ, τ} sign σ sign τ · #{matrices with row sums a - ρ σ⁻¹ and column sums b - ρ τ⁻¹}` (terms with a negative
entry omitted) equals `∑_σ sign σ [b = a ∘ σ⁻¹]`.  This is the comparison of the coefficients of `x^a y^b` in
the Cauchy identity `Δ(x) Δ(y) ∏_{i,j} (1 - x_i y_j)⁻¹ = det (1 - x_i y_j)⁻¹`. -/
@[kb "etingof2011" "Lemma 4.48, p. 62"]
theorem signed_sum_contingency (a b : Fin N → ℕ) :
    ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, rhoExp N (σ.symm i) ≤ a i) ∧ (∀ i, rhoExp N (τ.symm i) ≤ b i) then
          (contingency (fun i => a i - rhoExp N (σ.symm i)) (fun i => b i - rhoExp N (τ.symm i)) : ℂ)
        else 0) =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if b = a ∘ σ.symm then 1 else 0) := by
  classical
  set D := ∑ i, a i + 1 with hD
  have haD : ∀ j, a j < D := fun j => by
    have : a j ≤ ∑ i, a i := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    omega
  set H := ∏ i : Fin N, ∏ j : Fin N, geomT D (xv i * yv j)
  have h1 : ((∏ i, ∏ j ∈ Ioi i, ((xv i - xv j) * (yv i - yv j))) * H).coeff (pairExp a b) =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, rhoExp N (σ.symm i) ≤ a i) ∧ (∀ i, rhoExp N (τ.symm i) ≤ b i) then
          (contingency (fun i => a i - rhoExp N (σ.symm i)) (fun i => b i - rhoExp N (τ.symm i)) : ℂ)
        else 0) := by
    rw [deltaDelta_eq_sum, sum_mul, coeff_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_mul, coeff_sum]
    refine sum_congr rfl fun τ _ => ?_
    rw [smul_mul_assoc, coeff_smul, smul_eq_mul, coeff_monomial_mul']
    simp only [pairExp_le_iff, Pi.le_def, one_mul]
    split_ifs with hle
    · congr 1
      rw [pairExp_sub, coeff_prod_geomT, card_matBox_eq_contingency]
      · rfl
      · calc ∑ i, (a - fun i => rhoExp N (σ.symm i)) i ≤ ∑ i, a i :=
              sum_le_sum fun i _ => Nat.sub_le _ _
          _ < D := by omega
    · rfl
  have h2 : ((∏ i, ∏ j ∈ Ioi i, ((xv i - xv j) * (yv i - yv j))) * H).coeff (pairExp a b) =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * (if b = a ∘ σ.symm then 1 else 0) := by
    rw [← cauchy_poly, sum_mul, coeff_sum]
    refine sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, Units.smul_def, coeff_smul, zsmul_eq_mul, cauchy_term_mul,
      coeff_mul_of_sub_one_mem _ _ (prod_sub_one_mem_truncIdeal D _) (by simpa using haD),
      coeff_prod_geomT_perm]
    simp [haD]
  rw [← h1, h2]

/-- A permutation `π` with `a ∘ π` strictly decreasing, for `a` strictly decreasing, is the identity. -/
lemma perm_eq_one_of_strictAnti {a : Fin N → ℕ} (ha : StrictAnti a) {π : Equiv.Perm (Fin N)}
    (h : StrictAnti (a ∘ π)) : π = 1 := by
  have hmono : StrictMono π := fun i j hij => ha.lt_iff_gt.1 (h hij)
  have hle : ∀ i : Fin N, (i : ℕ) ≤ (π i : ℕ) := fun i => hmono.le_apply
  have hsum : ∑ i : Fin N, (π i : ℕ) = ∑ i : Fin N, (i : ℕ) := Equiv.sum_comp π (fun i : Fin N => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 hsum.symm
  ext i
  exact (this i (mem_univ i)).symm

/-- **Orthonormality in combinatorial form.**  For strictly decreasing exponent vectors `a, b` (such as `λ + ρ`
and `μ + ρ`), the signed count of contingency tables is `1` if `a = b` and `0` otherwise. -/
@[kb "etingof2011" "Lemma 4.48, p. 62"]
theorem signed_sum_contingency_strictAnti {a b : Fin N → ℕ} (ha : StrictAnti a) (hb : StrictAnti b) :
    ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if (∀ i, rhoExp N (σ.symm i) ≤ a i) ∧ (∀ i, rhoExp N (τ.symm i) ≤ b i) then
          (contingency (fun i => a i - rhoExp N (σ.symm i)) (fun i => b i - rhoExp N (τ.symm i)) : ℂ)
        else 0) = if a = b then 1 else 0 := by
  rw [signed_sum_contingency, sum_eq_single (1 : Equiv.Perm (Fin N))]
  · rw [show a ∘ ⇑(Equiv.symm (1 : Equiv.Perm (Fin N))) = a from rfl]
    simp [eq_comm]
  · intro σ _ hσ
    rw [if_neg, mul_zero]
    intro h
    apply hσ
    have : σ.symm = 1 := perm_eq_one_of_strictAnti ha (h ▸ hb)
    rw [← Equiv.Perm.inv_def] at this
    exact inv_eq_one.1 this
  · simp

end FrobeniusDet

end UndergradKB.RepresentationTheory
