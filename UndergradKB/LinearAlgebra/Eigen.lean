import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import UndergradKB.Common.Attr

/-! # Invariant subspaces, eigenvalues and polynomials of an operator (Axler 5.A-5.B; Hefferon Five.II, Five.IV)

`V` is a vector space over a field `K` (Axler's `F`); the results are stated over a general field
whenever the book's proof works over one.  A subspace `U` is *invariant* under `T` when
`∀ v ∈ U, T v ∈ U`.
-/

open Polynomial Module End
open scoped Matrix

namespace UndergradKB.LinearAlgebra

section Operators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The subspaces `{0}`, `V`, `null T` and `range T` are invariant under `T`. -/
@[kb "axler2024" "5.4, p. 151"]
theorem axler_5_4 (T : End K V) :
    (∀ v ∈ (⊥ : Submodule K V), T v ∈ (⊥ : Submodule K V)) ∧
    (∀ v ∈ (⊤ : Submodule K V), T v ∈ (⊤ : Submodule K V)) ∧
    (∀ v ∈ LinearMap.ker T, T v ∈ LinearMap.ker T) ∧
    (∀ v ∈ LinearMap.range T, T v ∈ LinearMap.range T) := by
  refine ⟨?_, fun _ _ => Submodule.mem_top, ?_, ?_⟩
  · intro v hv
    rw [Submodule.mem_bot] at hv ⊢
    simp [hv]
  · intro v hv
    simp [LinearMap.mem_ker.mp hv]
  · intro v _
    exact ⟨v, rfl⟩

/-- `p(T)` commutes with `T`. -/
lemma aeval_comm_apply (T : End K V) (p : K[X]) (v : V) :
    T (aeval T p v) = aeval T p (T v) := by
  have h : Commute (aeval T p) T := by
    simpa using (Commute.all p X).map (aeval T : K[X] →ₐ[K] End K V)
  exact congr($(h.eq) v).symm

/-- For every polynomial `p`, the null space and the range of `p(T)` are invariant under `T`. -/
@[kb "axler2024" "5.18, p. 157"]
theorem axler_5_18 (T : End K V) (p : K[X]) :
    (∀ v ∈ LinearMap.ker (aeval T p), T v ∈ LinearMap.ker (aeval T p)) ∧
    (∀ v ∈ LinearMap.range (aeval T p), T v ∈ LinearMap.range (aeval T p)) := by
  constructor
  · intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← aeval_comm_apply, hv, map_zero]
  · rintro v ⟨w, rfl⟩
    exact ⟨T w, (aeval_comm_apply T p w).symm⟩

end Operators

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A square matrix `A` has eigenvalue `μ` with eigenvector `z` (nonzero) when `A z = μ z`; in terms
of Mathlib this says `μ` is an eigenvalue of the operator `Matrix.toLin' A`. -/
@[kb "hefferon2020" "Five.II.3.5, p. 423"]
theorem hefferon_Five_II_3_5 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) (μ : K) :
    (∃ z : n → K, z ≠ 0 ∧ A.mulVec z = μ • z) ↔ HasEigenvalue (Matrix.toLin' A) μ := by
  constructor
  · rintro ⟨z, hz, h⟩
    exact hasEigenvalue_of_hasEigenvector
      ⟨mem_eigenspace_iff.mpr (by simpa [Matrix.toLin'_apply] using h), hz⟩
  · intro h
    obtain ⟨z, hz⟩ := h.exists_hasEigenvector
    exact ⟨z, hz.2, by simpa [Matrix.toLin'_apply] using mem_eigenspace_iff.mp hz.1⟩

/-- Rotation by 90 degrees on `K × K`: `(w, z) ↦ (-z, w)`. -/
def rot90 (K : Type*) [Field K] : End K (K × K) where
  toFun v := (-v.2, v.1)
  map_add' v w := by simp [add_comm]
  map_smul' c v := by simp

@[simp] lemma rot90_apply (v : K × K) : rot90 K v = (-v.2, v.1) := rfl

lemma hasEigenvalue_rot90_iff (μ : K) : HasEigenvalue (rot90 K) μ ↔ μ ^ 2 + 1 = 0 := by
  constructor
  · intro h
    obtain ⟨⟨w, z⟩, hv⟩ := h.exists_hasEigenvector
    have h1 := mem_eigenspace_iff.mp hv.1
    simp only [rot90_apply, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h1
    obtain ⟨e1, e2⟩ := h1
    have hz : z ≠ 0 := by
      rintro rfl
      apply hv.2
      simp only [neg_zero] at e1
      simp [e2]
    have : (μ ^ 2 + 1) * z = 0 := by
      rw [e2] at e1
      linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_right hz
  · intro h
    refine hasEigenvalue_of_hasEigenvector (x := (μ, 1)) ⟨mem_eigenspace_iff.mpr ?_, ?_⟩
    · simp only [rot90_apply, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      constructor
      · linear_combination -h
      · ring
    · simp

/-- Rotation by 90 degrees of `ℝ²` has no eigenvalue, while rotation of `ℂ²` has exactly the
eigenvalues `i` and `-i`. -/
@[kb "axler2024" "5.9, p. 153"]
theorem axler_5_9 :
    (∀ μ : ℝ, ¬ HasEigenvalue (rot90 ℝ) μ) ∧
    (∀ μ : ℂ, HasEigenvalue (rot90 ℂ) μ ↔ μ = Complex.I ∨ μ = -Complex.I) := by
  constructor
  · intro μ h
    rw [hasEigenvalue_rot90_iff] at h
    nlinarith [sq_nonneg μ]
  · intro μ
    rw [hasEigenvalue_rot90_iff]
    constructor
    · intro h
      have : (μ - Complex.I) * (μ + Complex.I) = 0 := by
        linear_combination h - Complex.I_sq
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (rfl | rfl) <;> simp

/-- Multiplication by `z` on the polynomial space `K[z]` has no eigenvalue (so finite dimension is
needed for the existence of eigenvalues over an algebraically closed field). -/
@[kb "axler2024" "5.20, p. 161"]
theorem axler_5_20 (μ : K) : ¬ HasEigenvalue (LinearMap.mulLeft K (X : K[X])) μ := by
  intro h
  obtain ⟨p, hp⟩ := h.exists_hasEigenvector
  have h1 := mem_eigenspace_iff.mp hp.1
  simp only [LinearMap.mulLeft_apply] at h1
  have : (X - C μ) * p = 0 := by
    rw [sub_mul, h1]
    simp [Polynomial.C_mul']
  rcases mul_eq_zero.mp this with h | h
  · exact X_sub_C_ne_zero μ h
  · exact hp.2 h

end Eigen

section Minpoly

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma natDegree_minpoly_le_finrank (T : End K V) : (minpoly K T).natDegree ≤ finrank K V := by
  rw [← LinearMap.charpoly_natDegree]
  exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly T) (LinearMap.charpoly_monic T).ne_zero

/-- An operator on a finite-dimensional space has at most `dim V` distinct eigenvalues. -/
@[kb "axler2024" "5.12, p. 154"]
theorem axler_5_12 (T : End K V) (s : Finset K) (hs : ∀ μ ∈ s, HasEigenvalue T μ) :
    s.card ≤ finrank K V := by
  have hne : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  have hle : s.val ≤ (minpoly K T).roots := by
    rw [Multiset.le_iff_subset s.nodup]
    intro μ hμ
    rw [mem_roots hne]
    exact (hasEigenvalue_iff_isRoot).mp (hs μ hμ)
  calc s.card = Multiset.card s.val := rfl
    _ ≤ Multiset.card (minpoly K T).roots := Multiset.card_le_card hle
    _ ≤ (minpoly K T).natDegree := card_roots' _
    _ ≤ finrank K V := natDegree_minpoly_le_finrank T

/-- Existence and uniqueness of the minimal polynomial: there is exactly one monic polynomial of
least degree annihilating `T`, and its degree is at most `dim V`. -/
@[kb "axler2024" "5.22, p. 162"]
theorem axler_5_22 (T : End K V) :
    (∃! p : K[X], p.Monic ∧ aeval T p = 0 ∧
      ∀ q : K[X], q.Monic → aeval T q = 0 → p.natDegree ≤ q.natDegree) ∧
    (minpoly K T).natDegree ≤ finrank K V := by
  have hint : IsIntegral K T := Algebra.IsIntegral.isIntegral T
  refine ⟨⟨minpoly K T, ⟨minpoly.monic hint, minpoly.aeval K T, ?_⟩, ?_⟩,
    natDegree_minpoly_le_finrank T⟩
  · intro q hq hq0
    exact natDegree_le_of_dvd (minpoly.dvd K T hq0) hq.ne_zero
  · rintro p ⟨hpm, hp0, hpmin⟩
    have h1 : minpoly K T ∣ p := minpoly.dvd K T hp0
    have h2 : p.natDegree ≤ (minpoly K T).natDegree :=
      hpmin _ (minpoly.monic hint) (minpoly.aeval K T)
    exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm h1 h2

/-- The zeros of the minimal polynomial are exactly the eigenvalues of `T`. -/
@[kb "axler2024" "5.27, p. 164"]
theorem axler_5_27a (T : End K V) (μ : K) : (minpoly K T).IsRoot μ ↔ HasEigenvalue T μ :=
  hasEigenvalue_iff_isRoot.symm

/-- Over an algebraically closed field the minimal polynomial is a product `∏ (z - λⱼ)` over a list
containing exactly the eigenvalues. -/
@[kb "axler2024" "5.27, p. 164"]
theorem axler_5_27b [IsAlgClosed K] (T : End K V) :
    ∃ l : List K, minpoly K T = (l.map fun μ => X - C μ).prod ∧ ∀ μ, μ ∈ l ↔ HasEigenvalue T μ := by
  have hint : IsIntegral K T := Algebra.IsIntegral.isIntegral T
  have hne : minpoly K T ≠ 0 := minpoly.ne_zero hint
  refine ⟨(minpoly K T).roots.toList, ?_, ?_⟩
  · have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (minpoly.monic hint)
      (IsAlgClosed.card_roots_eq_natDegree)
    rw [← h]
    conv_lhs => rw [← h]
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  · intro μ
    rw [Multiset.mem_toList, mem_roots hne]
    exact hasEigenvalue_iff_isRoot.symm

end Minpoly

section Restrict

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma restrict_pow_apply (T : End K V) (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) (n : ℕ)
    (u : U) : (((LinearMap.restrict T hU) ^ n) u : V) = (T ^ n) (u : V) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

lemma aeval_restrict_apply (T : End K V) (U : Submodule K V) (hU : ∀ x ∈ U, T x ∈ U) (p : K[X])
    (u : U) : ((aeval (LinearMap.restrict T hU) p u : U) : V) = aeval T p (u : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [aeval_monomial, Module.algebraMap_end_apply, restrict_pow_apply]

/-- For a `T`-invariant subspace `U`, the minimal polynomial of the restriction `T|_U` divides the
minimal polynomial of `T`. -/
@[kb "axler2024" "5.31, p. 166"]
theorem axler_5_31 [FiniteDimensional K V] (T : End K V) (U : Submodule K V)
    (hU : ∀ x ∈ U, T x ∈ U) : minpoly K (LinearMap.restrict T hU) ∣ minpoly K T := by
  apply minpoly.dvd
  ext u
  rw [aeval_restrict_apply, minpoly.aeval]
  simp

end Restrict

section Quotient

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma mapQ_pow_apply (T : End K V) (U : Submodule K V) (hU : U ≤ U.comap T) (n : ℕ) (v : V) :
    ((U.mapQ U T hU) ^ n) (U.mkQ v) = U.mkQ ((T ^ n) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    have h : (U.mapQ U T hU) (U.mkQ v) = U.mkQ (T v) := rfl
    rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, h, ih]

lemma aeval_mapQ_apply (T : End K V) (U : Submodule K V) (hU : U ≤ U.comap T) (p : K[X]) (v : V) :
    aeval (U.mapQ U T hU) p (U.mkQ v) = U.mkQ (aeval T p v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial]
    simp only [mul_apply_eq_comp, Module.algebraMap_end_apply, map_smul, mapQ_pow_apply]

/-- The quotient operator `T/U` on `V/U` of an operator `T` with invariant subspace `U` satisfies
`(T/U)(v + U) = T v + U`, and in finite dimension every eigenvalue of `T/U` is an eigenvalue of
`T`. -/
@[kb "axler2024" "Ex5A.38, p. 160"]
theorem axler_5A_38 [FiniteDimensional K V] (T : End K V) (U : Submodule K V)
    (hU : ∀ x ∈ U, T x ∈ U) :
    (∀ v : V, (U.mapQ U T hU) (U.mkQ v) = U.mkQ (T v)) ∧
    ∀ μ : K, HasEigenvalue (U.mapQ U T hU) μ → HasEigenvalue T μ := by
  refine ⟨fun v => by simp, fun μ h => ?_⟩
  rw [hasEigenvalue_iff_isRoot] at h ⊢
  have hdvd : minpoly K (U.mapQ U T hU) ∣ minpoly K T := by
    apply minpoly.dvd
    refine LinearMap.ext fun q => ?_
    obtain ⟨v, rfl⟩ := U.mkQ_surjective q
    rw [LinearMap.zero_apply]
    change aeval (U.mapQ U T hU) (minpoly K T) (U.mkQ v) = 0
    rw [aeval_mapQ_apply, minpoly.aeval]
    simp
  exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr h).trans hdvd)

end Quotient

section Companion

variable {K : Type*} [Field K]

/-- The companion matrix of `p = z^n + a_{n-1} z^{n-1} + ... + a_0`: `n × n`, with `1` just below the
diagonal and last column `(-a_0, ..., -a_{n-1})` (Axler, 5.26 and Exercise 5B.16). -/
def companion (p : K[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  Matrix.of fun i j =>
    (if (j : ℕ) + 1 = i then 1 else 0) - (if (j : ℕ) + 1 = p.natDegree then p.coeff i else 0)

lemma companion_mulVec_single (p : K[X]) (j i : Fin p.natDegree) :
    (companion p *ᵥ Pi.single j 1) i =
      (if (j : ℕ) + 1 = i then 1 else 0) - (if (j : ℕ) + 1 = p.natDegree then p.coeff i else 0) := by
  simp [companion, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma companion_pow_e (p : K[X]) (hp : 0 < p.natDegree) (k : ℕ) (hk : k < p.natDegree) :
    (companion p ^ k) *ᵥ Pi.single ⟨0, hp⟩ 1 = Pi.single ⟨k, hk⟩ 1 := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    have hk' : k < p.natDegree := by omega
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih hk']
    funext i
    rw [companion_mulVec_single]
    have : (k + 1 = p.natDegree) = False := by simp [hk.ne]
    simp only [this, Pi.single_apply, Fin.ext_iff, ite_false, sub_zero]
    simp [eq_comm]

lemma companion_pow_natDegree (p : K[X]) (hp : 0 < p.natDegree) :
    (companion p ^ p.natDegree) *ᵥ Pi.single ⟨0, hp⟩ 1 = fun i : Fin p.natDegree => -p.coeff (i : ℕ) := by
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  have hm' : m < p.natDegree := by omega
  have h : companion p ^ p.natDegree = companion p * companion p ^ m := by
    rw [← pow_succ']
    exact congrArg (companion p ^ ·) hm
  rw [h, ← Matrix.mulVec_mulVec, companion_pow_e p hp m hm']
  funext i
  rw [companion_mulVec_single]
  have e1 : m + 1 = p.natDegree := hm.symm
  have e2 : ¬ (p.natDegree = (i : ℕ)) := by have := i.2; omega
  simp [e1, e2]

lemma sum_coeff_apply {n : ℕ} (q : K[X]) (d : ℕ) (w : ℕ → (Fin n → K))
    (hw : ∀ k < d, ∀ i : Fin n, w k i = if (i : ℕ) = k then 1 else 0) (i : Fin n)
    (hi : (i : ℕ) < d) : (∑ k ∈ Finset.range d, q.coeff k • w k) i = q.coeff i := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k hk => by rw [hw k (Finset.mem_range.mp hk) i])]
  simp [hi]

lemma aeval_companion_mulVec (p q : K[X]) (v : Fin p.natDegree → K) :
    (aeval (companion p) q) *ᵥ v =
      ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k • ((companion p ^ k) *ᵥ v) := by
  rw [aeval_eq_sum_range, Matrix.sum_mulVec]
  simp [Matrix.smul_mulVec]

/-- The companion matrix of a monic polynomial `p` of positive degree has `p` as its minimal
polynomial; in particular every monic polynomial is the minimal polynomial of some operator. -/
@[kb "axler2024" "5.26, p. 164", kb "axler2024" "Ex5B.16, p. 170"]
theorem axler_5_26 (p : K[X]) (hm : p.Monic) (hp : 0 < p.natDegree) :
    minpoly K (companion p) = p := by
  have hint : IsIntegral K (companion p) := Algebra.IsIntegral.isIntegral _
  have hv' : ∀ k < p.natDegree, ∀ i : Fin p.natDegree,
      ((companion p ^ k) *ᵥ Pi.single ⟨0, hp⟩ 1) i = if (i : ℕ) = k then 1 else 0 := by
    intro k hk i
    rw [companion_pow_e p hp k hk, Pi.single_apply]
    simp [Fin.ext_iff]
  have h0 : aeval (companion p) p *ᵥ Pi.single ⟨0, hp⟩ 1 = 0 := by
    rw [aeval_companion_mulVec, Finset.sum_range_succ, companion_pow_natDegree,
      hm.coeff_natDegree]
    funext i
    rw [Pi.add_apply, sum_coeff_apply p p.natDegree _ hv' i i.2]
    simp
  have hall : aeval (companion p) p = 0 := by
    ext i j
    have hj : aeval (companion p) p *ᵥ Pi.single j 1 = 0 := by
      have hjj : Pi.single j 1 = (companion p ^ (j : ℕ)) *ᵥ Pi.single ⟨0, hp⟩ 1 :=
        (companion_pow_e p hp j j.2).symm
      have hc : Commute (aeval (companion p) p) (companion p ^ (j : ℕ)) := by
        simpa using (Commute.all p (X ^ (j : ℕ))).map (aeval (companion p) :
          K[X] →ₐ[K] Matrix (Fin p.natDegree) (Fin p.natDegree) K)
      rw [hjj, Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    have := congrFun hj i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hdvd := minpoly.dvd K (companion p) hall
  have hmm := minpoly.monic hint
  have hle : p.natDegree ≤ (minpoly K (companion p)).natDegree := by
    by_contra hlt
    push Not at hlt
    have h1 : aeval (companion p) (minpoly K (companion p)) *ᵥ Pi.single ⟨0, hp⟩ 1 = 0 := by
      rw [minpoly.aeval, Matrix.zero_mulVec]
    rw [aeval_companion_mulVec] at h1
    have h2 := congrFun h1 ⟨(minpoly K (companion p)).natDegree, hlt⟩
    rw [sum_coeff_apply _ ((minpoly K (companion p)).natDegree + 1) _
      (fun k hk i => hv' k (by omega) i) _ (by simp)] at h2
    have := hmm.coeff_natDegree
    simp only [Pi.zero_apply] at h2
    rw [h2] at this
    exact zero_ne_one this
  exact (eq_of_monic_of_dvd_of_natDegree_le hmm hm hdvd hle).symm

end Companion

end UndergradKB.LinearAlgebra
