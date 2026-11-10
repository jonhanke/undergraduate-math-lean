import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.Hyper
import UndergradKB.Combinatorics.AeqB.GosperForm
import UndergradKB.Combinatorics.AeqB.GosperAlgorithm

/-!
# Algorithms Poly and Hyper (Petkovsek–Wilf–Zeilberger, "A = B", §8.3, 8.4)

* Algorithm Poly (CO-487): the polynomial solutions of `L y = f` of degree `≤ d` are the solutions
  of an affine linear system on `degreeLT`; with the degree bound of Proposition 8.3.1 every
  polynomial solution is found.
* Algorithm Hyper (CO-488, CO-490): a finite candidate set `(a, b, z, c)`; a hypergeometric
  solution exists iff some candidate works, and every hypergeometric solution comes from a
  candidate.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

variable {K : Type*} [Field K] [CharZero K]

/-! ### Algorithm Poly -/

/-- The map `y ↦ L y = ∑ p_i(n) y(n+i)` as a `K`-linear endomorphism of `K[n]`. -/
def applyOpLin (p : ℕ → K[X]) (r : ℕ) : K[X] →ₗ[K] K[X] where
  toFun := applyOp p r
  map_add' y z := by
    simp only [applyOp, add_comp, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [applyOp, smul_comp, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]

theorem applyOpLin_apply (p : ℕ → K[X]) (r : ℕ) (y : K[X]) : applyOpLin p r y = applyOp p r y :=
  rfl

/-- The linear map of algorithm Poly: `L` restricted to polynomials of degree `< d`
(unknown coefficients `y_0, …, y_{d-1}`). -/
def polyMap (p : ℕ → K[X]) (r d : ℕ) : degreeLT K d →ₗ[K] K[X] :=
  applyOpLin p r ∘ₗ (degreeLT K d).subtype

/-- The polynomial solutions of `L y = 0` of degree `≤ d` form the kernel of `polyMap p r (d+1)`. -/
theorem mem_ker_polyMap_iff (p : ℕ → K[X]) (r d : ℕ) (y : K[X]) :
    (y.natDegree ≤ d ∧ applyOp p r y = 0) ↔
      ∃ hy : y ∈ degreeLT K (d + 1), (⟨y, hy⟩ : degreeLT K (d + 1)) ∈ LinearMap.ker (polyMap p r (d + 1)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y ∈ degreeLT K (d + 1) := by
      rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
      exact degree_le_of_natDegree_le h1
    exact ⟨hy, h2⟩
  · rintro ⟨hy, h⟩
    rw [degreeLT_succ_eq_degreeLE, mem_degreeLE] at hy
    exact ⟨natDegree_le_of_degree_le hy, h⟩

/-- More generally the solutions of `L y = f` of degree `≤ d` are the preimage of `f`. -/
theorem mem_preimage_polyMap_iff (p : ℕ → K[X]) (r d : ℕ) (f y : K[X]) :
    (y.natDegree ≤ d ∧ applyOp p r y = f) ↔
      ∃ hy : y ∈ degreeLT K (d + 1), polyMap p r (d + 1) ⟨y, hy⟩ = f := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy : y ∈ degreeLT K (d + 1) := by
      rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
      exact degree_le_of_natDegree_le h1
    exact ⟨hy, h2⟩
  · rintro ⟨hy, h⟩
    rw [degreeLT_succ_eq_degreeLE, mem_degreeLE] at hy
    exact ⟨natDegree_le_of_degree_le hy, h⟩

open Classical in
theorem degreePoly_ne_zero (p : ℕ → K[X]) (r : ℕ) (b : ℤ)
    (hbmax : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b) :
    degreePoly p r b ≠ 0 := by
  set S := (Finset.range (r + 1)).filter
      (fun j => qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b) with hS
  have hne : S.Nonempty := by
    obtain ⟨j, hj, h⟩ := hbmax
    exact ⟨j, by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, h⟩⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image S id hne
  have hcoeff : (degreePoly p r b).coeff j₀ = (qPoly p r j₀).leadingCoeff := by
    unfold degreePoly
    rw [finsetSum_coeff, Finset.sum_eq_single j₀]
    · rw [coeff_C_mul]
      have := (monic_descPochhammer K j₀).leadingCoeff
      rw [leadingCoeff, descPochhammer_natDegree] at this
      rw [this, mul_one]
    · intro j hj hjne
      have hlt : j < j₀ := lt_of_le_of_ne (hmax j hj) hjne
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact hlt),
        mul_zero]
    · intro h; exact absurd hj₀ h
  intro h0
  have hq : qPoly p r j₀ ≠ 0 := ((Finset.mem_filter.1 hj₀).2).1
  have := congrArg (fun q => q.coeff j₀) h0
  simp only [coeff_zero] at this
  rw [hcoeff] at this
  exact leadingCoeff_ne_zero.2 hq this

/-- The nonnegative integer roots of the degree polynomial are bounded. -/
theorem exists_root_bound (p : ℕ → K[X]) (r : ℕ) (b : ℤ)
    (hbmax : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b) :
    ∃ d₁ : ℕ, ∀ x : ℕ, (degreePoly p r b).eval (x : K) = 0 → x ≤ d₁ := by
  classical
  have hα := degreePoly_ne_zero p r b hbmax
  have hfin : {x : ℕ | (degreePoly p r b).eval (x : K) = 0}.Finite := by
    have : {x : ℕ | (x : K) ∈ (degreePoly p r b).roots.toFinset}.Finite :=
      Set.Finite.preimage (Nat.cast_injective.injOn) (Finset.finite_toSet _)
    refine this.subset fun x hx => ?_
    show (x : K) ∈ (degreePoly p r b).roots.toFinset
    rw [Multiset.mem_toFinset, mem_roots hα]
    exact hx
  obtain ⟨d₁, hd₁⟩ := hfin.bddAbove
  exact ⟨d₁, fun x hx => hd₁ hx⟩

/-- CO-487. Algorithm Poly is complete: for `L = ∑_{i ≤ r} p_i N^i` (with `b = max (deg q_j - j)`
attained, as in Proposition 8.3.1) and any `f`, there is a degree bound `d` (computed as in
Proposition 8.3.1 from `deg f - b`, `-b - 1` and the largest nonnegative integer root of the degree
polynomial) such that every polynomial solution `y` of `L y = f` lies in `degreeLT (d+1)` and is a
solution of the linear system `polyMap p r (d+1) y = f`.  So solving the linear system (undetermined
coefficients) finds all polynomial solutions. -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Poly), p. 160"]
theorem poly_complete (p : ℕ → K[X]) (r : ℕ) (f : K[X]) (b : ℤ)
    (hb : ∀ j ≤ r, qPoly p r j ≠ 0 → ((qPoly p r j).natDegree : ℤ) - j ≤ b)
    (hbmax : ∃ j ≤ r, qPoly p r j ≠ 0 ∧ ((qPoly p r j).natDegree : ℤ) - j = b) :
    ∃ d : ℕ, ∀ y : K[X], applyOp p r y = f →
      ∃ hy : y ∈ degreeLT K (d + 1), polyMap p r (d + 1) ⟨y, hy⟩ = f := by
  obtain ⟨d₁, hd₁⟩ := exists_root_bound p r b hbmax
  refine ⟨(max (max ((f.natDegree : ℤ) - b) (-b - 1)) d₁).toNat, fun y hy => ?_⟩
  rw [← mem_preimage_polyMap_iff]
  refine ⟨?_, hy⟩
  rcases natDegree_le_of_applyOp_eq p r y f b hb hbmax d₁ hd₁ hy
      (max (max ((f.natDegree : ℤ) - b) (-b - 1)) d₁)
      (fun _ => (le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) with h | h
  · subst h; simp
  · omega

/-! ### Algorithm Hyper -/

/-- The coefficients `z^i P_i(n)` of the auxiliary recurrence (8.4.6). -/
def auxCoef (p : ℕ → K[X]) (a b : K[X]) (z : K) (d : ℕ) : ℕ → K[X] :=
  fun i => C (z ^ i) * hyperP p a b d i

/-- The auxiliary recurrence is the recurrence operator with coefficients `z^i P_i` applied to `c`;
so its polynomial solutions are found by algorithm Poly (`poly_complete`). -/
theorem auxRecurrence_iff (p : ℕ → K[X]) (a b c : K[X]) (z : K) (d : ℕ) :
    AuxRecurrence p a b c z d ↔ applyOp (auxCoef p a b z d) d c = 0 := Iff.rfl

/-- The finitely many data tried by algorithm Hyper (CO-488): a monic factor `a` of `p_0(n)`,
a monic factor `b` of `p_d(n - d + 1)`, a nonzero root `z` of `∑ α_i z^i`, and a nonzero
polynomial solution `c` of the auxiliary recurrence (8.4.6). -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Hyper), p. 162"]
def IsHyperCandidate (p : ℕ → K[X]) (d : ℕ) (a b : K[X]) (z : K) (c : K[X]) : Prop :=
  a.Monic ∧ a ∣ p 0 ∧ b.Monic ∧ b ∣ (p d).comp (X + C (1 - (d : K))) ∧ z ≠ 0 ∧
    (∑ i ∈ Finset.range (d + 1), hyperAlpha p a b d i * z ^ i = 0) ∧ c ≠ 0 ∧
    AuxRecurrence p a b c z d

/-- A hypergeometric sequence with a prescribed rational ratio `z a c(n+1) / (b c)` exists
(for nonzero `a, b, c`, `z`). -/
theorem exists_hyper_of_ratio (z : K) (hz : z ≠ 0) (a b c : K[X]) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    ∃ y : ℕ → K, IsHypergeometric y ∧
      ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((((eventually_eval_ne_zero ha).and
    (eventually_eval_ne_zero hb)).and (eventually_eval_ne_zero hc)).and
      (eventually_eval_shift_ne_zero hc 1))
  have hS : ∀ j, N ≤ j → hyperRatio z a b c j ≠ 0 := by
    intro j hj
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hN j hj
    simp only [hyperRatio]
    exact mul_ne_zero (mul_ne_zero hz (div_ne_zero h1 h2)) (div_ne_zero (by simpa using h4) h3)
  let y : ℕ → K := fun n => if n < N then 0 else ∏ j ∈ Finset.Ico N n, hyperRatio z a b c j
  have hyne : ∀ n, N ≤ n → y n ≠ 0 := by
    intro n hn
    simp only [y, if_neg (not_lt.2 hn)]
    exact Finset.prod_ne_zero_iff.2 fun j hj => hS j (Finset.mem_Ico.1 hj).1
  have hyrec : ∀ n, N ≤ n → y (n + 1) = hyperRatio z a b c n * y n := by
    intro n hn
    simp only [y, if_neg (not_lt.2 hn), if_neg (not_lt.2 (hn.trans (Nat.le_succ n)))]
    rw [Finset.prod_Ico_succ_top hn, mul_comm]
  have hev : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n :=
    eventually_atTop.2 ⟨N, hyrec⟩
  refine ⟨y, ?_, hev⟩
  rw [isHypergeometric_iff]
  refine ⟨eventually_atTop.2 ⟨N, hyne⟩, C z * a * c.comp (X + 1), b * c, ?_, mul_ne_zero hb hc, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 hz) ha) (comp_X_add_one_ne_zero hc)
  · filter_upwards [hev, eventually_ge_atTop N] with n h1 h2
    obtain ⟨⟨⟨ha', hb'⟩, hc'⟩, hc1⟩ := hN n h2
    simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one]
    rw [h1, hyperRatio]
    field_simp

/-- CO-490 (soundness of the output). Every candidate of Algorithm Hyper yields a hypergeometric
solution of `∑ p_i(n) y(n+i) = 0` with ratio `z a(n) c(n+1) / (b(n) c(n))`. -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Hyper), p. 162"]
theorem hyper_candidate_sound (p : ℕ → K[X]) (d : ℕ) (a b : K[X]) (z : K) (c : K[X])
    (h : IsHyperCandidate p d a b z c) :
    ∃ y : ℕ → K, IsHypergeometric y ∧
      (∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n) ∧
      ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0 := by
  obtain ⟨ha, -, hb, -, hz, -, hc, hrec⟩ := h
  obtain ⟨y, hy, hS⟩ := exists_hyper_of_ratio z hz a b c ha.ne_zero hb.ne_zero hc
  exact ⟨y, hy, hS, hyper_sound p d z a b c hb.ne_zero hc hrec y hS⟩

/-- CO-490 (completeness of the search). Every hypergeometric solution `y` of
`∑_{i ≤ d} p_i(n) y(n+i) = 0` (with `d ≥ 1`, `p_0, p_d ≠ 0`) arises from a candidate of
Algorithm Hyper, i.e. has ratio `z a(n) c(n+1) / (b(n) c(n))` for a candidate `(a, b, z, c)`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 8.4.1, p. 162"]
theorem hyper_candidate_complete (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (hp0 : p 0 ≠ 0)
    (hpd : p d ≠ 0) (y : ℕ → K) (hy : IsHypergeometric y)
    (hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0) :
    ∃ a b z c, IsHyperCandidate p d a b z c ∧
      ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio z a b c n * y n := by
  obtain ⟨a, b, c, ha, hbm, hcm, hab, hac, hbc, hrel, -⟩ := gosper_algorithm hy
  set u : K := a.leadingCoeff with hu
  have hu0 : u ≠ 0 := leadingCoeff_ne_zero.2 ha
  set a' : K[X] := a * C u⁻¹ with ha'
  have ha'm : a'.Monic := monic_mul_leadingCoeff_inv ha
  have haa' : a = a' * C u := by
    rw [ha', mul_assoc, ← C_mul, inv_mul_cancel₀ hu0, C_1, mul_one]
  have hunit : IsUnit (C u⁻¹ : K[X]) := isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hu0))
  have hS : ∀ᶠ n : ℕ in atTop, y (n + 1) = hyperRatio u a' b c n * y n := by
    filter_upwards [hrel, eventually_eval_ne_zero hbm.ne_zero, eventually_eval_ne_zero hcm.ne_zero]
      with n h1 hb' hc'
    simp only [eval_mul, eval_comp, eval_add, eval_X, eval_one] at h1
    rw [hyperRatio]
    have e : a.eval (n : K) = a'.eval (n : K) * u := by rw [haa', eval_mul, eval_C]
    rw [e] at h1
    field_simp
    linear_combination h1
  have hnec := hyper_necessary p d hd hp0 hpd y hy.1 hL u hu0 a' b c hbm hcm
    (fun h => (isCoprime_mul_unit_right_left hunit _ _).2 (hab h))
    ((isCoprime_mul_unit_right_left hunit _ _).2 hac) hbc hS
  obtain ⟨h1, h2, h3, h4⟩ := hnec
  refine ⟨a', b, u, c, ⟨ha'm, h2, hbm, h3, hu0, h1, hcm.ne_zero, h4⟩, hS⟩

/-- CO-488, CO-490. Algorithm Hyper is correct and complete: a recurrence `∑_{i ≤ d} p_i(n) y(n+i) = 0`
(`d ≥ 1`, `p_0, p_d ≠ 0`) has a hypergeometric solution if and only if some candidate
`(a, b, z, c)` works (a monic factor `a` of `p_0`, a monic factor `b` of `p_d(n - d + 1)`, a nonzero
root `z` of `∑ α_i z^i`, and a nonzero polynomial solution `c` of the auxiliary recurrence). -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Hyper), p. 162"]
theorem hyper_exists_iff (p : ℕ → K[X]) (d : ℕ) (hd : 0 < d) (hp0 : p 0 ≠ 0) (hpd : p d ≠ 0) :
    (∃ y : ℕ → K, IsHypergeometric y ∧
        ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (d + 1), (p i).eval (n : K) * y (n + i) = 0) ↔
      ∃ a b z c, IsHyperCandidate p d a b z c := by
  constructor
  · rintro ⟨y, hy, hL⟩
    obtain ⟨a, b, z, c, h, -⟩ := hyper_candidate_complete p d hd hp0 hpd y hy hL
    exact ⟨a, b, z, c, h⟩
  · rintro ⟨a, b, z, c, h⟩
    obtain ⟨y, hy, -, hL⟩ := hyper_candidate_sound p d a b z c h
    exact ⟨y, hy, hL⟩

/-! #### The candidate set is finite -/

/-- The polynomial `∑ α_i z^i` in `z` whose nonzero roots are tried by Hyper. -/
def hyperZPoly (p : ℕ → K[X]) (a b : K[X]) (d : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (d + 1), C (hyperAlpha p a b d i) * X ^ i

theorem eval_hyperZPoly (p : ℕ → K[X]) (a b : K[X]) (d : ℕ) (z : K) :
    (hyperZPoly p a b d).eval z = ∑ i ∈ Finset.range (d + 1), hyperAlpha p a b d i * z ^ i := by
  simp [hyperZPoly, eval_finsetSum]

theorem hyperZPoly_ne_zero (p : ℕ → K[X]) (a b : K[X]) (d : ℕ) (hp0 : p 0 ≠ 0) (hb : b ≠ 0) :
    hyperZPoly p a b d ≠ 0 := by
  classical
  have hP0 : hyperP p a b d 0 ≠ 0 := by
    unfold hyperP
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    exact mul_ne_zero hp0 (Finset.prod_ne_zero_iff.2 fun j _ => comp_X_add_C_ne_zero' hb _)
  have hne : (Finset.range (d + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup (Finset.range (d + 1)) hne
    (fun i => (hyperP p a b d i).natDegree)
  have hex : ∃ i ∈ Finset.range (d + 1), hyperAlpha p a b d i ≠ 0 := by
    by_cases hPi : hyperP p a b d i = 0
    · have hm : hyperDeg p a b d = 0 := by
        rw [hyperDeg, hmax, hPi]; simp
      refine ⟨0, by simp, ?_⟩
      have h0 : (hyperP p a b d 0).natDegree = 0 := by
        have : (hyperP p a b d 0).natDegree ≤ hyperDeg p a b d :=
          Finset.le_sup (f := fun i => (hyperP p a b d i).natDegree) (by simp)
        omega
      have := leadingCoeff_ne_zero.2 hP0
      rw [leadingCoeff, h0] at this
      rw [hyperAlpha, hm]
      exact this
    · refine ⟨i, hi, ?_⟩
      rw [hyperAlpha, hyperDeg, hmax]
      exact leadingCoeff_ne_zero.2 hPi
  obtain ⟨i₀, hi₀, hα⟩ := hex
  intro h0
  apply hα
  have := congrArg (fun q => q.coeff i₀) h0
  simp only [hyperZPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
  simpa [Finset.sum_ite_eq', hi₀] using this

/-- CO-488. The search space of Algorithm Hyper is finite: only finitely many triples
`(a, b, z)` (monic factors `a ∣ p_0`, `b ∣ p_d(n-d+1)`, nonzero roots `z`) have to be
examined; for each, `c` is found by algorithm Poly. -/
@[kb "petkovsekwilfzeilberger1996" "text (Algorithm Hyper), p. 162"]
theorem hyper_candidates_finite (p : ℕ → K[X]) (d : ℕ) (hp0 : p 0 ≠ 0) (hpd : p d ≠ 0) :
    {t : K[X] × K[X] × K | ∃ c, IsHyperCandidate p d t.1 t.2.1 t.2.2 c}.Finite := by
  classical
  have hA : {a : K[X] | a.Monic ∧ a ∣ p 0}.Finite := by
    haveI := fintypeSubtypeMonicDvd (p 0) hp0
    exact Set.toFinite _
  have hB : {b : K[X] | b.Monic ∧ b ∣ (p d).comp (X + C (1 - (d : K)))}.Finite := by
    haveI := fintypeSubtypeMonicDvd ((p d).comp (X + C (1 - (d : K)))) (comp_X_add_C_ne_zero' hpd _)
    exact Set.toFinite _
  have hU : (⋃ ab ∈ ({a : K[X] | a.Monic ∧ a ∣ p 0} ×ˢ
      {b : K[X] | b.Monic ∧ b ∣ (p d).comp (X + C (1 - (d : K)))}),
      (fun z : K => (ab.1, ab.2, z)) '' {z : K | IsRoot (hyperZPoly p ab.1 ab.2 d) z}).Finite := by
    refine (hA.prod hB).biUnion fun ab hab => ?_
    refine Set.Finite.image _ ?_
    exact finite_setOf_isRoot (hyperZPoly_ne_zero p _ _ d hp0 hab.2.1.ne_zero)
  refine hU.subset ?_
  rintro ⟨a, b, z⟩ ⟨c, ha, hadvd, hb, hbdvd, hz, hα, -, -⟩
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
  refine ⟨(a, b), ⟨⟨ha, hadvd⟩, ⟨hb, hbdvd⟩⟩, z, ?_, rfl⟩
  rw [IsRoot.def, eval_hyperZPoly]
  exact hα

end UndergradKB.Combinatorics.AeqB

end
