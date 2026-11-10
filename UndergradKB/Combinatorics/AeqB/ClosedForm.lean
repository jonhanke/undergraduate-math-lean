import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Similar
import UndergradKB.Combinatorics.AeqB.SequenceRing
import UndergradKB.Combinatorics.AeqB.Operators
import UndergradKB.Combinatorics.AeqB.SolutionSpace
import UndergradKB.Combinatorics.AeqB.OperatorsMore
import UndergradKB.Combinatorics.AeqB.Hyper
import UndergradKB.Combinatorics.AeqB.HyperAlgorithm

/-!
# Closed forms, solution spaces, recurrence guessing, canonical and normal forms
(Petkovsek–Wilf–Zeilberger, "A = B", §1.2, 8.1, 8.2, 8.7, 9.x)
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB
open Polynomial Filter

universe u

/-! ### CO-543, CO-544: canonical and normal forms (§1.2) -/

section Forms

/-- CO-543. A canonical form for a class `α` of objects is a description `c : α → β` that is
one-to-one: objects are equal iff their descriptions are equal. -/
@[kb "petkovsekwilfzeilberger1996" "text (canonical form), p. 18"]
def IsCanonicalForm {α β : Type*} (c : α → β) : Prop := Function.Injective c

/-- CO-543. With a canonical form `c`, `A = B` iff `c(A) = c(B)`. -/
@[kb "petkovsekwilfzeilberger1996" "text (canonical form), p. 18"]
theorem IsCanonicalForm.eq_iff {α β : Type*} {c : α → β} (hc : IsCanonicalForm c) (A B : α) :
    A = B ↔ c A = c B := (Function.Injective.eq_iff hc).symm

/-- CO-544. A normal form for objects of an additive group `G`: names (possibly several per object)
with a map `val` onto `G`, subtraction of names, and a test recognizing the names of `0`. -/
@[kb "petkovsekwilfzeilberger1996" "text (normal form), p. 18"]
structure NormalForm (G : Type u) [AddGroup G] where
  /-- the representations ("names") of objects -/
  Name : Type u
  /-- the object named by a representation -/
  val : Name → G
  /-- every object has a name -/
  surj : Function.Surjective val
  /-- subtraction of names -/
  sub : Name → Name → Name
  val_sub : ∀ a b, val (sub a b) = val a - val b
  /-- the test: does the name represent `0`? -/
  isZero : Name → Bool
  isZero_iff : ∀ a, isZero a = true ↔ val a = 0

/-- CO-544. A normal form decides equality: two names represent the same object iff the name of
their difference is recognized as `0`; so `A = B` reduces to `A - B = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text (normal form), p. 18"]
theorem NormalForm.val_eq_iff {G : Type u} [AddGroup G] (N : NormalForm G) (a b : N.Name) :
    N.val a = N.val b ↔ N.isZero (N.sub a b) = true := by
  rw [N.isZero_iff, N.val_sub, sub_eq_zero]

end Forms

/-! ### CO-475, CO-476: closed forms -/

variable {K : Type u} [Field K] [CharZero K]

/-- CO-475. `f` is of closed form if it is (for large `n`) a linear combination of a fixed number
`r` of hypergeometric terms. -/
@[kb "petkovsekwilfzeilberger1996" "Definition 8.1.1, p. 151"]
def IsClosedForm (f : ℕ → K) : Prop :=
  ∃ (r : ℕ) (c : Fin r → K) (h : Fin r → ℕ → K), (∀ i, IsHypergeometric (h i)) ∧
    ∀ᶠ n : ℕ in atTop, f n = ∑ i, c i * h i n

theorem IsHypergeometric.isClosedForm {h : ℕ → K} (hh : IsHypergeometric h) : IsClosedForm h :=
  ⟨1, fun _ => 1, fun _ => h, fun _ => hh, Eventually.of_forall fun n => by simp⟩

/-- CO-476 (the decision step). If a sum `f` (e.g. produced by creative telescoping) satisfies
`L f = 0` and has a closed form, then `f` is, for large `n`, a sum of pairwise dissimilar
hypergeometric terms each of which is itself a hypergeometric solution of `L u = 0`
(Theorem 8.7.1).  So Hyper's list of hypergeometric solutions, together with matching of initial
values, decides whether `f` has a closed form. -/
@[kb "petkovsekwilfzeilberger1996" "text (closed form of a definite sum), p. 151"]
theorem closedForm_dissimilar_solutions (L : RecOp K) (f : ℕ → K) (hf : IsClosedForm f)
    (hL : ∀ᶠ n : ℕ in atTop, RecOp.act L f n = 0) :
    ∃ (r : ℕ) (J : Finset (Fin r)) (u : Fin r → ℕ → K), (∀ j ∈ J, IsHypergeometric (u j)) ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ IsSimilar (u i) (u j)) ∧
      (∀ᶠ n : ℕ in atTop, f n = ∑ j ∈ J, u j n) ∧
      ∀ j ∈ J, ∀ᶠ n : ℕ in atTop, RecOp.act L (u j) n = 0 := by
  obtain ⟨r, c, h, hh, hfc⟩ := hf
  have hL' : ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => ∑ i, c i * h i m) n = 0 := by
    filter_upwards [RecOp.act_congr_eventually L hfc, hL] with n h1 h2
    rw [← h1]; exact h2
  obtain ⟨J, u, h1, h2, h3, h4⟩ := exists_dissimilar_parts_kill L c h hh hL'
  exact ⟨r, J, u, h1, h2, by filter_upwards [hfc, h3] with n a b; rw [a, b], h4⟩

/-- CO-500 helper: the linear hull `L(H_K)` of the hypergeometric terms in `S(K)`. -/
def hyperHull (K : Type u) [Field K] [CharZero K] : Submodule K (SeqRing K) :=
  Submodule.span K {g | ∃ h : ℕ → K, IsHypergeometric h ∧ (h : SeqRing K) = g}

/-- CO-500. Corollary 8.7.1: for a recurrence operator `L` with polynomial coefficients,
`Ker L ∩ L(H_K)` has a basis consisting of hypergeometric terms: there is a linearly independent
family of hypergeometric solutions of `L y = 0` (in `S(K)`) spanning every solution that lies in the
linear hull of the hypergeometric terms. -/
@[kb "petkovsekwilfzeilberger1996" "Corollary 8.7.1, p. 169"]
theorem kernel_inter_hull_basis (L : RecOp K) :
    ∃ (ι : Type u) (b : ι → ℕ → K), (∀ i, IsHypergeometric (b i)) ∧
      (∀ i, ∀ᶠ n : ℕ in atTop, RecOp.act L (b i) n = 0) ∧
      LinearIndependent K (fun i => ((b i : ℕ → K) : SeqRing K)) ∧
      ∀ g ∈ hyperHull K, (∃ f : ℕ → K, (f : SeqRing K) = g ∧
          ∀ᶠ n : ℕ in atTop, RecOp.act L f n = 0) →
        g ∈ Submodule.span K (Set.range fun i => ((b i : ℕ → K) : SeqRing K)) := by
  classical
  let S : Set (SeqRing K) := {g | ∃ h : ℕ → K, IsHypergeometric h ∧ (h : SeqRing K) = g ∧
    ∀ᶠ n : ℕ in atTop, RecOp.act L h n = 0}
  obtain ⟨B, hBS, hspan, hli⟩ := exists_linearIndependent K S
  have hex : ∀ i : B, ∃ h : ℕ → K, IsHypergeometric h ∧ (h : SeqRing K) = i.1 ∧
      ∀ᶠ n : ℕ in atTop, RecOp.act L h n = 0 := fun i => hBS i.2
  choose b hb1 hb2 hb3 using hex
  have hfun : (fun i : B => ((b i : ℕ → K) : SeqRing K)) = (Subtype.val : B → SeqRing K) :=
    funext hb2
  refine ⟨B, b, hb1, hb3, by rw [hfun]; exact hli, ?_⟩
  rw [hfun, Subtype.range_coe]
  intro g hg ⟨f, hfg, hfL⟩
  obtain ⟨m, c, gs, hsum⟩ := Submodule.mem_span_set'.1 hg
  have hgs : ∀ i, ∃ h : ℕ → K, IsHypergeometric h ∧ (h : SeqRing K) = (gs i : SeqRing K) :=
    fun i => (gs i).2
  choose h hh hhg using hgs
  have hgerm : (((fun n => ∑ i, c i * h i n : ℕ → K)) : SeqRing K) = g := by
    rw [← hsum, coe_sum_germ Finset.univ (fun i n => c i * h i n)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hhg i, ← Germ.coe_smul]
    rfl
  have hfsum : ∀ᶠ n : ℕ in atTop, f n = ∑ i, c i * h i n :=
    SeqRing.coe_eq_coe_iff.1 (hfg.trans hgerm.symm)
  have hL' : ∀ᶠ n : ℕ in atTop, RecOp.act L (fun m => ∑ i, c i * h i m) n = 0 := by
    filter_upwards [RecOp.act_congr_eventually L hfsum, hfL] with n h1 h2
    rw [← h1]; exact h2
  obtain ⟨J, u, h1, -, h3, h4⟩ := exists_dissimilar_parts_kill L c h hh hL'
  have hg2 : g = ∑ j ∈ J, ((u j : ℕ → K) : SeqRing K) := by
    rw [← hgerm, ← coe_sum_germ J u]
    exact SeqRing.coe_eq_coe_iff.2 h3
  rw [hg2, hspan]
  refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
  exact ⟨u j, h1 j hj, rfl, h4 j hj⟩

/-! ### CO-514: guessing recurrences (findrec) -/

section Findrec

/-- The polynomial `∑_j c_j n^j` with the given coefficient vector. -/
def coeffPoly {K : Type u} [Field K] (D : ℕ) (c : Fin (D + 1) → K) : K[X] :=
  ∑ j, C (c j) * X ^ (j : ℕ)

theorem eval_coeffPoly {K : Type u} [Field K] (D : ℕ) (c : Fin (D + 1) → K) (x : K) :
    (coeffPoly D c).eval x = ∑ j, c j * x ^ (j : ℕ) := by
  simp [coeffPoly, eval_finsetSum]

/-- CO-514. The linear map of algorithm findrec: the unknowns are the coefficients `c_{ij}` of
`p_i(n) = ∑_j c_{ij} n^j` (`i ≤ r`, `j ≤ D`), and the `M` equations
`∑_i p_i(m) y(m+i) = 0`, `m < M`, are imposed on the known terms of `y`. -/
def findrecMap {K : Type u} [Field K] (y : ℕ → K) (r D M : ℕ) :
    (Fin (r + 1) → Fin (D + 1) → K) →ₗ[K] (Fin M → K) where
  toFun c m := ∑ i : Fin (r + 1), ∑ j : Fin (D + 1), c i j * ((m : ℕ) : K) ^ (j : ℕ) * y (m + i)
  map_add' c c' := by
    funext m
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- CO-514. A coefficient array lies in the kernel of `findrecMap` iff the corresponding
polynomial coefficients satisfy the recurrence on the first `M` equations. -/
@[kb "petkovsekwilfzeilberger1996" "text (findrec), p. 185"]
theorem mem_ker_findrecMap_iff {K : Type u} [Field K] (y : ℕ → K) (r D M : ℕ)
    (c : Fin (r + 1) → Fin (D + 1) → K) :
    c ∈ LinearMap.ker (findrecMap y r D M) ↔
      ∀ m : Fin M, ∑ i : Fin (r + 1), (coeffPoly D (c i)).eval ((m : ℕ) : K) * y (m + i) = 0 := by
  rw [LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun m => ?_
  simp only [findrecMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, eval_coeffPoly,
    Finset.sum_mul]

/-- CO-514. Any true recurrence of order at most `r` and degree at most `D`,
`∑_{i ≤ r} p_i(n) y(n+i) = 0` for all `n`, gives a coefficient array in the kernel of
`findrecMap y r D M`, for every `M`; so the kernel contains all true recurrences of that shape
(and the solutions found from finitely many terms are the candidates to be verified). -/
@[kb "petkovsekwilfzeilberger1996" "text (findrec), p. 185"]
theorem coeffs_mem_ker_findrecMap {K : Type u} [Field K] (y : ℕ → K) (r D M : ℕ)
    (p : Fin (r + 1) → K[X]) (hp : ∀ i, (p i).natDegree ≤ D)
    (h : ∀ n : ℕ, ∑ i : Fin (r + 1), (p i).eval (n : K) * y (n + i) = 0) :
    (fun i (j : Fin (D + 1)) => (p i).coeff j) ∈ LinearMap.ker (findrecMap y r D M) := by
  rw [mem_ker_findrecMap_iff]
  intro m
  have : ∀ i, coeffPoly D (fun j : Fin (D + 1) => (p i).coeff j) = p i := by
    intro i
    rw [coeffPoly, Fin.sum_univ_eq_sum_range (fun j => C ((p i).coeff j) * X ^ j) (D + 1)]
    exact ((p i).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (hp i))).symm
  simp only [this]
  exact h m

/-- CO-514. For a recurrence operator `L = ∑_{i ≤ r} p_i(n) N^i` with `deg p_i ≤ D` annihilating
`y` (for all `n`), the coefficient array of `L` lies in the kernel of `findrecMap y r D M`. -/
@[kb "petkovsekwilfzeilberger1996" "text (findrec), p. 185"]
theorem recOp_coeffs_mem_ker_findrecMap {K : Type u} [Field K] (y : ℕ → K) (r D M : ℕ)
    (L : RecOp K) (hsupp : ∀ k ∈ L.support, k ≤ r) (hdeg : ∀ k, (L.coeff k).natDegree ≤ D)
    (h : ∀ n : ℕ, RecOp.act L y n = 0) :
    (fun (i : Fin (r + 1)) (j : Fin (D + 1)) => (L.coeff i).coeff j) ∈
      LinearMap.ker (findrecMap y r D M) := by
  refine coeffs_mem_ker_findrecMap y r D M (fun i => L.coeff i) (fun i => hdeg i) fun n => ?_
  have := h n
  rw [RecOp.act_def] at this
  rw [Fin.sum_univ_eq_sum_range (fun i => (L.coeff i).eval (n : K) * y (n + i)) (r + 1)]
  refine Eq.trans ?_ this
  symm
  refine Finset.sum_subset (fun k hk => Finset.mem_range.2 (Nat.lt_succ_of_le (hsupp k hk)))
    fun k _ hk => ?_
  rw [SkewPolynomial.notMem_support_iff.1 hk]
  simp

end Findrec

/-! ### CO-479: solution spaces of first-order equations in `K^ℕ` -/

section SolutionSpaces

/-- The solutions in `K^ℕ` (not modulo finitely many terms) of `a(n) y(n+1) + b(n) y(n) = 0`
for all `n`. -/
def firstOrderSol (a b : ℕ → K) : Submodule K (ℕ → K) where
  carrier := {y | ∀ n, a n * y (n + 1) + b n * y n = 0}
  zero_mem' := fun n => by simp
  add_mem' := fun {y z} hy hz n => by
    have h1 := hy n
    have h2 := hz n
    simp only [Pi.add_apply]
    linear_combination h1 + h2
  smul_mem' := fun c y hy n => by
    have h1 := hy n
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * h1

/-- `a = (1, 0, 1, 0, …)`. -/
def evenSeq (K : Type u) [Field K] : ℕ → K := fun n => if Even n then 1 else 0

/-- `b = (0, 1, 0, 1, …)`. -/
def oddSeq (K : Type u) [Field K] : ℕ → K := fun n => if Even n then 0 else 1

theorem mem_firstOrderSol_even_odd (y : ℕ → K) :
    y ∈ firstOrderSol (evenSeq K) (oddSeq K) ↔ ∀ n, Odd n → y n = 0 := by
  constructor
  · intro h n hn
    have h1 := h n
    have hne : ¬ Even n := Nat.not_even_iff_odd.2 hn
    simpa [evenSeq, oddSeq, hne] using h1
  · intro h n
    by_cases hn : Even n
    · have : Odd (n + 1) := hn.add_one
      simp [evenSeq, oddSeq, hn, h (n + 1) this]
    · have := h n (Nat.not_even_iff_odd.1 hn)
      simp [evenSeq, oddSeq, hn, this]

/-- CO-479 (Example 8.2.1, first equation). In `K^ℕ`, the first-order equation
`a(n) y(n+1) + b(n) y(n) = 0` with `a = (1,0,1,0,…)`, `b = (0,1,0,1,…)` has an
infinite-dimensional solution space (the solutions are the sequences vanishing at odd indices). -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.2.1, p. 155"]
theorem not_finite_firstOrderSol_even_odd :
    ¬ Module.Finite K (firstOrderSol (evenSeq K) (oddSeq K)) := by
  intro hfin
  classical
  let v : ℕ → firstOrderSol (evenSeq K) (oddSeq K) := fun k =>
    ⟨Pi.single (2 * k) 1, (mem_firstOrderSol_even_odd _).2 fun n hn => by
      have : n ≠ 2 * k := by rintro rfl; exact (Nat.not_even_iff_odd.2 hn) (even_two_mul k)
      simp [Pi.single_apply, this]⟩
  have hli : LinearIndependent K v := by
    refine LinearIndependent.of_comp (firstOrderSol (evenSeq K) (oddSeq K)).subtype ?_
    have := (Pi.linearIndependent_single_one ℕ K).comp (fun k : ℕ => 2 * k)
      (fun a b (h : 2 * a = 2 * b) => by omega)
    exact this
  have : Finite ℕ := hli.finite_of_isNoetherian
  exact not_finite ℕ

/-- CO-479 (Example 8.2.1, second equation). The equation `a(n) y(n+1) - y(n) = 0`
has only the zero solution in `K^ℕ`: its solution space has dimension `0`. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.2.1, p. 155"]
theorem firstOrderSol_even_neg_one :
    firstOrderSol (evenSeq K) (fun _ => -1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have h : ∀ n, evenSeq K n * y (n + 1) + -1 * y n = 0 := hy
  have hodd : ∀ n, Odd n → y n = 0 := by
    intro n hn
    have := h n
    have hne : ¬ Even n := Nat.not_even_iff_odd.2 hn
    simp [evenSeq, hne] at this
    exact this
  funext n
  by_cases hn : Even n
  · have h1 := h n
    have h2 := hodd (n + 1) hn.add_one
    simp [evenSeq, hn, h2] at h1
    simpa using h1
  · simpa using hodd n (Nat.not_even_iff_odd.1 hn)

/-- `p(n) = (n-1)(n-4)(n-7)`. -/
def exP (K : Type u) [Field K] (n : ℕ) : K := ((n : K) - 1) * ((n : K) - 4) * ((n : K) - 7)

/-- `q(n) = n(n-3)(n-6)`. -/
def exQ (K : Type u) [Field K] (n : ℕ) : K := (n : K) * ((n : K) - 3) * ((n : K) - 6)

/-- The solution space of `p(n) y(n+1) = q(n) y(n)` in `K^ℕ`, `p, q` as in Example 8.2.2. -/
def exSol (K : Type u) [Field K] : Submodule K (ℕ → K) where
  carrier := {y | ∀ n, exP K n * y (n + 1) = exQ K n * y n}
  zero_mem' := fun n => by simp
  add_mem' := fun {y z} hy hz n => by
    have h1 := hy n
    have h2 := hz n
    simp only [Pi.add_apply]
    linear_combination h1 + h2
  smul_mem' := fun c y hy n => by
    have h1 := hy n
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * h1

theorem exP_zero : exP K 0 = -28 := by norm_num [exP]
theorem exP_two : exP K 2 = 10 := by norm_num [exP]
theorem exP_three : exP K 3 = 8 := by norm_num [exP]
theorem exP_five : exP K 5 = -8 := by norm_num [exP]
theorem exP_six : exP K 6 = -10 := by norm_num [exP]
theorem exP_eight : exP K 8 = 28 := by norm_num [exP]
theorem exQ_zero : exQ K 0 = 0 := by norm_num [exQ]
theorem exQ_two : exQ K 2 = 8 := by norm_num [exQ]
theorem exQ_three : exQ K 3 = 0 := by norm_num [exQ]
theorem exQ_five : exQ K 5 = -10 := by norm_num [exQ]
theorem exQ_six : exQ K 6 = 0 := by norm_num [exQ]

theorem exP_ne_zero_of_ge {n : ℕ} (hn : 8 ≤ n) : exP K n ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have : exP K (m + 8) = (((m + 7) * (m + 4) * (m + 1) : ℕ) : K) := by
    simp only [exP]; push_cast; ring
  rw [this]
  exact Nat.cast_ne_zero.2 (by positivity)

theorem eq_zero_of_mem_exSol {y : ℕ → K} (hy : y ∈ exSol K) (h0 : y 0 = 0) (h2 : y 2 = 0)
    (h5 : y 5 = 0) (h8 : y 8 = 0) : y = 0 := by
  have h : ∀ n, exP K n * y (n + 1) = exQ K n * y n := hy
  have key : ∀ (c z : K), c ≠ 0 → c * z = 0 → z = 0 := fun c z hc e =>
    (mul_eq_zero.1 e).resolve_left hc
  have y1 : y 1 = 0 := key (-28) _ (by norm_num) (by simpa [exP_zero, exQ_zero, h0] using h 0)
  have y3 : y 3 = 0 := key 10 _ (by norm_num) (by simpa [exP_two, exQ_two, h2] using h 2)
  have y4 : y 4 = 0 := key 8 _ (by norm_num) (by simpa [exP_three, exQ_three, y3] using h 3)
  have y6 : y 6 = 0 := key (-8) _ (by norm_num) (by simpa [exP_five, exQ_five, h5] using h 5)
  have y7 : y 7 = 0 := key (-10) _ (by norm_num) (by simpa [exP_six, exQ_six, y6] using h 6)
  have hge : ∀ n, 8 ≤ n → y n = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h8
    | succ n hn ih =>
      exact key _ _ (exP_ne_zero_of_ge hn) (by rw [h n, ih, mul_zero])
  funext n
  by_cases hn : 8 ≤ n
  · exact hge n hn
  · push Not at hn
    interval_cases n <;> assumption

/-- `(0, …)` solutions of Example 8.2.2. -/
def exV0 (K : Type u) [Field K] : ℕ → K := fun n => if n = 0 then 1 else 0
/-- The solution with `y(2) = 1`, `y(3) = 4/5`. -/
def exV2 (K : Type u) [Field K] : ℕ → K := fun n => if n = 2 then 1 else if n = 3 then 4 / 5 else 0
/-- The solution with `y(5) = 1`, `y(6) = 5/4`. -/
def exV5 (K : Type u) [Field K] : ℕ → K := fun n => if n = 5 then 1 else if n = 6 then 5 / 4 else 0

theorem exV0_mem : exV0 K ∈ exSol K := by
  intro n
  rcases n with _ | n
  · simp [exV0, exQ_zero]
  · simp [exV0]

theorem exV2_mem : exV2 K ∈ exSol K := by
  intro n
  rcases n with _ | _ | _ | _ | n
  · simp [exV2]
  · simp [exV2, exP]
  · norm_num [exV2, exP, exQ]
  · simp [exV2, exQ]
  · simp [exV2]

theorem exV5_mem : exV5 K ∈ exSol K := by
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · simp [exV5]
  · simp [exV5]
  · simp [exV5]
  · simp [exV5]
  · simp [exV5, exP]
  · norm_num [exV5, exP, exQ]
  · simp [exV5, exQ]
  · simp [exV5]

theorem exP_mem : exP K ∈ exSol K := by
  intro n
  simp only [exP, exQ]
  push_cast
  ring

/-- CO-479 (Example 8.2.2). For `p(n) = (n-1)(n-4)(n-7)`, `q(n) = n(n-3)(n-6)`, the first-order
equation `p(n) y(n+1) = q(n) y(n)` has a four-dimensional solution space in `K^ℕ` (with
the solutions `δ₀`, `(0,0,1,4/5,0,…)`, `(0,…,0,1,5/4,0,…)` and `p(n)` itself): a first-order
equation with polynomial coefficients can have a `k`-dimensional solution space (here `k = 4`). -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.2.2, p. 155"]
theorem finrank_exSol : Module.finrank K (exSol K) = 4 := by
  let ev : (ℕ → K) →ₗ[K] (Fin 4 → K) :=
    LinearMap.pi fun i => LinearMap.proj (![0, 2, 5, 8] i : ℕ)
  let Φ : exSol K →ₗ[K] (Fin 4 → K) := ev ∘ₗ (exSol K).subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have e0 := congrFun hy 0
    have e1 := congrFun hy 1
    have e2 := congrFun hy 2
    have e3 := congrFun hy 3
    simp only [Φ, ev, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, Pi.zero_apply] at e0 e1 e2 e3
    exact Subtype.ext (eq_zero_of_mem_exSol y.2 e0 e1 e2 e3)
  haveI : Module.Finite K (exSol K) := Module.Finite.of_injective Φ hinj
  have h1 : Module.finrank K (exSol K) ≤ 4 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  let v : Fin 4 → exSol K := ![⟨exV0 K, exV0_mem⟩, ⟨exV2 K, exV2_mem⟩, ⟨exV5 K, exV5_mem⟩,
    ⟨exP K, exP_mem⟩]
  have hli : LinearIndependent K v := by
    refine LinearIndependent.of_comp (exSol K).subtype ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e8 := congrFun hg 8
    have e0 := congrFun hg 0
    have e2 := congrFun hg 2
    have e5 := congrFun hg 5
    simp only [Fin.sum_univ_four, Function.comp_apply, Submodule.subtype_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e8 e0 e2 e5
    simp [v, exV0, exV2, exV5, exP_eight, exP_zero, exP_two, exP_five] at e8 e0 e2 e5
    have g3 : g 3 = 0 := by simpa using e8
    rw [g3] at e0 e2 e5
    intro i
    fin_cases i
    · simpa using e0
    · simpa using e2
    · simpa using e5
    · exact g3
  have h2 : 4 ≤ Module.finrank K (exSol K) := by
    simpa using hli.fintype_card_le_finrank
  omega

end SolutionSpaces

/-! ### CO-494: the involution recurrence has no hypergeometric solution -/

section Involution

/-- The coefficients of `y(n+2) - y(n+1) - (n+1) y(n) = 0`, i.e. `p_0 = -(n+1)`, `p_1 = -1`,
`p_2 = 1`. -/
def invCoef (K : Type u) [Field K] : ℕ → K[X] := fun i =>
  if i = 0 then -(X + C 1) else if i = 1 then -1 else 1

theorem invCoef_zero : invCoef K 0 = -(X + C 1) := by unfold invCoef; rw [if_pos rfl]
theorem invCoef_one : invCoef K 1 = -1 := by
  unfold invCoef; rw [if_neg (by norm_num), if_pos rfl]
theorem invCoef_two : invCoef K 2 = 1 := by
  unfold invCoef; rw [if_neg (by norm_num), if_neg (by norm_num)]

theorem hyperDeg_eq_of {p : ℕ → K[X]} {a b : K[X]} {d m : ℕ}
    (h1 : ∀ i ≤ d, (hyperP p a b d i).natDegree ≤ m)
    (h2 : ∃ i ≤ d, (hyperP p a b d i).natDegree = m) : hyperDeg p a b d = m := by
  unfold hyperDeg
  apply le_antisymm
  · exact Finset.sup_le fun i hi => h1 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  · obtain ⟨i, hi, he⟩ := h2
    rw [← he]
    exact Finset.le_sup (f := fun i => (hyperP p a b d i).natDegree)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- CO-494 (non-hypergeometricity). No hypergeometric term satisfies the involution recurrence
`y(n+2) = y(n+1) + (n+1) y(n)` for large `n`; hence the number of involutions, which satisfies it
(`Involutions.involutionNumber_rec`), is P-recursive but, if not a multiple of a hypergeometric
solution, not hypergeometric.  The proof is the case analysis of algorithm Hyper
(Theorem 8.4.1): `b = 1`, `a ∈ {1, n+1}`, and the degree condition `∑ α_i z^i = 0` fails. -/
@[kb "petkovsekwilfzeilberger1996" "Example 8.4.3, p. 165"]
theorem not_hypergeometric_involution_rec (y : ℕ → K) (hy : IsHypergeometric y) :
    ¬ ∀ᶠ n : ℕ in atTop, y (n + 2) = y (n + 1) + ((n : K) + 1) * y n := by
  intro hrec
  have hL : ∀ᶠ n : ℕ in atTop, ∑ i ∈ Finset.range (2 + 1), (invCoef K i).eval (n : K) *
      y (n + i) = 0 := by
    filter_upwards [hrec] with n e
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero, invCoef_zero,
      invCoef_one, invCoef_two, eval_neg, eval_add, eval_X, eval_C, eval_one]
    linear_combination e
  have hX1 : (X + C 1 : K[X]) ≠ 0 := X_add_C_ne_zero 1
  have hp0 : invCoef K 0 ≠ 0 := by rw [invCoef_zero]; exact neg_ne_zero.2 hX1
  have hp2 : invCoef K 2 ≠ 0 := by rw [invCoef_two]; exact one_ne_zero
  obtain ⟨a, b, z, c, ⟨ha, hadvd, hb, hbdvd, hz, hα, -, -⟩, -⟩ :=
    hyper_candidate_complete (invCoef K) 2 (by norm_num) hp0 hp2 y hy hL
  have hb1 : b = 1 := by
    rw [invCoef_two, one_comp] at hbdvd
    exact hb.eq_one_of_isUnit (isUnit_of_dvd_one hbdvd)
  subst hb1
  have hP : ∀ i, hyperP (invCoef K) a 1 2 i = invCoef K i *
      ∏ j ∈ Finset.range i, a.comp (X + C (j : K)) := by
    intro i; simp only [hyperP, one_comp, Finset.prod_const_one, mul_one]
  have hirr : Irreducible (X + C 1 : K[X]) := irreducible_of_degree_eq_one (degree_X_add_C 1)
  have ha1 : a ∣ X + C 1 := by rw [invCoef_zero, dvd_neg] at hadvd; exact hadvd
  have hcases : a = 1 ∨ a = X + C 1 := by
    obtain ⟨c', hc'⟩ := ha1
    rcases hirr.isUnit_or_isUnit hc' with hu | hu
    · exact Or.inl (ha.eq_one_of_isUnit hu)
    · right
      refine eq_of_monic_of_associated ha (monic_X_add_C 1) ?_
      exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc'.symm⟩
  rcases hcases with rfl | rfl
  · -- a = 1: P = (-(n+1), -1, 1), m = 1
    have hP' : ∀ i, hyperP (invCoef K) 1 1 2 i = invCoef K i := by
      intro i; rw [hP]; simp only [one_comp, Finset.prod_const_one, mul_one]
    have hm : hyperDeg (invCoef K) 1 1 2 = 1 := by
      refine hyperDeg_eq_of (fun i hi => ?_) ⟨0, by omega, ?_⟩
      · rw [hP']
        interval_cases i
        · rw [invCoef_zero, natDegree_neg, natDegree_X_add_C]
        · rw [invCoef_one]; simp
        · rw [invCoef_two]; simp
      · rw [hP', invCoef_zero, natDegree_neg, natDegree_X_add_C]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hyperAlpha, hm, hP', invCoef_zero,
      invCoef_one, invCoef_two, coeff_neg, coeff_add, coeff_X_one, coeff_C, coeff_one] at hα
    norm_num at hα
  · -- a = X + 1: P = (-(n+1), -(n+1), (n+1)(n+2)), m = 2
    have hP0 : hyperP (invCoef K) (X + C 1) 1 2 0 = -(X + C 1) := by
      rw [hP, invCoef_zero]; simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    have hP1 : hyperP (invCoef K) (X + C 1) 1 2 1 = -(X + C 1) := by
      rw [hP, invCoef_one, Finset.prod_range_one]
      simp only [add_comp, X_comp, C_comp, Nat.cast_zero, C_0, add_zero, neg_one_mul]
    have hP2 : hyperP (invCoef K) (X + C 1) 1 2 2 = (X + C 1) * (X + C 2) := by
      rw [hP, invCoef_two, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
      simp only [add_comp, X_comp, C_comp, Nat.cast_zero, Nat.cast_one, C_0, add_zero, one_mul]
      have : (C 1 + C 1 : K[X]) = C 2 := by rw [← C_add]; norm_num
      rw [add_assoc, this]
    have hmon : ((X + C 1) * (X + C 2) : K[X]).Monic := (monic_X_add_C 1).mul (monic_X_add_C 2)
    have hdeg2 : ((X + C 1) * (X + C 2) : K[X]).natDegree = 2 := by
      rw [(monic_X_add_C 1).natDegree_mul (monic_X_add_C 2), natDegree_X_add_C, natDegree_X_add_C]
    have hdneg : (-(X + C 1) : K[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X_add_C]
    have hm : hyperDeg (invCoef K) (X + C 1) 1 2 = 2 := by
      refine hyperDeg_eq_of (fun i hi => ?_) ⟨2, le_rfl, by rw [hP2, hdeg2]⟩
      interval_cases i
      · rw [hP0, hdneg]; norm_num
      · rw [hP1, hdneg]; norm_num
      · rw [hP2, hdeg2]
    have c2 : (hyperP (invCoef K) (X + C 1) 1 2 2).coeff 2 = 1 := by
      rw [hP2, ← hdeg2]; exact hmon.coeff_natDegree
    have c0 : (hyperP (invCoef K) (X + C 1) 1 2 0).coeff 2 = 0 := by
      rw [hP0]; exact coeff_eq_zero_of_natDegree_lt (by rw [hdneg]; norm_num)
    have c1 : (hyperP (invCoef K) (X + C 1) 1 2 1).coeff 2 = 0 := by
      rw [hP1]; exact coeff_eq_zero_of_natDegree_lt (by rw [hdneg]; norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hyperAlpha, hm, c0, c1, c2] at hα
    norm_num at hα
    exact hz hα

end Involution

end UndergradKB.Combinatorics.AeqB

end
