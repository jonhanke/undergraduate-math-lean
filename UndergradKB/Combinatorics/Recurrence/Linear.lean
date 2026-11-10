import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import UndergradKB.Common.Attr

/-!
# Linear recurrences with constant coefficients: the advancement operator
(Keller–Trotter, Sections 9.3–9.5)

Sequences are functions `ℕ → K` over a field `K` (the book uses `ℤ → ℂ`; the statements here are
for sequences indexed from `0`, which is the situation of every recurrence with initial values).
The advancement operator `A` is the shift `(A f) n = f (n + 1)`, and a polynomial `p` acts on
sequences as `p(A) = Polynomial.aeval advance p`.

The dimension count comes from Mathlib's `LinearRecurrence.solSpace_rank`.
-/

namespace UndergradKB.Combinatorics.Recurrence

open Polynomial Finset

variable {K : Type*} [Field K]

/-- CO-222. The advancement operator `A` on sequences: `(A f) n = f (n + 1)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) advancement operator, p. 212"]
def advance : Module.End K (ℕ → K) where
  toFun f := fun n => f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma advance_apply (f : ℕ → K) (n : ℕ) : advance f n = f (n + 1) := rfl

lemma advance_pow_apply (i : ℕ) (f : ℕ → K) (n : ℕ) : (advance ^ i : Module.End K (ℕ → K)) f n =
    f (n + i) := by
  induction i generalizing f with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_apply_eq_comp, ih]; rfl

/-- CO-222. The polynomial `p(A)` of the advancement operator acts by
`(p(A) f)(n) = ∑ p_i f(n + i)`; so `p(A) f = g` is a linear recurrence with constant coefficients. -/
@[kb "kellertrotter2017" "text (9.3.1), p. 213"]
theorem aeval_advance_apply (p : K[X]) (f : ℕ → K) (n : ℕ) :
    (aeval advance p : Module.End K (ℕ → K)) f n =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i * f (n + i) := by
  rw [aeval_eq_sum_range]
  simp [LinearMap.sum_apply, advance_pow_apply]

lemma aeval_X_sub_C_apply (r : K) (f : ℕ → K) (n : ℕ) :
    (aeval advance (X - C r) : Module.End K (ℕ → K)) f n = f (n + 1) - r * f n := by
  simp [Module.algebraMap_end_apply, advance_apply]

/-- CO-226. If `(A - r) f = 0` then `f n = f 0 * r ^ n` (and conversely). The book assumes `r ≠ 0`
(to work on `ℤ`); on `ℕ`-indexed sequences this is not needed. -/
@[kb "kellertrotter2017" "Lemma 9.19, p. 224"]
theorem advance_sub_eq_zero_iff (r : K) (f : ℕ → K) :
    (aeval advance (X - C r) : Module.End K (ℕ → K)) f = 0 ↔ ∀ n, f n = f 0 * r ^ n := by
  constructor
  · intro h n
    induction n with
    | zero => simp
    | succ n ih =>
      have := congrFun h n
      rw [aeval_X_sub_C_apply] at this
      simp only [Pi.zero_apply] at this
      rw [pow_succ, ← mul_assoc, ← ih]
      linear_combination this
  · intro h
    funext n
    rw [aeval_X_sub_C_apply, h (n + 1), h n]
    simp [pow_succ]
    ring

/-- CO-227. Every solution of `p(A) f = g` is a particular solution `f₀` plus a solution of the
homogeneous equation `p(A) h = 0`, and conversely. -/
@[kb "kellertrotter2017" "Lemma 9.20, p. 224"]
theorem solution_eq_particular_add_homogeneous (p : K[X]) (g f₀ : ℕ → K)
    (h₀ : (aeval advance p : Module.End K (ℕ → K)) f₀ = g) (f : ℕ → K) :
    (aeval advance p : Module.End K (ℕ → K)) f = g ↔
      ∃ h, (aeval advance p : Module.End K (ℕ → K)) h = 0 ∧ f = f₀ + h := by
  constructor
  · intro hf
    refine ⟨f - f₀, by rw [map_sub, hf, h₀, sub_self], by abel⟩
  · rintro ⟨h, hh, rfl⟩
    rw [map_add, h₀, hh, add_zero]

/-! ### The solution space of `p(A) f = 0` for monic `p` -/

/-- The linear recurrence of Mathlib corresponding to a monic polynomial `p`
(`f (n + k) = -∑_{i<k} p_i f (n + i)`). -/
def recOfMonic (p : K[X]) : LinearRecurrence K := ⟨p.natDegree, fun i => -p.coeff i⟩

lemma isSolution_recOfMonic_iff {p : K[X]} (hp : p.Monic) (f : ℕ → K) :
    (recOfMonic p).IsSolution f ↔ (aeval advance p : Module.End K (ℕ → K)) f = 0 := by
  constructor
  · intro h
    funext n
    rw [aeval_advance_apply, sum_range_succ, hp.coeff_natDegree, one_mul]
    have := h n
    change f (n + p.natDegree) = ∑ i : Fin p.natDegree, -p.coeff i * f (n + i) at this
    rw [Fin.sum_univ_eq_sum_range (fun i => -p.coeff i * f (n + i)) p.natDegree] at this
    simp only [neg_mul, sum_neg_distrib] at this
    simp only [Pi.zero_apply]
    linear_combination this
  · intro h n
    have := congrFun h n
    rw [aeval_advance_apply, sum_range_succ, hp.coeff_natDegree, one_mul] at this
    simp only [Pi.zero_apply] at this
    change f (n + p.natDegree) = ∑ i : Fin p.natDegree, -p.coeff i * f (n + i)
    rw [Fin.sum_univ_eq_sum_range (fun i => -p.coeff i * f (n + i)) p.natDegree]
    simp only [neg_mul, sum_neg_distrib]
    linear_combination this

lemma mem_solSpace_recOfMonic {p : K[X]} (hp : p.Monic) (f : ℕ → K) :
    f ∈ (recOfMonic p).solSpace ↔ (aeval advance p : Module.End K (ℕ → K)) f = 0 := by
  rw [← LinearRecurrence.is_sol_iff_mem_solSpace, isSolution_recOfMonic_iff hp]

lemma finrank_solSpace_recOfMonic (p : K[X]) :
    Module.finrank K (recOfMonic p).solSpace = p.natDegree :=
  Module.finrank_eq_of_rank_eq (by simpa [recOfMonic] using (recOfMonic p).solSpace_rank)

/-- For monic `p`, a family of `deg p` linearly independent solutions of `p(A) f = 0` spans the
solution space. -/
theorem exists_coeffs_of_linearIndependent {p : K[X]} (hp : p.Monic) {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = p.natDegree) (w : ι → ℕ → K)
    (hw : ∀ i, (aeval advance p : Module.End K (ℕ → K)) (w i) = 0) (hli : LinearIndependent K w)
    (f : ℕ → K) (hf : (aeval advance p : Module.End K (ℕ → K)) f = 0) :
    ∃ c : ι → K, f = ∑ i, c i • w i := by
  have : FiniteDimensional K (recOfMonic p).solSpace := Module.Finite.of_basis (recOfMonic p).basis
  let wV : ι → (recOfMonic p).solSpace := fun i => ⟨w i, (mem_solSpace_recOfMonic hp _).2 (hw i)⟩
  have hliV : LinearIndependent K wV :=
    LinearIndependent.of_comp (recOfMonic p).solSpace.subtype hli
  have htop := hliV.span_eq_top_of_card_eq_finrank'
    (hcard.trans (finrank_solSpace_recOfMonic p).symm)
  have hmem : (⟨f, (mem_solSpace_recOfMonic hp _).2 hf⟩ : (recOfMonic p).solSpace) ∈
      Submodule.span K (Set.range wV) := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa [wV] using this.symm

/-- The conclusion of `exists_coeffs_of_linearIndependent` in the reverse direction: finite
linear combinations of solutions are solutions. -/
lemma aeval_sum_smul {p : K[X]} {ι : Type*} [Fintype ι] (w : ι → ℕ → K) (c : ι → K)
    (hw : ∀ i, (aeval advance p : Module.End K (ℕ → K)) (w i) = 0) :
    (aeval advance p : Module.End K (ℕ → K)) (∑ i, c i • w i) = 0 := by
  rw [map_sum]
  exact sum_eq_zero fun i _ => by rw [map_smul, hw i, smul_zero]

/-! ### Distinct roots: Theorem 9.21 -/

/-- Geometric sequences with distinct ratios are linearly independent (Vandermonde). -/
theorem linearIndependent_geom {k : ℕ} (r : Fin k → K) (hr : Function.Injective r) :
    LinearIndependent K (fun i : Fin k => (fun n : ℕ => r i ^ n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hdet : (Matrix.vandermonde r).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact Matrix.det_vandermonde_ne_zero_iff.2 hr
  have : (Matrix.vandermonde r).transpose.mulVec c = 0 := by
    funext j
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    rw [← this]
    exact sum_congr rfl fun i _ => by ring
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet this) i

lemma geom_mem_ker_prod {k : ℕ} (r : Fin k → K) (j : Fin k) :
    (aeval advance (∏ i, (X - C (r i))) : Module.End K (ℕ → K)) (fun n => r j ^ n) = 0 := by
  rw [← Finset.prod_erase_mul univ (fun i => (X - C (r i))) (mem_univ j), map_mul,
    mul_apply_eq_comp]
  have : (aeval advance (X - C (r j)) : Module.End K (ℕ → K)) (fun n => r j ^ n) = 0 := by
    funext n
    rw [aeval_X_sub_C_apply]
    simp [pow_succ]
    ring
  rw [this, map_zero]

/-- CO-228. If `p(A) = (A - r_1) ⋯ (A - r_k)` with distinct roots `r_i`, then the solutions of
`p(A) f = 0` are exactly the sequences `n ↦ c_1 r_1^n + ⋯ + c_k r_k^n`. (The book also assumes
the roots nonzero, which is unnecessary here since sequences are indexed from `0`.)
Note `aeval advance (∏ (X - C r_i)) = ∏ (A - r_i)` by `map_prod`. -/
@[kb "kellertrotter2017" "Theorem 9.21, p. 224"]
theorem solutions_distinct_roots {k : ℕ} (r : Fin k → K) (hr : Function.Injective r)
    (f : ℕ → K) :
    (aeval advance (∏ i, (X - C (r i))) : Module.End K (ℕ → K)) f = 0 ↔
      ∃ c : Fin k → K, ∀ n, f n = ∑ i, c i * r i ^ n := by
  have hmon : (∏ i, (X - C (r i))).Monic := monic_prod_X_sub_C r univ
  have hdeg : (∏ i : Fin k, (X - C (r i))).natDegree = k := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (r i)]
    simp
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := exists_coeffs_of_linearIndependent hmon (by simp [hdeg])
      (fun i => (fun n : ℕ => r i ^ n)) (geom_mem_ker_prod r) (linearIndependent_geom r hr) f hf
    refine ⟨c, fun n => ?_⟩
    rw [hc]
    simp
  · rintro ⟨c, hc⟩
    have : f = ∑ i, c i • (fun n : ℕ => r i ^ n) := by
      funext n; rw [hc n]; simp
    rw [this]
    exact aeval_sum_smul _ _ (geom_mem_ker_prod r)

/-! ### Repeated root: Lemma 9.22 -/

/-- Iterating `A - r` on `r^n * F n` iterates the forward difference of `F`. -/
lemma pow_sub_apply (r : K) (j : ℕ) :
    ∀ F : K → K, ((aeval advance (X - C r) : Module.End K (ℕ → K)) ^ j) (fun n : ℕ => r ^ n * F (n : K)) =
      fun n => r ^ (n + j) * (fwdDiff (1 : K))^[j] F (n : K) := by
  induction j with
  | zero => intro F; simp
  | succ j ih =>
    intro F
    have h1 : (aeval advance (X - C r) : Module.End K (ℕ → K)) (fun n : ℕ => r ^ n * F (n : K)) =
        fun n : ℕ => r ^ n * (fun x => r * fwdDiff (1 : K) F x) (n : K) := by
      funext n
      rw [aeval_X_sub_C_apply]
      simp only [fwdDiff, Nat.cast_add, Nat.cast_one]
      ring
    rw [pow_succ, mul_apply_eq_comp, h1, ih (fun x => r * fwdDiff (1 : K) F x)]
    funext n
    have h2 : (fwdDiff (1 : K))^[j] (fun x => r * fwdDiff (1 : K) F x) =
        r • (fwdDiff (1 : K))^[j] (fwdDiff (1 : K) F) := by
      have := fwdDiff_iter_const_smul (h := (1 : K)) (R := K) r (fwdDiff (1 : K) F) j
      exact this
    rw [h2, Function.iterate_succ_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- CO-229. For `r ≠ 0` and characteristic zero, the solutions of `(A - r)^k f = 0` are exactly the
sequences `(c_0 + c_1 n + ⋯ + c_{k-1} n^(k-1)) r^n`. -/
@[kb "kellertrotter2017" "Lemma 9.22, p. 225"]
theorem solutions_repeated_root [CharZero K] (k : ℕ) (r : K) (hr : r ≠ 0) (f : ℕ → K) :
    (aeval advance ((X - C r) ^ k) : Module.End K (ℕ → K)) f = 0 ↔
      ∃ c : Fin k → K, ∀ n : ℕ, f n = (∑ j : Fin k, c j * (n : K) ^ (j : ℕ)) * r ^ n := by
  have hmon : ((X - C r) ^ k).Monic := (monic_X_sub_C r).pow k
  have hdeg : ((X - C r) ^ k).natDegree = k := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  let w : Fin k → ℕ → K := fun j n => r ^ n * (n : K) ^ (j : ℕ)
  have hw : ∀ j, (aeval advance ((X - C r) ^ k) : Module.End K (ℕ → K)) (w j) = 0 := by
    intro j
    rw [map_pow, pow_sub_apply r k (fun x => x ^ (j : ℕ))]
    funext n
    rw [fwdDiff_iter_pow_eq_zero_of_lt j.2]
    simp
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hinj : Function.Injective (fun i : Fin k => ((i : ℕ) : K)) :=
      Nat.cast_injective.comp Fin.val_injective
    have hdet : (Matrix.vandermonde fun i : Fin k => ((i : ℕ) : K)).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.2 hinj
    have : (Matrix.vandermonde fun i : Fin k => ((i : ℕ) : K)).mulVec c = 0 := by
      funext i
      have := congrFun hc (i : ℕ)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, w] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
      have hrn : r ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hr
      refine (mul_eq_zero.1 ?_).resolve_left hrn
      rw [← this, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet this) i
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := exists_coeffs_of_linearIndependent hmon (by simp [hdeg]) w hw hli f hf
    refine ⟨c, fun n => ?_⟩
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Finset.sum_mul]
    exact sum_congr rfl fun j _ => by ring
  · rintro ⟨c, hc⟩
    have : f = ∑ j, c j • w j := by
      funext n
      rw [hc n]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w, Finset.sum_mul]
      exact sum_congr rfl fun j _ => by ring
    rw [this]
    exact aeval_sum_smul _ _ hw

/-! ### Zero as a root: translates -/

/-- CO-223. If `p = A^m q(A)`, then `f` solves `p(A) f = g` iff the shift `A^m f` solves
`q(A) h = g`. -/
@[kb "kellertrotter2017" "text (9.3.3), p. 213"]
theorem aeval_X_pow_mul_apply (m : ℕ) (q : K[X]) (f : ℕ → K) :
    (aeval advance (X ^ m * q) : Module.End K (ℕ → K)) f =
      (aeval advance q : Module.End K (ℕ → K)) ((advance ^ m : Module.End K (ℕ → K)) f) := by
  rw [mul_comm, map_mul, map_pow, aeval_X, mul_apply_eq_comp]

/-- CO-223. Conversely every sequence `h` is the shift `A^m f` of a sequence `f` (namely
`f n = h (n - m)` for `n ≥ m`), so solutions of `A^m q(A) f = g` are exactly translates of
solutions of `q(A) h = g`. -/
@[kb "kellertrotter2017" "text (9.3.3), p. 213"]
theorem advance_pow_translate (m : ℕ) (h : ℕ → K) :
    (advance ^ m : Module.End K (ℕ → K)) (fun n => if m ≤ n then h (n - m) else 0) = h := by
  funext n
  rw [advance_pow_apply]
  simp

end UndergradKB.Combinatorics.Recurrence
