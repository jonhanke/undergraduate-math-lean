import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import UndergradKB.Combinatorics.Recurrence.Linear
import UndergradKB.Common.Attr

/-!
# The general homogeneous linear recurrence (Keller–Trotter, Sections 9.2 and 9.5.4)

* `IsLinearRecSolution`: the linear recurrence `c_0 a_{n+k} + ⋯ + c_k a_n = g(n)` and its
  translation into an advancement operator equation `q(A) a = g`.
* `solutions_general`: the general solution of `p(A) f = 0` for a factored `p`.
-/

namespace UndergradKB.Combinatorics.Recurrence

open Polynomial Finset

variable {K : Type*} [Field K]

/-! ### CO-221: linear recurrences with constant coefficients -/

/-- CO-221. The sequence `a` satisfies the linear recurrence with constant coefficients
`c 0 * a (n + k) + c 1 * a (n + k - 1) + ⋯ + c k * a n = g n` for all `n`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear recurrence equation, p. 211"]
def IsLinearRecSolution {k : ℕ} (c : Fin (k + 1) → K) (g a : ℕ → K) : Prop :=
  ∀ n, ∑ i : Fin (k + 1), c i * a (n + (k - (i : ℕ))) = g n

/-- CO-221. A linear recurrence of order `k ≥ 1` in the book's sense: `c 0 ≠ 0` and `c k ≠ 0`.
It is homogeneous when `g = 0`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear recurrence equation, p. 211"]
structure IsLinearRecurrence {k : ℕ} (c : Fin (k + 1) → K) : Prop where
  one_le : 1 ≤ k
  first_ne : c 0 ≠ 0
  last_ne : c (Fin.last k) ≠ 0

/-- CO-221. The characteristic polynomial `q = ∑ c_i X^(k-i)` of the recurrence. -/
noncomputable def charPoly {k : ℕ} (c : Fin (k + 1) → K) : K[X] :=
  ∑ i : Fin (k + 1), C (c i) * X ^ (k - (i : ℕ))

/-- CO-221. The linear recurrence `∑ c_i a_{n+k-i} = g(n)` is the advancement operator equation
`q(A) a = g` with `q = ∑ c_i X^(k-i)`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear recurrence equation, p. 211"]
theorem isLinearRecSolution_iff_aeval {k : ℕ} (c : Fin (k + 1) → K) (g a : ℕ → K) :
    IsLinearRecSolution c g a ↔ (aeval advance (charPoly c) : Module.End K (ℕ → K)) a = g := by
  have key : ∀ n, (aeval advance (charPoly c) : Module.End K (ℕ → K)) a n =
      ∑ i : Fin (k + 1), c i * a (n + (k - (i : ℕ))) := by
    intro n
    simp [charPoly, map_sum, LinearMap.sum_apply, advance_pow_apply]
  constructor
  · intro h; funext n; rw [key]; exact h n
  · intro h n; rw [← key, h]

/-! ### CO-230: the general case -/

lemma isCoprime_pow_sub {a b : K} (hab : a ≠ b) (m l : ℕ) :
    IsCoprime ((X - C a) ^ m) ((X - C b) ^ l) :=
  (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow

/-- CO-230. If `p(A) = ∏ (A - r_i)^(m_i)` with distinct nonzero roots `r_i`, then the solutions of
`p(A) f = 0` are exactly the sequences `∑_i (c_{i0} + c_{i1} n + ⋯ + c_{i,m_i-1} n^(m_i-1)) r_i^n`. -/
@[kb "kellertrotter2017" "text (9.5.4), p. 226"]
theorem solutions_general [CharZero K] {k : ℕ} (r : Fin k → K) (m : Fin k → ℕ)
    (hr : Function.Injective r) (hr0 : ∀ i, r i ≠ 0) (f : ℕ → K) :
    (aeval advance (∏ i, (X - C (r i)) ^ m i) : Module.End K (ℕ → K)) f = 0 ↔
      ∃ c : (i : Fin k) → Fin (m i) → K, ∀ n : ℕ,
        f n = ∑ i, ∑ j : Fin (m i), c i j * (n : K) ^ (j : ℕ) * r i ^ n := by
  induction k generalizing f with
  | zero =>
    simp only [Finset.univ_eq_empty, prod_empty, map_one, Finset.sum_empty]
    constructor
    · intro h
      refine ⟨fun i => i.elim0, fun n => ?_⟩
      have := congrFun h n
      simpa using this
    · rintro ⟨c, hc⟩
      funext n
      simp [hc n]
  | succ k ih =>
    have hr' : Function.Injective (fun i : Fin k => r i.succ) := hr.comp (Fin.succ_injective _)
    have hcop : IsCoprime ((X - C (r 0)) ^ m 0) (∏ i : Fin k, (X - C (r i.succ)) ^ m i.succ) :=
      IsCoprime.prod_right fun i _ =>
        isCoprime_pow_sub (fun h => (Fin.succ_ne_zero i) (hr h.symm)) _ _
    rw [Fin.prod_univ_succ]
    have hker := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
      (advance : Module.End K (ℕ → K)) hcop
    have hmem : ∀ g, (aeval advance ((X - C (r 0)) ^ m 0 *
        ∏ i : Fin k, (X - C (r i.succ)) ^ m i.succ) : Module.End K (ℕ → K)) g = 0 ↔
        g ∈ LinearMap.ker (aeval advance ((X - C (r 0)) ^ m 0)) ⊔
          LinearMap.ker (aeval advance (∏ i : Fin k, (X - C (r i.succ)) ^ m i.succ)) := by
      intro g
      rw [hker, LinearMap.mem_ker]
    rw [hmem, Submodule.mem_sup]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      rw [LinearMap.mem_ker, solutions_repeated_root _ _ (hr0 0)] at hx
      rw [LinearMap.mem_ker, ih (fun i => r i.succ) (fun i => m i.succ) hr' (fun i => hr0 _)] at hy
      obtain ⟨c0, h0⟩ := hx
      obtain ⟨c', h'⟩ := hy
      refine ⟨Fin.cons (α := fun i => Fin (m i) → K) c0 c', fun n => ?_⟩
      rw [Pi.add_apply, h0, h', Fin.sum_univ_succ]
      simp [Finset.sum_mul]
    · rintro ⟨c, hc⟩
      refine ⟨fun n => ∑ j : Fin (m 0), c 0 j * (n : K) ^ (j : ℕ) * r 0 ^ n,
        ?_, fun n => ∑ i : Fin k, ∑ j : Fin (m i.succ),
          c i.succ j * (n : K) ^ (j : ℕ) * r i.succ ^ n, ?_, ?_⟩
      · rw [LinearMap.mem_ker, solutions_repeated_root _ _ (hr0 0)]
        exact ⟨c 0, fun n => by simp [Finset.sum_mul]⟩
      · rw [LinearMap.mem_ker, ih (fun i => r i.succ) (fun i => m i.succ) hr' (fun i => hr0 _)]
        exact ⟨fun i => c i.succ, fun n => rfl⟩
      · funext n
        rw [Pi.add_apply, hc n, Fin.sum_univ_succ]

end UndergradKB.Combinatorics.Recurrence
