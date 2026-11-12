import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import UndergradKB.Common.Attr

/-!
# The Rothe-Hagen identity

CO-051: for real `t, r, s` and natural `n`,
`∑_{k=0}^n C(tk+r, k) C(tn-tk+s, n-k) r/(tk+r) = C(tn+r+s, n)`
with generalized binomial coefficients.  Instead of generating functions the proof uses a
recurrence in `r` (a Pascal-type rule satisfied by both sides) and polynomial interpolation
(a polynomial in `r` vanishing at all natural numbers is zero).
-/

namespace UndergradKB.Combinatorics.AeqB
open Finset

/-- Falling factorial `y (y-1) ... (y-j+1)`. -/
def rhFf (y : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => rhFf y j * (y - j)

/-- Generalized binomial coefficient `C(y, m)`. -/
noncomputable def rhGbinom (y : ℝ) (m : ℕ) : ℝ := rhFf y m / (m.factorial : ℝ)

/-- Polynomial form of `r/(tk+r) * C(tk+r, k)`. -/
noncomputable def rhTerm (t : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, r => r * rhFf (t * ((k : ℝ) + 1) + r - 1) k / ((k + 1).factorial : ℝ)

lemma rhFf_succ' (y : ℝ) (m : ℕ) : rhFf y (m + 1) = y * rhFf (y - 1) m := by
  induction m with
  | zero => simp [rhFf]
  | succ m ih =>
    rw [rhFf, ih, rhFf]
    push_cast
    ring

lemma rhGbinom_pascal (y : ℝ) (m : ℕ) :
    rhGbinom y (m + 1) = rhGbinom (y - 1) (m + 1) + rhGbinom (y - 1) m := by
  unfold rhGbinom
  rw [rhFf_succ', rhFf]
  have h1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2 : (m.factorial : ℝ) ≠ 0 := by positivity
  rw [h1]
  field_simp
  ring

lemma rhTerm_rec (t x : ℝ) (j : ℕ) :
    rhTerm t (j + 1) x = rhTerm t (j + 1) (x - 1) + rhTerm t j (x + t - 1) := by
  cases j with
  | zero => simp [rhTerm, rhFf]
  | succ i =>
    simp only [rhTerm]
    have e1 : t * (((i + 1 : ℕ) : ℝ) + 1) + x - 1 - 1 = t * ((i : ℝ) + 2) + x - 2 := by
      push_cast; ring
    have e2 : t * (((i + 1 : ℕ) : ℝ) + 1) + (x - 1) - 1 = t * ((i : ℝ) + 2) + x - 2 := by
      push_cast; ring
    have e3 : t * ((i : ℝ) + 1) + (x + t - 1) - 1 = t * ((i : ℝ) + 2) + x - 2 := by ring
    rw [rhFf_succ', e1, e2, e3, rhFf]
    have h1 : ((i + 1 + 1).factorial : ℝ) = ((i : ℝ) + 2) * ((i + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h2 : ((i + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [h1]
    field_simp
    push_cast
    ring

lemma rhTerm_zero_arg (t : ℝ) (k : ℕ) (hk : 0 < k) : rhTerm t k 0 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [rhTerm]

/-- The left-hand side, in polynomial form. -/
noncomputable def rhG (t : ℝ) (n : ℕ) (r s : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), rhTerm t k r * rhGbinom (t * ((n - k : ℕ) : ℝ) + s) (n - k)

/-- The right-hand side. -/
noncomputable def rhH (t : ℝ) (n : ℕ) (r s : ℝ) : ℝ := rhGbinom (t * n + r + s) n

lemma rhG_rec (t : ℝ) (m : ℕ) (r s : ℝ) :
    rhG t (m + 1) r s - rhG t (m + 1) (r - 1) s = rhG t m (r + t - 1) s := by
  unfold rhG
  rw [sum_range_succ' _ (m + 1), sum_range_succ' _ (m + 1)]
  have h0 : ∀ x : ℝ, rhTerm t 0 x = 1 := fun _ => rfl
  rw [h0, h0, add_sub_add_right_eq_sub, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  rw [← sub_mul, show rhTerm t (k + 1) r - rhTerm t (k + 1) (r - 1) = rhTerm t k (r + t - 1) by
    rw [rhTerm_rec t r k]; ring]
  simp only [Nat.add_sub_add_right]

lemma rhH_rec (t : ℝ) (m : ℕ) (r s : ℝ) :
    rhH t (m + 1) r s - rhH t (m + 1) (r - 1) s = rhH t m (r + t - 1) s := by
  unfold rhH
  rw [rhGbinom_pascal]
  have : t * ((m + 1 : ℕ) : ℝ) + r + s - 1 = t * (m : ℝ) + (r + t - 1) + s := by
    push_cast; ring
  rw [this, show t * ((m + 1 : ℕ) : ℝ) + (r - 1) + s = t * (m : ℝ) + (r + t - 1) + s by
    push_cast; ring]
  ring

lemma rhG_zero_arg (t : ℝ) (n : ℕ) (s : ℝ) : rhG t n 0 s = rhH t n 0 s := by
  unfold rhG rhH
  rw [sum_range_succ', sum_eq_zero]
  · simp [rhTerm]
  · intro k _
    rw [rhTerm_zero_arg t (k + 1) (by omega)]
    simp

/-! ### Polynomial functions -/

/-- `f` is given by a real polynomial. -/
def RhPoly (f : ℝ → ℝ) : Prop := ∃ P : Polynomial ℝ, ∀ x, f x = P.eval x

lemma RhPoly.const (c : ℝ) : RhPoly (fun _ => c) := ⟨Polynomial.C c, by simp⟩

lemma RhPoly.id : RhPoly (fun x => x) := ⟨Polynomial.X, by simp⟩

lemma RhPoly.add {f g : ℝ → ℝ} (hf : RhPoly f) (hg : RhPoly g) : RhPoly (fun x => f x + g x) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun x => by simp [hP, hQ]⟩

lemma RhPoly.sub {f g : ℝ → ℝ} (hf : RhPoly f) (hg : RhPoly g) : RhPoly (fun x => f x - g x) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P - Q, fun x => by simp [hP, hQ]⟩

lemma RhPoly.mul {f g : ℝ → ℝ} (hf : RhPoly f) (hg : RhPoly g) : RhPoly (fun x => f x * g x) := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun x => by simp [hP, hQ]⟩

lemma RhPoly.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ S, RhPoly (f i)) :
    RhPoly (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RhPoly.const 0
  | insert a S ha ih =>
    have := (h a (mem_insert_self _ _)).add (ih fun i hi => h i (mem_insert_of_mem hi))
    simpa [sum_insert ha] using this

lemma rhFf_poly (c : ℝ) (j : ℕ) : RhPoly (fun r => rhFf (r + c) j) := by
  induction j with
  | zero => simpa [rhFf] using RhPoly.const 1
  | succ j ih =>
    have h2 : RhPoly (fun r : ℝ => r + c - (j : ℝ)) :=
      (RhPoly.id.add (RhPoly.const c)).sub (RhPoly.const (j : ℝ))
    simpa [rhFf] using ih.mul h2

lemma rhTerm_poly (t : ℝ) (k : ℕ) : RhPoly (fun r => rhTerm t k r) := by
  cases k with
  | zero => simpa [rhTerm] using RhPoly.const 1
  | succ j =>
    have h := (RhPoly.id.mul (rhFf_poly (t * ((j : ℝ) + 1) - 1) j)).mul
      (RhPoly.const (1 / ((j + 1).factorial : ℝ)))
    convert h using 2 with r
    simp only [rhTerm]
    rw [show t * ((j : ℝ) + 1) + r - 1 = r + (t * ((j : ℝ) + 1) - 1) by ring]
    ring

lemma rhGbinom_poly (c : ℝ) (m : ℕ) : RhPoly (fun r => rhGbinom (r + c) m) := by
  have h := (rhFf_poly c m).mul (RhPoly.const (1 / (m.factorial : ℝ)))
  convert h using 2 with r
  simp only [rhGbinom]
  ring

lemma rhG_poly (t : ℝ) (n : ℕ) (s : ℝ) : RhPoly (fun r => rhG t n r s) := by
  unfold rhG
  apply RhPoly.sum
  intro k _
  exact (rhTerm_poly t k).mul (RhPoly.const _)

lemma rhH_poly (t : ℝ) (n : ℕ) (s : ℝ) : RhPoly (fun r => rhH t n r s) := by
  have h := rhGbinom_poly (t * n + s) n
  convert h using 2 with r
  simp only [rhH]
  rw [show t * (n : ℝ) + r + s = r + (t * n + s) by ring]

lemma rhPoly_zero {f : ℝ → ℝ} (hf : RhPoly f) (h : ∀ m : ℕ, f m = 0) : ∀ x, f x = 0 := by
  obtain ⟨P, hP⟩ := hf
  have hz : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → ℝ))
    · rintro _ ⟨m, rfl⟩
      show Polynomial.IsRoot P (m : ℝ)
      rw [Polynomial.IsRoot.def, ← hP]; exact h m
    · exact Set.infinite_range_of_injective Nat.cast_injective
  intro x
  rw [hP, hz]; simp

lemma rhG_eq_rhH (t : ℝ) (n : ℕ) : ∀ r s : ℝ, rhG t n r s = rhH t n r s := by
  induction n with
  | zero => intro r s; simp [rhG, rhH, rhTerm, rhGbinom, rhFf]
  | succ m ih =>
    intro r s
    have hN : ∀ j : ℕ, rhG t (m + 1) j s - rhH t (m + 1) j s = 0 := by
      intro j
      induction j with
      | zero => simp [rhG_zero_arg]
      | succ j ihj =>
        have a := rhG_rec t m ((j : ℝ) + 1) s
        have b := rhH_rec t m ((j : ℝ) + 1) s
        rw [add_sub_cancel_right] at a b
        rw [ih] at a
        push_cast
        linarith
    have hp : RhPoly (fun r => rhG t (m + 1) r s - rhH t (m + 1) r s) :=
      (rhG_poly t (m + 1) s).sub (rhH_poly t (m + 1) s)
    have := rhPoly_zero hp hN r
    simpa [sub_eq_zero] using this

/-- CO-051. The Rothe-Hagen identity in polynomial form, valid for all real `t, r, s`: the
summand `r/(tk+r) * C(tk+r, k)` is written as the polynomial `r * (tk+r-1)^{\underline{k-1}} / k!`
(and `1` for `k = 0`).  The proof is by a Pascal-type recurrence in `r` satisfied by both sides
and polynomial interpolation (a polynomial in `r` vanishing on all naturals is zero), instead of
the generating functions used in the book. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 33"]
theorem rothe_hagen (t r s : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), rhTerm t k r * rhGbinom (t * n - t * k + s) (n - k) =
      rhGbinom (t * n + r + s) n := by
  rw [← rhH, ← rhG_eq_rhH t n r s, rhG]
  apply sum_congr rfl
  intro k hk
  have : k ≤ n := by have := mem_range.1 hk; omega
  rw [Nat.cast_sub this]
  ring_nf

lemma rhTerm_eq (t r : ℝ) (k : ℕ) (h : t * k + r ≠ 0) :
    rhTerm t k r = rhGbinom (t * k + r) k * (r / (t * k + r)) := by
  cases k with
  | zero =>
    have : r ≠ 0 := by simpa using h
    simp [rhTerm, rhGbinom, rhFf, this]
  | succ j =>
    have h' : t * ((j : ℝ) + 1) + r ≠ 0 := by simpa using h
    simp only [rhTerm, rhGbinom]
    push_cast
    rw [rhFf_succ', show t * ((j : ℝ) + 1) + r - 1 = t * ((j : ℝ) + 1) + r - 1 from rfl]
    field_simp

/-- CO-051. The Rothe-Hagen identity in the book's literal form
`∑ C(tk+r,k) C(tn-tk+s,n-k) r/(tk+r) = C(tn+r+s,n)` with generalized binomial coefficients.
Lean adds the genericity hypothesis `t*k + r ≠ 0` for `k ≤ n` so that the quotient makes sense;
the unconditional polynomial version is `rothe_hagen`.  The proof is by a recurrence in `r`
and polynomial interpolation, not by generating functions. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 33"]
theorem rothe_hagen_book (t r s : ℝ) (n : ℕ) (h : ∀ k ≤ n, t * k + r ≠ 0) :
    ∑ k ∈ range (n + 1), rhGbinom (t * k + r) k * rhGbinom (t * n - t * k + s) (n - k) *
        (r / (t * k + r)) = rhGbinom (t * n + r + s) n := by
  rw [← rothe_hagen t r s n]
  apply sum_congr rfl
  intro k hk
  rw [rhTerm_eq t r k (h k (by have := mem_range.1 hk; omega))]
  ring

/-- CO-051 (special case `t = 3`, `r = 1`, `s = 0`):
`∑_k C(3k+1,k)/(3k+1) * C(3n-3k, n-k) = C(3n+1, n)`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 33"]
theorem rothe_hagen_three (n : ℕ) :
    ∑ k ∈ range (n + 1), rhGbinom (3 * k + 1) k * (1 / (3 * k + 1)) *
        rhGbinom (3 * n - 3 * k) (n - k) = rhGbinom (3 * n + 1) n := by
  have := rothe_hagen_book 3 1 0 n (fun k _ => by positivity)
  simp only [add_zero] at this
  rw [← this]
  apply sum_congr rfl
  intro k _
  ring

end UndergradKB.Combinatorics.AeqB
