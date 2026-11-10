import Mathlib.Algebra.LinearRecurrence
import Mathlib.NumberTheory.Real.GoldenRatio
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 9 (recurrence equations): thin wrappers over Mathlib
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter
open scoped goldenRatio

/-- CO-217. Fibonacci numbers: f₀ = 0, f₁ = 1 and f_{n+2} = f_n + f_{n+1}. -/
@[kb "kellertrotter2017" "text (Fibonacci sequence), p. 208"]
theorem text_p208_fibonacci :
    Nat.fib 0 = 0 ∧ Nat.fib 1 = 1 ∧ ∀ n, Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  ⟨rfl, rfl, fun _ => Nat.fib_add_two⟩

/-- CO-225. The solutions of a homogeneous linear recurrence of order `k` form a `k`-dimensional
subspace of the sequence space. -/
@[kb "kellertrotter2017" "Theorem 9.18, p. 223"]
theorem thm_9_18 {K : Type*} [CommRing K] [StrongRankCondition K] (E : LinearRecurrence K) :
    Module.rank K E.solSpace = E.order :=
  LinearRecurrence.solSpace_rank E

/-- CO-231. Binet's formula for the Fibonacci numbers (Exercises 9.9.5, 9.9.18). -/
@[kb "kellertrotter2017" "text (Exercise 9.9.5), p. 234"]
theorem ex_9_9_5_binet (n : ℕ) : (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5 :=
  Real.coe_fib_eq n


/-- CO-224. A linear operator on a real vector space is additive and homogeneous, and the
operators themselves form a vector space (operations act pointwise). -/
@[kb "kellertrotter2017" "Definition (unnumbered) linear operator, p. 223"]
theorem def_p223_linear_operator {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : Module.End ℝ V) (x y : V) (c : ℝ) :
    f (x + y) = f x + f y ∧ f (c • x) = c • f x ∧ (f + g) x = f x + g x ∧ (c • f) x = c • f x :=
  ⟨map_add f x y, map_smul f c x, rfl, rfl⟩

end UndergradKB.Combinatorics.Course.KellerTrotter
