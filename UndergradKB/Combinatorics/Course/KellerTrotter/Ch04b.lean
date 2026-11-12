import Mathlib.Basic.Real.Basic
import Mathlib.Order.Monotone.Basic
import UndergradKB.Combinatorics.Graph.ErdosSzekeres
import UndergradKB.Combinatorics.Graph.Complexity
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 4: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch04b

/-- CO-073. Erdős–Szekeres: any sequence of `m n + 1` distinct reals has an increasing
subsequence of `m + 1` terms or a decreasing one of `n + 1` terms. -/
@[kb "kellertrotter2017" "Theorem 4.2, p. 83"]
theorem thm_4_2_erdos_szekeres (m n : ℕ) (f : Fin (m * n + 1) → ℝ) (hf : Function.Injective f) :
    (∃ s : Finset (Fin (m * n + 1)), s.card = m + 1 ∧ StrictMonoOn f s) ∨
    (∃ s : Finset (Fin (m * n + 1)), s.card = n + 1 ∧ StrictAntiOn f s) :=
  erdos_szekeres m n f hf

/-- CO-074. The Erdős–Szekeres bound is sharp: some sequence of `m n` distinct reals has no
increasing subsequence of `m + 1` terms and no decreasing one of `n + 1` terms. -/
@[kb "kellertrotter2017" "text, p. 88"]
theorem text_4_erdos_szekeres_sharp (m n : ℕ) :
    ∃ f : Fin (m * n) → ℝ, Function.Injective f ∧
      (∀ s : Finset (Fin (m * n)), StrictMonoOn f s → s.card ≤ m) ∧
      (∀ s : Finset (Fin (m * n)), StrictAntiOn f s → s.card ≤ n) :=
  erdos_szekeres_sharp m n

/-- CO-077. `P ⊆ NP` (partial: stated under closure of polynomial-time computability under
composition and polynomial-time computability of dropping the certificate). -/
@[kb "kellertrotter2017" "text, p. 90"]
theorem text_4_p_subset_np {α Γ : Type} (hcomp : Complexity.PolyTimeCompClosed)
    (ea : α → List Γ) (hproj : Complexity.PolyTime (Complexity.pairEnc ea) ea Prod.fst)
    (L : α → Prop) (hL : Complexity.InP ea L) : Complexity.InNP ea L :=
  Complexity.inP_subset_inNP hcomp ea hproj L hL

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch04b
