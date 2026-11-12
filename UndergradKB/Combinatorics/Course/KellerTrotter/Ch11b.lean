import UndergradKB.Combinatorics.Graph.Ramsey
import UndergradKB.Combinatorics.Graph.RamseyMore
import UndergradKB.Combinatorics.Graph.RamseyValues
import UndergradKB.Combinatorics.Graph.RamseyEulerMore
import UndergradKB.Combinatorics.Counting.Stirling
import UndergradKB.Combinatorics.Counting.TreesEGF
import UndergradKB.Combinatorics.Probability.Discrete
import UndergradKB.Combinatorics.Probability.ErdosGirth
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 11: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch11b

/-- CO-258. Every graph on at least six vertices has a triangle or an independent set of size
three, and the five-cycle shows that six cannot be lowered. -/
@[kb "kellertrotter2017" "Lemma 11.1, p. 253"]
theorem lem_11_1_six_vertices :
    (∀ (V : Type) [Fintype V], 6 ≤ Fintype.card V → ∀ G : SimpleGraph V,
        ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree 3) ∧
      ((SimpleGraph.cycleGraph 5).CliqueFree 3 ∧ (SimpleGraph.cycleGraph 5)ᶜ.CliqueFree 3) :=
  ⟨fun V _ h G => six_vertices_triangle_or_independent V h G,
    cycleGraph_five_no_triangle_no_independent⟩

/-- CO-259. Ramsey's theorem for graphs: `R(m, n)` exists and `R(m, n) ≤ C(m+n-2, m-1)`. -/
@[kb "kellertrotter2017" "Theorem 11.2, p. 254"]
theorem thm_11_2_ramsey (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    RamseyProp m n (ramseyNumber m n) ∧ ramseyNumber m n ≤ (m + n - 2).choose (m - 1) :=
  ramseyNumber_le m n hm hn

/-- CO-260 (partial). The known small Ramsey values `R(3,3) = 6` and `R(4,4) = 18` (the other
entries of the book's table of bounds are not formalized). -/
@[kb "kellertrotter2017" "text (small Ramsey numbers), p. 254"]
theorem text_p254_small_ramsey_values : ramseyNumber 3 3 = 6 ∧ ramseyNumber 4 4 = 18 :=
  ⟨ramseyNumber_three_three, ramseyNumber_four_four⟩

/-- CO-261. The diagonal Ramsey numbers satisfy `R(n, n) ≤ C(2n-2, n-1)`, and `C(2n-2, n-1)` is
asymptotic to `4ⁿ / (4 √(π n))` (Stirling). -/
@[kb "kellertrotter2017" "text (diagonal upper bound), p. 255"]
theorem text_p255_diagonal_upper_bound :
    (∀ n : ℕ, 1 ≤ n → RamseyProp n n (ramseyNumber n n) ∧
        ramseyNumber n n ≤ (2 * n - 2).choose (n - 1)) ∧
      Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => ((2 * n - 2).choose (n - 1) : ℝ))
        (fun n : ℕ => 4 ^ n / (4 * √(Real.pi * n))) :=
  ⟨ramseyNumber_diagonal_le, choose_two_mul_sub_two_isEquivalent⟩

/-- CO-526 (partial). Stirling's approximation: `n! ∼ √(2πn) (n/e)ⁿ`, with the explicit two-sided
bound `√(2πn)(n/e)ⁿ ≤ n! ≤ √(2πn)(n/e)ⁿ e^{1/(12n)}`. -/
@[kb "kellertrotter2017" "text (Stirling approximation), p. 255"]
theorem text_p255_stirling :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (n.factorial : ℝ))
        (fun n : ℕ => √(2 * Real.pi * n) * (n / Real.exp 1) ^ n) ∧
      ∀ n : ℕ, n ≠ 0 → √(2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤ n.factorial ∧
        (n.factorial : ℝ) ≤ √(2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨Stirling.factorial_isEquivalent, fun _ hn => Stirling.stirling_bounds hn⟩

/-- CO-262. Erdős's lower bound: if `2 C(N, n) < 2^{C(n,2)}` there is a graph on `N` vertices with
neither an `n`-clique nor an independent `n`-set; consequently
`R(n, n) ≥ (n / (e √2)) 2^{n/2}`. -/
@[kb "kellertrotter2017" "Theorem 11.4, p. 256"]
theorem thm_11_4_ramsey_lower_bound :
    (∀ N n : ℕ, 2 * N.choose n < 2 ^ n.choose 2 →
        ∃ G : SimpleGraph (Fin N), G.CliqueFree n ∧ Gᶜ.CliqueFree n) ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) / (Real.exp 1 * √2) * 2 ^ ((n : ℝ) / 2) ≤ ramseyNumber n n :=
  ⟨exists_graph_no_clique_no_independent, ramseyNumber_diag_ge⟩

/-- CO-249. First moment method: if a random count `X` of bad structures has `E(X) < 1`, some
outcome of positive probability has none. -/
@[kb "kellertrotter2017" "text (first moment method), p. 257"]
theorem text_p257_first_moment {Ω : Type*} [Fintype Ω] (μ : Probability.FinProbSpace Ω)
    (X : Ω → ℕ) (h : (μ.expect fun ω => (X ω : ℝ)) < 1) : ∃ ω : Ω, 0 < μ.p ω ∧ X ω = 0 :=
  Probability.FinProbSpace.first_moment μ X h

/-- CO-263. General Ramsey theorem: for `s`-subsets coloured with `r` colours and prescribed sizes
`h α`, for `n` large every colouring of the `s`-subsets of `[n]` has a colour class `α` with a
set of size `h α` all of whose `s`-subsets have colour `α`. -/
@[kb "kellertrotter2017" "Theorem 11.6, p. 258"]
theorem thm_11_6_general_ramsey (s r : ℕ) (h : Fin r → ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ φ : Finset ℕ → Fin r,
      ∃ α : Fin r, ∃ H ⊆ Finset.Icc 1 n, H.card = h α ∧ ∀ S ⊆ H, S.card = s → φ S = α :=
  ramsey_general s r h

/-- CO-250. Erdős: for all `g` and `t` there is a graph with chromatic number greater than `t` and
girth greater than `g`. -/
@[kb "kellertrotter2017" "Theorem 11.7, p. 258"]
theorem thm_11_7_large_girth_large_chromatic (g t : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (t : ℕ∞) < G.chromaticNumber ∧ (g : ℕ∞) < G.egirth :=
  exists_graph_large_girth_large_chromatic g t

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch11b
