import UndergradKB.Combinatorics.Counting.Misc
import UndergradKB.Combinatorics.Counting.Sperner
import UndergradKB.Combinatorics.Order.Posets4
import UndergradKB.Combinatorics.Order.OnlineAntichain
import UndergradKB.Combinatorics.Order.Covers
import UndergradKB.Combinatorics.Order.Dominance
import UndergradKB.Combinatorics.Order.GaleRyser
import UndergradKB.Combinatorics.Order.GaleRyserSwap
import UndergradKB.Combinatorics.Graph.Online
import UndergradKB.Combinatorics.Graph.StableMatching
import UndergradKB.Combinatorics.Graph.RamseyMore
import UndergradKB.Combinatorics.Probability.RegularChain
import UndergradKB.Combinatorics.Probability.LocalLemma
import UndergradKB.Combinatorics.Probability.RamseyLLL5
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 16: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch16b

/-- CO-284. Builder can force Assigner to use three colours on-line even when the final graph is
a path on four vertices. -/
@[kb "kellertrotter2017" "Example 16.1, p. 339"]
theorem ex_16_1_three_colours_on_path (σ : Online.Strategy) :
    ∃ G : SimpleGraph ℕ, Online.Supp 4 G ∧
      (∃ π : Fin 4 ≃ Fin 4, ∀ i j : Fin 4,
        G.Adj (i : ℕ) (j : ℕ) ↔ (SimpleGraph.pathGraph 4).Adj (π i) (π j)) ∧
      (Online.Improper σ G 4 ∨ 3 ≤ (Finset.image (Online.colour σ G) (Finset.range 4)).card) :=
  Online.three_colours_on_path σ

/-- CO-285. For every `n`, Builder can present a forest on at most `2^(n-1)` vertices forcing
Assigner to use `n` colours on-line (or to colour improperly). -/
@[kb "kellertrotter2017" "Theorem 16.2, p. 340"]
theorem thm_16_2_builder_forces_colours (n : ℕ) (hn : 1 ≤ n) (σ : Online.Strategy) :
    ∃ G : SimpleGraph ℕ, ∃ p ≤ 2 ^ (n - 1), Online.Supp p G ∧ G.IsAcyclic ∧
      (Online.Improper σ G p ∨ n ≤ (Finset.image (Online.colour σ G) (Finset.range p)).card) :=
  Online.builder_forces_colours n hn σ

/-- CO-177. On-line partition into antichains: if a poset has height at most `h` (every chain has at
most `h` elements), the strategy that puts a new point in the class given by the lengths of the
longest chains below and above it uses at most `C(h+1, 2)` antichains. -/
@[kb "kellertrotter2017" "Theorem 16.4, p. 341"]
theorem thm_16_4_online_antichain_partition {P : Type*} [PartialOrder P] (x : ℕ → P) {n h : ℕ}
    (hinj : Set.InjOn x (Set.Iio n))
    (hh : ∀ C : Finset P, IsChain (fun x1 x2 : P => x1 ≤ x2) (C : Set P) → C.card ≤ h) :
    (∀ a b : ℕ, a < n → b < n → a ≠ b →
        Online.antichainClass (Online.presented x) a =
            Online.antichainClass (Online.presented x) b →
          ¬x a ≤ x b ∧ ¬x b ≤ x a) ∧
      (Finset.image (Online.antichainClass (Online.presented x)) (Finset.range n)).card ≤
        (h + 1).choose 2 :=
  Online.online_antichain_partition x hinj hh

/-- CO-178. Szemerédi: against any valid on-line strategy Builder can present a poset of height at
most `h` forcing at least `C(h+1, 2)` antichain labels, and at least `h` on its maximal elements. -/
@[kb "kellertrotter2017" "Theorem 16.5, p. 341"]
theorem thm_16_5_szemeredi_online_antichain (h : ℕ) (σ : OnlineAntichain.Strategy)
    (hσ : OnlineAntichain.Valid σ) :
    ∃ (k : ℕ) (r : OnlineAntichain.Rel), OnlineAntichain.IsPos k r ∧
      OnlineAntichain.HeightLe k r h ∧ (h + 1).choose 2 ≤ (OnlineAntichain.labs σ k r).card ∧
        h ≤ (OnlineAntichain.maxLabs σ k r).card :=
  szemeredi_online_antichain h σ hσ

/-- CO-329. The extremal families in Sperner's theorem are exactly the families of all
`⌊n/2⌋`-subsets or of all `⌈n/2⌉`-subsets. -/
@[kb "kellertrotter2017" "text (extremal Sperner families), p. 343"]
theorem text_p343_sperner_extremal {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset (Finset α)} (hA : IsAntichain (fun x1 x2 : Finset α => x1 ⊆ x2) (A : Set (Finset α)))
    (hcard : A.card = (Fintype.card α).choose (Fintype.card α / 2)) :
    A = Finset.powersetCard (Fintype.card α / 2) Finset.univ ∨
      A = Finset.powersetCard ((Fintype.card α + 1) / 2) Finset.univ :=
  Counting.sperner_extremal hA hcard

/-- CO-253. For a regular transition matrix `P`, the rows of `P^m` converge to a positive
probability vector `W` with `W P = W`. -/
@[kb "kellertrotter2017" "Theorem 16.9, p. 345"]
theorem thm_16_9_regular_chain_limit {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Matrix n n ℝ} (hP : Markov.IsRegular P) :
    ∃ W : n → ℝ, (∀ c : n, 0 < W c) ∧ ∑ c : n, W c = 1 ∧
      (∀ j : n, Filter.Tendsto (fun m : ℕ => (P ^ m) j) Filter.atTop (nhds W)) ∧
        Matrix.vecMul W P = W :=
  Markov.regular_chain_limit hP

/-- CO-309. Stable Matching Theorem: for any strict preference lists of `n` males and `n` females
there is a stable perfect matching. -/
@[kb "kellertrotter2017" "text (Stable Matching Theorem), p. 345"]
theorem text_p345_stable_matching {M F : Type*} {P : StableMatching.PrefProfile M F} [Fintype M]
    [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, StableMatching.IsStable P σ :=
  StableMatching.exists_stable hcard

/-- CO-287. The proposal algorithm halts with a stable matching: the final state is a stable
perfect matching, each step strictly decreases a measure, males only move down their lists and
females only improve. -/
@[kb "kellertrotter2017" "text (proposal algorithm correctness), p. 346"]
theorem text_p346_proposal_algorithm_correct :
    (∀ {M F : Type*} {P : StableMatching.PrefProfile M F} [Fintype M] [Fintype F],
      Fintype.card M = Fintype.card F →
        ∃ σ : M ≃ F, StableMatching.IsStable P σ ∧
          (∀ m : M, StableMatching.IsProp P (StableMatching.run P fun _ => ∅) m (σ m)) ∧
          ¬∃ R' : StableMatching.State M F,
            StableMatching.Step P (StableMatching.run P fun _ => ∅) R') ∧
    (∀ {M F : Type*} {P : StableMatching.PrefProfile M F} [Fintype M] [Fintype F]
      {R R' : StableMatching.State M F}, StableMatching.Step P R R' →
        StableMatching.meas R' < StableMatching.meas R) ∧
    (∀ {M F : Type*} {P : StableMatching.PrefProfile M F} {R R' : StableMatching.State M F},
      StableMatching.Step P R R' → ∀ {m : M} {g g' : F}, StableMatching.IsProp P R m g →
        StableMatching.IsProp P R' m g' → P.rankM m g' ≤ P.rankM m g) ∧
    (∀ {M F : Type*} {P : StableMatching.PrefProfile M F} {R R' : StableMatching.State M F},
      StableMatching.Step P R R' → ∀ {m0 : M} {g : F}, StableMatching.IsProp P R m0 g →
        ∃ m1 : M, StableMatching.IsProp P R' m1 g ∧ P.rankF g m0 ≤ P.rankF g m1) :=
  ⟨fun h => StableMatching.run_correct h, fun h => StableMatching.step_meas_lt h,
    fun h => StableMatching.step_male_down h,
    fun h => StableMatching.step_female_up h⟩

/-- CO-332. If a `0`-`1` matrix has row sum string `R` and column sum string `C`, then the
conjugate (dual) of `R` dominates `C` in the dominance order. -/
@[kb "kellertrotter2017" "text (necessary condition), p. 347"]
theorem text_p347_dominates_conj_of_matrix {m n : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ)
    (M : Fin m → Fin n → Bool) (hR : ∀ i, rowSum M i = R i) (hC : ∀ j, colSum M j = C j) :
    Dominates (conj R) C :=
  dominates_conj_of_matrix R C M hR hC

/-- CO-180. If the partition `V` covers `W` in the dominance order, then they differ by moving one
unit from a position `i` to a position `j > i`, with the stated pattern on the entries in between. -/
@[kb "kellertrotter2017" "Proposition 16.11, p. 348"]
theorem prop_16_11_cover_description {m n t : ℕ} {V : Fin m → ℕ} {W : Fin n → ℕ}
    (h : IsCover V W t) :
    n ≤ m + 1 ∧ ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ n ∧
      (∀ α : ℕ, 1 ≤ α → α < i → extZero V (α - 1) = extZero W (α - 1)) ∧
      (∀ β : ℕ, j < β → β ≤ m → extZero V (β - 1) = extZero W (β - 1)) ∧
      extZero V (i - 1) = 1 + extZero W (i - 1) ∧
      ((j ≤ m ∧ extZero W (j - 1) = 1 + extZero V (j - 1)) ∨
        (j = n ∧ n = m + 1 ∧ extZero W (j - 1) = 1)) ∧
      (i + 1 < j → ∀ γ : ℕ, i < γ → γ < j →
        extZero W (γ - 1) = extZero V (γ - 1) ∧ extZero V (γ - 1) = extZero V (i - 1) - 1) :=
  cover_description h

/-- CO-334. Gale–Ryser: for partition strings `R` and `C` of the same total `t`, a `0`-`1` matrix
with row sums `R` and column sums `C` exists if and only if the conjugate of `R` dominates `C`
(equivalently, by the partial sums criterion). -/
@[kb "kellertrotter2017" "Theorem 16.12, p. 349"]
theorem thm_16_12_gale_ryser :
    (∀ {m n : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ), Antitone C → ∑ i, R i = ∑ j, C j →
      ((∃ M : Fin m → Fin n → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j) ↔
        ∀ s ≤ n, psum C s ≤ ∑ i : Fin m, min (R i) s)) ∧
    (∀ {m n t : ℕ} (R : Fin m → ℕ) (C : Fin n → ℕ), IsPartitionString R t →
      IsPartitionString C t →
        ((∃ M : Fin m → Fin n → Bool, (∀ i, rowSum M i = R i) ∧ ∀ j, colSum M j = C j) ↔
          Dominates (conj R) C)) :=
  ⟨fun R C hC hs => gale_ryser_partial_sums R C hC hs, fun R C hR hC => gale_ryser R C hR hC⟩

/-- CO-265. Van der Waerden: for `r` colours and length `t` there is `n₀` such that every
`r`-colouring of `{1, …, n}` with `n ≥ n₀` has a monochromatic `t`-term arithmetic progression. -/
@[kb "kellertrotter2017" "Theorem 16.13, p. 349"]
theorem thm_16_13_van_der_waerden (r t : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c : ℕ → Fin r, ∃ x : Fin t → ℕ, IsArithProg x ∧
      (∀ i, x i ∈ Finset.Icc 1 n) ∧ ∃ α : Fin r, ∀ i, c (x i) = α :=
  van_der_waerden r t

/-- CO-335 (partial). The construction in the proof of Gale–Ryser: a column-sum string reachable
by transfers from the column sums of a realizable matrix is again realizable (one swap per step),
starting from the left-justified matrix whose column sums are the conjugate of `R`. -/
@[kb "kellertrotter2017" "text (swap construction), p. 349"]
theorem text_p349_swap_construction :
    (∀ {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (M : ι → κ → Bool) {i j : κ}, colSum M j < colSum M i →
        ∃ M' : ι → κ → Bool, rowSum M' = rowSum M ∧
          colSum M' = Function.update
            (Function.update (colSum M) i (colSum M i - 1)) j (colSum M j + 1)) ∧
    (∀ {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      {R : ι → ℕ} {c C : κ → ℕ},
      (∃ M : ι → κ → Bool, rowSum M = R ∧ colSum M = c) →
        Relation.ReflTransGen GaleRyserSwap.Transfer c C →
          ∃ M : ι → κ → Bool, rowSum M = R ∧ colSum M = C) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {R : ι → ℕ}, (∀ r, R r ≤ n) →
      ∀ {C : Fin n → ℕ},
        Relation.ReflTransGen GaleRyserSwap.Transfer
            (colSum (GaleRyserSwap.leftJustified n R)) C →
          ∃ M : ι → Fin n → Bool, rowSum M = R ∧ colSum M = C) :=
  ⟨fun M => GaleRyserSwap.exists_swap_step M,
    fun h hr => GaleRyserSwap.exists_matrix_of_transfers h hr,
    fun hR => GaleRyserSwap.exists_matrix_of_chain hR⟩

section LocalLemma

open Probability

/-- CO-255. The Lovász Local Lemma (asymmetric form): if `P(E_i) ≤ x_i ∏_{j ∈ N(i)} (1 - x_j)` with
`0 < x_i < 1` and each event independent of the others outside its neighbourhood, then for every
index set `S` the probability that none of the events in `S` occurs is at least `∏_{j ∈ S}(1-x_j)`,
in particular positive. -/
@[kb "kellertrotter2017" "Lemma 16.14, p. 350"]
theorem lem_16_14_local_lemma {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [DecidableEq ι]
    {μ : FinProbSpace Ω} {E : ι → Finset Ω} {N : ι → Finset ι} {x : ι → ℝ}
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.prob (E i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (hind : LLLIndep μ E N) :
    ∀ S : Finset ι, ∏ j ∈ S, (1 - x j) ≤ μ.prob (noneOf E S) ∧ 0 < μ.prob (noneOf E S) :=
  fun S => ⟨lovasz_local_lemma hx0 hx1 hP hind S, lovasz_local_lemma_pos hx0 hx1 hP hind S⟩

/-- CO-256. Symmetric Local Lemma: if each `P(E_i) ≤ p`, each event depends on at most `d` others
and `e p (d+1) ≤ 1`, then with positive probability no event occurs (indeed no event in any
index set `S` occurs, with probability at least `(1 - 1/(d+1))^|S|`). -/
@[kb "kellertrotter2017" "Lemma 16.15, p. 352"]
theorem lem_16_15_symmetric_local_lemma {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*}
    [DecidableEq ι] {μ : FinProbSpace Ω} {E : ι → Finset Ω} {N : ι → Finset ι}
    (hind : LLLIndep μ E N) (p : ℝ) (d : ℕ) (hd : 1 ≤ d) (hP : ∀ i, μ.prob (E i) ≤ p)
    (hN : ∀ i, (N i).card ≤ d) (hep : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∀ S : Finset ι, (1 - 1 / ((d : ℝ) + 1)) ^ S.card ≤ μ.prob (noneOf E S) ∧
      0 < μ.prob (noneOf E S) :=
  fun S => ⟨lovasz_local_lemma_symmetric hind p d hd hP hN hep S,
    lovasz_local_lemma_symmetric_pos hind p d hd hP hN hep S⟩

/-- CO-257. The variant of the symmetric Local Lemma with hypothesis `4 p d ≤ 1`: no event in `S`
occurs with probability at least `(1 - 1/(2d))^|S| > 0`. -/
@[kb "kellertrotter2017" "text (Local Lemma with 4pd < 1), p. 352"]
theorem text_p352_local_lemma_four_pd {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*}
    [DecidableEq ι] {μ : FinProbSpace Ω} {E : ι → Finset Ω} {N : ι → Finset ι}
    (hind : LLLIndep μ E N) (p : ℝ) (d : ℕ) (hd : 1 ≤ d) (hP : ∀ i, μ.prob (E i) ≤ p)
    (hN : ∀ i, (N i).card ≤ d) (h4 : 4 * p * d ≤ 1) :
    ∀ S : Finset ι, 0 < (1 - 1 / (2 * (d : ℝ))) ^ S.card ∧
      (1 - 1 / (2 * (d : ℝ))) ^ S.card ≤ μ.prob (noneOf E S) :=
  fun S => lovasz_local_lemma_four_pd hind p d hd hP hN h4 S

end LocalLemma

/-- CO-266. The Local Lemma gives a lower bound `R(3, n) ≥ c n² / ln² n`: for large `n` there is a
triangle-free graph on `⌊n² / (6400 ln² n)⌋` vertices with no independent set of size `n`. -/
@[kb "kellertrotter2017" "text (R(3,n) lower bound), p. 352"]
theorem text_p352_ramsey_three_lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ G : SimpleGraph (Fin ⌊(n : ℝ) ^ 2 / (6400 * Real.log n ^ 2)⌋₊), G.CliqueFree 3 ∧
        ∀ A : Finset (Fin ⌊(n : ℝ) ^ 2 / (6400 * Real.log n ^ 2)⌋₊), A.card = n →
          ¬G.IsIndepSet (A : Set _) :=
  ramsey_three_lower_bound

/-- CO-024. A binary relation is a subset `S` of `X × Y`; it is the graph of a function exactly when
every `x` has exactly one `y` with `(x, y) ∈ S`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) binary relation, function, p. 361"]
theorem def_p361_relation_is_function {X Y : Type*} (S : Set (X × Y)) :
    (∃ f : X → Y, S = {p : X × Y | p.2 = f p.1}) ↔ ∀ x : X, ∃! y : Y, (x, y) ∈ S :=
  relation_is_function_iff S

/-- CO-343. Dedekind cuts of the rationals: each rational `q` gives a cut `{p | p < q}`, the map is
injective and order-preserving in both directions, and the cut for `√2` is a cut that is not
rational. -/
@[kb "kellertrotter2017" "Definition (unnumbered) Dedekind cut, rational cut, p. 379"]
theorem def_p379_dedekind_cut :
    (∀ q : ℚ, Order.IsCut (Order.rationalCut q)) ∧
      (∀ q r : ℚ, Order.rationalCut q ⊆ Order.rationalCut r ↔ q ≤ r) ∧
      Function.Injective Order.rationalCut ∧ Order.IsCut Order.sqrtTwoCut ∧
      ∀ q : ℚ, Order.sqrtTwoCut ≠ Order.rationalCut q :=
  ⟨Order.isCut_rationalCut, Order.rationalCut_subset_iff, Order.rationalCut_injective,
    Order.isCut_sqrtTwoCut, Order.sqrtTwoCut_not_rational⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch16b
