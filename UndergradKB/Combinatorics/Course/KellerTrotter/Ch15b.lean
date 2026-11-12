import UndergradKB.Combinatorics.Counting.Basic2
import UndergradKB.Combinatorics.Polya.CycleIndex
import UndergradKB.Combinatorics.Polya.Inventory
import UndergradKB.Combinatorics.Polya.PairGroup
import UndergradKB.Combinatorics.Polya.Graphs
import UndergradKB.Common.Attr

/-!
# Keller–Trotter, Chapter 15: course wrappers of results proved in this library (wave 3)
-/

namespace UndergradKB.Combinatorics.Course.KellerTrotter.Ch15b

open scoped Classical
open MulAction Polya

attribute [local instance] arrowAction

/-- Proposition 15.8, p. 322 (CO-316). For a finite group `G` acting on a finite set, the sum of
the sizes of the stabilizers over the orbit of a point `x` equals `|G|`. -/
@[kb "kellertrotter2017" "Proposition 15.8, p. 322"]
theorem prop_15_8_stabilizer_sum {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    (x : X) :
    ∑ y ∈ (MulAction.orbit G x).toFinset, Fintype.card (MulAction.stabilizer G y) =
      Fintype.card G :=
  sum_card_stabilizer_orbit x

/-- CO-318. The number of `m`-colourings of a set fixed by a permutation is `m` to the power of its
number of cycles, since each cycle must be monochromatic. -/
@[kb "kellertrotter2017" "text (fixed colourings), p. 323"]
theorem text_p323_fixed_colorings {S C : Type*} [Fintype S] [Fintype C] (σ : Equiv.Perm S) :
    (Finset.univ.filter fun f : S → C => σ • f = f).card = Fintype.card C ^ numCycles σ :=
  card_fixed_colorings σ

/-- CO-320. The number of nonequivalent `m`-colourings of `S` under a permutation group `G` is the
cycle index evaluated at `x_i = m` for all `i`. -/
@[kb "kellertrotter2017" "text (P_G(m,...,m)), p. 324"]
theorem text_p324_count_colorings {S : Type*} [Fintype S] {G : Type*} [Group G] [Fintype G]
    [MulAction G S] (m : ℕ) :
    (Fintype.card (MulAction.orbitRel.Quotient G (S → Fin m)) : ℚ) =
      (MvPolynomial.aeval fun _ : ℕ => (m : ℚ)) (cycleIndex G S) :=
  card_orbits_colorings_fin m

/-- CO-321. Pólya's enumeration theorem: substituting `x_k = c₁^k + ⋯ + c_m^k` into the cycle index
gives the generating function of nonequivalent colourings by colour content. -/
@[kb "kellertrotter2017" "Theorem 15.11, p. 326"]
theorem thm_15_11_polya {S C : Type*} [Fintype S] [Fintype C] {G : Type*} [Group G] [Fintype G]
    [MulAction G S] :
    ∑ ω : MulAction.orbitRel.Quotient G (S → C), ∏ s : S, MvPolynomial.X (Quotient.out ω s) =
      (MvPolynomial.aeval fun k : ℕ => ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k)
        (cycleIndex G S) :=
  polya_enumeration

/-- CO-322. The generating function of Pólya's theorem, the pattern inventory, is the cycle index
with `x_k` replaced by `c₁^k + ⋯ + c_m^k`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) pattern inventory, p. 327"]
theorem def_p327_pattern_inventory (G S C : Type*) [Fintype S] [Fintype C] [Group G] [Fintype G]
    [MulAction G S] :
    patternInventory G S C =
      (MvPolynomial.aeval fun k : ℕ => ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k)
        (cycleIndex G S) :=
  patternInventory_eq_cycleIndex G S C

/-- CO-323. The pair group `S_n^(2)` is the image of `S_n` acting on `2`-element subsets of `[n]`;
a permutation fixes a graph (as a colouring of the pairs) exactly when it maps edges to edges. -/
@[kb "kellertrotter2017" "Definition (unnumbered) pair group, p. 331"]
theorem def_p331_pair_group {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    σ • edgeColoring G = edgeColoring G ↔ ∀ u v : Fin n, G.Adj u v → G.Adj (σ u) (σ v) :=
  smul_edgeColoring_eq_self_iff σ G

/-- CO-324. The cycle index of the pair group of `S₄` is
`(x₁⁶ + 9 x₁² x₂² + 8 x₃² + 6 x₂ x₄) / 24`. -/
@[kb "kellertrotter2017" "text (cycle index of S_4^(2)), p. 331"]
theorem text_p331_pair_group_cycle_index_four :
    cycleIndex (pairGroup 4) (PairSet 4) =
      MvPolynomial.C (1 / 24 : ℚ) *
        (MvPolynomial.X 1 ^ 6 + 9 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 2 +
          8 * MvPolynomial.X 3 ^ 2 + 6 * MvPolynomial.X 2 * MvPolynomial.X 4) :=
  cycleIndex_pairGroup_four

/-- CO-325. Substituting `x_i := 1 + x^i` in the pair-group cycle index counts nonisomorphic graphs
on four vertices by number of edges: the polynomial is `1 + x + 2x² + 3x³ + 2x⁴ + x⁵ + x⁶`, and
there are `11` graphs in all. -/
@[kb "kellertrotter2017" "text (11 graphs on four vertices), p. 331"]
theorem text_p331_graphs_on_four_vertices :
    (∑ ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool),
        (Polynomial.X : Polynomial ℚ) ^ edgeCount ω.out =
      1 + Polynomial.X + 2 * Polynomial.X ^ 2 + 3 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4 +
        Polynomial.X ^ 5 + Polynomial.X ^ 6) ∧
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool)) = 11 ∧
    Nat.card (Quotient (isoSetoid 4)) = 11 ∧
    ∀ k : ℕ, (Finset.univ.filter fun ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4))
        (P4 → Bool) => edgeCount ω.out = k).card = [1, 1, 2, 3, 2, 1, 1].getD k 0 :=
  ⟨sum_orbits_X_pow_edgeCount, card_orbits_graphs_four, card_isoClasses_four,
    card_orbits_graphs_four_by_edges⟩

/-- CO-017. There are `2^{C(n,2)}` graphs on the vertex set `[n]`, and `C(C(n,2), k)` of them with
exactly `k` edges. -/
@[kb "kellertrotter2017" "text (number of graphs on [n]), p. 330"]
theorem text_p330_number_of_graphs (n k : ℕ) :
    Nat.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 ∧
      Nat.card { G : SimpleGraph (Fin n) // G.edgeSet.ncard = k } = (n.choose 2).choose k :=
  ⟨card_simpleGraph_fin n, card_simpleGraph_fin_edges n k⟩

end UndergradKB.Combinatorics.Course.KellerTrotter.Ch15b
