import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.Polya.PairGroup

/-!
# The pair group and counting graphs on four vertices (Keller--Trotter, Chapter 15.5.3)

The symmetric group `S_n` acts on the `2`-element subsets of `[n]`; its image in the permutations
of the pairs is the pair group `S_n^(2)`.  A graph on `[n]` is the same thing as a colouring of the
pairs by "edge / non-edge", and two graphs are isomorphic iff the colourings are in the same orbit.
We compute the cycle index of `S_4^(2)` (by evaluating the permutations of the pairs for all 24
permutations of `[4]` in the kernel) and deduce that there are `11` graphs on four vertices, with
`1, 1, 2, 3, 2, 1, 1` of them having `0, ..., 6` edges.
-/

namespace UndergradKB.Combinatorics.Polya

open Finset MulAction

section Periods

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
lemma isPeriodic_perm [Finite S] (σ : Equiv.Perm S) (s : S) :
    s ∈ Function.periodicPts (fun x => σ x) := by
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  show (fun x => σ x)^[orderOf σ] s = s
  rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
  rfl

omit [DecidableEq S] in
/-- Decidable form of `minimalPeriod σ s = k`. -/
lemma minimalPeriod_eq_iff_pow {σ : Equiv.Perm S} {s : S} {k : ℕ} :
    Function.minimalPeriod (fun x => σ x) s = k ↔
      (0 < k ∧ (σ ^ k) s = s ∧ ∀ j ∈ range k, 0 < j → (σ ^ j) s ≠ s) := by
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts (isPeriodic_perm σ s)
  have hper := Function.isPeriodicPt_minimalPeriod (fun x => σ x) s
  have hit : ∀ n, (fun x => σ x)^[n] s = (σ ^ n) s := fun n => by
    rw [Equiv.Perm.iterate_eq_pow]
  constructor
  · rintro rfl
    refine ⟨hpos, by simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using hper, ?_⟩
    intro j hj hj0 h
    have := Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod
      (f := fun x => σ x) (x := s) (n := j) (by omega) (mem_range.1 hj)
    exact this (by simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using h)
  · rintro ⟨hk, hk1, hk2⟩
    have hle : Function.minimalPeriod (fun x => σ x) s ≤ k :=
      Function.IsPeriodicPt.minimalPeriod_le hk
        (by simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using hk1)
    by_contra hne
    exact hk2 _ (mem_range.2 (lt_of_le_of_ne hle hne)) hpos
      (by simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using hper)

/-- The number of `k`-cycles of `σ`, computed (decidably) from the powers of `σ`: the points
of period exactly `k`, divided by `k`. -/
def perCount (σ : Equiv.Perm S) (k : ℕ) : ℕ :=
  (univ.filter fun s : S => 0 < k ∧ (σ ^ k) s = s ∧ ∀ j ∈ range k, 0 < j → (σ ^ j) s ≠ s).card / k

lemma numCyclesOfLength_eq_perCount (σ : Equiv.Perm S) (k : ℕ) :
    numCyclesOfLength σ k = perCount σ k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [numCyclesOfLength, perCount, Nat.div_zero]
    refine Multiset.count_eq_zero.2 fun h => ?_
    have := one_le_of_mem_cycleLengths σ (Multiset.mem_toFinset.2 h |> Multiset.mem_toFinset.1)
    omega
  · have h := numCyclesOfLength_mul σ k
    have : (univ.filter fun s : S => Function.minimalPeriod (fun x => σ x) s = k)
        = univ.filter fun s : S => 0 < k ∧ (σ ^ k) s = s ∧ ∀ j ∈ range k, 0 < j → (σ ^ j) s ≠ s := by
      ext s; simp [minimalPeriod_eq_iff_pow]
    rw [this] at h
    rw [perCount, ← h, Nat.mul_div_cancel _ hk]

lemma cycleMonomial_eq_perCount (σ : Equiv.Perm S) :
    cycleMonomial σ = ∏ k ∈ range (Fintype.card S + 1),
      (MvPolynomial.X k : MvPolynomial ℕ ℚ) ^ perCount σ k := by
  rw [cycleMonomial_eq_prod_range]
  exact prod_congr rfl fun k _ => by rw [numCyclesOfLength_eq_perCount]

end Periods

section PairGroup

/-- The set of the `2`-element subsets of `[n]` (the objects permuted by the pair group). -/
abbrev PairSet (n : ℕ) := Set.powersetCard (Fin n) 2

/-- A computable `Fintype` structure on the pairs (needed so that the kernel can evaluate the
action of the 24 permutations of `[4]`). -/
instance (n : ℕ) : Fintype (PairSet n) :=
  Fintype.subtype (Finset.powersetCard 2 (univ : Finset (Fin n))) (fun s => by
    simp [Set.powersetCard, Finset.mem_powersetCard])

/-- CO-323. The pair group `S_n^(2)`: the image of `S_n` in the permutations of the `2`-element
subsets of `[n]` (the permutation group of the pairs induced by the vertex permutations). -/
@[kb "kellertrotter2017" "Definition (unnumbered) pair group, p. 331"]
abbrev pairGroup (n : ℕ) : Subgroup (Equiv.Perm (PairSet n)) :=
  (MulAction.toPermHom (Equiv.Perm (Fin n)) (PairSet n)).range

noncomputable instance (n : ℕ) : Fintype (pairGroup n) := Fintype.ofFinite _

/-- The cycle index of the image of a group in its permutation action equals the cycle index of the
group when the action is faithful. -/
lemma cycleIndex_range {G S : Type*} [Group G] [Fintype G] [Fintype S] [MulAction G S]
    [Fintype (MulAction.toPermHom G S).range]
    (hinj : Function.Injective (MulAction.toPermHom G S)) :
    cycleIndex (MulAction.toPermHom G S).range S = cycleIndex G S := by
  let e := (MonoidHom.ofInjective hinj).toEquiv
  have hc : Fintype.card (MulAction.toPermHom G S).range = Fintype.card G :=
    (Fintype.card_congr e).symm
  unfold cycleIndex
  rw [hc]
  congr 1
  refine Fintype.sum_equiv e.symm _ _ fun h => ?_
  congr 1
  obtain ⟨g, hg⟩ := h.2
  have : h = e g := Subtype.ext hg.symm
  rw [this]
  simp [e]
  ext x
  rfl

/-- The pairs of `[4]`. -/
abbrev P4 := PairSet 4

/-- The numbers of cycles of length `0, ..., 6` of the permutation of the pairs of `[4]` induced
by a permutation of `[4]`. -/
def cycleVec (σ : Equiv.Perm (Fin 4)) : List ℕ :=
  (List.range 7).map (perCount (MulAction.toPerm σ : Equiv.Perm P4))

set_option maxRecDepth 100000 in
/-- The 24 permutations of `[4]` induce on the six pairs: the identity (1 permutation, six
fixed pairs), two 2-cycles and two fixed pairs (9 permutations: the transpositions and the
double transpositions), two 3-cycles (8), one 2-cycle and one 4-cycle (6). -/
lemma cycleVec_multiset :
    (univ : Finset (Equiv.Perm (Fin 4))).val.map cycleVec =
      Multiset.replicate 1 [0,6,0,0,0,0,0] + Multiset.replicate 9 [0,2,2,0,0,0,0]
        + Multiset.replicate 8 [0,0,0,2,0,0,0] + Multiset.replicate 6 [0,0,1,0,1,0,0] := by
  decide +kernel

lemma card_P4 : Fintype.card P4 = 6 := by decide +kernel

/-- Monomial attached to a vector of cycle counts. -/
noncomputable def monOfVec (l : List ℕ) : MvPolynomial ℕ ℚ :=
  ∏ k ∈ range 7, (MvPolynomial.X k : MvPolynomial ℕ ℚ) ^ l.getD k 0

lemma cycleMonomial_eq_monOfVec (σ : Equiv.Perm (Fin 4)) :
    cycleMonomial (MulAction.toPerm σ : Equiv.Perm P4) = monOfVec (cycleVec σ) := by
  rw [cycleMonomial_eq_perCount, card_P4, monOfVec]
  refine prod_congr rfl fun k hk => ?_
  have hk' : k < 7 := by simpa using hk
  simp [cycleVec, hk']

/-- The cycle index of `S_4` acting on the six pairs. -/
theorem cycleIndex_perm_four :
    cycleIndex (Equiv.Perm (Fin 4)) P4 =
      MvPolynomial.C (1 / 24 : ℚ) * (MvPolynomial.X 1 ^ 6
        + 9 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 2
        + 8 * MvPolynomial.X 3 ^ 2 + 6 * MvPolynomial.X 2 * MvPolynomial.X 4) := by
  unfold cycleIndex
  have hcard : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    simp [Fintype.card_perm, Nat.factorial]
  rw [hcard, Nat.cast_ofNat]
  congr 1
  simp_rw [cycleMonomial_eq_monOfVec]
  rw [Finset.sum_eq_multiset_sum]
  have : (fun σ => monOfVec (cycleVec σ)) = monOfVec ∘ cycleVec := rfl
  rw [this, ← Multiset.map_map, cycleVec_multiset]
  simp [monOfVec, prod_range_succ]
  ring

/-- CO-324. The cycle index of the pair group `S_4^(2)` is
`(x₁⁶ + 9 x₁² x₂² + 8 x₃² + 6 x₂ x₄) / 24`. -/
@[kb "kellertrotter2017" "text (cycle index of the pair group of S_4), p. 331"]
theorem cycleIndex_pairGroup_four :
    cycleIndex (pairGroup 4) (PairSet 4) =
      MvPolynomial.C (1 / 24 : ℚ) * (MvPolynomial.X 1 ^ 6
        + 9 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ 2
        + 8 * MvPolynomial.X 3 ^ 2 + 6 * MvPolynomial.X 2 * MvPolynomial.X 4) := by
  have hfaith : FaithfulSMul (Equiv.Perm (Fin 4)) (PairSet 4) :=
    Set.powersetCard.faithfulSMul (G := Equiv.Perm (Fin 4)) (α := Fin 4) (n := 2)
      (by norm_num) (by simp; norm_num)
  have hinj : Function.Injective (MulAction.toPermHom (Equiv.Perm (Fin 4)) (PairSet 4)) :=
    MulAction.toPerm_injective
  rw [← cycleIndex_perm_four]
  exact cycleIndex_range hinj

end PairGroup

section Graphs

attribute [local instance] arrowAction

variable {n : ℕ}

/-- The pair `{u, v}` of two distinct vertices. -/
def pairOf (u v : Fin n) (h : u ≠ v) : PairSet n :=
  ⟨{u, v}, Set.powersetCard.mem_iff.2 (Finset.card_pair h)⟩

lemma pairOf_comm (u v : Fin n) (h : u ≠ v) : pairOf v u h.symm = pairOf u v h :=
  Subtype.ext (Finset.pair_comm v u)

lemma smul_pairOf (σ : Equiv.Perm (Fin n)) (u v : Fin n) (h : u ≠ v) :
    σ • pairOf u v h = pairOf (σ u) (σ v) (σ.injective.ne h) := by
  apply Subtype.ext
  rw [Set.powersetCard.coe_smul]
  simp [pairOf, Finset.smul_finset_def]

lemma exists_pairOf (s : PairSet n) : ∃ (u v : Fin n) (h : u ≠ v), s = pairOf u v h := by
  obtain ⟨u, v, huv, hs⟩ := Finset.card_eq_two.1 s.2
  exact ⟨u, v, huv, Subtype.ext hs⟩

open Classical in
/-- The colouring of the pairs of `[n]` by "edge / non-edge" determined by a graph. -/
noncomputable def edgeColoring (G : SimpleGraph (Fin n)) : PairSet n → Bool :=
  fun s => decide (∃ u v : Fin n, G.Adj u v ∧ (s : Finset (Fin n)) = {u, v})

open Classical in
lemma edgeColoring_eq_true_iff (G : SimpleGraph (Fin n)) (s : PairSet n) :
    edgeColoring G s = true ↔ ∃ u v : Fin n, G.Adj u v ∧ (s : Finset (Fin n)) = {u, v} :=
  decide_eq_true_iff

lemma edgeColoring_pairOf (G : SimpleGraph (Fin n)) (u v : Fin n) (h : u ≠ v) :
    edgeColoring G (pairOf u v h) = true ↔ G.Adj u v := by
  rw [edgeColoring_eq_true_iff]
  constructor
  · rintro ⟨a, b, hab, he⟩
    have he' : ({u, v} : Finset (Fin n)) = {a, b} := he
    have hu : u ∈ ({a, b} : Finset (Fin n)) := he' ▸ Finset.mem_insert_self u _
    have hv : v ∈ ({a, b} : Finset (Fin n)) := he' ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl h
    · exact hab
    · exact hab.symm
    · exact absurd rfl h
  · exact fun hadj => ⟨u, v, hadj, rfl⟩

lemma smul_apply_pairOf (σ : Equiv.Perm (Fin n)) (c : PairSet n → Bool) (u v : Fin n)
    (h : u ≠ v) :
    (σ • c) (pairOf u v h) = c (pairOf (σ⁻¹ u) (σ⁻¹ v) (σ⁻¹.injective.ne h)) := by
  show c (σ⁻¹ • pairOf u v h) = _
  rw [smul_pairOf]

/-- Two graphs have colourings in the relation `σ • c(G) = c(G')` iff `σ` is an isomorphism
`G ≃ G'`, i.e. `uv` is an edge of `G` iff `σu σv` is an edge of `G'`. -/
lemma smul_edgeColoring_eq_iff (σ : Equiv.Perm (Fin n)) (G G' : SimpleGraph (Fin n)) :
    σ • edgeColoring G = edgeColoring G' ↔ ∀ u v, G.Adj u v ↔ G'.Adj (σ u) (σ v) := by
  constructor
  · intro H u v
    by_cases huv : u = v
    · subst huv; simp
    · have := congrFun H (pairOf (σ u) (σ v) (σ.injective.ne huv))
      rw [smul_apply_pairOf] at this
      simp at this
      have e1 := edgeColoring_pairOf G u v huv
      have e2 := edgeColoring_pairOf G' (σ u) (σ v) (σ.injective.ne huv)
      rw [← e1, ← e2, this]
  · intro H
    funext s
    obtain ⟨a, b, hab, rfl⟩ := exists_pairOf s
    rw [smul_apply_pairOf]
    have e1 := edgeColoring_pairOf G (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹.injective.ne hab)
    have e2 := edgeColoring_pairOf G' a b hab
    have := H (σ⁻¹ a) (σ⁻¹ b)
    simp at this
    rw [Bool.eq_iff_iff, e1, e2]
    exact this

lemma adj_of_map_adj (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    (h : ∀ u v, G.Adj u v → G.Adj (σ u) (σ v)) (u v : Fin n) (hadj : G.Adj (σ u) (σ v)) :
    G.Adj u v := by
  classical
  let A : Finset (Fin n × Fin n) := univ.filter fun p => G.Adj p.1 p.2
  let φ : Fin n × Fin n → Fin n × Fin n := fun p => (σ p.1, σ p.2)
  have hφ : Function.Injective φ := by
    intro p q hpq
    simp only [φ, Prod.mk.injEq] at hpq
    exact Prod.ext (σ.injective hpq.1) (σ.injective hpq.2)
  have hsub : A.image φ ⊆ A := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    simp only [A, φ, mem_filter, mem_univ, true_and] at hp ⊢
    exact h _ _ hp
  have heq : A.image φ = A :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_image_of_injective _ hφ])
  have hmem : (σ u, σ v) ∈ A := by simp [A, hadj]
  rw [← heq] at hmem
  obtain ⟨p, hp, hpe⟩ := mem_image.1 hmem
  have := hφ (show φ p = φ (u, v) from hpe)
  subst this
  simpa [A] using hp

/-- CO-323. A permutation of the vertices fixes the graph `G` (that is, fixes its colouring of the
pairs) exactly when it sends edges to edges; for finite graphs this is the same as sending edges
to edges and non-edges to non-edges. -/
@[kb "kellertrotter2017" "text (a permutation fixes a graph iff it maps edges to edges), p. 331"]
theorem smul_edgeColoring_eq_self_iff (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    σ • edgeColoring G = edgeColoring G ↔ ∀ u v, G.Adj u v → G.Adj (σ u) (σ v) := by
  rw [smul_edgeColoring_eq_iff]
  exact ⟨fun H u v => (H u v).1, fun H u v =>
    ⟨H u v, adj_of_map_adj G σ H u v⟩⟩

/-- The graph on `[n]` whose edges are the pairs coloured `true`. -/
def colorGraph (c : PairSet n → Bool) : SimpleGraph (Fin n) where
  Adj u v := ∃ h : u ≠ v, c (pairOf u v h) = true
  symm := ⟨fun u v ⟨h, hc⟩ => ⟨h.symm, by rwa [pairOf_comm]⟩⟩
  loopless := ⟨fun u ⟨h, _⟩ => h rfl⟩

/-- CO-323. Graphs on `[n]` are the same as colourings of the pairs of `[n]` by two colours. -/
@[kb "kellertrotter2017" "text (graphs as colourings of the pairs), p. 331"]
noncomputable def graphEquivColoring (n : ℕ) : SimpleGraph (Fin n) ≃ (PairSet n → Bool) where
  toFun := edgeColoring
  invFun := colorGraph
  left_inv G := by
    ext u v
    constructor
    · rintro ⟨h, hc⟩
      exact (edgeColoring_pairOf G u v h).1 hc
    · intro hadj
      exact ⟨hadj.ne, (edgeColoring_pairOf G u v hadj.ne).2 hadj⟩
  right_inv c := by
    funext s
    obtain ⟨u, v, h, rfl⟩ := exists_pairOf s
    rw [← Bool.coe_iff_coe, edgeColoring_pairOf]
    exact ⟨fun ⟨_, hc⟩ => by simpa using hc, fun hc => ⟨h, by simpa using hc⟩⟩

/-- Isomorphism of graphs on `[n]`, as a setoid. -/
def isoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G G' := Nonempty (G ≃g G')
  iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Two graphs on `[n]` are isomorphic iff their colourings of the pairs lie in the same orbit
of `S_n`. -/
lemma nonempty_iso_iff_mem_orbit (G G' : SimpleGraph (Fin n)) :
    Nonempty (G ≃g G') ↔
      edgeColoring G' ∈ MulAction.orbit (Equiv.Perm (Fin n)) (edgeColoring G) := by
  rw [MulAction.mem_orbit_iff]
  simp_rw [smul_edgeColoring_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, fun u v => e.map_rel_iff.symm⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, fun {u v} => (hσ u v).symm⟩⟩

/-- Isomorphism classes of graphs on `[n]` correspond to orbits of `S_n` on the colourings of
the pairs. -/
noncomputable def isoClassesEquivOrbits (n : ℕ) :
    Quotient (isoSetoid n) ≃ MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (PairSet n → Bool) :=
  Quotient.congr (graphEquivColoring n) fun G G' => by
    rw [MulAction.orbitRel_apply]
    show Nonempty (G ≃g G') ↔ edgeColoring G ∈ MulAction.orbit _ (edgeColoring G')
    rw [← nonempty_iso_iff_mem_orbit]
    exact ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

end Graphs

section Count

attribute [local instance] arrowAction

open scoped Classical

/-- The number of edges of a graph given as a colouring of the pairs. -/
def edgeCount (c : P4 → Bool) : ℕ := (univ.filter fun s => c s = true).card

/-- CO-325. The generating function of the orbits of `S_4` on graphs by number of edges is the
cycle index of the pair group with `x_i := 1 + x ^ i` substituted: it equals
`1 + x + 2x² + 3x³ + 2x⁴ + x⁵ + x⁶`. -/
@[kb "kellertrotter2017" "text (substitution x_i := 1 + x^i), p. 332"]
theorem sum_orbits_X_pow_edgeCount :
    ∑ ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool),
        (Polynomial.X : Polynomial ℚ) ^ edgeCount ω.out
      = 1 + Polynomial.X + 2 * Polynomial.X ^ 2 + 3 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4
        + Polynomial.X ^ 5 + Polynomial.X ^ 6 := by
  have h := polya_weighted (G := Equiv.Perm (Fin 4)) (S := P4) (C := Bool) (R := Polynomial ℚ)
    (fun b => if b then Polynomial.X else 1)
  have hw : ∀ f : P4 → Bool, ∏ s, (fun b : Bool => if b then (Polynomial.X : Polynomial ℚ) else 1) (f s)
      = Polynomial.X ^ edgeCount f := by
    intro f
    simp [edgeCount, Finset.prod_ite]
  simp_rw [hw] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr!
  rw [cycleIndex_perm_four]
  simp only [map_mul, map_add, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Fintype.sum_bool, ite_true, map_ofNat]
  simp only [Bool.false_eq_true, ite_false, one_pow, pow_one]
  have h24 : algebraMap ℚ (Polynomial ℚ) (1 / 24) * 24 = 1 := by
    rw [← map_ofNat (algebraMap ℚ (Polynomial ℚ)) 24, ← map_mul]; norm_num
  linear_combination (1 + Polynomial.X + 2 * Polynomial.X ^ 2 + 3 * Polynomial.X ^ 3
    + 2 * Polynomial.X ^ 4 + Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℚ) * h24

/-- CO-325. There are `11` graphs on four vertices up to isomorphism: the number of orbits of `S_4`
on the colourings of the six pairs by two colours. -/
@[kb "kellertrotter2017" "text (11 nonisomorphic graphs on four vertices), p. 332"]
theorem card_orbits_graphs_four :
    Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool)) = 11 := by
  have h := card_orbits_colorings (G := Equiv.Perm (Fin 4)) (S := P4) (C := Bool)
  have hr : MvPolynomial.aeval (fun _ => (Fintype.card Bool : ℚ)) (cycleIndex (Equiv.Perm (Fin 4)) P4)
      = 11 := by
    rw [cycleIndex_perm_four]
    simp only [map_mul, map_add, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_ofNat,
      Fintype.card_bool, Algebra.algebraMap_self, RingHom.id_apply]
    norm_num
  rw [hr] at h
  rw [Fintype.card_eq_nat_card] at h
  exact_mod_cast h

/-- CO-325, for isomorphism classes of graphs on the vertex set `[4]`: there are `11`. -/
@[kb "kellertrotter2017" "text (11 nonisomorphic graphs on four vertices), p. 332"]
theorem card_isoClasses_four : Nat.card (Quotient (isoSetoid 4)) = 11 := by
  rw [Nat.card_congr (isoClassesEquivOrbits 4)]
  exact card_orbits_graphs_four

/-- CO-325. The numbers of orbits of `S_4` on graphs, by number of edges, are the coefficients
of the polynomial obtained from the cycle index by `x_i := 1 + x^i`: `1, 1, 2, 3, 2, 1, 1`
for `0, ..., 6` edges (and none for more edges). -/
@[kb "kellertrotter2017" "text (graphs on four vertices by number of edges), p. 332"]
theorem card_orbits_graphs_four_by_edges (k : ℕ) :
    (univ.filter fun ω : MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool) =>
        edgeCount ω.out = k).card = [1, 1, 2, 3, 2, 1, 1].getD k 0 := by
  apply Nat.cast_injective (R := ℚ)
  have key : (((univ.filter fun ω :
        MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool) => edgeCount ω.out = k).card
          : ℕ) : ℚ)
      = (1 + Polynomial.X + 2 * Polynomial.X ^ 2 + 3 * Polynomial.X ^ 3 + 2 * Polynomial.X ^ 4
        + Polynomial.X ^ 5 + Polynomial.X ^ 6 : Polynomial ℚ).coeff k := by
    rw [← sum_orbits_X_pow_edgeCount]
    have hsum := map_sum (Polynomial.lcoeff ℚ k) (fun ω :
      MulAction.orbitRel.Quotient (Equiv.Perm (Fin 4)) (P4 → Bool) =>
        (Polynomial.X : Polynomial ℚ) ^ edgeCount ω.out) univ
    simp only [Polynomial.lcoeff_apply] at hsum
    rw [hsum]
    simp only [Polynomial.coeff_X_pow, Finset.sum_boole]
    exact congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun _ _ => eq_comm))
  rw [key]
  rcases lt_or_ge k 7 with hk | hk
  · interval_cases k <;> simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hn : ([1, 1, 2, 3, 2, 1, 1] : List ℕ)[k]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [List.getD_eq_getElem?_getD, hn]
    have h1 : k ≠ 1 := by omega
    have h2 : k ≠ 2 := by omega
    have h3 : k ≠ 3 := by omega
    have h4 : k ≠ 4 := by omega
    have h5 : k ≠ 5 := by omega
    have h6 : k ≠ 6 := by omega
    have h0 : k ≠ 0 := by omega
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, h0, h2, h3, h4, h5, h6, h1.symm]

end Count

section CycleType

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma card_support_cycleOf_eq_minimalPeriod (σ : Equiv.Perm S) {x : S} (hx : σ x ≠ x) :
    (σ.cycleOf x).support.card = Function.minimalPeriod (fun y => σ y) x := by
  have hc : (σ.cycleOf x).IsCycle := Equiv.Perm.isCycle_cycleOf σ hx
  have hcx : σ.cycleOf x x ≠ x := by rwa [Equiv.Perm.cycleOf_apply_self]
  have hit : ∀ n, (fun y => σ y)^[n] x = (σ ^ n) x := fun n => by
    rw [Equiv.Perm.iterate_eq_pow]
  apply Nat.dvd_antisymm
  · rw [← hc.orderOf]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hc.pow_eq_one_iff' hcx, Equiv.Perm.cycleOf_pow_apply_self]
    have := Function.isPeriodicPt_minimalPeriod (fun y => σ y) x
    simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using this
  · refine Function.IsPeriodicPt.minimalPeriod_dvd ?_
    have h1 : (σ.cycleOf x ^ (σ.cycleOf x).support.card) = 1 := by
      rw [← hc.orderOf]; exact pow_orderOf_eq_one _
    have h2 := congrArg (fun g => g x) h1
    simp only [Equiv.Perm.cycleOf_pow_apply_self, Equiv.Perm.coe_one, id_eq] at h2
    simpa [Function.IsPeriodicPt, Function.IsFixedPt, hit] using h2

lemma card_period_eq_mul_count (σ : Equiv.Perm S) {i : ℕ} (hi : 2 ≤ i) :
    (univ.filter fun x : S => Function.minimalPeriod (fun y => σ y) x = i).card
      = i * σ.cycleType.count i := by
  let T : Finset (Equiv.Perm S) :=
    σ.cycleFactorsFinset.filter fun c => c.support.card = i
  have hmoved : ∀ x : S, Function.minimalPeriod (fun y => σ y) x = i → σ x ≠ x := by
    intro x hxi hfix
    have : Function.minimalPeriod (fun y => σ y) x = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.2 hfix
    omega
  have hfib : ∀ c ∈ T,
      (univ.filter fun x : S => Function.minimalPeriod (fun y => σ y) x = i ∧
        σ.cycleOf x = c).card = i := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have : (univ.filter fun x : S => Function.minimalPeriod (fun y => σ y) x = i ∧
        σ.cycleOf x = c) = c.support := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hp, rfl⟩
        exact Equiv.Perm.mem_support.2 (by rw [Equiv.Perm.cycleOf_apply_self]; exact hmoved x hp)
      · intro hx
        have hcx : c = σ.cycleOf x := Equiv.Perm.cycle_is_cycleOf hx hc.1
        have hxσ : σ x ≠ x := Equiv.Perm.mem_support.1
          (Equiv.Perm.mem_cycleFactorsFinset_support_le hc.1 hx)
        refine ⟨?_, hcx.symm⟩
        rw [← card_support_cycleOf_eq_minimalPeriod σ hxσ, ← hcx]
        exact hc.2
    rw [this]
    exact hc.2
  have hcount : σ.cycleType.count i = T.card := by
    rw [Equiv.Perm.CycleType.count_def, Fintype.card_subtype]
    refine Finset.card_bij (fun c _ => (c : Equiv.Perm S)) ?_ ?_ ?_
    · intro c hc
      simp only [T, mem_filter, mem_univ, true_and] at hc ⊢
      exact ⟨c.2, hc⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro c hc
      simp only [T, mem_filter] at hc
      exact ⟨⟨c, hc.1⟩, by simp [hc.2], rfl⟩
  rw [hcount, Finset.card_eq_sum_card_fiberwise (f := fun x => σ.cycleOf x) (t := T)]
  · rw [Finset.sum_congr rfl (g := fun _ => i), sum_const, smul_eq_mul, mul_comm]
    intro c hc
    rw [Finset.filter_filter]
    exact hfib c hc
  · intro x hx
    have hx := mem_filter.1 (Finset.mem_coe.1 hx)
    have hxσ := hmoved x hx.2
    simp only [T, mem_filter, Finset.mem_coe]
    refine ⟨Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 hxσ), ?_⟩
    rw [card_support_cycleOf_eq_minimalPeriod σ hxσ]
    exact hx.2

/-- CO-314. For `i ≥ 2`, the number of `i`-cycles of a permutation (counted via the orbits of the
cyclic group, as in `numCyclesOfLength`) is the multiplicity of `i` in Mathlib's `cycleType`. -/
@[kb "kellertrotter2017" "text (cycle notation), p. 319"]
theorem numCyclesOfLength_eq_count_cycleType (σ : Equiv.Perm S) {i : ℕ} (hi : 2 ≤ i) :
    numCyclesOfLength σ i = σ.cycleType.count i := by
  have h := numCyclesOfLength_mul σ i
  have h' := card_period_eq_mul_count σ hi
  have h'' : numCyclesOfLength σ i * i = i * σ.cycleType.count i := by
    rw [h, ← h']
  exact Nat.eq_of_mul_eq_mul_right (by omega) (h''.trans (mul_comm _ _))

/-- CO-314. The number of `1`-cycles of a permutation is its number of fixed points (which
Mathlib's `cycleType` omits). -/
@[kb "kellertrotter2017" "text (cycle notation), p. 319"]
theorem numCyclesOfLength_one (σ : Equiv.Perm S) :
    numCyclesOfLength σ 1 = (univ.filter fun x : S => σ x = x).card := by
  have h := numCyclesOfLength_mul σ 1
  rw [mul_one] at h
  rw [h]
  congr 1
  ext x
  simp [Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt]

/-- CO-314. The cycle lengths of the book (all cycles, including the fixed points) are Mathlib's
`cycleType` (which lists only the cycles of length at least `2`) together with one `1` for every
fixed point. -/
@[kb "kellertrotter2017" "text (cycle notation), p. 319"]
theorem cycleLengths_eq_cycleType_add (σ : Equiv.Perm S) :
    cycleLengths σ = σ.cycleType + Multiset.replicate (univ.filter fun x : S => σ x = x).card 1 := by
  ext n
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · have h0 : numCyclesOfLength σ 0 = 0 := by
        rw [numCyclesOfLength_eq_perCount]; simp [perCount]
      have h1 : σ.cycleType.count 0 = 0 :=
        Multiset.count_eq_zero.2 fun h => by have := Equiv.Perm.two_le_of_mem_cycleType h; omega
      have h2 : (cycleLengths σ).count 0 = 0 := h0
      rw [Multiset.count_add, h1, h2, Multiset.count_replicate]
      simp
    · rw [Multiset.count_add]
      have h1 : σ.cycleType.count 1 = 0 :=
        Multiset.count_eq_zero.2 fun h => by have := Equiv.Perm.two_le_of_mem_cycleType h; omega
      have := numCyclesOfLength_one σ
      rw [h1]
      simpa [Multiset.count_replicate, numCyclesOfLength] using this
  · rw [Multiset.count_add]
    have := numCyclesOfLength_eq_count_cycleType σ hn
    simp only [numCyclesOfLength] at this
    rw [this, Multiset.count_replicate]
    simp; omega

end CycleType

end UndergradKB.Combinatorics.Polya
