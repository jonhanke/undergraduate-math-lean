import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Card
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-!
# Graph coloring (Keller–Trotter, Section 5.4)

* CO-105: a graph is 2-colorable iff it has no odd cycle;
* CO-268: the First Fit (greedy) coloring along a linear order of the vertices;
* CO-126: `χ(G) ≤ D + 1` when all degrees are at most `D`;
* CO-110, CO-111: interval graphs, and `χ = ω` for them.
-/

namespace UndergradKB.Combinatorics

open SimpleGraph

/-! ### Two-colorable graphs -/

section Bipartite

variable {V : Type*}

/-- Every walk can be replaced by a path of the same parity, unless the graph has an odd cycle. -/
lemma exists_path_or_odd_cycle {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (∃ q : G.Walk u v, q.IsPath ∧ q.length ≤ p.length ∧ (Even q.length ↔ Even p.length)) ∨
      ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  classical
  induction p with
  | nil => exact Or.inl ⟨.nil, .nil, le_rfl, Iff.rfl⟩
  | @cons u w v h p' ih =>
    rcases ih with ⟨q', hq', hlen, hpar⟩ | hcyc
    · by_cases hu : u ∈ q'.support
      · have hspec := q'.take_spec hu
        have hlen' : (q'.takeUntil u hu).length + (q'.dropUntil u hu).length = q'.length := by
          rw [← Walk.length_append, hspec]
        by_cases hev : Even (q'.takeUntil u hu).length
        · right
          refine ⟨u, .cons h (q'.takeUntil u hu), ?_, ?_⟩
          · rw [Walk.cons_isCycle_iff]
            refine ⟨hq'.takeUntil hu, fun he => ?_⟩
            have h1 := (hq'.takeUntil hu).length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
            rw [h1] at hev
            exact absurd hev (by decide)
          · simpa [Nat.odd_add_one] using hev
        · left
          refine ⟨q'.dropUntil u hu, hq'.dropUntil hu, ?_, ?_⟩
          · simp only [Walk.length_cons]; omega
          · simp only [Walk.length_cons, Nat.even_iff] at hev hpar ⊢
            omega
      · left
        refine ⟨.cons h q', hq'.cons hu, ?_, ?_⟩
        · simp only [Walk.length_cons]; omega
        · simp only [Walk.length_cons, Nat.even_add_one]
          exact not_congr hpar
    · exact Or.inr hcyc

/-- A graph with no odd cycle has only even closed walks. -/
lemma even_length_of_no_odd_cycle {G : SimpleGraph V}
    (h : ∀ (x : V) (c : G.Walk x x), c.IsCycle → ¬ Odd c.length) {u : V} (w : G.Walk u u) :
    Even w.length := by
  rcases exists_path_or_odd_cycle w with ⟨q, hq, -, hpar⟩ | ⟨x, c, hc, ho⟩
  · have hnil : q.Nil := hq.nil_iff_eq.mpr rfl
    have h0 : q.length = 0 := Walk.length_eq_zero_iff.mpr hnil
    exact hpar.mp (by rw [h0]; simp)
  · exact absurd ho (h x c hc)

/-- CO-105. Theorem 5.21: a graph is 2-colorable if and only if it contains no odd cycle
(a cycle being a closed walk with `Walk.IsCycle`, of odd length). -/
@[kb "kellertrotter2017" "Theorem 5.21, p. 106"]
theorem colorable_two_iff_no_odd_cycle (G : SimpleGraph V) :
    G.Colorable 2 ↔ ∀ (x : V) (c : G.Walk x x), c.IsCycle → ¬ Odd c.length := by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · intro h x c _ ho
    exact (Nat.not_even_iff_odd.mpr ho) (h x c)
  · intro h u w
    exact even_length_of_no_odd_cycle h w

end Bipartite

/-! ### First Fit -/

section FirstFit

variable {V : Type*} (G : SimpleGraph V) [LinearOrder V] [WellFoundedLT V]

/-- CO-268. First Fit (greedy) coloring along the linear order of `V`: each vertex receives the
least natural number not used on any earlier neighbour. -/
@[kb "kellertrotter2017" "text, p. 110"]
noncomputable def firstFit : V → ℕ :=
  WellFounded.fix (wellFounded_lt (α := V))
    fun v ih => sInf {c : ℕ | ∀ u (h : u < v), G.Adj u v → ih u h ≠ c}

lemma firstFit_eq (v : V) :
    firstFit G v = sInf {c : ℕ | ∀ u, u < v → G.Adj u v → firstFit G u ≠ c} := by
  unfold firstFit
  rw [WellFounded.fix_eq]

variable [Finite V]

lemma firstFit_mem (v : V) :
    firstFit G v ∈ {c : ℕ | ∀ u, u < v → G.Adj u v → firstFit G u ≠ c} := by
  rw [firstFit_eq]
  apply Nat.sInf_mem
  obtain ⟨c, hc⟩ := (Set.finite_range (firstFit G)).infinite_compl.nonempty
  exact ⟨c, fun u _ _ h => hc ⟨u, h⟩⟩

lemma firstFit_ne {u v : V} (huv : u < v) (h : G.Adj u v) : firstFit G u ≠ firstFit G v :=
  firstFit_mem G v u huv h

/-- CO-268. The First Fit coloring is a proper coloring. -/
@[kb "kellertrotter2017" "text, p. 110"]
noncomputable def firstFitColoring : G.Coloring ℕ :=
  Coloring.mk (firstFit G) fun {u v} h => by
    rcases lt_trichotomy u v with huv | rfl | hvu
    · exact firstFit_ne G huv h
    · exact absurd h (G.loopless.irrefl _)
    · exact (firstFit_ne G hvu h.symm).symm

/-- The First Fit color of `v` is at most the number of earlier neighbours of `v`. -/
lemma firstFit_le_ncard (v : V) : firstFit G v ≤ {u | u < v ∧ G.Adj u v}.ncard := by
  by_contra hlt
  rw [not_le] at hlt
  set S : Set V := {u | u < v ∧ G.Adj u v} with hS
  have hSfin : S.Finite := Set.toFinite _
  have hsub : ((Finset.range (S.ncard + 1) : Finset ℕ) : Set ℕ) ⊆ firstFit G '' S := by
    intro c hc
    simp only [Finset.coe_range, Set.mem_Iio] at hc
    by_contra hne
    have hmem : c ∈ {c : ℕ | ∀ u, u < v → G.Adj u v → firstFit G u ≠ c} :=
      fun u hu hadj he => hne ⟨u, ⟨hu, hadj⟩, he⟩
    have := Nat.sInf_le hmem
    rw [← firstFit_eq] at this
    omega
  have h1 := Set.ncard_le_ncard hsub (hSfin.image _)
  have h2 := Set.ncard_image_le (f := firstFit G) hSfin
  rw [Set.ncard_coe_finset, Finset.card_range] at h1
  omega

end FirstFit

/-- CO-126 (Exercise 5.9.27). If every vertex has degree at most `D`, then `G` is
`(D+1)`-colorable, via First Fit. -/
@[kb "kellertrotter2017" "Exercise 5.9.27, p. 131"]
theorem colorable_of_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (h : ∀ v, G.degree v ≤ D) : G.Colorable (D + 1) := by
  let _ : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  refine ⟨Coloring.mk (fun v => ⟨firstFit G v, ?_⟩) fun {u v} hadj he => ?_⟩
  · have h1 := firstFit_le_ncard G v
    have h2 : {u | u < v ∧ G.Adj u v}.ncard ≤ G.degree v := by
      calc {u | u < v ∧ G.Adj u v}.ncard ≤ ((G.neighborFinset v : Finset V) : Set V).ncard :=
            Set.ncard_le_ncard (fun u hu => by simpa using hu.2.symm) (Set.toFinite _)
        _ = G.degree v := by rw [Set.ncard_coe_finset, card_neighborFinset_eq_degree]
    have := h v
    omega
  · exact (firstFitColoring G).valid hadj (Fin.mk.inj_iff.mp he)

/-- CO-126 in the form `χ(G) ≤ Δ(G) + 1`. -/
theorem chromaticNumber_le_maxDegree_add_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.chromaticNumber ≤ G.maxDegree + 1 :=
  (colorable_of_degree_le G _ fun v => G.degree_le_maxDegree v).chromaticNumber_le

/-- CO-126, `χ(G) ≤ D + 1` form. -/
theorem chromaticNumber_le_of_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (h : ∀ v, G.degree v ≤ D) : G.chromaticNumber ≤ D + 1 :=
  (colorable_of_degree_le G D h).chromaticNumber_le

/-! ### Interval graphs -/

section Interval

/-- CO-110. The intersection graph of an indexed family of sets: distinct indices are adjacent
iff their sets meet. -/
@[kb "kellertrotter2017" "Definition (unnumbered) intersection graph, p. 111"]
def intersectionGraph {ι α : Type*} (S : ι → Set α) : SimpleGraph ι where
  Adj x y := x ≠ y ∧ (S x ∩ S y).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Set.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- CO-110. An interval graph: the intersection graph of a family of closed real intervals
`[a v, b v]` (with `a v ≤ b v`). -/
@[kb "kellertrotter2017" "Definition (unnumbered) interval graph, p. 111"]
def IsIntervalGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b : V → ℝ, (∀ v, a v ≤ b v) ∧ G = intersectionGraph fun v => Set.Icc (a v) (b v)

/-- CO-111. Theorem 5.28: for an interval graph (on finitely many vertices), `χ(G) = ω(G)`. -/
@[kb "kellertrotter2017" "Theorem 5.28, p. 111"]
theorem IsIntervalGraph.chromaticNumber_eq_cliqueNum {V : Type*} [Finite V] {G : SimpleGraph V}
    (hG : IsIntervalGraph G) : G.chromaticNumber = G.cliqueNum := by
  classical
  refine le_antisymm ?_ G.cliqueNum_le_chromaticNumber
  obtain ⟨a, b, hab, hGeq⟩ := hG
  have hadj : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (Set.Icc (a u) (b u) ∩ Set.Icc (a v) (b v)).Nonempty := by
    intro u v
    rw [hGeq]
    rfl
  have := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let key : V → ℝ ×ₗ Fin (Fintype.card V) := fun v => toLex (a v, e v)
  have hkey : Function.Injective key := fun x y h => by
    have h2 : (a x, e x) = (a y, e y) := h
    exact e.injective (Prod.mk.inj h2).2
  let _ : LinearOrder V := LinearOrder.lift' key hkey
  have hlt : ∀ {u v : V}, u < v → a u ≤ a v := by
    intro u v h
    have h' : key u < key v := h
    rcases Prod.Lex.toLex_lt_toLex.mp h' with h1 | ⟨h1, _⟩
    · exact h1.le
    · exact h1.le
  have hWF : WellFoundedLT V := inferInstance
  -- the earlier neighbours of `v`, together with `v`, form a clique
  have hclique : ∀ v : V, ({u | u < v ∧ G.Adj u v}.ncard + 1) ≤ G.cliqueNum := by
    intro v
    have hfin : {u | u < v ∧ G.Adj u v}.Finite := Set.toFinite _
    let T : Finset V := insert v hfin.toFinset
    have hvT : v ∉ hfin.toFinset := by simp
    have hcard : T.card = {u | u < v ∧ G.Adj u v}.ncard + 1 := by
      rw [Finset.card_insert_of_notMem hvT, Set.ncard_eq_toFinset_card _ hfin]
    -- the left endpoint of `v` lies in the interval of each earlier neighbour
    have hmem : ∀ u, u < v → G.Adj u v → a v ∈ Set.Icc (a u) (b u) := by
      intro u huv hadjuv
      obtain ⟨-, z, ⟨hz1, hz2⟩, ⟨hz3, -⟩⟩ := (hadj u v).mp hadjuv
      exact ⟨hlt huv, hz3.trans hz2⟩
    have hT : G.IsClique (T : Set V) := by
      intro x hx y hy hxy
      have hx' : x = v ∨ x ∈ hfin.toFinset := by simpa [T] using hx
      have hy' : y = v ∨ y ∈ hfin.toFinset := by simpa [T] using hy
      rw [hfin.mem_toFinset] at hx' hy'
      rw [hadj]
      refine ⟨hxy, a v, ?_, ?_⟩
      · rcases hx' with rfl | ⟨hx1, hx2⟩
        · exact ⟨le_rfl, hab _⟩
        · exact hmem x hx1 hx2
      · rcases hy' with rfl | ⟨hy1, hy2⟩
        · exact ⟨le_rfl, hab _⟩
        · exact hmem y hy1 hy2
    rw [← hcard]
    exact hT.card_le_cliqueNum
  refine Colorable.chromaticNumber_le ⟨Coloring.mk (fun v => ⟨firstFit G v, ?_⟩) fun {u v} h he => ?_⟩
  · have := firstFit_le_ncard G v
    have := hclique v
    omega
  · exact (firstFitColoring G).valid h (Fin.mk.inj_iff.mp he)

end Interval

end UndergradKB.Combinatorics
