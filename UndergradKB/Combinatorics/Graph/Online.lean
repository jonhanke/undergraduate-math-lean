import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr

/-!
# On-line graph colouring (Keller–Trotter, Section 16.1)

Builder presents vertices `0, 1, 2, …` one at a time, together with their adjacency to the
vertices presented earlier; Assigner colours each vertex immediately.  A graph `G : SimpleGraph ℕ`
stands for a whole play: the first `p` vertices are the ones presented, and the vertex `k`
is presented with the adjacency to `0, …, k-1` given by `G`.

An on-line strategy of Assigner is a function that, for every `k`, takes the graph presented so
far (on vertices `0, …, k`, the new vertex being `k`) and returns the colour of vertex `k`.
Since Assigner is deterministic, her earlier colours are determined by the same data.
-/

namespace UndergradKB.Combinatorics

open SimpleGraph

namespace Online

/-- CO-283. An on-line colouring strategy for Assigner: the colour of the new vertex `k`
(a natural number) is a function of the graph presented so far on vertices `0, …, k`. -/
@[kb "kellertrotter2017" "Definition (unnumbered) on-line coloring, p. 339"]
def Strategy : Type := (k : ℕ) → SimpleGraph (Fin (k + 1)) → ℕ

/-- The colour that the strategy `σ` gives to vertex `k` when Builder presents the graph `G`
(vertex `k` is presented together with its adjacency to the vertices `0, …, k-1`). -/
def colour (σ : Strategy) (G : SimpleGraph ℕ) (k : ℕ) : ℕ :=
  σ k (G.comap (fun i : Fin (k + 1) => (i : ℕ)))

/-- CO-283. The colouring produced by `σ` on the first `b` presented vertices fails to be
proper: two adjacent vertices among `0, …, b-1` received the same colour (Assigner loses). -/
@[kb "kellertrotter2017" "Definition (unnumbered) on-line coloring, p. 339"]
def Improper (σ : Strategy) (G : SimpleGraph ℕ) (b : ℕ) : Prop :=
  ∃ i j, i < b ∧ j < b ∧ G.Adj i j ∧ colour σ G i = colour σ G j

/-- `G` has all its edges among the vertices `< b` (the graph presented in `b` rounds). -/
def Supp (b : ℕ) (G : SimpleGraph ℕ) : Prop := ∀ v w, G.Adj v w → v < b ∧ w < b

/-- `G` extends `G₀` by `p` further vertices `m, …, m+p-1`, all new edges lying among them. -/
def Ext (m p : ℕ) (G₀ G : SimpleGraph ℕ) : Prop :=
  G₀ ≤ G ∧ ∀ v w, G.Adj v w → ¬ G₀.Adj v w → m ≤ v ∧ m ≤ w ∧ v < m + p ∧ w < m + p

lemma colour_congr (σ : Strategy) {G G' : SimpleGraph ℕ} {k : ℕ}
    (h : ∀ a b, a ≤ k → b ≤ k → (G.Adj a b ↔ G'.Adj a b)) : colour σ G k = colour σ G' k := by
  unfold colour
  congr 1
  ext a b
  simp only [SimpleGraph.comap_adj]
  exact h _ _ (Nat.lt_succ_iff.1 a.2) (Nat.lt_succ_iff.1 b.2)

lemma Ext.supp {m p : ℕ} {G₀ G : SimpleGraph ℕ} (h : Ext m p G₀ G) (hs : Supp m G₀) :
    Supp (m + p) G := by
  intro v w hvw
  by_cases h0 : G₀.Adj v w
  · have := hs v w h0
    omega
  · have := h.2 v w hvw h0
    omega

lemma Ext.trans {m p p' : ℕ} {G₀ G G' : SimpleGraph ℕ} (h : Ext m p G₀ G)
    (h' : Ext (m + p) p' G G') : Ext m (p + p') G₀ G' := by
  refine ⟨h.1.trans h'.1, fun v w hvw hn => ?_⟩
  by_cases hG : G.Adj v w
  · have := h.2 v w hG hn
    omega
  · have := h'.2 v w hvw hG
    omega

lemma Ext.colour_eq {m p : ℕ} {G₀ G : SimpleGraph ℕ} (σ : Strategy) (h : Ext m p G₀ G)
    {i : ℕ} (hi : i < m) : colour σ G₀ i = colour σ G i := by
  apply colour_congr
  intro a b ha hb
  constructor
  · exact fun hab => h.1 hab
  · intro hab
    by_contra hn
    have := h.2 a b hab hn
    omega

lemma Ext.improper {m p : ℕ} {G₀ G : SimpleGraph ℕ} (σ : Strategy) (h : Ext m p G₀ G)
    (himp : Improper σ G₀ m) : Improper σ G (m + p) := by
  obtain ⟨i, j, hi, hj, hadj, hc⟩ := himp
  exact ⟨i, j, by omega, by omega, h.1 hadj, by
    rw [← h.colour_eq σ hi, ← h.colour_eq σ hj]; exact hc⟩

/-- A set of vertices closed under adjacency is closed under reachability. -/
lemma reach_closed {G : SimpleGraph ℕ} (P : ℕ → Prop)
    (hP : ∀ v w, G.Adj v w → P v → P w) {a c : ℕ} (h : G.Reachable a c) (ha : P a) : P c := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

/-- Reachability from an old vertex in an extension stays within the old graph. -/
lemma Ext.reach_restrict {m p : ℕ} {G₀ G : SimpleGraph ℕ} (h : Ext m p G₀ G) (hs : Supp m G₀)
    {a c : ℕ} (ha : a < m) (hr : G.Reachable a c) : G₀.Reachable a c := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have : c < m ∧ Relation.ReflTransGen G₀.Adj a c := by
    induction hr with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | @tail b c' _ hbc ih =>
      have hn : G₀.Adj b c' := by
        by_contra hn
        have := h.2 b c' hbc hn
        omega
      exact ⟨(hs b c' hn).2, ih.2.tail hn⟩
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).2 this.2

/-- A vertex `≥ m` reaches only vertices `≥ m` in an extension of a graph supported on `[0,m)`. -/
lemma Ext.reach_new {m p : ℕ} {G₀ G : SimpleGraph ℕ} (h : Ext m p G₀ G) (hs : Supp m G₀)
    {a c : ℕ} (ha : m ≤ a) (hr : G.Reachable a c) : m ≤ c := by
  refine reach_closed (fun v => m ≤ v) (fun v w hvw hv => ?_) hr ha
  by_cases h0 : G₀.Adj v w
  · have := (hs v w h0).1
    omega
  · exact (h.2 v w hvw h0).2.1

/-- `addStar G x ys k`: add to `G` the edges from `x` to `ys 0, …, ys (k-1)`. -/
def addStar (G : SimpleGraph ℕ) (x : ℕ) (ys : ℕ → ℕ) : ℕ → SimpleGraph ℕ
  | 0 => G
  | k + 1 => addStar G x ys k ⊔ SimpleGraph.edge x (ys k)

lemma addStar_adj (G : SimpleGraph ℕ) (x : ℕ) (ys : ℕ → ℕ) (k v w : ℕ) :
    (addStar G x ys k).Adj v w ↔
      G.Adj v w ∨ ∃ i < k, ((v = x ∧ w = ys i) ∨ (v = ys i ∧ w = x)) ∧ v ≠ w := by
  induction k with
  | zero => simp [addStar]
  | succ k ih =>
    simp only [addStar, SimpleGraph.sup_adj, ih, SimpleGraph.edge_adj]
    constructor
    · rintro ((h | ⟨i, hi, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, h⟩
      · exact Or.inr ⟨k, by omega, h⟩
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hik : i < k
        · exact Or.inl (Or.inr ⟨i, hik, h⟩)
        · obtain rfl : i = k := by omega
          exact Or.inr h

lemma addStar_le (G : SimpleGraph ℕ) (x : ℕ) (ys : ℕ → ℕ) (k : ℕ) : G ≤ addStar G x ys k :=
  fun v w h => (addStar_adj G x ys k v w).2 (Or.inl h)

/-- Joining a fresh vertex to pairwise non-reachable vertices of a forest gives a forest. -/
lemma addStar_acyclic {G : SimpleGraph ℕ} (hG : G.IsAcyclic) (x : ℕ) (ys : ℕ → ℕ) (k : ℕ)
    (hx : ∀ w, ¬ G.Adj x w) (hy : ∀ j < k, ys j ≠ x)
    (hnr : ∀ i j, i < k → j < k → i ≠ j → ¬ G.Reachable (ys i) (ys j)) :
    (addStar G x ys k).IsAcyclic := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    have ih' := ih (fun j hj => hy j (by omega))
      (fun i j hi hj hij => hnr i j (by omega) (by omega) hij)
    show (addStar G x ys k ⊔ SimpleGraph.edge x (ys k)).IsAcyclic
    refine ih'.sup_edge_of_not_reachable ?_
    intro hr
    have hP := reach_closed (G := addStar G x ys k)
      (fun v => v = x ∨ ∃ i < k, G.Reachable (ys i) v) (fun v w hvw hv => ?_) hr (Or.inl rfl)
    · rcases hP with h | ⟨i, hi, h⟩
      · exact hy k (by omega) h
      · exact hnr i k (by omega) (by omega) (by omega) h
    · rcases (addStar_adj G x ys k v w).1 hvw with h | ⟨i, hi, h, hne⟩
      · rcases hv with rfl | ⟨i, hi, hr⟩
        · exact absurd h (hx w)
        · exact Or.inr ⟨i, hi, hr.trans h.reachable⟩
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨i, hi, Reachable.refl _⟩
        · exact Or.inl rfl


/-- The core of Builder's strategy (Theorem 16.2), stated for an arbitrary already presented
graph `G₀` supported on the vertices `< m`: Builder can add at most `2^k` new vertices, forming a
new forest part with no edges to the old vertices, such that Assigner either errs or is forced to
use `k+1` colours on the new vertices. -/
theorem force (σ : Strategy) : ∀ k m (G₀ : SimpleGraph ℕ), Supp m G₀ →
    ∃ p, p ≤ 2 ^ k ∧ ∃ G : SimpleGraph ℕ, Ext m p G₀ G ∧ (G₀.IsAcyclic → G.IsAcyclic) ∧
      (Improper σ G (m + p) ∨
        k + 1 ≤ ((Finset.Ico m (m + p)).image (colour σ G)).card) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro m G₀ hs0
  have Q : ∀ i ≤ k, ∃ p G, p + 1 ≤ 2 ^ i ∧ Ext m p G₀ G ∧ (G₀.IsAcyclic → G.IsAcyclic) ∧
      (Improper σ G (m + p) ∨ ∃ ys : ℕ → ℕ, (∀ j < i, m ≤ ys j ∧ ys j < m + p) ∧
        (∀ j j', j < i → j' < i → j ≠ j' → colour σ G (ys j) ≠ colour σ G (ys j')) ∧
        (∀ j j', j < i → j' < i → j ≠ j' → ¬ G.Reachable (ys j) (ys j'))) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨0, G₀, by simp, ⟨le_rfl, fun v w h hn => absurd h hn⟩, id,
        Or.inr ⟨fun _ => 0, by intros; omega, by intros; omega, by intros; omega⟩⟩
    | succ i ih =>
      intro hi
      obtain ⟨p, G, hp, hExt, hAc, hcase⟩ := ih (by omega)
      have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; omega
      rcases hcase with himp | ⟨ys, hrange, hcol, hreach⟩
      · exact ⟨p, G, by omega, hExt, hAc, Or.inl himp⟩
      · have hSupp : Supp (m + p) G := hExt.supp hs0
        obtain ⟨p', hp', G', hExt', hAc', hcase'⟩ := IH i (by omega) (m + p) G hSupp
        refine ⟨p + p', G', by omega, hExt.trans hExt', fun h => hAc' (hAc h), ?_⟩
        rcases hcase' with himp' | hcard
        · exact Or.inl (by rwa [← add_assoc])
        · right
          have hT : ((Finset.range i).image (fun j => colour σ G' (ys j))).card ≤ i :=
            Finset.card_image_le.trans (by simp)
          obtain ⟨c, hc, hcT⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := (Finset.range i).image (fun j => colour σ G' (ys j)))
            (t := (Finset.Ico (m + p) (m + p + p')).image (colour σ G')) (by omega)
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hc
          rw [Finset.mem_Ico] at hv
          have hstab : ∀ j < i, colour σ G' (ys j) = colour σ G (ys j) := fun j hj =>
            (hExt'.colour_eq σ (hrange j hj).2).symm
          have hne : ∀ j < i, colour σ G' (ys j) ≠ colour σ G' v := fun j hj h =>
            hcT (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, h⟩)
          have hupd : ∀ j, j < i + 1 →
              (j = i ∧ Function.update ys i v j = v) ∨ (j < i ∧ Function.update ys i v j = ys j) := by
            intro j hj
            by_cases h : j = i
            · subst h; exact Or.inl ⟨rfl, by simp⟩
            · exact Or.inr ⟨by omega, by simp [Function.update, h]⟩
          refine ⟨Function.update ys i v, ?_, ?_, ?_⟩
          · intro j hj
            rcases hupd j hj with ⟨_, h⟩ | ⟨hji, h⟩
            · rw [h]; omega
            · rw [h]; have := hrange j hji; omega
          · intro j j' hj hj' hjj'
            rcases hupd j hj with ⟨hj0, h⟩ | ⟨hji, h⟩ <;> rcases hupd j' hj' with ⟨hj0', h'⟩ | ⟨hji', h'⟩
            · omega
            · rw [h, h']; exact fun e => hne j' hji' e.symm
            · rw [h, h']; exact hne j hji
            · rw [h, h', hstab j hji, hstab j' hji']; exact hcol j j' hji hji' hjj'
          · intro j j' hj hj' hjj'
            rcases hupd j hj with ⟨hj0, h⟩ | ⟨hji, h⟩ <;> rcases hupd j' hj' with ⟨hj0', h'⟩ | ⟨hji', h'⟩
            · omega
            · rw [h, h']
              intro hr
              have := hExt'.reach_new hSupp (by omega) hr
              have := hrange j' hji'
              omega
            · rw [h, h']
              intro hr
              have := hExt'.reach_new hSupp (by omega) hr.symm
              have := hrange j hji
              omega
            · rw [h, h']
              intro hr
              exact hreach j j' hji hji' hjj'
                (hExt'.reach_restrict hSupp (hrange j hji).2 hr)
  obtain ⟨p, G, hp, hExt, hAc, hcase⟩ := Q k le_rfl
  have hpow : 0 < 2 ^ k := by positivity
  rcases hcase with himp | ⟨ys, hrange, hcol, hreach⟩
  · exact ⟨p, by omega, G, hExt, hAc, Or.inl himp⟩
  · have hSupp : Supp (m + p) G := hExt.supp hs0
    set Gx := addStar G (m + p) ys k with hGx
    have hExtx : Ext m (p + 1) G₀ Gx := by
      refine ⟨hExt.1.trans (addStar_le _ _ _ _), fun v w hvw hn => ?_⟩
      rcases (addStar_adj G (m + p) ys k v w).1 hvw with h | ⟨i, hi, h, hne⟩
      · have := hExt.2 v w h hn
        omega
      · have := hrange i hi
        omega
    have hstab : ∀ i < m + p, colour σ Gx i = colour σ G i := by
      intro i hi
      apply colour_congr
      intro a b ha hb
      rw [hGx, addStar_adj]
      constructor
      · rintro (h | ⟨j, hj, h, hne⟩)
        · exact h
        · omega
      · exact Or.inl
    refine ⟨p + 1, by omega, Gx, hExtx, fun h => ?_, ?_⟩
    · exact addStar_acyclic (hAc h) (m + p) ys k
        (fun w hw => by have := (hSupp _ _ hw).1; omega)
        (fun j hj => by have := hrange j hj; omega) hreach
    · by_cases hcx : ∃ j < k, colour σ Gx (m + p) = colour σ Gx (ys j)
      · obtain ⟨j, hj, hc⟩ := hcx
        have := hrange j hj
        refine Or.inl ⟨m + p, ys j, by omega, by omega, ?_, hc⟩
        rw [hGx, addStar_adj]
        exact Or.inr ⟨j, hj, Or.inl ⟨rfl, rfl⟩, by omega⟩
      · push Not at hcx
        right
        have hinj : Set.InjOn (fun j => colour σ Gx (ys j)) (Finset.range k : Set ℕ) := by
          intro j hj j' hj' he
          by_contra hjj
          rw [Finset.mem_coe, Finset.mem_range] at hj hj'
          simp only at he
          rw [hstab _ (hrange j hj).2, hstab _ (hrange j' hj').2] at he
          exact hcol j j' hj hj' hjj he
        have hnot : colour σ Gx (m + p) ∉ (Finset.range k).image (fun j => colour σ Gx (ys j)) := by
          intro h
          obtain ⟨j, hj, hjc⟩ := Finset.mem_image.1 h
          exact hcx j (Finset.mem_range.1 hj) hjc.symm
        have hcard : (insert (colour σ Gx (m + p))
            ((Finset.range k).image (fun j => colour σ Gx (ys j)))).card = k + 1 := by
          rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
            Finset.card_range]
        rw [← hcard]
        apply Finset.card_le_card
        intro c hc
        rw [Finset.mem_insert, Finset.mem_image] at hc
        rw [Finset.mem_image]
        rcases hc with rfl | ⟨j, hj, rfl⟩
        · exact ⟨m + p, Finset.mem_Ico.2 ⟨by omega, by omega⟩, rfl⟩
        · have := hrange j (Finset.mem_range.1 hj)
          exact ⟨ys j, Finset.mem_Ico.2 ⟨this.1, by omega⟩, rfl⟩


/-- CO-285. Keller–Trotter Theorem 16.2. For every `n ≥ 1` and every on-line strategy `σ` of
Assigner, Builder can present a forest on `p ≤ 2^(n-1)` vertices (vertices `0, …, p-1`, edges
only among them, acyclic) on which Assigner either errs (two adjacent vertices get the same
colour) or is forced to use at least `n` colours.

(Builder's moves in the proof depend only on the colours Assigner has already announced; the
statement is formalised as "for every strategy of Assigner there is a play".) -/
@[kb "kellertrotter2017" "Theorem 16.2, p. 340"]
theorem builder_forces_colours (n : ℕ) (hn : 1 ≤ n) (σ : Strategy) :
    ∃ G : SimpleGraph ℕ, ∃ p ≤ 2 ^ (n - 1), Supp p G ∧ G.IsAcyclic ∧
      (Improper σ G p ∨ n ≤ ((Finset.range p).image (colour σ G)).card) := by
  obtain ⟨p, hp, G, hExt, hAc, hcase⟩ := force σ (n - 1) 0 ⊥ (by intro v w h; simp at h)
  have hS : Supp (0 + p) G := hExt.supp (by intro v w h; simp at h)
  refine ⟨G, p, hp, by simpa using hS, hAc isAcyclic_bot, ?_⟩
  simpa [Nat.sub_add_cancel hn] using hcase

/-- Graphs on three or four vertices used for Example 16.1. -/
def pathCase1 : SimpleGraph ℕ := SimpleGraph.fromEdgeSet {s(0, 2), s(1, 2), s(1, 3)}

def pathCase2 : SimpleGraph ℕ := SimpleGraph.fromEdgeSet {s(0, 2), s(2, 3), s(1, 3)}

lemma pathCase1_supp : Supp 4 pathCase1 := by
  intro v w h
  simp only [pathCase1, SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    Sym2.eq_iff] at h
  omega

lemma pathCase2_supp : Supp 4 pathCase2 := by
  intro v w h
  simp only [pathCase2, SimpleGraph.fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
    Sym2.eq_iff] at h
  omega

/-- CO-284. Keller–Trotter Example 16.1: Builder can force Assigner to use three colours (or to
err), even when the final graph is a path on four vertices (`pathGraph 4`, up to relabelling of
the vertices presented). -/
@[kb "kellertrotter2017" "Example 16.1, p. 339"]
theorem three_colours_on_path (σ : Strategy) :
    ∃ G : SimpleGraph ℕ, Supp 4 G ∧
      (∃ π : Fin 4 ≃ Fin 4, ∀ i j : Fin 4,
        G.Adj (i : ℕ) (j : ℕ) ↔ (SimpleGraph.pathGraph 4).Adj (π i) (π j)) ∧
      (Improper σ G 4 ∨ 3 ≤ ((Finset.range 4).image (colour σ G)).card) := by
  have hiso1 : ∃ π : Fin 4 ≃ Fin 4, ∀ i j : Fin 4,
      pathCase1.Adj (i : ℕ) (j : ℕ) ↔ (SimpleGraph.pathGraph 4).Adj (π i) (π j) := by
    refine ⟨Equiv.swap 1 2, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [pathCase1, SimpleGraph.pathGraph_adj] <;> decide
  have hiso2 : ∃ π : Fin 4 ≃ Fin 4, ∀ i j : Fin 4,
      pathCase2.Adj (i : ℕ) (j : ℕ) ↔ (SimpleGraph.pathGraph 4).Adj (π i) (π j) := by
    refine ⟨⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [pathCase2, SimpleGraph.pathGraph_adj] <;> decide
  have h0 : colour σ pathCase2 0 = colour σ pathCase1 0 := by
    apply colour_congr
    intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [pathCase1, pathCase2]
  have h1 : colour σ pathCase2 1 = colour σ pathCase1 1 := by
    apply colour_congr
    intro x y hx hy
    interval_cases x <;> interval_cases y <;> simp [pathCase1, pathCase2]
  have card3 : ∀ (G : SimpleGraph ℕ) (i j k : ℕ), i < 4 → j < 4 → k < 4 →
      colour σ G i ≠ colour σ G j → colour σ G i ≠ colour σ G k → colour σ G j ≠ colour σ G k →
      3 ≤ ((Finset.range 4).image (colour σ G)).card := by
    intro G i j k hi hj hk hij hik hjk
    have : ({colour σ G i, colour σ G j, colour σ G k} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.2 ⟨_, _, _, hij, hik, hjk, rfl⟩
    rw [← this]
    apply Finset.card_le_card
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rw [Finset.mem_image]
    rcases hc with rfl | rfl | rfl
    · exact ⟨i, Finset.mem_range.2 hi, rfl⟩
    · exact ⟨j, Finset.mem_range.2 hj, rfl⟩
    · exact ⟨k, Finset.mem_range.2 hk, rfl⟩
  by_cases hab : colour σ pathCase1 0 = colour σ pathCase1 1
  · -- Assigner gave `x` and `y` the same colour: use `pathCase2`
    refine ⟨pathCase2, pathCase2_supp, hiso2, ?_⟩
    by_cases hc : colour σ pathCase2 2 = colour σ pathCase2 0
    · exact Or.inl ⟨2, 0, by omega, by omega, by simp [pathCase2], hc⟩
    by_cases hd : colour σ pathCase2 3 = colour σ pathCase2 2
    · exact Or.inl ⟨3, 2, by omega, by omega, by simp [pathCase2], hd⟩
    by_cases he : colour σ pathCase2 3 = colour σ pathCase2 1
    · exact Or.inl ⟨3, 1, by omega, by omega, by simp [pathCase2], he⟩
    right
    refine card3 pathCase2 0 2 3 (by omega) (by omega) (by omega) (fun h => hc h.symm) ?_ (fun h => hd h.symm)
    intro h
    exact he (by rw [h1, ← hab, ← h0, ← h])
  · refine ⟨pathCase1, pathCase1_supp, hiso1, ?_⟩
    by_cases hc : colour σ pathCase1 2 = colour σ pathCase1 0
    · exact Or.inl ⟨2, 0, by omega, by omega, by simp [pathCase1], hc⟩
    by_cases hd : colour σ pathCase1 2 = colour σ pathCase1 1
    · exact Or.inl ⟨2, 1, by omega, by omega, by simp [pathCase1], hd⟩
    right
    exact card3 pathCase1 0 1 2 (by omega) (by omega) (by omega) hab (fun h => hc h.symm)
      (fun h => hd h.symm)


/-! ### On-line partition of a poset into antichains (Theorem 16.4) -/

section Antichains

open Classical in
/-- The chains of presented points `0, …, k` (as sets of indices) having `k` as their least
element, for the presented relation `le`. -/
noncomputable def downChains (le : ℕ → ℕ → Prop) (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (k + 1)).powerset.filter fun C =>
    k ∈ C ∧ (∀ i ∈ C, le k i) ∧ ∀ i ∈ C, ∀ j ∈ C, le i j ∨ le j i

open Classical in
/-- The chains of presented points `0, …, k` having `k` as their greatest element. -/
noncomputable def upChains (le : ℕ → ℕ → Prop) (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (k + 1)).powerset.filter fun C =>
    k ∈ C ∧ (∀ i ∈ C, le i k) ∧ ∀ i ∈ C, ∀ j ∈ C, le i j ∨ le j i

/-- CO-177. The class `(r, s)` that Assigner's strategy gives to the new point `k`: `r` is the
largest size of a chain among the points `0, …, k` with `k` as its least element, and `s` the
largest size of such a chain with `k` as greatest element.  (Only the relation `le` on the
indices `≤ k` is used, so this is an on-line strategy; see `antichainClass_congr`.) -/
@[kb "kellertrotter2017" "Theorem 16.4, p. 341"]
noncomputable def antichainClass (le : ℕ → ℕ → Prop) (k : ℕ) : ℕ × ℕ :=
  ((downChains le k).sup Finset.card, (upChains le k).sup Finset.card)

/-- The class of the new point depends only on the order among the points presented so far. -/
lemma antichainClass_congr {le le' : ℕ → ℕ → Prop} {k : ℕ}
    (h : ∀ i j, i ≤ k → j ≤ k → (le i j ↔ le' i j)) :
    antichainClass le k = antichainClass le' k := by
  classical
  have hd : downChains le k = downChains le' k := by
    unfold downChains
    apply Finset.filter_congr
    intro C hC
    have hCk : ∀ i ∈ C, i ≤ k := fun i hi =>
      Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_powerset.1 hC hi))
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (h _ _ le_rfl (hCk i hi)).1 (h2 i hi),
        fun i hi j hj => (h3 i hi j hj).imp (h _ _ (hCk i hi) (hCk j hj)).1
          (h _ _ (hCk j hj) (hCk i hi)).1⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (h _ _ le_rfl (hCk i hi)).2 (h2 i hi),
        fun i hi j hj => (h3 i hi j hj).imp (h _ _ (hCk i hi) (hCk j hj)).2
          (h _ _ (hCk j hj) (hCk i hi)).2⟩
  have hu : upChains le k = upChains le' k := by
    unfold upChains
    apply Finset.filter_congr
    intro C hC
    have hCk : ∀ i ∈ C, i ≤ k := fun i hi =>
      Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_powerset.1 hC hi))
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (h _ _ (hCk i hi) le_rfl).1 (h2 i hi),
        fun i hi j hj => (h3 i hi j hj).imp (h _ _ (hCk i hi) (hCk j hj)).1
          (h _ _ (hCk j hj) (hCk i hi)).1⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun i hi => (h _ _ (hCk i hi) le_rfl).2 (h2 i hi),
        fun i hi j hj => (h3 i hi j hj).imp (h _ _ (hCk i hi) (hCk j hj)).2
          (h _ _ (hCk j hj) (hCk i hi)).2⟩
  simp only [antichainClass, hd, hu]

variable {P : Type*} [PartialOrder P]

/-- Presented points `x 0, x 1, …` of a poset `P`, with the induced presented relation. -/
def presented (x : ℕ → P) : ℕ → ℕ → Prop := fun i j => x i ≤ x j

lemma singleton_mem_downChains (x : ℕ → P) (k : ℕ) : {k} ∈ downChains (presented x) k := by
  classical
  unfold downChains
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (by simp), by simp, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact le_rfl
  · intro i hi j hj
    rw [Finset.mem_singleton] at hi hj
    subst hi hj
    exact Or.inl le_rfl

lemma singleton_mem_upChains (x : ℕ → P) (k : ℕ) : {k} ∈ upChains (presented x) k := by
  classical
  unfold upChains
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (by simp), by simp, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact le_rfl
  · intro i hi j hj
    rw [Finset.mem_singleton] at hi hj
    subst hi hj
    exact Or.inl le_rfl

lemma one_le_class (x : ℕ → P) (k : ℕ) :
    1 ≤ (antichainClass (presented x) k).1 ∧ 1 ≤ (antichainClass (presented x) k).2 := by
  constructor
  · exact (by simp : ({k} : Finset ℕ).card = 1).symm.le.trans
      (Finset.le_sup (f := Finset.card) (singleton_mem_downChains x k))
  · exact (by simp : ({k} : Finset ℕ).card = 1).symm.le.trans
      (Finset.le_sup (f := Finset.card) (singleton_mem_upChains x k))

lemma exists_down (x : ℕ → P) (k : ℕ) :
    ∃ C ∈ downChains (presented x) k, C.card = (antichainClass (presented x) k).1 :=
  (Finset.exists_mem_eq_sup _ ⟨_, singleton_mem_downChains x k⟩ Finset.card).imp
    fun _ h => ⟨h.1, h.2.symm⟩

lemma exists_up (x : ℕ → P) (k : ℕ) :
    ∃ C ∈ upChains (presented x) k, C.card = (antichainClass (presented x) k).2 :=
  (Finset.exists_mem_eq_sup _ ⟨_, singleton_mem_upChains x k⟩ Finset.card).imp
    fun _ h => ⟨h.1, h.2.symm⟩

/-- Same-class points presented in order `a < b` are incomparable. -/
lemma incomparable_of_class_eq (x : ℕ → P) {a b : ℕ} (hab : a < b)
    (h : antichainClass (presented x) a = antichainClass (presented x) b) :
    ¬ x b ≤ x a ∧ ¬ x a ≤ x b := by
  classical
  obtain ⟨C, hC, hCc⟩ := exists_down x a
  obtain ⟨D, hD, hDc⟩ := exists_up x a
  unfold downChains at hC
  unfold upChains at hD
  rw [Finset.mem_filter, Finset.mem_powerset] at hC hD
  have hbC : b ∉ C := fun hb => by
    have := Finset.mem_range.1 (hC.1 hb); omega
  have hbD : b ∉ D := fun hb => by
    have := Finset.mem_range.1 (hD.1 hb); omega
  constructor
  · intro hba
    have hmem : insert b C ∈ downChains (presented x) b := by
      unfold downChains
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => ?_, Finset.mem_insert_self _ _, fun i hi => ?_, fun i hi j hj => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · simp
        · have := Finset.mem_range.1 (hC.1 hi); simp only [Finset.mem_range]; omega
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact le_rfl
        · exact hba.trans (hC.2.2.1 i hi)
      · rcases Finset.mem_insert.1 hi with hi' | hi' <;> rcases Finset.mem_insert.1 hj with hj' | hj'
        · left; show x i ≤ x j; rw [hi', hj']
        · left; show x i ≤ x j; rw [hi']; exact hba.trans (hC.2.2.1 j hj')
        · right; show x j ≤ x i; rw [hj']; exact hba.trans (hC.2.2.1 i hi')
        · exact hC.2.2.2 i hi' j hj'
    have h1 := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_insert_of_notMem hbC, hCc] at h1
    have : (antichainClass (presented x) b).1 = (antichainClass (presented x) a).1 := by rw [h]
    simp only [antichainClass] at this h1
    omega
  · intro hab'
    have hmem : insert b D ∈ upChains (presented x) b := by
      unfold upChains
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun i hi => ?_, Finset.mem_insert_self _ _, fun i hi => ?_, fun i hi j hj => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · simp
        · have := Finset.mem_range.1 (hD.1 hi); simp only [Finset.mem_range]; omega
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact le_rfl
        · exact (hD.2.2.1 i hi).trans hab'
      · rcases Finset.mem_insert.1 hi with hi' | hi' <;> rcases Finset.mem_insert.1 hj with hj' | hj'
        · left; show x i ≤ x j; rw [hi', hj']
        · right; show x j ≤ x i; rw [hi']; exact (hD.2.2.1 j hj').trans hab'
        · left; show x i ≤ x j; rw [hj']; exact (hD.2.2.1 i hi').trans hab'
        · exact hD.2.2.2 i hi' j hj'
    have h1 := Finset.le_sup (f := Finset.card) hmem
    rw [Finset.card_insert_of_notMem hbD, hDc] at h1
    have : (antichainClass (presented x) b).2 = (antichainClass (presented x) a).2 := by rw [h]
    simp only [antichainClass] at this h1
    omega

/-- The class sizes satisfy `r + s - 1 ≤ h` when all chains of `P` have at most `h` elements. -/
lemma class_sum_le (x : ℕ → P) {n h : ℕ} (hinj : Set.InjOn x (Set.Iio n))
    (hh : ∀ C : Finset P, IsChain (· ≤ ·) (C : Set P) → C.card ≤ h) {k : ℕ} (hk : k < n) :
    (antichainClass (presented x) k).1 + (antichainClass (presented x) k).2 ≤ h + 1 := by
  classical
  obtain ⟨C, hC, hCc⟩ := exists_down x k
  obtain ⟨D, hD, hDc⟩ := exists_up x k
  unfold downChains at hC
  unfold upChains at hD
  rw [Finset.mem_filter, Finset.mem_powerset] at hC hD
  have hsub : ∀ i ∈ C ∪ D, i < n := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · have := Finset.mem_range.1 (hC.1 hi); omega
    · have := Finset.mem_range.1 (hD.1 hi); omega
  have hinj' : Set.InjOn x ((C ∪ D : Finset ℕ) : Set ℕ) := fun i hi j hj hij =>
    hinj (hsub i (Finset.mem_coe.1 hi)) (hsub j (Finset.mem_coe.1 hj)) hij
  have hchain : IsChain (· ≤ ·) (((C ∪ D).image x : Finset P) : Set P) := by
    intro u hu v hv _
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_union] at hu hv
    obtain ⟨i, hi, rfl⟩ := hu
    obtain ⟨j, hj, rfl⟩ := hv
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hC.2.2.2 i hi j hj
    · exact Or.inr ((hD.2.2.1 j hj).trans (hC.2.2.1 i hi))
    · exact Or.inl ((hD.2.2.1 i hi).trans (hC.2.2.1 j hj))
    · exact hD.2.2.2 i hi j hj
  have h1 := hh _ hchain
  rw [Finset.card_image_of_injOn hinj'] at h1
  have hint : C ∩ D = {k} := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hi'⟩
      have e : x k = x i := le_antisymm (hC.2.2.1 i hi) (hD.2.2.1 i hi')
      exact (hinj (hsub i (Finset.mem_union_left _ hi)) (hsub k (Finset.mem_union_left _ hC.2.1))
        e.symm)
    · rintro rfl
      exact ⟨hC.2.1, hD.2.1⟩
  have := Finset.card_union_add_card_inter C D
  rw [hint, Finset.card_singleton] at this
  rw [← hCc, ← hDc]
  omega

/-- CO-177. Keller–Trotter Theorem 16.4 (on-line antichain partition). Points `x 0, …, x (n-1)`
of a poset (pairwise distinct) are presented one at a time; Assigner puts the new point into the
class `antichainClass (presented x) k = (r, s)` computed from the points presented so far.
Then (i) any two points of the same class are incomparable, i.e. each class is an antichain, and
(ii) if every chain has at most `h` points, then at most `C(h+1, 2)` classes are used. -/
@[kb "kellertrotter2017" "Theorem 16.4, p. 341"]
theorem online_antichain_partition (x : ℕ → P) {n h : ℕ} (hinj : Set.InjOn x (Set.Iio n))
    (hh : ∀ C : Finset P, IsChain (· ≤ ·) (C : Set P) → C.card ≤ h) :
    (∀ a b, a < n → b < n → a ≠ b →
      antichainClass (presented x) a = antichainClass (presented x) b →
        ¬ x a ≤ x b ∧ ¬ x b ≤ x a) ∧
    ((Finset.range n).image (antichainClass (presented x))).card ≤ (h + 1).choose 2 := by
  refine ⟨fun a b ha hb hab hc => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hab with hlt | hlt
    · have := incomparable_of_class_eq x hlt hc
      exact ⟨this.2, this.1⟩
    · have := incomparable_of_class_eq x hlt hc.symm
      exact ⟨this.1, this.2⟩
  · classical
    let T : Finset (ℕ × ℕ) :=
      ((Finset.Icc 1 h) ×ˢ (Finset.Icc 1 h)).filter (fun p => p.1 + p.2 ≤ h + 1)
    have hsub : (Finset.range n).image (antichainClass (presented x)) ⊆ T := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have h1 := one_le_class x k
      have h2 := class_sum_le x hinj hh (Finset.mem_range.1 hk)
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
    refine (Finset.card_le_card hsub).trans ?_
    have : T.card ≤ ((Finset.Icc 1 (h + 1)).powersetCard 2).card := by
      refine Finset.card_le_card_of_injOn (fun p => ({p.1, p.1 + p.2} : Finset ℕ)) ?_ ?_
      · intro p hp
        simp only [T, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq,
          Finset.mem_coe] at hp
        rw [Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rw [Finset.mem_Icc]
          omega
        · rw [Finset.card_pair]; omega
      · intro p hp q hq hpq
        simp only [T, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq,
          Finset.mem_coe] at hp hq
        have e1 : p.1 ∈ ({q.1, q.1 + q.2} : Finset ℕ) := by
          simp only at hpq; rw [← hpq]; simp
        have e2 : p.1 + p.2 ∈ ({q.1, q.1 + q.2} : Finset ℕ) := by
          simp only at hpq; rw [← hpq]; simp
        have e3 : q.1 ∈ ({p.1, p.1 + p.2} : Finset ℕ) := by
          simp only at hpq; rw [hpq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at e1 e2 e3
        ext <;> omega
    rw [Finset.card_powersetCard, Nat.card_Icc] at this
    simpa using this

end Antichains

end Online

end UndergradKB.Combinatorics
