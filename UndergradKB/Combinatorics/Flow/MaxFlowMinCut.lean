import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Max
import UndergradKB.Combinatorics.Flow.Network

/-!
# The max-flow min-cut theorem (Keller–Trotter, Chapters 13 and 14)

* `Network.exists_augPath`: if the sink can be reached from the source by residual steps, there is an augmenting path
  (of distinct vertices);
* `Network.labelled_isCut`, `Network.capacity_labelled_eq_value` (text p. 293): when the labelling stops with the sink
  unlabelled, the labelled vertices form a cut whose capacity is the value of the current flow;
* `Network.maxFlow_minCut` (Theorem 13.10);
* `Network.exists_integral_maxFlow` (Theorem 14.1).
-/

namespace UndergradKB.Combinatorics.Flow

open Finset

namespace Network

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}

/-- Cut an augmenting path at an intermediate vertex. -/
def AugPath.truncate {φ : V → V → ℝ} {a b : V} (p : N.AugPath φ a b) (j : Fin (p.len + 1)) :
    N.AugPath φ a (p.vert j) where
  len := j
  vert i := p.vert (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)
  injective := p.injective.comp (Fin.castLE_injective _)
  first := (congrArg p.vert (Fin.ext (by simp))).trans p.first
  last := by
    congr 1
  step i := by
    have := p.step ⟨i, by omega⟩
    convert this using 2 <;> ext <;> simp
/-- Extend an augmenting path by one residual step to a new vertex. -/
def AugPath.snoc {φ : V → V → ℝ} {a b c : V} (p : N.AugPath φ a b) (h : N.Residual φ b c)
    (hc : ∀ i, p.vert i ≠ c) : N.AugPath φ a c where
  len := p.len + 1
  vert := Fin.snoc p.vert c
  injective := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij; exact absurd hij.symm (hc j)
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij; exact absurd hij (hc i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hij
        rw [p.injective hij]
  first := by
    have := Fin.snoc_castSucc (α := fun _ => V) (p := p.vert) (x := c) (i := 0)
    simp only [Fin.castSucc_zero] at this
    rw [this, p.first]
  last := by simp
  step i := by
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
      rwa [p.last]
    | cast i =>
      have := p.step i
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact this

/-- If the sink (or any vertex) can be reached from the source by residual steps, there is an augmenting path of
distinct vertices. -/
theorem exists_augPath {φ : V → V → ℝ} {a b : V} (h : Relation.ReflTransGen (N.Residual φ) a b) :
    Nonempty (N.AugPath φ a b) := by
  induction h with
  | refl => exact ⟨⟨0, fun _ => a, fun i j _ => Fin.ext (by omega), rfl, rfl, fun i => i.elim0⟩⟩
  | @tail c d _ hcb ih =>
    obtain ⟨p⟩ := ih
    by_cases hc : ∃ j, p.vert j = d
    · obtain ⟨j, hj⟩ := hc
      exact ⟨hj ▸ p.truncate j⟩
    · push Not at hc
      exact ⟨p.snoc (p.last ▸ hcb) hc⟩

open Classical in
/-- The labelled vertices of the labelling algorithm: those reachable from the source by residual steps. -/
noncomputable def labelled (N : Network V) (φ : V → V → ℝ) : Finset V :=
  univ.filter fun v => Relation.ReflTransGen (N.Residual φ) N.source v

lemma mem_labelled {φ : V → V → ℝ} {v : V} :
    v ∈ N.labelled φ ↔ Relation.ReflTransGen (N.Residual φ) N.source v := by
  classical
  simp [labelled]

/-- CO-298. If the labelling stops with the sink unlabelled, the labelled vertices form a cut. -/
@[kb "kellertrotter2017" "text (labelling algorithm stops with the sink unlabelled), p. 293"]
theorem labelled_isCut {φ : V → V → ℝ} (ht : N.sink ∉ N.labelled φ) : N.IsCut (N.labelled φ) :=
  ⟨mem_labelled.2 Relation.ReflTransGen.refl, ht⟩

/-- CO-298. If the labelling stops with the sink unlabelled, the capacity of the cut formed by the labelled vertices
equals the value of the current flow: every edge from a labelled to an unlabelled vertex is full and every edge back
is empty. -/
@[kb "kellertrotter2017" "text (labelling algorithm stops with the sink unlabelled), p. 293"]
theorem capacity_labelled_eq_value {φ : V → V → ℝ} (hφ : N.IsFlow φ) (ht : N.sink ∉ N.labelled φ) :
    N.capacity (N.labelled φ) = N.value φ := by
  rw [value_eq_sum_cut hφ (labelled_isCut ht), capacity]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_compl, mem_labelled] at hy
  rw [mem_labelled] at hx
  have h1 : φ x y = N.cap x y := by
    by_cases hxy : N.adj x y
    · by_contra hne
      exact hy (hx.tail (Or.inl ⟨hxy, lt_of_le_of_ne (hφ.le_cap x y) hne⟩))
    · rw [hφ.eq_zero_of_not_adj hxy, N.cap_of_not_adj x y hxy]
  have h2 : φ y x = 0 := by
    by_cases hyx : N.adj y x
    · by_contra hne
      exact hy (hx.tail (Or.inr ⟨hyx, lt_of_le_of_ne (hφ.nonneg y x) (Ne.symm hne)⟩))
    · exact hφ.eq_zero_of_not_adj hyx
  rw [h1, h2, sub_zero]

/-- A positive amount below the residual capacity of every step of an augmenting path from the source to the
sink. -/
lemma exists_pos_le_residualCap {φ : V → V → ℝ} (hφ : N.IsFlow φ) (p : N.AugPath φ N.source N.sink) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : Fin p.len, δ ≤ N.residualCap φ (p.vert i.castSucc) (p.vert i.succ) := by
  have hpos : ∀ i : Fin p.len, 0 < N.residualCap φ (p.vert i.castSucc) (p.vert i.succ) := by
    intro i
    unfold residualCap
    rcases p.step i with ⟨h, hlt⟩ | ⟨h, hlt⟩
    · rw [ite_eq_left h]; linarith
    · rw [ite_eq_right (N.oriented _ _ h)]; exact hlt
  rcases Nat.eq_zero_or_pos p.len with h0 | hlen
  · exfalso
    apply N.source_ne_sink
    have : (0 : Fin (p.len + 1)) = Fin.last p.len := Fin.ext (by simp [h0])
    exact p.first.symm.trans ((congrArg p.vert this).trans p.last)
  · have hne : (Finset.univ : Finset (Fin p.len)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hlen⟩⟩
    refine ⟨Finset.univ.inf' hne fun i => N.residualCap φ (p.vert i.castSucc) (p.vert i.succ), ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hne).2 fun i _ => hpos i
    · exact fun i => Finset.inf'_le _ (Finset.mem_univ i)

/-- CO-297. If the sink is labelled, the flow can be augmented: there is a flow of strictly larger value. -/
@[kb "kellertrotter2017" "text (labelling algorithm, sink labelled), p. 293"]
theorem exists_larger_of_sink_labelled {φ : V → V → ℝ} (hφ : N.IsFlow φ) (ht : N.sink ∈ N.labelled φ) :
    ∃ ψ, N.IsFlow ψ ∧ N.value φ < N.value ψ := by
  obtain ⟨p⟩ := exists_augPath (mem_labelled.1 ht)
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_residualCap hφ p
  obtain ⟨hψ, hv⟩ := N.augment hφ p hδ.le hle
  exact ⟨_, hψ, by rw [hv]; linarith⟩

/-- The set of flows is compact (closed and bounded in a finite-dimensional space). -/
lemma isCompact_flows (N : Network V) : IsCompact {φ : V → V → ℝ | N.IsFlow φ} := by
  have hset : {φ : V → V → ℝ | N.IsFlow φ} = Set.Icc 0 N.cap ∩
      ⋂ v ∈ ({w | w ≠ N.source ∧ w ≠ N.sink} : Set V), {φ | netOut φ v = 0} := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_iInter]
    constructor
    · intro h
      exact ⟨⟨fun x y => h.nonneg x y, fun x y => h.le_cap x y⟩, fun v hv => h.conserve v hv.1 hv.2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨fun x y => h0 x y, fun x y => h1 x y, fun v hs ht => h2 v ⟨hs, ht⟩⟩
  rw [hset]
  refine isCompact_Icc.inter_right (isClosed_biInter fun v _ => isClosed_eq ?_ continuous_const)
  unfold netOut
  fun_prop

/-- A maximum flow exists. -/
lemma exists_maxFlow (N : Network V) : ∃ φ, N.IsFlow φ ∧ ∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ := by
  have hne : ({φ : V → V → ℝ | N.IsFlow φ}).Nonempty :=
    ⟨0, ⟨fun _ _ => le_rfl, fun x y => N.cap_nonneg x y, fun v _ _ => by simp [netOut]⟩⟩
  have hcont : Continuous fun φ : V → V → ℝ => N.value φ := by
    unfold value netOut
    fun_prop
  obtain ⟨φ, hφ, hmax⟩ := N.isCompact_flows.exists_isMaxOn hne hcont.continuousOn
  exact ⟨φ, hφ, fun ψ hψ => hmax hψ⟩

/-- CO-296. **Max-flow min-cut theorem.** The maximum value of a flow equals the minimum capacity of a cut: there are a
flow `φ` and a cut `L` with `value φ = capacity L`, `φ` has the largest value among all flows and `L` the smallest
capacity among all cuts. -/
@[kb "kellertrotter2017" "Theorem 13.10, p. 292"]
theorem maxFlow_minCut (N : Network V) :
    ∃ φ L, N.IsFlow φ ∧ N.IsCut L ∧ N.value φ = N.capacity L ∧
      (∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ∧ (∀ M, N.IsCut M → N.capacity L ≤ N.capacity M) := by
  obtain ⟨φ, hφ, hmax⟩ := N.exists_maxFlow
  have ht : N.sink ∉ N.labelled φ := by
    intro ht
    obtain ⟨ψ, hψ, hlt⟩ := exists_larger_of_sink_labelled hφ ht
    exact absurd (hmax ψ hψ) (not_le.2 hlt)
  refine ⟨φ, N.labelled φ, hφ, labelled_isCut ht, (capacity_labelled_eq_value hφ ht).symm, hmax, ?_⟩
  intro M hM
  rw [capacity_labelled_eq_value hφ ht]
  exact value_le_capacity hφ hM

/-- A flow is maximum exactly when the sink cannot be labelled (no augmenting path). -/
theorem isMax_iff_sink_not_labelled {φ : V → V → ℝ} (hφ : N.IsFlow φ) :
    (∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ) ↔ N.sink ∉ N.labelled φ := by
  constructor
  · intro hmax ht
    obtain ⟨ψ, hψ, hlt⟩ := exists_larger_of_sink_labelled hφ ht
    exact absurd (hmax ψ hψ) (not_le.2 hlt)
  · intro ht ψ hψ
    rw [← capacity_labelled_eq_value hφ ht]
    exact value_le_capacity hψ (labelled_isCut ht)

/-- CO-300. **Integrality theorem.** If every capacity is an integer, some maximum flow takes an integer value on every
edge (Ford–Fulkerson started from the zero flow only ever augments by integers). -/
@[kb "kellertrotter2017" "Theorem 14.1, p. 303"]
theorem exists_integral_maxFlow (N : Network V) (hcap : ∀ x y, ∃ n : ℕ, N.cap x y = n) :
    ∃ φ, N.IsFlow φ ∧ (∀ x y, ∃ n : ℕ, φ x y = n) ∧ ∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value φ := by
  classical
  choose c hc using hcap
  set B := Finset.univ.sup fun xy : V × V => c xy.1 xy.2
  have hcB : ∀ x y, c x y ≤ B := fun x y =>
    Finset.le_sup (f := fun xy : V × V => c xy.1 xy.2) (Finset.mem_univ (x, y))
  set S := {φ : V → V → ℝ | N.IsFlow φ ∧ ∀ x y, ∃ n : ℕ, φ x y = n}
  have hfin : S.Finite := by
    refine (Set.finite_range fun g : V → V → Fin (B + 1) => fun x y => ((g x y : ℕ) : ℝ)).subset ?_
    rintro φ ⟨hφ, hint⟩
    choose n hn using hint
    refine ⟨fun x y => ⟨n x y, ?_⟩, ?_⟩
    · have h1 := hφ.le_cap x y
      rw [hn, hc] at h1
      have := hcB x y
      exact Nat.lt_succ_of_le ((Nat.cast_le.1 h1).trans this)
    · ext x y
      exact (hn x y).symm
  have hne : S.Nonempty := ⟨0, ⟨fun _ _ => le_rfl, fun x y => N.cap_nonneg x y, fun v _ _ => by simp [netOut]⟩,
    fun _ _ => ⟨0, by simp⟩⟩
  obtain ⟨φ, ⟨hφ, hint⟩, hmax⟩ := Set.exists_max_image S N.value hfin hne
  refine ⟨φ, hφ, hint, (isMax_iff_sink_not_labelled hφ).2 ?_⟩
  intro ht
  obtain ⟨p⟩ := exists_augPath (mem_labelled.1 ht)
  -- every residual capacity along the path is a positive integer, so one can augment by `1`
  have hle : ∀ i : Fin p.len, (1 : ℝ) ≤ N.residualCap φ (p.vert i.castSucc) (p.vert i.succ) := by
    intro i
    unfold residualCap
    rcases p.step i with ⟨h, hlt⟩ | ⟨h, hlt⟩
    · rw [ite_eq_left h]
      obtain ⟨a, ha⟩ := hint (p.vert i.castSucc) (p.vert i.succ)
      rw [ha, hc] at hlt ⊢
      have : a < c (p.vert i.castSucc) (p.vert i.succ) := by exact_mod_cast hlt
      have : (a : ℝ) + 1 ≤ c (p.vert i.castSucc) (p.vert i.succ) := by exact_mod_cast this
      linarith
    · rw [ite_eq_right (N.oriented _ _ h)]
      obtain ⟨a, ha⟩ := hint (p.vert i.succ) (p.vert i.castSucc)
      rw [ha] at hlt ⊢
      have : 0 < a := by exact_mod_cast hlt
      exact_mod_cast this
  obtain ⟨hψ, hv⟩ := N.augment hφ p zero_le_one hle
  have hψint : ∀ x y, ∃ n : ℕ, φ x y + N.pathChange p 1 x y = n := by
    intro x y
    obtain ⟨a, ha⟩ := hint x y
    have h0 := hψ.nonneg x y
    rcases N.pathChange_cases p 1 x y with h | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact ⟨a, by rw [h, ha, add_zero]⟩
    · exact ⟨a + 1, by rw [h, ha]; push_cast; ring⟩
    · simp only [h, ha] at h0 ⊢
      have : 1 ≤ a := by
        have : (1 : ℝ) ≤ a := by linarith
        exact_mod_cast this
      exact ⟨a - 1, by rw [Nat.cast_sub this]; push_cast; ring⟩
  have := hmax _ ⟨hψ, hψint⟩
  rw [hv] at this
  linarith

end Network

end UndergradKB.Combinatorics.Flow
